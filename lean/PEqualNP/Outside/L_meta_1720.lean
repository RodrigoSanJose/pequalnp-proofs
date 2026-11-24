import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1720.Degree

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- The degree pass follows the gate-list fold in L_meta_1622.

theorem getD_app_lt {α : Type} (l l' : List α) (d : α) (i : ℕ) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_app_len {α : Type} (l : List α) (a d : α) : (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

def dflt : Gate := Gate.mk GateOp.or []

def run {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [f w g]) w

theorem run_snoc {α : Type} (f : List α → Gate → α) (gs : List Gate) (g : Gate) (w : List α) :
    run f (gs ++ [g]) w = run f gs w ++ [f (run f gs w) g] := by
  simp [run]

theorem run_length {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) :
    (run f gs w).length = w.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem run_lt {α : Type} (f : List α → Gate → α) (gs : List Gate) (w : List α) (d : α) (i : ℕ)
    (h : i < w.length) : (run f gs w).getD i d = w.getD i d := by
  induction gs using List.reverseRecOn with
  | nil => rfl
  | append_singleton gs g ih =>
    rw [run_snoc, getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih]

theorem run_gate {α : Type} (f : List α → Gate → α) (d : α)
    (hf : ∀ (g : Gate) (w w' : List α), (∀ i ∈ g.inputs, w.getD i d = w'.getD i d) → f w g = f w' g)
    (gs : List Gate) (w : List α) (L : ℕ) (hL : w.length = L) (k : ℕ) (hk : k < gs.length)
    (hr : ∀ i ∈ (gs.getD k dflt).inputs, i < L + k) :
    (run f gs w).getD (L + k) d = f (run f gs w) (gs.getD k dflt) := by
  subst hL
  induction gs using List.reverseRecOn with
  | nil => simp at hk
  | append_singleton gs g ih =>
    rw [run_snoc]
    rcases Nat.lt_or_ge k gs.length with h | h
    · have e : (gs ++ [g]).getD k dflt = gs.getD k dflt := getD_app_lt _ _ _ _ h
      rw [e] at hr ⊢
      rw [getD_app_lt _ _ _ _ (by rw [run_length]; omega), ih h hr]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)
    · have hk' : k = gs.length := by
        simp only [List.length_append, List.length_singleton] at hk
        omega
      subst hk'
      have e : (gs ++ [g]).getD gs.length dflt = g := getD_app_len _ _ _
      rw [e] at hr ⊢
      have e2 : w.length + gs.length = (run f gs w).length := (run_length f gs w).symm
      rw [e2, getD_app_len]
      apply hf
      intro i hi
      symm
      exact getD_app_lt _ _ _ _ (by rw [run_length]; have := hr i hi; omega)

def ldf (d : List ℕ) (g : Gate) : ℕ := g.lineDegree d

theorem ldf_congr (g : Gate) (w w' : List ℕ)
    (h : ∀ i ∈ g.inputs, w.getD i 0 = w'.getD i 0) : ldf w g = ldf w' g := by
  unfold ldf Gate.lineDegree
  rw [List.map_congr_left h]

theorem deg_run (C : Circuit) (N : ℕ) (M : Finset ℕ) : C.lineDegrees N M =
    run ldf C.gates ((List.range N).map fun i => if i ∈ M then 1 else 0) := rfl

theorem deg_input (C : Circuit) (N : ℕ) (M : Finset ℕ) (w : ℕ) (h : w < N) :
    (C.lineDegrees N M).getD w 0 = if w ∈ M then 1 else 0 := by
  rw [deg_run, run_lt _ _ _ _ _ (by simpa using h),
    List.getD_eq_getElem _ _ (by simpa using h)]
  simp

theorem deg_gate (C : Circuit) (N : ℕ) (M : Finset ℕ) (hR : ReadsBack N C) (k : ℕ)
    (hk : k < C.gates.length) :
    (C.lineDegrees N M).getD (N + k) 0 = (C.gates.getD k dflt).lineDegree (C.lineDegrees N M) := by
  rw [deg_run]
  exact run_gate ldf 0 ldf_congr C.gates _ N (by simp) k hk (hR k hk)

theorem gate_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : C.gates.getD k dflt ∈ C.gates := by
  rw [List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem _

abbrev Mon2 (C : Circuit) :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

abbrev pdeg (N : ℕ) (C : Circuit) (w : ℕ) :=
  (C.lineDegrees (N + N) (Finset.range N)).getD w 0

abbrev ldeg (N : ℕ) (C : Circuit) (w : ℕ) :=
  (C.lineDegrees (N + N) (Finset.Ico N (N + N))).getD w 0

theorem pdeg_input {N : ℕ} {C : Circuit} {i : ℕ} (hi : i < N + N) :
    pdeg N C i = if i < N then 1 else 0 := by
  simpa using deg_input C (N + N) (Finset.range N) i hi

theorem gate_inputs_pair {C : Circuit} (hm : Mon2 C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] := by
  have hmem : gateAt C j ∈ C.gates := gate_mem C j hj
  have h := (hm _ hmem).2
  rcases he : (gateAt C j).inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [he] at h
  · simp [he] at h
  · exact ⟨a, b, rfl⟩
  · simp [he] at h

theorem pdeg_gate_zero_iff {N : ℕ} {C : Circuit} (hm : Mon2 C) (hr : ReadsBack (N + N) C)
    {j : ℕ} (hj : j < C.gates.length) :
    pdeg N C (N + N + j) = 0 ↔ ∀ i ∈ (gateAt C j).inputs, pdeg N C i = 0 := by
  obtain ⟨a, b, hin⟩ := gate_inputs_pair hm hj
  obtain ⟨hop, _⟩ := hm _ (show gateAt C j ∈ C.gates from gate_mem C j hj)
  have h := deg_gate C (N + N) (Finset.range N) hr j hj
  change pdeg N C (N + N + j) = (gateAt C j).lineDegree _ at h
  rw [h]
  rcases hop with hOp | hOp
  · simp [Gate.lineDegree, hOp, hin, Nat.add_eq_zero_iff]
  · simp [Gate.lineDegree, hOp, hin]

end PEqualNP.Outside.L_meta_1720.Degree

namespace PEqualNP.Outside.L_meta_1720.Count

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1720.Degree

abbrev purePoint (N : ℕ) (C : Circuit) (j : ℕ) := ldeg N C (N + N + j) = 0

abbrev mixed (N : ℕ) (C : Circuit) (j : ℕ) :=
  0 < pdeg N C (N + N + j) ∧ 0 < ldeg N C (N + N + j)

abbrev Boundary (N : ℕ) (C : Circuit) (i : ℕ) :=
  pdeg N C i = 0 ∧ 0 < ldeg N C i ∧
    ∃ j < C.gates.length, i ∈ (gateAt C j).inputs ∧ mixed N C j

def frontier (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range (N + N + C.gates.length)).filter (Boundary N C)

def pointGates (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (purePoint N C)

def mixedGates (N : ℕ) (C : Circuit) : Finset ℕ :=
  (Finset.range C.gates.length).filter (mixed N C)

theorem mem_frontier {N : ℕ} {C : Circuit} (hr : ReadsBack (N + N) C) {i : ℕ} :
    i ∈ frontier N C ↔ Boundary N C i := by
  simp only [frontier, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
  rintro ⟨_, _, j, hj, hi, _⟩
  have := hr j hj i hi
  omega

theorem pointGates_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j | j < C.gates.length ∧ purePoint N C j} = (pointGates N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [pointGates]

theorem mixedGates_ncard (N : ℕ) (C : Circuit) :
    Set.ncard {j | j < C.gates.length ∧ mixed N C j} = (mixedGates N C).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [mixedGates]

theorem point_mixed_budget (N : ℕ) (C : Circuit) :
    (pointGates N C).card + (mixedGates N C).card ≤ C.size := by
  have hdis : Disjoint (pointGates N C) (mixedGates N C) := by
    rw [Finset.disjoint_left]
    intro j hp hm
    simp only [pointGates, mixedGates, Finset.mem_filter, Finset.mem_range] at hp hm
    have hz := hp.2
    have hpos := hm.2.2
    omega
  rw [← Finset.card_union_of_disjoint hdis, Circuit.size, ← Finset.card_range C.gates.length]
  apply Finset.card_le_card (Finset.union_subset ?_ ?_)
  · exact Finset.filter_subset _ _
  · exact Finset.filter_subset _ _

theorem point_free_operand_unique {N : ℕ} {C : Circuit} (hm : Mon2 C)
    (hr : ReadsBack (N + N) C) {j i i' : ℕ} (hj : j < C.gates.length)
    (hpos : 0 < pdeg N C (N + N + j)) (hi : i ∈ (gateAt C j).inputs)
    (hi' : i' ∈ (gateAt C j).inputs) (hzero : pdeg N C i = 0)
    (hzero' : pdeg N C i' = 0) : i = i' := by
  by_contra hne
  obtain ⟨a, b, hab⟩ := gate_inputs_pair hm hj
  have hz : ∀ w ∈ (gateAt C j).inputs, pdeg N C w = 0 := by
    rw [hab] at hi hi' ⊢
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi hi' ⊢
    rcases hi with rfl | rfl <;> rcases hi' with rfl | rfl
    · exact False.elim (hne rfl)
    · rintro w (rfl | rfl)
      · exact hzero
      · exact hzero'
    · rintro w (rfl | rfl)
      · exact hzero'
      · exact hzero
    · exact False.elim (hne rfl)
  have := (pdeg_gate_zero_iff hm hr hj).2 hz
  omega

theorem frontier_budget {N : ℕ} {C : Circuit} (hm : Mon2 C) (hr : ReadsBack (N + N) C) :
    (frontier N C).card ≤ (mixedGates N C).card := by
  classical
  have h : ∀ i ∈ frontier N C, ∃ j ∈ mixedGates N C, i ∈ (gateAt C j).inputs := by
    intro i hi
    obtain ⟨_, _, j, hj, hin, hmix⟩ := (mem_frontier hr).1 hi
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hmix⟩, hin⟩
  let pick (i : ℕ) : ℕ := if hi : i ∈ frontier N C then Classical.choose (h i hi) else 0
  have hp (i : ℕ) (hi : i ∈ frontier N C) :
      pick i ∈ mixedGates N C ∧ i ∈ (gateAt C (pick i)).inputs := by
    simpa only [pick, dite_eq_left hi] using Classical.choose_spec (h i hi)
  apply Finset.card_le_card_of_injOn pick (fun i hi => (hp i hi).1)
  intro i hi i' hi' he
  obtain ⟨hj, hin⟩ := hp i hi
  have hin' := (hp i' hi').2
  rw [← he] at hin'
  obtain ⟨hjlt, hmix⟩ := Finset.mem_filter.1 hj
  exact point_free_operand_unique hm hr (Finset.mem_range.1 hjlt) hmix.1 hin hin'
    ((mem_frontier hr).1 hi).1 ((mem_frontier hr).1 hi').1

end PEqualNP.Outside.L_meta_1720.Count

namespace PEqualNP.Outside.L_meta_1720.Semantic


abbrev Row (N : ℕ) := Fin N → Bool

def unit {N : ℕ} (p : Fin N) : Row N :=
  fun a => decide (a = p)

def weight {N : ℕ} (x : Row N) : ℕ :=
  (Finset.univ.filter fun p => x p = true).card

theorem weight_unit {N : ℕ} (p : Fin N) : weight (unit p) = 1 := by
  have h : (Finset.univ.filter fun a => unit p a = true) = {p} := by
    ext a
    simp [unit]
  simp [weight, h]

theorem weight_zero (N : ℕ) : weight (fun _ : Fin N => false) = 0 := by
  simp [weight]

def support {N : ℕ} (f : Row N → Bool) : Finset (Fin N) :=
  Finset.univ.filter fun p => f (unit p) = true

theorem mem_support {N : ℕ} (f : Row N → Bool) (p : Fin N) :
    p ∈ support f ↔ f (unit p) = true := by
  simp [support]

noncomputable def xBucket {N : ℕ} (E : Finset ℕ)
    (coeff line : ℕ → Row N → Bool) (l : Fin N) : Finset ℕ := by
  classical
  exact E.filter fun h => support (line h) = {l} ∧ (support (coeff h)).Nonempty

def yBucket {N : ℕ} (E : Finset ℕ)
    (coeff line : ℕ → Row N → Bool) (p : Fin N) : Finset ℕ :=
  E.filter fun h => 2 ≤ (support (line h)).card ∧ support (coeff h) = {p}

def fires {N : ℕ} (f : ℕ → Row N → Bool) (B : Finset ℕ) (x : Row N) : Prop :=
  ∃ h ∈ B, f h x = true

private theorem singleton_of_mem_of_card_le_one {α : Type*} [DecidableEq α]
    {s : Finset α} {a : α} (ha : a ∈ s) (hc : s.card ≤ 1) : s = {a} := by
  ext b
  exact ⟨fun hb => Finset.mem_singleton.mpr ((Finset.card_le_one.mp hc) b hb a ha),
    fun hb => (Finset.mem_singleton.mp hb).symm ▸ ha⟩

theorem bucket_spec {N k : ℕ} (I : Fin N → Fin N → Prop)
    (E : Finset ℕ) (H : Set ℕ) (coeff line : ℕ → Row N → Bool)
    (F : Row N → Row N → Bool) (hk : 1 ≤ k)
    (unique : ∀ a b : Fin N, a ≠ b → ∃! l : Fin N, I a l ∧ I b l)
    (split : ∀ x y, F x y = true ↔
      ∃ h ∈ E, line h y = true ∧ (h ∈ H ∨ coeff h x = true))
    (positive : ∀ p l, I p l → F (unit p) (unit l) = true)
    (sound : ∀ x y, weight y ≤ k →
      (¬ ∃ p l, I p l ∧ x p = true ∧ y l = true) → F x y = false) :
    (∀ l, xBucket E coeff line l ⊆ E) ∧
    (∀ p, yBucket E coeff line p ⊆ E) ∧
    (Pairwise fun a b => Disjoint (xBucket E coeff line a) (xBucket E coeff line b)) ∧
    (Pairwise fun a b => Disjoint (yBucket E coeff line a) (yBucket E coeff line b)) ∧
    (∀ l p, Disjoint (xBucket E coeff line l) (yBucket E coeff line p)) ∧
    (∀ l h, h ∈ xBucket E coeff line l → ∃ p, coeff h (unit p) = true) ∧
    (∀ l p, fires coeff (xBucket E coeff line l) (unit p) → I p l) ∧
    (∀ l x, (∀ p, I p l → x p = false) → ¬ fires coeff (xBucket E coeff line l) x) ∧
    (∀ p l, fires line (yBucket E coeff line p) (unit l) → I p l) ∧
    (∀ p y, weight y ≤ k → (∀ l, I p l → y l = false) →
      ¬ fires line (yBucket E coeff line p) y) ∧
    (∀ p l, I p l → fires coeff (xBucket E coeff line l) (unit p) ∨
      fires line (yBucket E coeff line p) (unit l)) := by
  classical
  have xmem {l : Fin N} {h : ℕ} (hm : h ∈ xBucket E coeff line l) :
      h ∈ E ∧ support (line h) = {l} ∧ (support (coeff h)).Nonempty :=
    Finset.mem_filter.mp hm
  have ymem {p : Fin N} {h : ℕ} (hm : h ∈ yBucket E coeff line p) :
      h ∈ E ∧ 2 ≤ (support (line h)).card ∧ support (coeff h) = {p} :=
    Finset.mem_filter.mp hm
  have rect {h : ℕ} (he : h ∈ E) {p l : Fin N}
      (hp : p ∈ support (coeff h)) (hl : l ∈ support (line h)) : I p l := by
    by_contra hn
    have yes := (split (unit p) (unit l)).mpr
      ⟨h, he, (mem_support _ _).mp hl, .inr ((mem_support _ _).mp hp)⟩
    have no := sound (unit p) (unit l) (by rwa [weight_unit]) (by simpa [unit] using hn)
    rw [no] at yes
    cases yes
  have notConstant {h : ℕ} (he : h ∈ E) {l : Fin N}
      (hl : l ∈ support (line h)) : h ∉ H := by
    intro hh
    have yes := (split (fun _ => false) (unit l)).mpr
      ⟨h, he, (mem_support _ _).mp hl, .inl hh⟩
    have no := sound (fun _ => false) (unit l) (by rwa [weight_unit]) (by simp)
    rw [no] at yes
    cases yes
  have pointSmall {h : ℕ} (he : h ∈ E) (big : 2 ≤ (support (line h)).card) :
      (support (coeff h)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra ne
    obtain ⟨l, hl, m, hm, diff⟩ := Finset.one_lt_card.mp big
    obtain ⟨q, _, hq⟩ := unique a b ne
    have el := hq l ⟨rect he ha hl, rect he hb hl⟩
    have em := hq m ⟨rect he ha hm, rect he hb hm⟩
    exact diff (el.trans em.symm)
  have xpoint {l : Fin N} {h : ℕ} (hm : h ∈ xBucket E coeff line l) :
      line h (unit l) = true := by
    apply (mem_support _ _).mp
    simp [(xmem hm).2.1]
  have ypoint {p : Fin N} {h : ℕ} (hm : h ∈ yBucket E coeff line p) :
      coeff h (unit p) = true := by
    apply (mem_support _ _).mp
    simp [(ymem hm).2.2]
  refine ⟨(fun _ _ h => (xmem h).1), (fun _ _ h => (ymem h).1),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b ne
    apply Finset.disjoint_left.mpr
    intro h ha hb
    have eq := ((xmem ha).2.1).symm.trans (xmem hb).2.1
    have hm : a ∈ ({b} : Finset (Fin N)) := eq ▸ Finset.mem_singleton_self a
    exact ne (Finset.mem_singleton.mp hm)
  · intro a b ne
    apply Finset.disjoint_left.mpr
    intro h ha hb
    have eq := ((ymem ha).2.2).symm.trans (ymem hb).2.2
    have hm : a ∈ ({b} : Finset (Fin N)) := eq ▸ Finset.mem_singleton_self a
    exact ne (Finset.mem_singleton.mp hm)
  · intro l p
    apply Finset.disjoint_left.mpr
    intro h hx hy
    have hc := (ymem hy).2.1
    simp [(xmem hx).2.1] at hc
  · intro l h hm
    obtain ⟨p, hp⟩ := (xmem hm).2.2
    exact ⟨p, (mem_support _ _).mp hp⟩
  · rintro l p ⟨h, hm, hp⟩
    exact rect (xmem hm).1 ((mem_support _ _).mpr hp) ((mem_support _ _).mpr (xpoint hm))
  · intro l x noInc
    rintro ⟨h, hm, hx⟩
    have yes := (split x (unit l)).mpr ⟨h, (xmem hm).1, xpoint hm, .inr hx⟩
    have no := sound x (unit l) (by rwa [weight_unit]) (by
      rintro ⟨p,q,hpq,hp,hq⟩
      have eq : q = l := of_decide_eq_true hq
      subst q
      rw [noInc p hpq] at hp
      cases hp)
    rw [no] at yes
    cases yes
  · rintro p l ⟨h, hm, hl⟩
    exact rect (ymem hm).1 ((mem_support _ _).mpr (ypoint hm)) ((mem_support _ _).mpr hl)
  · intro p y hy noInc
    rintro ⟨h, hm, hl⟩
    have yes := (split (unit p) y).mpr ⟨h, (ymem hm).1, hl, .inr (ypoint hm)⟩
    have no := sound (unit p) y hy (by
      rintro ⟨q,l,hql,hq,hl⟩
      have eq : q = p := of_decide_eq_true hq
      subst q
      rw [noInc l hql] at hl
      cases hl)
    rw [no] at yes
    cases yes
  · intro p l hp
    obtain ⟨h, he, hl, hx⟩ := (split (unit p) (unit l)).mp (positive p l hp)
    have hlSupport := (mem_support _ _).mpr hl
    have hConst := notConstant he hlSupport
    have hx' := hx.resolve_left hConst
    have hpSupport : p ∈ support (coeff h) := (mem_support _ _).mpr hx'
    by_cases big : 2 ≤ (support (line h)).card
    · have single := singleton_of_mem_of_card_le_one hpSupport (pointSmall he big)
      exact .inr ⟨h, Finset.mem_filter.mpr ⟨he, big, single⟩, hl⟩
    · have single := singleton_of_mem_of_card_le_one hlSupport (by omega)
      exact .inl ⟨h, Finset.mem_filter.mpr ⟨he, single, ⟨p, hpSupport⟩⟩, hx'⟩

end PEqualNP.Outside.L_meta_1720.Semantic

namespace PEqualNP.Outside.L_meta_1720.Setup

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1720.Degree PEqualNP.Outside.L_meta_1720.Count
open PEqualNP.Outside.L_meta_1720.Semantic

abbrev value {N : ℕ} (C : Circuit) (x : Row N) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

abbrev evalPair {N : ℕ} (C : Circuit) (x y : Row N) : Bool :=
  circuitFun (N + N) C (Fin.append x y)

abbrev Indep (N : ℕ) (C : Circuit) :=
  ∀ (w : ℕ) (xa xb ya yb : Row N),
    (ldeg N C w = 0 → value C (Fin.append xa ya) w = value C (Fin.append xa yb) w) ∧
    (pdeg N C w = 0 → value C (Fin.append xa ya) w = value C (Fin.append xb ya) w)

abbrev Transposed (N : ℕ) (C : Circuit) :=
  ∃ (X : Circuit) (ph : ℕ → ℕ) (H : Set ℕ), (Mon2 X ∧ ReadsBack N X) ∧
    X.size ≤ Set.ncard {j | j < C.gates.length ∧ purePoint N C j} +
      3 * Set.ncard {j | j < C.gates.length ∧ mixed N C j} ∧
    ∀ x y : Row N, evalPair C x y = true ↔ evalPair C x (fun _ => false) = true ∨
      ∃ h, Boundary N C h ∧ value C (Fin.append (fun _ : Fin N => false) y) h = true ∧
        (h ∈ H ∨ value X x (ph h) = true)

abbrev GoodInputs {N : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit) :=
  ∀ p l, I p l → evalPair C (unit p) (unit l) = true

abbrev ForbiddenInputs {N : ℕ} (I : Fin N → Fin N → Prop) (k : ℕ) (C : Circuit) :=
  ∀ x y : Row N, weight y ≤ k →
    (¬ ∃ p l, I p l ∧ x p = true ∧ y l = true) → evalPair C x y = false

abbrev Target {N : ℕ} (I : Fin N → Fin N → Prop) (k : ℕ) (C : Circuit) :=
  ∃ (X Y : Circuit) (ps rh : Fin N → ℕ),
    (Mon2 X ∧ ReadsBack N X) ∧ (Mon2 Y ∧ ReadsBack N Y) ∧ X.size + Y.size ≤ 5 * C.size ∧
    (∀ (l p : Fin N), value X (unit p) (ps l) = true → I p l) ∧
    (∀ (l : Fin N) (x : Row N), (∀ p, I p l → x p = false) → value X x (ps l) = false) ∧
    (∀ (p l : Fin N), value Y (unit l) (rh p) = true → I p l) ∧
    (∀ (p : Fin N) (y : Row N), weight y ≤ k → (∀ l, I p l → y l = false) →
      value Y y (rh p) = false) ∧
    (∀ p l, I p l → value X (unit p) (ps l) = true ∨ value Y (unit l) (rh p) = true)

theorem append_unit {N : ℕ} (p l : Fin N) :
    Fin.append (unit p) (unit l) = fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l) := by
  have hdis (a b : Fin N) : Fin.castAdd N a ≠ Fin.natAdd N b := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  funext i
  induction i using Fin.addCases with
  | left a => simp only [Fin.append_left, unit, hdis, Fin.castAdd_inj, or_false]
  | right b => simp only [Fin.append_right, unit, Ne.symm (hdis p b), Fin.natAdd_inj, false_or]

theorem positive_degrees {q N k : ℕ} {C : Circuit} {I : Fin N → Fin N → Prop} [DecidableRel I]
    (hn : N = q ^ 2 + q + 1)
    (lines : ∀ l : Fin N, (Finset.univ.filter fun p : Fin N => I p l).card = q + 1)
    (hk : 1 ≤ k) (pos : GoodInputs I C) (neg : ForbiddenInputs I k C)
    (indep : Indep N C) :
    0 < pdeg N C C.output ∧ 0 < ldeg N C C.output := by
  let l : Fin N := ⟨0, by omega⟩
  rcases Finset.card_pos.mp (show 0 < (Finset.univ.filter fun p : Fin N => I p l).card by
      rw [lines]; omega) with ⟨p, hp⟩
  have hpos := pos p l (Finset.mem_filter.mp hp).2
  have hnoPoints := neg (fun _ => false) (unit l) (by rwa [weight_unit]) (by simp)
  have hnoLines := neg (unit p) (fun _ => false) (by rw [weight_zero]; omega) (by simp)
  constructor
  · by_contra! hz
    have e := (indep C.output (unit p) (fun _ => false) (unit l) (unit l)).2
      (Nat.eq_zero_of_le_zero hz)
    change evalPair C (unit p) (unit l) = evalPair C (fun _ => false) (unit l) at e
    rw [hpos, hnoPoints] at e
    cases e
  · by_contra! hz
    have e := (indep C.output (unit p) (unit p) (unit l) (fun _ => false)).1
      (Nat.eq_zero_of_le_zero hz)
    change evalPair C (unit p) (unit l) = evalPair C (unit p) (fun _ => false) at e
    rw [hpos, hnoLines] at e
    cases e

theorem line_count_le_size (N : ℕ) (C : Circuit) :
    Set.ncard {j : ℕ | j < C.gates.length ∧ pdeg N C (N + N + j) = 0} ≤ C.size := by
  let L := (Finset.range C.gates.length).filter fun j => pdeg N C (N + N + j) = 0
  have hset : {j : ℕ | j < C.gates.length ∧ pdeg N C (N + N + j) = 0} = (L : Set ℕ) := by
    ext j
    simp [L]
  rw [hset, Set.ncard_coe_finset, Circuit.size, ← Finset.card_range C.gates.length]
  exact Finset.card_le_card (Finset.filter_subset _ _)

end PEqualNP.Outside.L_meta_1720.Setup

namespace PEqualNP.Outside.L_meta_1720.Line


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Legal (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

abbrev wire (C : Circuit) (inputs : List Bool) (w : ℕ) : Bool :=
  (C.wires inputs).getD w false

private def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private theorem run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (x ++ [_])).length = _
    rw [ih]
    simp
    omega

private theorem run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (h : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (x ++ [_])).getD w false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ h]

theorem input_wire (C : Circuit) (x : List Bool) (w : ℕ) (h : w < x.length) :
    wire C x w = x.getD w false := run_getD _ _ _ h

theorem gateAt_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := List.getD_eq_getElem _ _ hj

theorem gate_wire (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length)
    (hBack : ReadsBack x.length C) :
    wire C x (x.length + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => wire C x i) := by
  let pre := run (C.gates.take j) x
  let g := C.gates[j]
  have hPre : pre.length = x.length + j := by
    simp [pre, run_length, Nat.min_eq_left hj.le]
  have hSplit : C.wires x = run (g :: C.gates.drop (j+1)) pre := by
    change run C.gates x = _
    have hFold : run C.gates x = run (C.gates.drop j) pre := by
      simpa only [run, List.foldl_append, pre] using
        congrArg (fun gs : List Gate => run gs x) (List.take_append_drop j C.gates).symm
    rw [hFold]
    rw [List.drop_eq_getElem_cons hj]
  have hG : gateAt C j = g := gateAt_getElem C j hj
  have hInternal (i : ℕ) (hi : i ∈ g.inputs) : pre.getD i false = wire C x i := by
    have hlt := hBack j hj i (by rw [hG]; exact hi)
    change pre.getD i false = (C.wires x).getD i false
    rw [hSplit]
    exact (run_getD _ _ _ (hPre.symm ▸ hlt)).symm
  rw [hG]
  change (C.wires x).getD (x.length + j) false = _
  rw (occs := [1]) [hSplit]
  change (run (C.gates.drop (j+1)) (pre ++ [g.op.eval (g.inputs.map fun i => pre.getD i false)])).getD
    (x.length + j) false = _
  rw [run_getD _ _ _ (by simp [hPre]), List.getD_append_right _ _ _ _ (by rw [hPre])]
  simp only [hPre, Nat.sub_self, List.getD_cons_zero]
  rw [List.map_congr_left hInternal]

private def appendGate (C : Circuit) (g : Gate) : Circuit := ⟨C.gates ++ [g], C.output⟩

private theorem append_wire (C : Circuit) (g : Gate) (x : List Bool) (w : ℕ)
    (hw : w < x.length + C.gates.length) : wire (appendGate C g) x w = wire C x w := by
  change (run (C.gates ++ [g]) x).getD w false = (run C.gates x).getD w false
  rw [show run (C.gates ++ [g]) x = run [g] (run C.gates x) by simp [run, List.foldl_append]]
  exact run_getD _ _ _ (by rw [run_length]; exact hw)

private theorem append_here (C : Circuit) (g : Gate) (x : List Bool) :
    wire (appendGate C g) x (x.length + C.gates.length) =
      g.op.eval (g.inputs.map fun i => wire C x i) := by
  change (run (C.gates ++ [g]) x).getD (x.length + C.gates.length) false = _
  rw [show run (C.gates ++ [g]) x = run [g] (run C.gates x) by simp [run, List.foldl_append]]
  change ((run C.gates x) ++ [_]).getD (x.length + C.gates.length) false = _
  rw [List.getD_append_right _ _ _ _ (by rw [run_length])]
  simp [run_length]
  rfl

private theorem append_back (C : Circuit) (g : Gate) (n : ℕ) (hBack : ReadsBack n C)
    (hG : ∀ i ∈ g.inputs, i < n + C.gates.length) : ReadsBack n (appendGate C g) := by
  intro j hj i hi
  have hj' : j < C.gates.length + 1 := by simpa [appendGate] using hj
  by_cases h : j < C.gates.length
  · have he : gateAt (appendGate C g) j = gateAt C j := List.getD_append _ _ _ _ h
    exact hBack j h i (he ▸ hi)
  · have e : j = C.gates.length := by omega
    subst j
    have he : gateAt (appendGate C g) C.gates.length = g := by
      simp [gateAt, appendGate]
    exact hG i (he ▸ hi)

/-- Copy a predecessor-closed collection of wires to a reduced input space. The predicate is
checked only on existing wires, and raw inputs are mapped by the provided map. -/
theorem extractClosed {α : Type*} (sourceCount targetCount : ℕ) (C : Circuit)
    (keep : ℕ → Bool) (raw : ℕ → ℕ) (source target : α → List Bool)
    (sourceLen : ∀ x, (source x).length = sourceCount)
    (targetLen : ∀ x, (target x).length = targetCount)
    (rawOk : ∀ i < sourceCount, keep i = true → raw i < targetCount ∧
      ∀ x, (target x).getD (raw i) false = (source x).getD i false)
    (legal : Legal C) (back : ReadsBack sourceCount C)
    (closed : ∀ j < C.gates.length, keep (sourceCount+j) = true →
      ∀ i ∈ (gateAt C j).inputs, keep i = true) :
    ∃ Y : Circuit, ∃ ρ : ℕ → ℕ,
      (Legal Y ∧ ReadsBack targetCount Y) ∧
      Y.size = ((Finset.range C.gates.length).filter fun j => keep (sourceCount + j) = true).card ∧
      ∀ i < sourceCount + C.gates.length, keep i = true →
        ρ i < targetCount + Y.gates.length ∧ ∀ x, wire Y (target x) (ρ i) = wire C (source x) i := by
  have step (j : ℕ) (hj : j ≤ C.gates.length) :
      ∃ Y : Circuit, ∃ ρ : ℕ → ℕ,
        (Legal Y ∧ ReadsBack targetCount Y) ∧
        Y.size = ((Finset.range j).filter fun k => keep (sourceCount + k) = true).card ∧
        ∀ i < sourceCount + j, keep i = true →
          ρ i < targetCount + Y.gates.length ∧ ∀ x, wire Y (target x) (ρ i) = wire C (source x) i := by
    induction j with
    | zero =>
      refine ⟨⟨[],0⟩, raw, ⟨by simp [Legal], by simp [ReadsBack]⟩, by simp [Circuit.size], ?_⟩
      · intro i hi hk
        obtain ⟨hr, hrValue⟩ := rawOk i (by omega) hk
        refine ⟨by simpa using hr, ?_⟩
        intro x
        rw [input_wire _ _ _ (by rw [targetLen]; exact hr), input_wire _ _ _ (by rw [sourceLen]; omega)]
        exact hrValue x
    | succ j ih =>
      have hJ : j < C.gates.length := by omega
      obtain ⟨Y, ρ, ⟨hLegal,hBack⟩, hSize, hρ⟩ := ih (by omega)
      by_cases hKeep : keep (sourceCount + j) = true
      · let g := gateAt C j
        let g' : Gate := ⟨g.op, g.inputs.map ρ⟩
        let Y' := appendGate Y g'
        let ρ' := Function.update ρ (sourceCount+j) (targetCount+Y.gates.length)
        have hg : g ∈ C.gates := by
          rw [show g = C.gates[j] from gateAt_getElem C j hJ]
          exact List.getElem_mem hJ
        have hgLegal : (g'.op = .and ∨ g'.op = .or) ∧ g'.inputs.length = 2 := by
          simpa [g'] using legal g hg
        have hRead (i : ℕ) (hi : i ∈ g.inputs) :=
          hρ i (back j hJ i hi) (closed j hJ hKeep i hi)
        have hgBack (i : ℕ) (hi : i ∈ g'.inputs) : i < targetCount + Y.gates.length := by
          obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hi
          exact (hRead w hw).1
        have hYLength : Y'.gates.length = Y.gates.length + 1 := by simp [Y', appendGate]
        refine ⟨Y', ρ', ⟨?_, append_back Y g' targetCount hBack hgBack⟩, ?_, ?_⟩
        · intro g₀ h₀
          have hMem : g₀ ∈ Y.gates ∨ g₀ = g' := by simpa [Y', appendGate] using h₀
          rcases hMem with h₀ | rfl
          · exact hLegal g₀ h₀
          · exact hgLegal
        · change Y'.gates.length = _
          rw [hYLength]
          simp [Finset.range_add_one, Finset.filter_insert, hKeep, ← hSize, Circuit.size]
        · intro i hi hk
          by_cases hEq : i = sourceCount + j
          · subst i
            rw [show ρ' (sourceCount+j) = targetCount + Y.gates.length by simp [ρ']]
            refine ⟨by omega, ?_⟩
            intro x
            have hV := gate_wire C (source x) j hJ (sourceLen x ▸ back : ReadsBack (source x).length C)
            rw [sourceLen x] at hV
            have hYV := append_here Y g' (target x)
            rw [targetLen x] at hYV
            rw [show Y' = appendGate Y g' from rfl, hYV, hV]
            change g.op.eval ((g.inputs.map ρ).map (fun w => wire Y (target x) w)) = _
            rw [List.map_map]
            congr 1
            exact List.map_congr_left (fun w hw => (hRead w hw).2 x)
          · have hLt : i < sourceCount + j := by omega
            obtain ⟨hBound,hValue⟩ := hρ i hLt hk
            have he : ρ' i = ρ i := Function.update_of_ne hEq _ _
            rw [he]
            refine ⟨by omega, ?_⟩
            intro x
            exact (append_wire Y g' (target x) (ρ i) (by rw [targetLen]; exact hBound)).trans (hValue x)
      · refine ⟨Y, ρ, ⟨hLegal,hBack⟩, ?_, ?_⟩
        · simpa [Finset.range_add_one, Finset.filter_insert, hKeep] using hSize
        · intro i hi hk
          have hLt : i < sourceCount + j := by
            by_contra h
            have he : i = sourceCount+j := by omega
            exact hKeep (by simpa only [← he] using hk)
          exact hρ i hLt hk
  exact step _ le_rfl

end PEqualNP.Outside.L_meta_1720.Line

namespace PEqualNP.Outside.L_meta_1720.Line


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1720.Degree

private theorem ofFn_split {N : ℕ} (y : Fin N → Bool) :
    List.ofFn (Fin.append (fun _ : Fin N => false) y) =
      List.ofFn (fun _ : Fin N => false) ++ List.ofFn y := by
  rw [List.ofFn_add]
  congr 1
  · congr 1
    funext i
    exact Fin.append_left _ _ i
  · congr 1
    funext i
    exact Fin.append_right _ _ i

/-- Keep every gate with point degree zero and relabel the line inputs to `Fin N`. -/
theorem lineExtract (N : ℕ) (C : Circuit) (hm : Mon2 C) (hr : ReadsBack (N+N) C) :
    ∃ Y : Circuit, ∃ ρ : ℕ → ℕ,
      (Legal Y ∧ ReadsBack N Y) ∧
      Y.size = Set.ncard {j : ℕ | j < C.gates.length ∧ pdeg N C (N+N+j) = 0} ∧
      ∀ w < N+N+C.gates.length, pdeg N C w = 0 →
        ρ w < N + Y.gates.length ∧ ∀ y : Fin N → Bool,
          wire Y (List.ofFn y) (ρ w) = wire C (List.ofFn (Fin.append (fun _ : Fin N => false) y)) w := by
  let keep (w : ℕ) := decide (pdeg N C w = 0)
  let src (y : Fin N → Bool) := List.ofFn (Fin.append (fun _ : Fin N => false) y)
  let dst (y : Fin N → Bool) := List.ofFn y
  have hSrc (y : Fin N → Bool) : (src y).length = N+N := by simp [src]
  have hDst (y : Fin N → Bool) : (dst y).length = N := by simp [dst]
  have hRaw (i : ℕ) (hi : i < N+N) (hk : keep i = true) : i-N < N ∧
      ∀ y, (dst y).getD (i-N) false = (src y).getD i false := by
    have hDegree : pdeg N C i = 0 := of_decide_eq_true hk
    rw [pdeg_input hi] at hDegree
    have hLower : N ≤ i := by
      by_contra h
      simp [show i < N by omega] at hDegree
    refine ⟨by omega, ?_⟩
    intro y
    unfold src dst
    rw [ofFn_split, List.getD_append_right _ _ _ _ (by simpa using hLower)]
    simp
  have hClosed (j : ℕ) (hj : j < C.gates.length) (hk : keep (N+N+j) = true) :
      ∀ i ∈ (gateAt C j).inputs, keep i = true := by
    intro i hi
    apply decide_eq_true
    exact (pdeg_gate_zero_iff hm hr hj).mp (of_decide_eq_true hk) i hi
  obtain ⟨Y,ρ,hLegal,hSize,hValue⟩ := extractClosed (N+N) N C keep (·-N) src dst
    hSrc hDst hRaw hm hr hClosed
  refine ⟨Y,ρ,hLegal,?_,?_⟩
  · let S := (Finset.range C.gates.length).filter (fun j => keep (N+N+j) = true)
    have hS : (S : Set ℕ) = {j : ℕ | j < C.gates.length ∧ pdeg N C (N+N+j) = 0} := by
      ext j
      simp [S, keep]
    rw [← hS, Set.ncard_coe_finset]
    exact hSize
  · intro i hi hp
    exact hValue i hi (decide_eq_true hp)

end PEqualNP.Outside.L_meta_1720.Line

namespace PEqualNP.Outside.L_meta_1720.Line


/-- Separate point and line pools charge each shared boundary wire at most once. -/
theorem bucket_pool_budget {N : ℕ} (A B : Fin N → Finset ℕ) (E : Finset ℕ)
    (hA : ∀ l, A l ⊆ E) (hB : ∀ p, B p ⊆ E)
    (hCross : ∀ l p, Disjoint (A l) (B p)) :
    (∀ l, A l ⊆ Finset.univ.biUnion A) ∧ (∀ p, B p ⊆ Finset.univ.biUnion B) ∧
      (Finset.univ.biUnion A).card + (Finset.univ.biUnion B).card ≤ E.card := by
  have hDisjoint : Disjoint (Finset.univ.biUnion A) (Finset.univ.biUnion B) := by
    apply Finset.disjoint_left.mpr
    intro w hwA hwB
    obtain ⟨l, _, hwA⟩ := Finset.mem_biUnion.mp hwA
    obtain ⟨p, _, hwB⟩ := Finset.mem_biUnion.mp hwB
    exact Finset.disjoint_left.mp (hCross l p) hwA hwB
  refine ⟨fun l w hw => Finset.mem_biUnion.mpr ⟨l, Finset.mem_univ l, hw⟩,
    fun p w hw => Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ p, hw⟩, ?_⟩
  rw [← Finset.card_union_of_disjoint hDisjoint]
  apply Finset.card_le_card
  intro w hw
  rcases Finset.mem_union.mp hw with h | h
  · obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp h
    exact hA l hl
  · obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.mp h
    exact hB p hp

end PEqualNP.Outside.L_meta_1720.Line

namespace PEqualNP.Outside.L_meta_1720.OrSupport


open PEqualNP.CircuitLowerBounds

/-- An OR chain whose first gate is at wire `start`: gate `j` reads the previous gate (for
`j = 0`, the wire `first`) and the wire `rest[j]`. One gate per entry of `rest`. -/
def orChain (start first : ℕ) (rest : List ℕ) : List Gate :=
  rest.foldl
    (fun gs v => gs ++ [⟨GateOp.or, [if gs.length = 0 then first else start + gs.length - 1, v]⟩])
    []

/-- The wire at the end of `orChain start first rest`. -/
def chainOut (start first : ℕ) (rest : List ℕ) : ℕ :=
  if rest.length = 0 then first else start + rest.length - 1

/-- The wires after running the gates `gs` on the wire list `w`. -/
def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (a b : List Gate) (w : List Bool) : run (a ++ b) w = run b (run a w) := by
  unfold run; rw [List.foldl_append]

theorem run_nil (w : List Bool) : run [] w = w := rfl

theorem run_singleton (g : Gate) (w : List Bool) :
    run [g] w = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)] := rfl

theorem run_prefix (gs : List Gate) :
    ∀ w : List Bool, ∃ t, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, ?_⟩
    · rw [show g :: gs = [g] ++ gs from rfl, run_append, run_singleton, ht]; simp
    · simp [hl]

theorem run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht, List.length_append, hl]

theorem getD_run (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht]; simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem getD_snoc_length (l : List Bool) (a : Bool) : (l ++ [a]).getD l.length false = a := by
  simp

theorem eval_or2 (a b : Bool) : GateOp.eval GateOp.or [a, b] = (a || b) := by
  cases a <;> cases b <;> rfl

theorem any_congr_mem {α : Type} (l : List α) (p q : α → Bool) (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem orChain_snoc_aux (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++
      [⟨GateOp.or, [if (orChain s f r).length = 0 then f else s + (orChain s f r).length - 1, v]⟩] := by
  unfold orChain; rw [List.foldl_append]; rfl

theorem orChain_length (s f : ℕ) (r : List ℕ) : (orChain s f r).length = r.length := by
  induction r using List.reverseRecOn with
  | nil => rfl
  | append_singleton r v ih => rw [orChain_snoc_aux]; simp [ih]

theorem orChain_snoc (s f : ℕ) (r : List ℕ) (v : ℕ) :
    orChain s f (r ++ [v]) = orChain s f r ++ [⟨GateOp.or, [chainOut s f r, v]⟩] := by
  rw [orChain_snoc_aux, orChain_length]; rfl

theorem orChain_ops (s f : ℕ) (r : List ℕ) :
    ∀ g ∈ orChain s f r, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction r using List.reverseRecOn with
  | nil => intro g hg; simp [orChain] at hg
  | append_singleton r v ih =>
    intro g hg
    rw [orChain_snoc, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · exact ⟨rfl, rfl⟩

theorem chainOut_lt (s f : ℕ) (r : List ℕ) (hf : f < s) : chainOut s f r < s + r.length := by
  unfold chainOut; split <;> omega

theorem orChain_eval (s f : ℕ) (r : List ℕ) (w : List Bool) (hw : w.length = s) (_hf : f < s)
    (hr : ∀ v ∈ r, v < s) :
    (run (orChain s f r) w).getD (chainOut s f r) false =
      (w.getD f false || r.any (fun v => w.getD v false)) := by
  induction r using List.reverseRecOn with
  | nil => simp [orChain, run_nil, chainOut]
  | append_singleton r v ih =>
    have hr' : ∀ u ∈ r, u < s := fun u hu => hr u (List.mem_append_left _ hu)
    have hv : v < s := hr v (by simp)
    rw [orChain_snoc, run_append, run_singleton]
    have hlen : (run (orChain s f r) w).length = s + r.length := by
      rw [run_length, orChain_length, hw]
    have hco : chainOut s f (r ++ [v]) = (run (orChain s f r) w).length := by
      rw [hlen]; simp [chainOut]
    rw [hco, getD_snoc_length]
    have hv' : (run (orChain s f r) w).getD v false = w.getD v false :=
      getD_run _ _ _ (by omega)
    simp only [List.map_cons, List.map_nil, eval_or2]
    rw [ih hr', hv', List.any_append]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

end PEqualNP.Outside.L_meta_1720.OrSupport

namespace PEqualNP.Outside.L_meta_1720


open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1720.OrSupport

/-- Exactly binary AND and OR gates. -/
abbrev BucketBinary (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2

private abbrev value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

private theorem value_beyond {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (h : n + C.size ≤ w) : value C x w = false := by
  apply List.getD_eq_default
  simpa [wires_eq, run_length, Circuit.size] using h

private theorem prefix_value {n : ℕ} {C D : Circuit} (hp : C.gates <+: D.gates)
    (x : Fin n → Bool) (w : ℕ) (h : w < n + C.size) :
    value D x w = value C x w := by
  obtain ⟨tail, htail⟩ := hp
  simp only [value, wires_eq, ← htail, run_append]
  apply getD_run
  simpa [run_length, Circuit.size] using h

private theorem chain_back (s f : ℕ) (r : List ℕ) (hf : f < s)
    (hr : ∀ v ∈ r, v < s) {j : ℕ} (hj : j < (orChain s f r).length)
    {w : ℕ} (hw : w ∈ (orChain s f r)[j].inputs) : w < s + j := by
  induction r using List.reverseRecOn with
  | nil => simp [orChain] at hj
  | append_singleton r a ih =>
    have hrr : ∀ v ∈ r, v < s := fun v hv => hr v (List.mem_append_left _ hv)
    rw [orChain_snoc] at hj
    by_cases hbefore : j < (orChain s f r).length
    · have hread : w ∈ (orChain s f r)[j].inputs := by
        simpa only [orChain_snoc, List.getElem_append_left hbefore] using hw
      exact ih hrr hbefore hread
    · have hidx : j = (orChain s f r).length := by
        simp only [List.length_append, List.length_singleton] at hj
        omega
      subst j
      have hw' : w = chainOut s f r ∨ w = a := by
        simpa only [orChain_snoc, List.getElem_append_right (le_refl _), Nat.sub_self,
          List.getElem_cons_zero, List.mem_cons, List.not_mem_nil, or_false] using hw
      rcases hw' with he | he
      · rw [he, orChain_length]
        exact chainOut_lt s f r hf
      · have ha : a < s := hr a (by simp)
        omega

private theorem append_back {n : ℕ} {C : Circuit} (tail : List Gate) (hBase : ReadsBack n C)
    (hTail : ∀ j (hj : j < tail.length), ∀ w ∈ tail[j].inputs, w < n + C.size + j) :
    ReadsBack n ⟨C.gates ++ tail, C.output⟩ := by
  intro j hj w hw
  change j < (C.gates ++ tail).length at hj
  have hm : w ∈ (C.gates ++ tail)[j].inputs := by
    change w ∈ ((C.gates ++ tail).getD j ⟨.or, []⟩).inputs at hw
    rwa [List.getD_eq_getElem _ _ hj] at hw
  by_cases h : j < C.gates.length
  · rw [List.getElem_append_left h] at hm
    apply hBase j h w
    change w ∈ (C.gates.getD j ⟨.or, []⟩).inputs
    rwa [List.getD_eq_getElem _ _ h]
  · have hle : C.gates.length ≤ j := by omega
    rw [List.getElem_append_right hle] at hm
    have ht := hTail (j - C.gates.length) (by simp at hj; omega) w hm
    unfold Circuit.size at ht
    omega

private def valOpt {n : ℕ} (C : Circuit) (x : Fin n → Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => value C x w

private theorem valOpt_prefix {n : ℕ} {C D : Circuit} (hp : C.gates <+: D.gates)
    (x : Fin n → Bool) (o : Option ℕ) (hv : ∀ w, o = some w → w < n + C.size) :
    valOpt D x o = valOpt C x o := by
  cases o with
  | none => rfl
  | some w => exact prefix_value hp x w (hv w rfl)

private theorem append_one_bucket {n : ℕ} (C : Circuit) (b : List ℕ) (mono : BucketBinary C)
    (back : ReadsBack n C) (valid : ∀ w ∈ b, w < n + C.size) :
    ∃ (D : Circuit) (o : Option ℕ), C.gates <+: D.gates ∧ BucketBinary D ∧ ReadsBack n D ∧
      D.size ≤ C.size + b.length ∧ (∀ w, o = some w → w < n + D.size) ∧
      ∀ x : Fin n → Bool, valOpt D x o = b.any (value C x) := by
  cases b with
  | nil => exact ⟨C, none, ⟨[], by simp⟩, mono, back, by simp,
      by simp, fun _ => rfl⟩
  | cons a b =>
    let s := n + C.size
    let gates := orChain s a b
    let D : Circuit := ⟨C.gates ++ gates, C.output⟩
    have va : a < s := valid a (by simp)
    have vb : ∀ w ∈ b, w < s := fun w hw => valid w (List.mem_cons_of_mem _ hw)
    have hlen : D.size = C.size + b.length := by
      simp [D, Circuit.size, gates, orChain_length]
    refine ⟨D, some (chainOut s a b), ⟨gates, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact mono g hg
      · obtain ⟨hop, hlen⟩ := orChain_ops s a b g hg
        exact ⟨Or.inr hop, hlen⟩
    · apply append_back gates back
      intro j hj w hw
      exact chain_back s a b va vb hj hw
    · rw [hlen]
      simp
    · intro w hw
      injection hw with he
      subst w
      rw [hlen, ← Nat.add_assoc]
      exact chainOut_lt s a b va
    · intro x
      simp only [valOpt, value, D, wires_eq, run_append, List.any_cons]
      apply orChain_eval s a b (run C.gates (List.ofFn x)) _ va vb
      simp [s, Circuit.size, run_length]

private theorem append_valid_buckets {n m : ℕ} (C : Circuit) (b : Fin m → List ℕ)
    (mono : BucketBinary C) (back : ReadsBack n C)
    (valid : ∀ i w, w ∈ b i → w < n + C.size) :
    ∃ (D : Circuit) (o : Fin m → Option ℕ), C.gates <+: D.gates ∧ BucketBinary D ∧ ReadsBack n D ∧
      D.size ≤ C.size + ∑ i, (b i).length ∧ (∀ i w, o i = some w → w < n + D.size) ∧
      ∀ (x : Fin n → Bool) i, valOpt D x (o i) = (b i).any (value C x) := by
  induction m generalizing C with
  | zero =>
    exact ⟨C, Fin.elim0, ⟨[], by simp⟩, mono, back, by simp,
      fun i => i.elim0, fun _ i => i.elim0⟩
  | succ m ih =>
    obtain ⟨M, root, hp, hm, hb, hs, hv, he⟩ := append_one_bucket C (b 0) mono back (valid 0)
    have hlen : C.size ≤ M.size := by
      obtain ⟨rest, hr⟩ := hp
      simp [Circuit.size, ← hr]
    obtain ⟨D, o, hMD, hdM, hdB, hdS, hdV, hdE⟩ :=
      ih M (fun i => b i.succ) hm hb (fun i w hw => (valid i.succ w hw).trans_le (Nat.add_le_add_left hlen n))
    have hlen' : M.size ≤ D.size := by
      obtain ⟨rest, hr⟩ := hMD
      simp [Circuit.size, ← hr]
    refine ⟨D, Fin.cons root o, hp.trans hMD, hdM, hdB, ?_, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      omega
    · intro i w hi
      refine Fin.cases ?_ (fun j => ?_) i hi
      · intro hz
        exact (hv w (by simpa using hz)).trans_le (Nat.add_le_add_left hlen' n)
      · intro hz
        exact hdV j w (by simpa using hz)
    · intro x i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (valOpt_prefix hMD x root hv).trans (he x)
      · simp only [Fin.cons_succ]
        rw [hdE x j]
        apply any_congr_mem
        intro w hw
        exact prefix_value hp x w (valid j.succ w hw)

/-- Append one OR output per bucket. Invalid original wires still read false. -/
private theorem append_or_buckets {n m : ℕ} (C : Circuit) (b : Fin m → List ℕ)
    (mono : BucketBinary C) (back : ReadsBack n C) :
    ∃ (D : Circuit) (o : Fin m → ℕ), BucketBinary D ∧ ReadsBack n D ∧
      D.size ≤ C.size + ∑ i, (b i).length ∧
      ∀ (x : Fin n → Bool) i, value D x (o i) = (b i).any (value C x) := by
  let valid (i : Fin m) := (b i).filter (fun w => decide (w < n + C.size))
  obtain ⟨D, o, _, hm, hb, hsize, _, hsem⟩ := append_valid_buckets C valid mono back
    (fun i w hw => of_decide_eq_true (List.mem_filter.mp hw).2)
  refine ⟨D, (fun i => (o i).getD (n + D.size)), hm, hb, ?_, ?_⟩
  · exact hsize.trans (Nat.add_le_add_left (Finset.sum_le_sum fun i _ => List.length_filter_le ..) _)
  · intro x i
    have h := hsem x i
    have eval : value D x ((o i).getD (n + D.size)) = valOpt D x (o i) := by
      cases h : o i with
      | none => exact value_beyond D x _ (le_refl _)
      | some w => rfl
    rw [eval, h]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, valid, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨w, ⟨hw, _⟩, htrue⟩
      exact ⟨w, hw, htrue⟩
    · rintro ⟨w, hw, htrue⟩
      have hv : w < n + C.size := by
        by_contra! hx
        rw [value_beyond C x w hx] at htrue
        contradiction
      exact ⟨w, ⟨hw, hv⟩, htrue⟩

/-- Disjoint buckets cost at most one appended gate per member of their common pool. -/
theorem aggregate_disjoint_buckets {n m : ℕ} (C : Circuit) (B : Fin m → Finset ℕ)
    (pool : Finset ℕ) (ph : ℕ → ℕ) (mono : BucketBinary C) (back : ReadsBack n C)
    (inside : ∀ i, B i ⊆ pool) (disjoint : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    ∃ (D : Circuit) (o : Fin m → ℕ), BucketBinary D ∧ ReadsBack n D ∧ D.size ≤ C.size + pool.card ∧
      ∀ (x : Fin n → Bool) i, value D x (o i) = true ↔ ∃ h ∈ B i, value C x (ph h) = true := by
  classical
  let b : Fin m → List ℕ := fun i => ((B i).toList.map ph)
  obtain ⟨D, o, hm, hb, hsize, hsem⟩ := append_or_buckets C b mono back
  have hsum : (∑ i, (B i).card) ≤ pool.card := by
    rw [← Finset.card_biUnion]
    · apply Finset.card_le_card
      intro h hh
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hh
      exact inside i hi
    · intro i _ j _ hij
      exact disjoint i j hij
  refine ⟨D, o, hm, hb, hsize.trans (Nat.add_le_add_left (by simpa [b] using hsum) _), ?_⟩
  intro x i
  rw [hsem]
  simp only [b, List.any_eq_true, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨w, ⟨h, hi, rfl⟩, hw⟩
    exact ⟨h, hi, hw⟩
  · rintro ⟨h, hi, hw⟩
    exact ⟨ph h, ⟨h, hi, rfl⟩, hw⟩

end PEqualNP.Outside.L_meta_1720

namespace PEqualNP.Outside.L_meta_1720

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.Outside.L_meta_1720.Degree PEqualNP.Outside.L_meta_1720.Count
open PEqualNP.Outside.L_meta_1720.Semantic PEqualNP.Outside.L_meta_1720.Setup

theorem assemble {N k : ℕ} (I : Fin N → Fin N → Prop) (C : Circuit)
    (hk : 1 ≤ k) (hm : Mon2 C) (hr : ReadsBack (N + N) C)
    (unique : ∀ p q : Fin N, p ≠ q → ∃! l : Fin N, I p l ∧ I q l)
    (pos : GoodInputs I C) (neg : ForbiddenInputs I k C) (trans : Transposed N C) :
    Target I k C := by
  classical
  obtain ⟨X, ph, H, ⟨hxmono, hxback⟩, hxsize, ht⟩ := trans
  obtain ⟨Y, rho, ⟨hymono, hyback⟩, hysize, hywire⟩ := Line.lineExtract N C hm hr
  let E := frontier N C
  let coeff (h : ℕ) (x : Row N) := Setup.value X x (ph h)
  let line (h : ℕ) (y : Row N) := Setup.value C (Fin.append (fun _ : Fin N => false) y) h
  have split (x y : Row N) : evalPair C x y = true ↔
      ∃ h ∈ E, line h y = true ∧ (h ∈ H ∨ coeff h x = true) := by
    have hz := neg x (fun _ => false) (by rw [weight_zero]; omega) (by simp)
    simpa only [hz, Bool.false_eq_true, false_or, E, mem_frontier hr] using ht x y
  let A := xBucket E coeff line
  let B := yBucket E coeff line
  obtain ⟨hA, hB, hAA, hBB, hAB, _, hXA, hXall, hYB, hYall, cover⟩ :=
    bucket_spec I E H coeff line (evalPair C) hk unique split pos neg
  obtain ⟨insideA, insideB, hpool⟩ := Line.bucket_pool_budget A B E hA hB hAB
  obtain ⟨X', ps, hxmono', hxback', hxsize', hxspec⟩ :=
    aggregate_disjoint_buckets X A (Finset.univ.biUnion A) ph hxmono hxback insideA hAA
  obtain ⟨Y', rh, hymono', hyback', hysize', hyspec⟩ :=
    aggregate_disjoint_buckets Y B (Finset.univ.biUnion B) rho hymono hyback insideB hBB
  have hxsem (l : Fin N) (x : Row N) : Setup.value X' x (ps l) = true ↔ fires coeff (A l) x :=
    hxspec x l
  have hysem (p : Fin N) (y : Row N) : Setup.value Y' y (rh p) = true ↔ fires line (B p) y := by
    rw [hyspec]
    unfold fires
    apply exists_congr
    intro h
    refine and_congr_right fun hi => ?_
    have he := hB p hi
    have hlt := (Finset.mem_range.1 (Finset.mem_filter.1 he).1)
    have hz := ((mem_frontier hr).1 he).1
    have hw := (hywire h hlt hz).2 y
    change Setup.value Y y (rho h) = line h y at hw
    change Setup.value Y y (rho h) = true ↔ line h y = true
    rw [hw]
  have hsize : X'.size + Y'.size ≤ 5 * C.size := by
    rw [pointGates_ncard, mixedGates_ncard] at hxsize
    have hpart := point_mixed_budget N C
    have hbdy := frontier_budget hm hr
    have hybase := line_count_le_size N C
    change _ + _ ≤ (frontier N C).card at hpool
    omega
  refine ⟨X', Y', ps, rh, ⟨hxmono', hxback'⟩, ⟨hymono', hyback'⟩, hsize,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro l p h
    exact hXA l p ((hxsem l _).1 h)
  · intro l x h
    cases hu : Setup.value X' x (ps l)
    · rfl
    · exact False.elim (hXall l x h ((hxsem l x).1 hu))
  · intro p l h
    exact hYB p l ((hysem p _).1 h)
  · intro p y hw h
    cases hu : Setup.value Y' y (rh p)
    · rfl
    · exact False.elim (hYall p y hw h ((hysem p y).1 hu))
  · intro p l h
    exact (cover p l h).imp (hxsem l (unit p)).2 (hysem p (unit l)).2

end PEqualNP.Outside.L_meta_1720

open PEqualNP.Outside.L_meta_1720 PEqualNP.Outside.L_meta_1720.Setup in
theorem PEqualNP.Outside.L_meta_1720 : (∀ (N21 : ℕ) (C21 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g21 ∈ C21.gates, (g21.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g21.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g21.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N21 + N21) C21 → (∀ j21 < C21.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i21 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD i21 0 = 0) ∨ (∀ h21b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21).inputs, (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21b 0 = 0)) → (∀ (w21 : ℕ) (xa21 xb21 ya21 yb21 : Fin N21 → Bool), ((C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xa21 yb21))).getD w21 false) ∧ ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21 0 = 0 → (C21.wires (List.ofFn (Fin.append xa21 ya21))).getD w21 false = (C21.wires (List.ofFn (Fin.append xb21 ya21))).getD w21 false) ∧ (C21.wires (List.ofFn (Fin.append (fun u21 : Fin N21 => false) (fun u21a : Fin N21 => false)))).getD w21 false = false) ∧ (∀ w21a : ℕ, 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD w21a 0 → 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD w21a 0 → ∃ c21 : ℕ → (Fin N21 → Bool) → Bool, (∀ h21 : ℕ, Monotone (c21 h21)) ∧ ∀ x21 y21 : Fin N21 → Bool, ((C21.wires (List.ofFn (Fin.append x21 y21))).getD w21a false = true ↔ ((C21.wires (List.ofFn (Fin.append x21 (fun u21b : Fin N21 => false)))).getD w21a false = true ∨ ∃ h21a : ℕ, ((C21.lineDegrees (N21 + N21) (Finset.range N21)).getD h21a 0 = 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD h21a 0 ∧ ∃ j21a < C21.gates.length, h21a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C21 j21a).inputs ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.range N21)).getD (N21 + N21 + j21a) 0 ∧ 0 < (C21.lineDegrees (N21 + N21) (Finset.Ico N21 (N21 + N21))).getD (N21 + N21 + j21a) 0) ∧ (C21.wires (List.ofFn (Fin.append (fun u21c : Fin N21 => false) y21))).getD h21a false = true ∧ c21 h21a x21 = true)))) → (∀ (N22 : ℕ) (C22 : PEqualNP.CircuitLowerBounds.Circuit), (∀ g22 ∈ C22.gates, (g22.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N22 + N22) C22 → (∀ j22b < C22.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD i22 0 = 0) ∨ (∀ h22b ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22b).inputs, (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22b 0 = 0)) → 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD C22.output 0 → 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD C22.output 0 → ∃ (X22 : PEqualNP.CircuitLowerBounds.Circuit) (ph22 : ℕ → ℕ) (H22 : Set ℕ), ((∀ g22a ∈ X22.gates, (g22a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g22a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g22a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N22 X22) ∧ X22.size ≤ Set.ncard {j22 : ℕ | j22 < C22.gates.length ∧ (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22) 0 = 0} + 3 * Set.ncard {j22a : ℕ | j22a < C22.gates.length ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22a) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22a) 0} ∧ (∀ h22 ∈ H22, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22 0 ∧ ∃ j22c < C22.gates.length, h22 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22c).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22c) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22c) 0)) ∧ ∀ x22 y22 : Fin N22 → Bool, (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 y22) = true ↔ (PEqualNP.MetaComplexity.circuitFun (N22 + N22) C22 (Fin.append x22 (fun u22 : Fin N22 => false)) = true ∨ ∃ h22a : ℕ, ((C22.lineDegrees (N22 + N22) (Finset.range N22)).getD h22a 0 = 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD h22a 0 ∧ ∃ j22d < C22.gates.length, h22a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C22 j22d).inputs ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.range N22)).getD (N22 + N22 + j22d) 0 ∧ 0 < (C22.lineDegrees (N22 + N22) (Finset.Ico N22 (N22 + N22))).getD (N22 + N22 + j22d) 0) ∧ (C22.wires (List.ofFn (Fin.append (fun u22a : Fin N22 => false) y22))).getD h22a false = true ∧ (h22a ∈ H22 ∨ (X22.wires (List.ofFn x22)).getD (ph22 h22a) false = true)))) → ∀ (q20 N20 k20 : ℕ) (I20 : Fin N20 → Fin N20 → Prop) [DecidableRel I20] (C20 : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q20 → N20 = q20 ^ 2 + q20 + 1 → (∀ l20c : Fin N20, (Finset.univ.filter (fun p20f => I20 p20f l20c)).card = q20 + 1) → (∀ pa20 pb20 : Fin N20, pa20 ≠ pb20 → ∃! lb20 : Fin N20, I20 pa20 lb20 ∧ I20 pb20 lb20) → 1 ≤ k20 → (∀ g20 ∈ C20.gates, (g20.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20.inputs.length = 2) → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N20 + N20) C20 → (∀ j20 < C20.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∃ i20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.Ico N20 (N20 + N20))).getD i20 0 = 0) ∨ (∀ h20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C20 j20).inputs, (C20.lineDegrees (N20 + N20) (Finset.range N20)).getD h20 0 = 0)) → (∀ p20g l20d : Fin N20, I20 p20g l20d → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 (fun i20a => decide (i20a = Fin.castAdd N20 p20g ∨ i20a = Fin.natAdd N20 l20d)) = true) → (∀ z20 : Fin (N20 + N20) → Bool, (Finset.univ.filter (fun l20e : Fin N20 => z20 (Fin.natAdd N20 l20e) = true)).card ≤ k20 → (¬ ∃ p20h l20f : Fin N20, I20 p20h l20f ∧ z20 (Fin.castAdd N20 p20h) = true ∧ z20 (Fin.natAdd N20 l20f) = true) → PEqualNP.MetaComplexity.circuitFun (N20 + N20) C20 z20 = false) → ∃ (X20 Y20 : PEqualNP.CircuitLowerBounds.Circuit) (ps20 rh20 : Fin N20 → ℕ), ((∀ g20a ∈ X20.gates, (g20a.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20a.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20a.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 X20) ∧ ((∀ g20b ∈ Y20.gates, (g20b.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g20b.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g20b.inputs.length = 2) ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack N20 Y20) ∧ X20.size + Y20.size ≤ 5 * C20.size ∧ (∀ w20 p20 : Fin N20, (X20.wires (List.ofFn (fun a20 => decide (a20 = p20)))).getD (ps20 w20) false = true → I20 p20 w20) ∧ (∀ (w20a : Fin N20) (x20 : Fin N20 → Bool), (∀ p20a : Fin N20, I20 p20a w20a → x20 p20a = false) → (X20.wires (List.ofFn x20)).getD (ps20 w20a) false = false) ∧ (∀ p20b l20 : Fin N20, (Y20.wires (List.ofFn (fun a20a => decide (a20a = l20)))).getD (rh20 p20b) false = true → I20 p20b l20) ∧ (∀ (p20c : Fin N20) (y20 : Fin N20 → Bool), (Finset.univ.filter (fun l20a : Fin N20 => y20 l20a = true)).card ≤ k20 → (∀ l20b : Fin N20, I20 p20c l20b → y20 l20b = false) → (Y20.wires (List.ofFn y20)).getD (rh20 p20c) false = false) ∧ (∀ p20d w20b : Fin N20, I20 p20d w20b → (X20.wires (List.ofFn (fun a20b => decide (a20b = p20d)))).getD (ps20 w20b) false = true ∨ (Y20.wires (List.ofFn (fun a20c => decide (a20c = w20b)))).getD (rh20 p20d) false = true) := by
  intro flag trans q N k I _ C _ hN hLines unique hk hm hr hand pos neg
  have hpos : GoodInputs I C := by
    intro p l h
    rw [evalPair, append_unit]
    exact pos p l h
  have hneg : ForbiddenInputs I k C := by
    intro x y hy hz
    apply neg (Fin.append x y)
    · simpa only [Fin.append_right, PEqualNP.Outside.L_meta_1720.Semantic.weight] using hy
    · simpa only [Fin.append_left, Fin.append_right] using hz
  have hIndep : Indep N C := by
    intro w xa xb ya yb
    have hf := (flag N C hm hr hand).1 w xa xb ya yb
    exact ⟨hf.1, hf.2.1⟩
  obtain ⟨hp, hl⟩ := positive_degrees hN hLines hk hpos hneg hIndep
  obtain ⟨X, ph, H, legal, hsize, _, htx⟩ := trans N C hm hr hand hp hl
  exact assemble I C hk hm hr unique hpos hneg ⟨X, ph, H, legal, hsize, htx⟩
