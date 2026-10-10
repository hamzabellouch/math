import OAI.Geometry.TranslativeCovering.PatternCross

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11

namespace FiniteJanson

variable {V : Type u_1} [Fintype V]

noncomputable def atom (p : V → ℝ) (x : V → Bool) : ℝ :=
  ∏ v, if x v then p v else 1 - p v

noncomputable def prob (p : V → ℝ) (A : Set (V → Bool)) : ℝ :=
  ∑ x, if x ∈ A then atom p x else 0

variable {p : V → ℝ}

theorem atom_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (x : V → Bool) :
    0 ≤ atom p x := by
  apply Finset.prod_nonneg
  intro v _
  split_ifs <;> linarith [(hp v).1, (hp v).2]

theorem sum_atom (p : V → ℝ) : ∑ x, atom p x = 1 := by
  simp only [atom]
  rw [← Fintype.prod_sum (fun v (b : Bool) => if b then p v else 1 - p v)]
  simp

theorem prob_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (A : Set (V → Bool)) :
    0 ≤ prob p A := by
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact atom_nonneg hp x
  · rfl

@[simp] theorem prob_univ (p : V → ℝ) : prob p Set.univ = 1 := by
  simp [prob, sum_atom]

@[simp] theorem prob_empty (p : V → ℝ) : prob p ∅ = 0 := by
  simp [prob]

theorem prob_mono (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A B : Set (V → Bool)} (hAB : A ⊆ B) : prob p A ≤ prob p B := by
  apply Finset.sum_le_sum
  intro x _
  by_cases ha : x ∈ A
  · simp [ha, hAB ha]
  · simp only [ha, ↓reduceIte]
    split_ifs
    · exact atom_nonneg hp x
    · rfl

theorem prob_compl (p : V → ℝ) (A : Set (V → Bool)) :
    prob p Aᶜ = 1 - prob p A := by
  have h : prob p A + prob p Aᶜ = 1 := by
    rw [prob, prob, ← Finset.sum_add_distrib, ← sum_atom p]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ A <;> simp [hx]
  linarith

theorem prob_inter_compl (p : V → ℝ) (A B : Set (V → Bool)) :
    prob p (A ∩ Bᶜ) = prob p A - prob p (A ∩ B) := by
  have h : prob p (A ∩ B) + prob p (A ∩ Bᶜ) = prob p A := by
    rw [prob, prob, prob, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ha, hb]
  linarith

theorem atom_lattice (p : V → ℝ) (x y : V → Bool) :
    atom p x * atom p y = atom p (x ⊓ y) * atom p (x ⊔ y) := by
  simp only [atom, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  change (if x v then p v else 1 - p v) * (if y v then p v else 1 - p v) =
    (if x v ⊓ y v then p v else 1 - p v) * (if x v ⊔ y v then p v else 1 - p v)
  cases hx : x v <;> cases hy : y v <;> simp [mul_comm]

noncomputable def ind (A : Set (V → Bool)) (x : V → Bool) : ℝ :=
  if x ∈ A then 1 else 0

theorem prob_eq (p : V → ℝ) (A : Set (V → Bool)) :
    prob p A = ∑ x, atom p x * ind A x := by
  apply Finset.sum_congr rfl
  intro x _
  simp [ind, mul_ite]

omit [Fintype V] in
theorem ind_nonneg (A : Set (V → Bool)) : 0 ≤ ind A := by
  intro x
  simp only [ind, Pi.zero_apply]
  split_ifs <;> norm_num

omit [Fintype V] in
theorem ind_mono {A : Set (V → Bool)} (hA : IsUpperSet A) : Monotone (ind A) := by
  intro x y hxy
  by_cases hx : x ∈ A
  · simp [ind, hx, hA hxy hx]
  · simp only [ind, hx, ↓reduceIte]
    split_ifs <;> norm_num

theorem harris (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A B : Set (V → Bool)} (hA : IsUpperSet A) (hB : IsUpperSet B) :
    prob p A * prob p B ≤ prob p (A ∩ B) := by
  have h := fkg (ind A) (ind B) (atom p) (atom_nonneg hp)
    (ind_nonneg A) (ind_nonneg B) (ind_mono hA) (ind_mono hB)
    (fun x y => (atom_lattice p x y).le)
  rw [← prob_eq, ← prob_eq, sum_atom, one_mul] at h
  apply h.trans_eq
  rw [prob_eq]
  apply Finset.sum_congr rfl
  intro x _
  by_cases ha : x ∈ A <;> by_cases hb : x ∈ B <;> simp [ind, ha, hb]

theorem harris_opposite (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    {A F : Set (V → Bool)} (hA : IsUpperSet A) (hF : IsLowerSet F) :
    prob p (A ∩ F) ≤ prob p A * prob p F := by
  have h := harris hp hA hF.compl
  rw [prob_compl, prob_inter_compl] at h
  nlinarith

theorem atom_split (p : V → ℝ) (S : Set V) (x : V → Bool) :
    atom p x = atom (fun v : S => p v) (fun v : S => x v) *
      atom (fun v : (Sᶜ : Set V) => p v) (fun v : (Sᶜ : Set V) => x v) := by
  exact (Fintype.prod_subtype_mul_prod_subtype (fun v => v ∈ S)
    (fun v => if x v then p v else 1 - p v)).symm

theorem prob_split (p : V → ℝ) (S : Set V)
    (A : Set (S → Bool)) (B : Set ((Sᶜ : Set V) → Bool)) :
    prob p {x | (fun v : S => x v) ∈ A ∧ (fun v : (Sᶜ : Set V) => x v) ∈ B} =
      prob (fun v : S => p v) A * prob (fun v : (Sᶜ : Set V) => p v) B := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => Bool)
  calc
    _ = ∑ z : (S → Bool) × ((Sᶜ : Set V) → Bool),
        (if z.1 ∈ A then atom (fun v : S => p v) z.1 else 0) *
        (if z.2 ∈ B then atom (fun v : (Sᶜ : Set V) => p v) z.2 else 0) := by
      apply Fintype.sum_equiv e
      intro x
      simp only [e, Equiv.piEquivPiSubtypeProd_apply, Set.mem_ofPred_eq]
      split_ifs with h hab hb
      · exact atom_split p S x
      · exfalso
        apply hb
        convert h.2
      · exfalso
        apply hab
        convert h.1
      · exfalso
        apply hab
        convert h.1
      · rename_i hh₁ hh₂
        exfalso
        apply h
        constructor
        · convert hh₁
        · convert hh₂
      · simp
      · simp
      · simp
    _ = _ := by
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, prob]
      congr 1 <;> apply Finset.sum_congr (by congr; apply Subsingleton.elim) <;> intro x hx <;> congr 1

def Supported (S : Set V) (A : Set (V → Bool)) : Prop :=
  ∀ x y, (∀ v ∈ S, x v = y v) → (x ∈ A ↔ y ∈ A)

theorem prob_independent (p : V → ℝ) (S : Set V)
    {A B : Set (V → Bool)} (hA : Supported S A) (hB : Supported (Sᶜ : Set V) B) :
    prob p (A ∩ B) = prob p A * prob p B := by
  let e := Equiv.piEquivPiSubtypeProd (fun v => v ∈ S) (fun _ => Bool)
  let A' : Set (S → Bool) := {x | e.symm (x, fun _ => false) ∈ A}
  let B' : Set ((Sᶜ : Set V) → Bool) := {x | e.symm (fun _ => false, x) ∈ B}
  have ha (x : V → Bool) : x ∈ A ↔ (fun v : S => x v) ∈ A' := by
    apply hA
    intro v hv
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv]
  have hb (x : V → Bool) : x ∈ B ↔ (fun v : (Sᶜ : Set V) => x v) ∈ B' := by
    apply hB
    intro v hv
    simp only [Set.mem_compl_iff] at hv
    simp [e, Equiv.piEquivPiSubtypeProd_symm_apply, hv]
  have hab : A ∩ B = {x | (fun v : S => x v) ∈ A' ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ B'} := by
    ext x
    exact and_congr (ha x) (hb x)
  have hae : A = {x | (fun v : S => x v) ∈ A' ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ (Set.univ : Set ((Sᶜ : Set V) → Bool))} := by
    ext x
    simpa using ha x
  have hbe : B = {x | (fun v : S => x v) ∈ (Set.univ : Set (S → Bool)) ∧
        (fun v : (Sᶜ : Set V) => x v) ∈ B'} := by
    ext x
    simpa using hb x
  rw [hab, prob_split, hae, hbe, prob_split, prob_split, prob_univ, prob_univ,
    mul_one, one_mul]

def occurs (H : Finset V) : Set (V → Bool) := {x | ∀ v ∈ H, x v = true}

omit [Fintype V] in
theorem occurs_upper (H : Finset V) : IsUpperSet (occurs H) := by
  intro x y hxy hx v hv
  have h := hxy v
  rw [hx v hv] at h
  exact top_le_iff.mp h

omit [Fintype V] in
theorem occurs_supported (H : Finset V) : Supported (H : Set V) (occurs H) := by
  intro x y hxy
  constructor <;> intro h v hv
  · rw [← hxy v hv]
    exact h v hv
  · rw [hxy v hv]
    exact h v hv

omit [Fintype V] in
@[simp] theorem occurs_union (H K : Finset V) : occurs (H ∪ K) = occurs H ∩ occurs K := by
  ext x
  simp [occurs, or_imp, forall_and]

def avoids {ι : Type u_2} (H : ι → Finset V) (s : Finset ι) : Set (V → Bool) :=
  {x | ∀ i ∈ s, x ∉ occurs (H i)}

omit [Fintype V] in
@[simp] theorem avoids_empty {ι : Type u_3} (H : ι → Finset V) : avoids H ∅ = Set.univ := by
  ext x
  simp [avoids]

omit [Fintype V] in
@[simp] theorem avoids_insert {ι : Type u_4} (H : ι → Finset V) (s : Finset ι) (i : ι) :
    avoids H (insert i s) = avoids H s ∩ (occurs (H i))ᶜ := by
  ext x
  simp [avoids, and_comm]

omit [Fintype V] in
theorem avoids_lower {ι : Type u_5} (H : ι → Finset V) (s : Finset ι) :
    IsLowerSet (avoids H s) := by
  intro x y hxy hy i hi hx
  exact hy i hi (occurs_upper (H i) hxy hx)

omit [Fintype V] in
theorem avoids_supported_compl {ι : Type u_6} (H : ι → Finset V) (s : Finset ι)
    (K : Finset V) (hs : ∀ i ∈ s, Disjoint K (H i)) :
    Supported (K : Set V)ᶜ (avoids H s) := by
  have he (x y : V → Bool) (hxy : ∀ v ∈ (K : Set V)ᶜ, x v = y v)
      (i : ι) (hi : i ∈ s) : x ∈ occurs (H i) ↔ y ∈ occurs (H i) := by
    apply occurs_supported
    intro v hv
    apply hxy
    exact fun hvK => Finset.disjoint_left.mp (hs i hi) hvK hv
  intro x y hxy
  simp only [avoids, Set.mem_ofPred_eq]
  exact forall_congr' fun i => forall_congr' fun hi => not_congr (he x y hxy i hi)

omit [Fintype V] in
theorem avoids_split {ι : Type u_7} (H : ι → Finset V) (s : Finset ι) (P : ι → Prop) :
    avoids H s = avoids H (s.filter P) ∩ avoids H (s.filter fun i => ¬ P i) := by
  ext x
  constructor
  · intro hx
    exact ⟨fun i hi => hx i (Finset.mem_filter.mp hi).1,
      fun i hi => hx i (Finset.mem_filter.mp hi).1⟩
  · rintro ⟨ha, hb⟩ i hi
    by_cases h : P i
    · exact ha i (Finset.mem_filter.mpr ⟨hi, h⟩)
    · exact hb i (Finset.mem_filter.mpr ⟨hi, h⟩)

theorem prob_remove_le {ι : Type u_8} (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (E : Set (V → Bool)) :
    prob p E - ∑ i ∈ s, prob p (E ∩ occurs (H i)) ≤ prob p (E ∩ avoids H s) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, avoids_insert, ← Set.inter_assoc, prob_inter_compl]
    have hsub : (E ∩ avoids H s) ∩ occurs (H i) ⊆ E ∩ occurs (H i) := by
      intro x hx
      exact ⟨hx.1.1, hx.2⟩
    have := prob_mono hp hsub
    linarith

theorem avoidance_step {ι : Type u_9} (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (a : ι) :
    prob p (avoids H (insert a s)) ≤ prob p (avoids H s) *
      Real.exp (-prob p (occurs (H a)) +
        ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
          prob p (occurs (H a) ∩ occurs (H i))) := by
  let near := s.filter (fun i => ¬ Disjoint (H a) (H i))
  let far := s.filter (fun i => Disjoint (H a) (H i))
  let F := avoids H far
  let B := occurs (H a)
  let A := avoids H s
  let c := prob p B - ∑ i ∈ near, prob p (B ∩ occurs (H i))
  have hsplit : A = F ∩ avoids H near := by
    ext x
    simp only [A, F, far, near, avoids, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Finset.mem_filter]
    constructor
    · intro h; exact ⟨fun i hi => h i hi.1, fun i hi => h i hi.1⟩
    · rintro ⟨h₁, h₂⟩ i hi
      by_cases hd : Disjoint (H a) (H i)
      · exact h₁ i ⟨hi, hd⟩
      · exact h₂ i ⟨hi, hd⟩
  have hsub : A ⊆ F := by rw [hsplit]; exact Set.inter_subset_left
  have hF : IsLowerSet F := avoids_lower H far
  have hB : IsUpperSet B := occurs_upper (H a)
  have hind : prob p (B ∩ F) = prob p B * prob p F := by
    apply prob_independent p (H a : Set V) (occurs_supported (H a))
    apply avoids_supported_compl H far (H a)
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hsum : (∑ i ∈ near, prob p ((B ∩ F) ∩ occurs (H i))) ≤
      (∑ i ∈ near, prob p (B ∩ occurs (H i))) * prob p F := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have h := harris_opposite hp (hB.inter (occurs_upper (H i))) hF
    have he : (B ∩ F) ∩ occurs (H i) = (B ∩ occurs (H i)) ∩ F := by
      ext x
      simp only [Set.mem_inter_iff]
      tauto
    rwa [he]
  have hlower : c * prob p F ≤ prob p (B ∩ A) := by
    have h := prob_remove_le hp H near (B ∩ F)
    rw [Set.inter_assoc, ← hsplit] at h
    rw [hind] at h
    dsimp [c]
    nlinarith
  have hstep : c * prob p A ≤ prob p (B ∩ A) := by
    by_cases hc : 0 ≤ c
    · exact (mul_le_mul_of_nonneg_left (prob_mono hp hsub) hc).trans hlower
    · have hc' : c ≤ 0 := le_of_not_ge hc
      exact (mul_nonpos_of_nonpos_of_nonneg hc' (prob_nonneg hp A)).trans
        (prob_nonneg hp (B ∩ A))
  have hraw : prob p (avoids H (insert a s)) ≤ prob p A * (1 - c) := by
    rw [avoids_insert, prob_inter_compl]
    change prob p A - prob p (A ∩ B) ≤ prob p A * (1 - c)
    rw [Set.inter_comm A B]
    nlinarith
  have hexp : 1 - c ≤ Real.exp (-c) := by
    have := Real.add_one_le_exp (-c)
    linarith
  apply (hraw.trans (mul_le_mul_of_nonneg_left hexp (prob_nonneg hp A))).trans_eq
  dsimp [A, c, B, near]
  rw [neg_sub, sub_eq_neg_add]

variable {ι : Type u_10}

noncomputable def mean (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, prob p (occurs (H i))

noncomputable def offCost (p : V → ℝ) (H : ι → Finset V) (i j : ι) : ℝ :=
  if i = j ∨ Disjoint (H i) (H j) then 0 else prob p (occurs (H i) ∩ occurs (H j))

noncomputable def offSum (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, offCost p H i j

@[simp] theorem offCost_self (p : V → ℝ) (H : ι → Finset V) (i : ι) :
    offCost p H i i = 0 := by simp [offCost]

theorem offCost_symm (p : V → ℝ) (H : ι → Finset V) (i j : ι) :
    offCost p H i j = offCost p H j i := by
  simp only [offCost, eq_comm, disjoint_comm, Set.inter_comm]

@[simp] theorem mean_insert (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (a : ι) (ha : a ∉ s) : mean p H (insert a s) = prob p (occurs (H a)) + mean p H s := by
  exact Finset.sum_insert ha

theorem offSum_insert (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (a : ι) (ha : a ∉ s) :
    offSum p H (insert a s) = offSum p H s +
      2 * ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
        prob p (occurs (H a) ∩ occurs (H i)) := by
  have hsum : (∑ i ∈ s, offCost p H a i) =
      ∑ i ∈ s.filter (fun i => ¬ Disjoint (H a) (H i)),
        prob p (occurs (H a) ∩ occurs (H i)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    have hai : a ≠ i := fun h => ha (h ▸ hi)
    by_cases hd : Disjoint (H a) (H i) <;> simp [offCost, hai, hd]
  simp only [offSum, Finset.sum_insert ha, offCost_self, zero_add,
    Finset.sum_add_distrib]
  rw [show (∑ i ∈ s, offCost p H i a) = ∑ i ∈ s, offCost p H a i by
    apply Finset.sum_congr rfl
    intro i _
    exact offCost_symm p H i a]
  rw [hsum]
  ring

theorem janson_first (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) :
    prob p (avoids H s) ≤ Real.exp (-mean p H s + offSum p H s / 2) := by
  induction s using Finset.induction_on with
  | empty => simp [mean, offSum]
  | @insert a s ha ih =>
    apply (avoidance_step hp H s a).trans
    apply (mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add, mean_insert p H s a ha, offSum_insert p H s a ha]
    congr 1
    ring

@[simp] theorem prob_singleton (p : V → ℝ) (x : V → Bool) :
    prob p {x} = atom p x := by
  simp [prob]

theorem prob_occurs (p : V → ℝ) (H : Finset V) :
    prob p (occurs H) = ∏ v ∈ H, p v := by
  let f (v : V) (b : Bool) : ℝ :=
    if v ∈ H then (if b then p v else 0) else (if b then p v else 1 - p v)
  have he : prob p (occurs H) = ∑ x : V → Bool, ∏ v, f v (x v) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ occurs H
    · rw [ite_eq_left hx]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ H
      · simp [f, hv, hx v hv]
      · simp [f, hv]
    · rw [ite_eq_right hx]
      symm
      apply Finset.prod_eq_zero_iff.mpr
      have hex : ∃ v ∈ H, x v ≠ true := by
        by_contra hn
        apply hx
        intro v hv
        by_contra hxv
        exact hn ⟨v, hv, hxv⟩
      obtain ⟨v, hv, hxv⟩ := hex
      exact ⟨v, Finset.mem_univ v, by simp [f, hv, hxv]⟩
  rw [he, ← Fintype.prod_sum]
  calc
    _ = ∏ v : V, if v ∈ H then p v else 1 := by
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : v ∈ H <;> simp [f, hv]
    _ = _ := by simp

variable {W : Type u_11} [Fintype W]

theorem atom_sum (p : V → ℝ) (q : W → ℝ) (x : V ⊕ W → Bool) :
    atom (Sum.elim p q) x = atom p (x ∘ Sum.inl) * atom q (x ∘ Sum.inr) := by
  exact Fintype.prod_sum_type _

theorem prob_sum (p : V → ℝ) (q : W → ℝ)
    (A : Set (V → Bool)) (B : Set (W → Bool)) :
    prob (Sum.elim p q) {x | x ∘ Sum.inl ∈ A ∧ x ∘ Sum.inr ∈ B} =
      prob p A * prob q B := by
  let : DecidableEq (V ⊕ W) := fun _ _ => Classical.propDecidable _
  calc
    _ = ∑ z : (V → Bool) × (W → Bool),
        (if z.1 ∈ A then atom p z.1 else 0) *
        (if z.2 ∈ B then atom q z.2 else 0) := by
      apply Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V W Bool)
      intro x
      simp only [Set.mem_ofPred_eq]
      by_cases ha : x ∘ Sum.inl ∈ A <;> by_cases hb : x ∘ Sum.inr ∈ B <;>
        simp [Equiv.sumArrowEquivProdArrow, ha, hb, atom_sum]
    _ = _ := by
      simp only [Fintype.sum_prod_type, ← Finset.mul_sum, ← Finset.sum_mul, prob]

noncomputable def gated (H : ι → Finset V) (i : ι) : Finset (V ⊕ ι) :=
  (H i).map Function.Embedding.inl ∪ {Sum.inr i}

omit [Fintype V] in
@[simp] theorem occurs_gated (H : ι → Finset V) (i : ι) (x : V ⊕ ι → Bool) :
    x ∈ occurs (gated H i) ↔ x ∘ Sum.inl ∈ occurs (H i) ∧ x (Sum.inr i) = true := by
  simp [gated, occurs, Function.comp_def, or_imp, forall_and, and_comm]

omit [Fintype V] in
theorem avoidance_gated_subset (H : ι → Finset V) (s : Finset ι) :
    {x : V ⊕ ι → Bool | x ∘ Sum.inl ∈ avoids H s} ⊆ avoids (gated H) s := by
  intro x hx i hi h
  exact hx i hi ((occurs_gated H i x).mp h).1

theorem prob_avoidance_le_gated [Fintype ι]
    (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (H : ι → Finset V) (s : Finset ι)
    {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    prob p (avoids H s) ≤ prob (Sum.elim p (fun _ : ι => q)) (avoids (gated H) s) := by
  have he : {x : V ⊕ ι → Bool | x ∘ Sum.inl ∈ avoids H s} =
      {x | x ∘ Sum.inl ∈ avoids H s ∧ x ∘ Sum.inr ∈ (Set.univ : Set (ι → Bool))} := by
    ext x; simp
  have hh : prob (Sum.elim p (fun _ : ι => q))
      {x | x ∘ Sum.inl ∈ avoids H s} = prob p (avoids H s) := by
    rw [he, prob_sum, prob_univ, mul_one]
  rw [← hh]
  apply prob_mono _ (avoidance_gated_subset H s)
  intro v
  cases v with
  | inl v => exact hp v
  | inr i => exact hq

theorem prob_gated [Fintype ι] (p : V → ℝ) (q : ℝ) (H : ι → Finset V) (i : ι) :
    prob (Sum.elim p (fun _ : ι => q)) (occurs (gated H i)) = q * prob p (occurs (H i)) := by
  rw [prob_occurs, gated, Finset.prod_union]
  · simp [Finset.prod_map, prob_occurs, mul_comm]
  · simp

theorem prob_gated_pair [Fintype ι] (p : V → ℝ) (q : ℝ) (H : ι → Finset V)
    (i j : ι) (hij : i ≠ j) :
    prob (Sum.elim p (fun _ : ι => q)) (occurs (gated H i) ∩ occurs (gated H j)) =
      q ^ 2 * prob p (occurs (H i) ∩ occurs (H j)) := by
  have he : occurs (gated H i) ∩ occurs (gated H j) =
      {x | x ∘ Sum.inl ∈ occurs (H i) ∩ occurs (H j) ∧
        x ∘ Sum.inr ∈ occurs ({i, j} : Finset ι)} := by
    ext x
    simp only [Set.mem_inter_iff, occurs_gated, Set.mem_ofPred_eq]
    simp only [occurs, Set.mem_ofPred_eq, Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
      Function.comp_apply]
    tauto
  rw [he, prob_sum, prob_occurs]
  simp [hij, pow_two, mul_assoc, mul_comm]

omit [Fintype V] in
theorem disjoint_gated (H : ι → Finset V) (i j : ι) (hij : i ≠ j) :
    Disjoint (gated H i) (gated H j) ↔ Disjoint (H i) (H j) := by
  simp [gated, Finset.disjoint_map, Ne.symm hij]

theorem mean_gated [Fintype ι] (p : V → ℝ) (q : ℝ)
    (H : ι → Finset V) (s : Finset ι) :
    mean (Sum.elim p (fun _ : ι => q)) (gated H) s = q * mean p H s := by
  simp only [mean, prob_gated, Finset.mul_sum]

theorem offSum_gated [Fintype ι] (p : V → ℝ) (q : ℝ)
    (H : ι → Finset V) (s : Finset ι) :
    offSum (Sum.elim p (fun _ : ι => q)) (gated H) s = q ^ 2 * offSum p H s := by
  simp only [offSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j; simp
  · simp only [offCost, hij, false_or, disjoint_gated H i j hij]
    split_ifs
    · simp
    · exact prob_gated_pair p q H i j hij

theorem janson_thinned [Fintype ι] (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) {q : ℝ} (hq : 0 ≤ q ∧ q ≤ 1) :
    prob p (avoids H s) ≤ Real.exp (-q * mean p H s + q ^ 2 * offSum p H s / 2) := by
  apply (prob_avoidance_le_gated hp H s hq).trans
  have hpar : ∀ v, 0 ≤ (Sum.elim p (fun _ : ι => q)) v ∧
      (Sum.elim p (fun _ : ι => q)) v ≤ 1 := by
    intro v
    cases v with
    | inl v => exact hp v
    | inr i => exact hq
  simpa only [mean_gated, offSum_gated, neg_mul] using janson_first hpar (gated H) s

noncomputable def depSum (p : V → ℝ) (H : ι → Finset V) (s : Finset ι) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if Disjoint (H i) (H j) then 0 else prob p (occurs (H i) ∩ occurs (H j))

theorem depSum_eq (p : V → ℝ) (H : ι → Finset V) (s : Finset ι)
    (hH : ∀ i ∈ s, (H i).Nonempty) : depSum p H s = mean p H s + offSum p H s := by
  simp only [depSum, mean, offSum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hdiag : ¬ Disjoint (H i) (H i) := by
    obtain ⟨v, hv⟩ := hH i hi
    exact fun h => Finset.disjoint_left.mp h hv hv
  have hs : (∑ j ∈ s, if j = i then prob p (occurs (H i)) else 0) =
      prob p (occurs (H i)) := by simp [hi]
  rw [← hs, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    simp only [ite_eq_right hdiag, Set.inter_self, offCost, true_or,
      ↓reduceIte, add_zero]
  · simp [offCost, hij, Ne.symm hij]

theorem mean_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (H : ι → Finset V) (s : Finset ι) :
    0 ≤ mean p H s := Finset.sum_nonneg fun _ _ => prob_nonneg hp _

theorem offSum_nonneg (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1) (H : ι → Finset V) (s : Finset ι) :
    0 ≤ offSum p H s := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  simp only [offCost]
  split_ifs
  · rfl
  · exact prob_nonneg hp _

theorem janson [Fintype ι] (hp : ∀ v, 0 ≤ p v ∧ p v ≤ 1)
    (H : ι → Finset V) (s : Finset ι) (hH : ∀ i ∈ s, (H i).Nonempty)
    (hm : 0 < mean p H s) :
    mean p H s ≤ depSum p H s ∧
    prob p (avoids H s) ≤ Real.exp (-(mean p H s)^2 / (2 * depSum p H s)) := by
  have he := depSum_eq p H s hH
  have ho := offSum_nonneg hp H s
  have hmd : mean p H s ≤ depSum p H s := by linarith
  have hd : 0 < depSum p H s := hm.trans_le hmd
  refine ⟨hmd, ?_⟩
  let q := mean p H s / depSum p H s
  have hq : 0 ≤ q ∧ q ≤ 1 :=
    ⟨(div_pos hm hd).le, (div_le_one hd).mpr hmd⟩
  apply (janson_thinned hp H s hq).trans
  apply Real.exp_le_exp.mpr
  have hod : offSum p H s ≤ depSum p H s := by linarith
  calc
    -q * mean p H s + q ^ 2 * offSum p H s / 2 ≤
        -q * mean p H s + q ^ 2 * depSum p H s / 2 := by
      gcongr
    _ = -(mean p H s)^2 / (2 * depSum p H s) := by
      dsimp [q]
      field_simp
      ring

end FiniteJanson

end OAI
