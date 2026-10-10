import OAI.Probability.ContinuumTransition.FiniteBounds

namespace OAI

universe u_1 u_2

section
open scoped Topology BigOperators ENNReal
open Filter MeasureTheory Set
namespace ContinuumTemperature

theorem ereal_sum_eq_top_of_exists {α : Type u_1} (s : Finset α) (f : α → EReal)
    (hf : ∀ i ∈ s, f i ≠ ⊥) (ht : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at ht
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    obtain ⟨j, hj, hjt⟩ := ht
    rcases Finset.mem_insert.mp hj with rfl | hj
    · rw [hjt]
      exact EReal.top_add_of_ne_bot (ereal_sum_ne_bot s f
        (fun k hk => hf k (Finset.mem_insert_of_mem hk)))
    · rw [ih (fun k hk => hf k (Finset.mem_insert_of_mem hk)) ⟨j, hj, hjt⟩]
      exact EReal.add_top_of_ne_bot (hf i (Finset.mem_insert_self _ _))

theorem energy_eq_top_iff (φ : ℝ → ℝ) {N : ℕ} (x : Fin N → Space) :
    energy φ x = ⊤ ↔ ¬Function.Injective x := by
  constructor
  · intro he hx
    rw [energy_eq_real_of_injective φ hx] at he
    exact EReal.coe_ne_top _ he
  · intro hx
    have hh : ∃ i j, i ≠ j ∧ x i = x j := by
      by_contra hc
      apply hx
      intro i j heq
      by_contra hne
      exact hc ⟨i, j, hne, heq⟩
    obtain ⟨i, j, hij, he⟩ := hh
    have hpair {i j : Fin N} (hij : i < j) (he : x i = x j) : energy φ x = ⊤ := by
      apply ereal_sum_eq_top_of_exists _ _
        (fun i _ => ereal_sum_ne_bot _ _ (fun j _ => radialPotential_ne_bot _ _))
      refine ⟨i, Finset.mem_univ _, ?_⟩
      apply ereal_sum_eq_top_of_exists _ _ (fun j _ => radialPotential_ne_bot _ _)
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, by
        simp [he, radialPotential]⟩
    rcases lt_or_gt_of_ne hij with h | h
    · exact hpair h he
    · exact hpair h he.symm

noncomputable def realPairEnergy (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : ℝ := by
  classical
  exact (1/2 : ℝ) * ∑ i, ∑ j, if i = j then 0 else φ ‖x i - x j‖

theorem realPairEnergy_eq_ordered (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι] [LinearOrder ι]
    (x : ι → Space) :
    realPairEnergy φ x = ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), φ ‖x i - x j‖ := by
  classical
  have hsplit (i j : ι) : (if i = j then 0 else φ ‖x i - x j‖) =
      (if i < j then φ ‖x i - x j‖ else 0) +
      (if j < i then φ ‖x j - x i‖ else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, ne_of_lt h, not_lt_of_ge h.le]
    · subst j; simp
    · simp [h, ne_of_gt h, not_lt_of_ge h.le, norm_sub_rev]
  calc
    realPairEnergy φ x = (1/2 : ℝ) * ∑ i, ∑ j,
        ((if i < j then φ ‖x i - x j‖ else 0) +
          (if j < i then φ ‖x j - x i‖ else 0)) := by
      unfold realPairEnergy
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      by_cases hij : i = j
      · simpa only [ite_eq_left hij] using hsplit i j
      · simpa only [ite_eq_right hij] using hsplit i j
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j : ι => if j < i then φ ‖x j - x i‖ else 0)]
      simp only [Finset.sum_filter]
      ring

noncomputable def symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {ι : Type u_1} [Fintype ι] (x : ι → Space) : ℝ :=
  if Function.Injective x then Real.exp (-β * realPairEnergy φ x) else 0

theorem boltzmann_eq_symmetricWeight (φ : ℝ → ℝ) (β : ℝ)
    {N : ℕ} (x : Fin N → Space) : boltzmann φ β x = symmetricWeight φ β x := by
  classical
  by_cases hx : Function.Injective x
  · simp only [boltzmann, energy_eq_real_of_injective φ hx, EReal.coe_ne_top,
      ite_false, EReal.toReal_coe, symmetricWeight, ite_eq_left hx, realPairEnergy_eq_ordered]
  · simp only [boltzmann, (energy_eq_top_iff φ x).2 hx, ite_true, symmetricWeight, ite_eq_right hx]

theorem realPairEnergy_relabel (φ : ℝ → ℝ) {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Space) : realPairEnergy φ (x ∘ e) = realPairEnergy φ x := by
  classical
  unfold realPairEnergy
  simp only [Function.comp_apply, ← e.injective.eq_iff]
  congr 1
  rw [← Equiv.sum_comp e]
  apply Finset.sum_congr rfl
  intro i _
  exact Equiv.sum_comp e (fun j => if e i = j then 0 else φ ‖x (e i) - x j‖)

theorem symmetricWeight_relabel (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} {κ : Type u_2}
    [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Space) :
    symmetricWeight φ β (x ∘ e) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (x ∘ e) ↔ Function.Injective x :=
    by
      constructor
      · intro hx i j hij
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        exact congrArg e (hx hij)
      · exact fun hx => hx.comp e.injective
  simp only [symmetricWeight, hh, realPairEnergy_relabel]

theorem symmetric_matrix_split {ι : Type u_1} [Fintype ι] (p : ι → Prop)
    [DecidablePred p] (F : ι → ι → ℝ) (hsym : ∀ i j, F i j = F j i) :
    (∑ i, ∑ j, F i j) =
      (∑ i : {i // p i}, ∑ j : {j // p j}, F i j) +
      (∑ i : {i // ¬p i}, ∑ j : {j // ¬p j}, F i j) +
      2 * (∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j) := by
  classical
  have houter := Fintype.sum_subtype_add_sum_subtype p (fun i => ∑ j, F i j)
  have hinner (i : ι) := Fintype.sum_subtype_add_sum_subtype p (F i)
  rw [← houter]
  simp_rw [← hinner, Finset.sum_add_distrib]
  have hh : (∑ i : {i // ¬p i}, ∑ j : {j // p j}, F i j) =
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, F i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact hsym _ _
  rw [hh]
  ring

theorem realPairEnergy_split (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (p : ι → Prop) [DecidablePred p] (x : ι → Space) :
    realPairEnergy φ x =
      realPairEnergy φ (fun i : {i // p i} => x i) +
      realPairEnergy φ (fun i : {i // ¬p i} => x i) +
      ∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖ := by
  classical
  have heq := symmetric_matrix_split p (fun i j => if i = j then 0 else φ ‖x i - x j‖)
    (fun i j => by by_cases h : i = j <;> simp [h, eq_comm, norm_sub_rev])
  have hcross (i : {i // p i}) (j : {i // ¬p i}) : (i : ι) ≠ j := by
    intro h
    exact j.property (h ▸ i.property)
  have hself (a b : {i // p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  have hself' (a b : {i // ¬p i}) : ((a : ι) = b) ↔ a = b := Subtype.coe_inj
  unfold realPairEnergy
  rw [heq]
  simp only [hself, hself', hcross, ite_false]
  ring

theorem symmetricWeight_nonneg (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) : 0 ≤ symmetricWeight φ β x := by
  unfold symmetricWeight
  split_ifs
  · positivity
  · rfl

theorem symmetricWeight_separated (φ : ℝ → ℝ) {β : ℝ} (hβ : 0 ≤ β)
    {ι : Type u_1} [Fintype ι] (p : ι → Prop) [DecidablePred p]
    {A B : Set Space} (hd : Disjoint A B)
    (hφ : ∀ a ∈ A, ∀ b ∈ B, φ ‖a - b‖ ≤ 0)
    (x : ι → Space) (hA : ∀ i, p i → x i ∈ A) (hB : ∀ i, ¬p i → x i ∈ B) :
    symmetricWeight φ β (fun i : {i // p i} => x i) *
      symmetricWeight φ β (fun i : {i // ¬p i} => x i) ≤ symmetricWeight φ β x := by
  classical
  by_cases ha : Function.Injective (fun i : {i // p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right ha, zero_mul] using symmetricWeight_nonneg φ β x
  by_cases hb : Function.Injective (fun i : {i // ¬p i} => x i)
  swap
  · simpa only [symmetricWeight, ite_eq_right hb, mul_zero] using symmetricWeight_nonneg φ β x
  have hx : Function.Injective x := by
    intro i j hij
    by_cases hi : p i <;> by_cases hj : p j
    · exact congrArg Subtype.val (ha (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
    · exact False.elim (Set.disjoint_left.mp hd (hA i hi) (hij ▸ hB j hj))
    · exact False.elim (Set.disjoint_left.mp hd (hA j hj) (hij ▸ hB i hi))
    · exact congrArg Subtype.val (hb (a₁ := ⟨i, hi⟩) (a₂ := ⟨j, hj⟩) hij)
  have hc : (∑ i : {i // p i}, ∑ j : {j // ¬p j}, φ ‖x i - x j‖) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact Finset.sum_nonpos (fun j _ => hφ _ (hA i i.property) _ (hB j j.property))
  simp only [symmetricWeight, ite_eq_left ha, ite_eq_left hb, ite_eq_left hx, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [realPairEnergy_split φ p x]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hβ hc]

theorem realPairEnergy_translate (φ : ℝ → ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    realPairEnergy φ (fun i => x i + v) = realPairEnergy φ x := by
  classical
  simp only [realPairEnergy, add_sub_add_right_eq_sub]

theorem symmetricWeight_translate (φ : ℝ → ℝ) (β : ℝ) {ι : Type u_1} [Fintype ι]
    (x : ι → Space) (v : Space) :
    symmetricWeight φ β (fun i => x i + v) = symmetricWeight φ β x := by
  classical
  have hh : Function.Injective (fun i => x i + v) ↔ Function.Injective x := by
    simp only [Function.Injective, add_left_inj]
  simp only [symmetricWeight, hh, realPairEnergy_translate]

end ContinuumTemperature
end

end OAI
