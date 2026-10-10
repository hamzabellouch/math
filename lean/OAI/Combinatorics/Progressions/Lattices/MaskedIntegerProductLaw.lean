import Mathlib.Probability.ProbabilityMassFunction.Monad
import OAI.Combinatorics.Progressions.Probability.PMFPointMassMixture

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical
variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def selectedIntegerMass (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (z : ∀ i : H, K i) : ℝ :=
  ∏ i : H, (p i (z i).val).toReal

noncomputable def selectedConditionedIntegerPMF (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (z : ∀ i : H, K i) (i : I) : PMF ℤ :=
  if hi : i ∈ H then PMF.pure (z ⟨i, hi⟩).val else p i

noncomputable def integerProductMass (p : I → PMF ℤ) (x : I → ℤ) : ℝ :=
  ∏ i, (p i (x i)).toReal

theorem integerProductMass_split (p : I → PMF ℤ) (H : Finset I) (x : I → ℤ) :
    integerProductMass p x = (∏ i : H, (p i (x i)).toReal) *
      ∏ i : {i // i ∉ H}, (p i (x i)).toReal := by
  have hu : @Finset.univ H (Subtype.fintype (fun i : I => i ∈ H)) =
      @Finset.univ H (Finset.Subtype.fintype H) := by ext i; simp
  simpa only [integerProductMass, hu] using
    (Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ H)
      (fun i => (p i (x i)).toReal)).symm

theorem selectedIntegerMass_conditioned_product (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (z : ∀ i : H, K i) (x : I → ℤ) :
    selectedIntegerMass p H K z * integerProductMass (selectedConditionedIntegerPMF p H K z) x =
      if ∀ i : H, (z i).val = x i then integerProductMass p x else 0 := by
  by_cases hx : ∀ i : H, (z i).val = x i
  · rw [ite_eq_left hx, integerProductMass_split _ H]
    have hm : selectedIntegerMass p H K z = ∏ i : H, (p i (x i)).toReal := by
      simp only [selectedIntegerMass, hx]
    have hs : (∏ i : H, (selectedConditionedIntegerPMF p H K z i (x i)).toReal) = 1 := by
      apply Finset.prod_eq_one
      intro i _
      simp only [selectedConditionedIntegerPMF, dite_eq_left i.property, hx,
        PMF.pure_apply_self, ENNReal.toReal_one]
    have hc : (∏ i : {i // i ∉ H},
        (selectedConditionedIntegerPMF p H K z i (x i)).toReal) =
          ∏ i : {i // i ∉ H}, (p i (x i)).toReal := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [selectedConditionedIntegerPMF, dite_eq_right i.property]
    rw [hs, hc, one_mul, hm, integerProductMass_split p H]
  · rw [ite_eq_right hx]
    obtain ⟨i, hi⟩ := not_forall.mp hx
    have hz : (selectedConditionedIntegerPMF p H K z i (x i)).toReal = 0 := by
      simp only [selectedConditionedIntegerPMF, dite_eq_left i.property,
        PMF.pure_apply_of_ne _ _ (Ne.symm hi), ENNReal.toReal_zero]
    have hp : integerProductMass (selectedConditionedIntegerPMF p H K z) x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i.val) hz
    rw [hp, mul_zero]

theorem selectedIntegerMass_product_decomposition (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (hK : ∀ i : H, ∀ k, p i k ≠ 0 → k ∈ K i) (x : I → ℤ) :
    (∑ z : ∀ i : H, K i, selectedIntegerMass p H K z *
      integerProductMass (selectedConditionedIntegerPMF p H K z) x) =
        integerProductMass p x := by
  simp_rw [selectedIntegerMass_conditioned_product]
  by_cases hx : ∀ i : H, x i ∈ K i
  · let z₀ : ∀ i : H, K i := fun i => ⟨x i, hx i⟩
    rw [Finset.sum_eq_single z₀]
    · simp [z₀]
    · intro z _ hz
      have hne : ¬∀ i : H, (z i).val = x i := by
        intro h
        apply hz
        funext i
        exact Subtype.ext (h i)
      rw [ite_eq_right hne]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hz : p i (x i) = 0 := by by_contra h; exact hi (hK i (x i) h)
    have hp : integerProductMass p x = 0 := Finset.prod_eq_zero
      (Finset.mem_univ i.val) (by simp only [hz, ENNReal.toReal_zero])
    simp [hp]

theorem selectedIntegerMass_masked_product_bounds (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (hK : ∀ i : H, ∀ k, p i k ≠ 0 → k ∈ K i)
    (E : (∀ i : H, K i) → Prop) (x : I → ℤ) :
    0 ≤ (∑ z : ∀ i : H, K i, if E z then selectedIntegerMass p H K z *
      integerProductMass (selectedConditionedIntegerPMF p H K z) x else 0) ∧
    (∑ z : ∀ i : H, K i, if E z then selectedIntegerMass p H K z *
      integerProductMass (selectedConditionedIntegerPMF p H K z) x else 0) ≤
        integerProductMass p x := by
  have hnonneg (z : ∀ i : H, K i) : 0 ≤ selectedIntegerMass p H K z *
      integerProductMass (selectedConditionedIntegerPMF p H K z) x := by
    unfold selectedIntegerMass integerProductMass
    positivity
  constructor
  · apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact hnonneg z
    · exact le_rfl
  · rw [← selectedIntegerMass_product_decomposition p H K hK x]
    apply Finset.sum_le_sum
    intro z _
    split_ifs <;> simp only [le_refl, hnonneg]

omit [Fintype I] in
theorem selectedIntegerMass_total (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (hK : ∀ i : H, ∀ k, p i k ≠ 0 → k ∈ K i) :
    (∑ z : ∀ i : H, K i, selectedIntegerMass p H K z) = 1 := by
  unfold selectedIntegerMass
  rw [← Fintype.prod_sum (fun (i : H) (z : K i) => (p i z.val).toReal)]
  apply Finset.prod_eq_one
  intro i _
  rw [Finset.sum_coe_sort (K i) (fun k => (p i k).toReal)]
  have hz (k : ℤ) (hk : k ∉ K i) : (p i k).toReal = 0 := by
    have hp : p i k = 0 := by by_contra h; exact hk (hK i k h)
    rw [hp, ENNReal.toReal_zero]
  exact (hasSum_sum_of_ne_finset_zero hz).unique (pmf_toReal_hasSum (p i))

omit [Fintype I] in
theorem selectedIntegerMass_masked_total_bounds (p : I → PMF ℤ) (H : Finset I)
    (K : H → Finset ℤ) (hK : ∀ i : H, ∀ k, p i k ≠ 0 → k ∈ K i)
    (E : (∀ i : H, K i) → Prop) :
    0 ≤ (∑ z : ∀ i : H, K i, if E z then selectedIntegerMass p H K z else 0) ∧
      (∑ z : ∀ i : H, K i, if E z then selectedIntegerMass p H K z else 0) ≤ 1 := by
  have hpos (z : ∀ i : H, K i) : 0 ≤ selectedIntegerMass p H K z := by
    unfold selectedIntegerMass
    positivity
  constructor
  · apply Finset.sum_nonneg
    intro z _
    split_ifs
    · exact hpos z
    · exact le_rfl
  · rw [← selectedIntegerMass_total p H K hK]
    apply Finset.sum_le_sum
    intro z _
    split_ifs
    · exact le_rfl
    · exact hpos z

end Erdos3

end

end OAI
