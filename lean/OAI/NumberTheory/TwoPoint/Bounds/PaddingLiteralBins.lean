import OAI.NumberTheory.TwoPoint.Bounds.PaddingBinSquare
import OAI.NumberTheory.TwoPoint.Bounds.PaddingTilt
import OAI.NumberTheory.TwoPoint.Walks.RetainedDivisorMass
import Mathlib.Data.Fintype.Powerset

namespace OAI

/-! The bin mass is the literal normalized sum of padding-divisor weights.
Boolean selections are finite subsets, so no extra multiplicity is present. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def selectedCoordinates (Q : Finset ℕ) (b : Q → Bool) : Finset Q :=
  univ.filter (fun p => b p = true)

noncomputable def selectionFinsetEquiv (Q : Finset ℕ) : (Q → Bool) ≃ Finset Q where
  toFun := selectedCoordinates Q
  invFun S p := decide (p ∈ S)
  left_inv b := by
    funext p
    cases hp : b p <;> simp [selectedCoordinates, hp]
  right_inv S := by ext p; simp [selectedCoordinates]

lemma selection_supported_iff (Q : Finset ℕ) (a b : Q → Bool) :
    PaddingSelectionSupported Q a b ↔ selectedCoordinates Q b ⊆ selectedCoordinates Q a := by
  simp only [PaddingSelectionSupported, subset_iff, selectedCoordinates,
    mem_filter, mem_univ, true_and]

lemma paddingTiltWeight_eq_five_pow (Q : Finset ℕ) (a : Q → Bool) :
    paddingTiltWeight Q a = (5 : ℝ) ^ (selectedCoordinates Q a).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingTiltWeight]

lemma paddingDivisorCoefficient_eq_four_pow (Q : Finset ℕ) (b : Q → Bool) :
    paddingDivisorCoefficient Q b = (4 : ℝ) ^ (selectedCoordinates Q b).card := by
  rw [← prod_const]
  simp only [selectedCoordinates, prod_filter, paddingDivisorCoefficient]

noncomputable def paddingSelectedDivisor (Q : Finset ℕ) (b : Q → Bool) : ℕ :=
  ∏ p ∈ selectedCoordinates Q b, p.val

lemma paddingSelectedDivisor_log (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (b : Q → Bool) : Real.log (paddingSelectedDivisor Q b) = paddingLog Q b := by
  rw [paddingSelectedDivisor, Nat.cast_prod, Real.log_prod]
  · simp only [selectedCoordinates, sum_filter, paddingLog]
  · intro p _
    exact_mod_cast (hQ p p.property).ne_zero

lemma paddingBinMass_normalized_sum (Q : Finset ℕ) (a : Q → Bool)
    (η c : ℝ) (j : ℤ) :
    paddingBinMass Q a η c j = (paddingTiltWeight Q a)⁻¹ *
      ∑ b : Q → Bool,
        if PaddingSelectionSupported Q a b ∧ paddingBin η c (paddingLog Q b) = j
        then paddingDivisorCoefficient Q b else 0 := by
  simp only [paddingBinMass, FiniteLaw.probability, FiniteLaw.average,
    paddingDivisorLaw_weight_eq, mul_sum]
  apply sum_congr rfl
  intro b _
  by_cases hs : PaddingSelectionSupported Q a b <;>
    by_cases hb : paddingBin η c (paddingLog Q b) = j <;>
      simp [hs, hb, div_eq_mul_inv, mul_comm]

/-- The finite subset formula exactly matches `rho`: sum the weight
`4^omega(q)` over available squarefree padding divisors in the bin and
normalize by `5^omega_Q`. -/
lemma paddingBinMass_subset_formula (Q : Finset ℕ) (a : Q → Bool)
    (η c : ℝ) (j : ℤ) :
    paddingBinMass Q a η c j = (5 : ℝ) ^ (-(selectedCoordinates Q a).card : ℤ) *
      ∑ S : Finset Q,
        if S ⊆ selectedCoordinates Q a ∧
          paddingBin η c (∑ p ∈ S, Real.log p.val) = j
        then (4 : ℝ) ^ S.card else 0 := by
  rw [paddingBinMass_normalized_sum, paddingTiltWeight_eq_five_pow]
  rw [zpow_neg, zpow_natCast]
  congr 1
  calc
    _ = ∑ S : Finset Q,
        if PaddingSelectionSupported Q a ((selectionFinsetEquiv Q).symm S) ∧
            paddingBin η c (paddingLog Q ((selectionFinsetEquiv Q).symm S)) = j
        then paddingDivisorCoefficient Q ((selectionFinsetEquiv Q).symm S) else 0 :=
      ((selectionFinsetEquiv Q).symm.sum_comp _).symm
    _ = _ := by
      apply sum_congr rfl
      intro S _
      rw [selection_supported_iff, paddingDivisorCoefficient_eq_four_pow]
      have hs : selectedCoordinates Q ((selectionFinsetEquiv Q).symm S) = S :=
        (selectionFinsetEquiv Q).apply_symm_apply S
      rw [hs]
      have hl : paddingLog Q ((selectionFinsetEquiv Q).symm S) =
          ∑ p ∈ S, Real.log p.val := by
        change (∑ p : Q, if decide (p ∈ S) then Real.log p.val else 0) = _
        simp only [decide_eq_true_eq]
        rw [← sum_filter, filter_mem_eq_inter, univ_inter]
      rw [hl]
      split_ifs <;> rfl

end TwoPointCorrelations

end OAI
