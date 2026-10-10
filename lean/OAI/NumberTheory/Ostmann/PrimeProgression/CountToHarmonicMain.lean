import OAI.NumberTheory.Ostmann.PrimeProgression.CountToHarmonicAbel

namespace OAI

open scoped BigOperators
open Set MeasureTheory
namespace Ostmann.Arithmetic.PrimeProgression

lemma continuousOn_of_hasDerivAt_Icc (F D : ℝ → ℝ) {A B : ℝ}
    (hF : ∀ t ∈ Icc A B, HasDerivAt F (D t) t) : ContinuousOn F (Icc A B) :=
  fun t ht => (hF t ht).continuousAt.continuousWithinAt

lemma continuousOn_inv_Icc {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun t : ℝ => t⁻¹) (Icc A B) := by
  apply ContinuousOn.inv₀ continuousOn_id
  intro t ht
  exact ne_of_gt (hA.trans_le ht.1)

theorem continuous_reciprocal_abel_identity (F D : ℝ → ℝ) {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hF : ∀ t ∈ Icc A B, HasDerivAt F (D t) t) (hD : ContinuousOn D (Icc A B)) :
    B⁻¹ * F B - A⁻¹ * F A + (∫ t in A..B, (t ^ 2)⁻¹ * F t) =
      ∫ t in A..B, t⁻¹ * D t := by
  have hcF := continuousOn_of_hasDerivAt_Icc F D hF
  have hInv := continuousOn_inv_Icc (B := B) hA
  have hSq := continuousOn_inv_sq (B := B) hA
  have hiD : IntervalIntegrable (fun t => t⁻¹ * D t) volume A B :=
    (hInv.mul hD).intervalIntegrable_of_Icc hAB
  have hiF : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * F t) volume A B :=
    (hSq.mul hcF).intervalIntegrable_of_Icc hAB
  have hderiv (t : ℝ) (ht : t ∈ Icc A B) :
      HasDerivAt (fun x : ℝ => x⁻¹ * F x) (t⁻¹ * D t - (t ^ 2)⁻¹ * F t) t := by
    convert (hasDerivAt_inv (ne_of_gt (hA.trans_le ht.1))).mul (hF t ht) using 1
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hderiv t (by simpa only [uIcc_of_le hAB] using ht)) (hiD.sub hiF)
  rw [intervalIntegral.integral_sub hiD hiF] at h
  linarith

theorem reciprocal_count_error_identity (c : ℕ → ℝ) (F D : ℝ → ℝ) {A B : ℝ}
    (hA : 0 < A) (hAB : A ≤ B)
    (hF : ∀ t ∈ Icc A B, HasDerivAt F (D t) t) (hD : ContinuousOn D (Icc A B)) :
    (∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, (n : ℝ)⁻¹ * c n) -
        (∫ t in A..B, t⁻¹ * D t) =
      B⁻¹ * (cumulativeSum c B - F B) - A⁻¹ * (cumulativeSum c A - F A) +
        ∫ t in A..B, (t ^ 2)⁻¹ * (cumulativeSum c t - F t) := by
  have hiC : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * cumulativeSum c t) volume A B :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hAB).mpr
      (cumulativeSum_inv_sq_integrable c hA)
  have hiF : IntervalIntegrable (fun t => (t ^ 2)⁻¹ * F t) volume A B :=
    ((continuousOn_inv_sq hA).mul (continuousOn_of_hasDerivAt_Icc F D hF)).intervalIntegrable_of_Icc hAB
  have hmain := continuous_reciprocal_abel_identity F D hA hAB hF hD
  rw [reciprocal_abel_identity c hA hAB, ← hmain]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hiC hiF]
  ring

end Ostmann.Arithmetic.PrimeProgression

end OAI
