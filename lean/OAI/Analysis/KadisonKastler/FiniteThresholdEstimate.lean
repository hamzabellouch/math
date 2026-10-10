import OAI.Analysis.KadisonKastler.FiniteThresholdProjection

namespace OAI

/-! # Upper and lower energy bounds for finite spectral threshold cuts -/

namespace KadisonKastler

open Finset MeasureTheory
open scoped BigOperators

noncomputable section

variable {H ι κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [Fintype ι] [Fintype κ]
  (P : ι → H →L[ℂ] H) (Q : κ → H →L[ℂ] H)
  (hP : ∀ i, IsStarProjection (P i)) (hQ : ∀ j, IsStarProjection (Q j))
  (hPo : ∀ i k, i ≠ k → P i * P k = 0)
  (hQo : ∀ j l, j ≠ l → Q j * Q l = 0)
  (hPt : ∑ i, P i = 1) (hQt : ∑ j, Q j = 1)
  (hc : ∀ i j, Commute (P i) (Q j))

include hP hQ hPo hQo hPt hQt hc

theorem jointProjection_vector_mass (ξ : H) :
    (∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2) = ‖ξ‖ ^ 2 := by
  have he := norm_jointProjection_weighted_sum_sq P Q hP hQ hPo hQo hc (fun _ => 1) ξ
  simpa only [one_smul,jointProjection_total P Q hPt hQt,one_apply_eq_self,
    norm_one,one_pow,one_mul] using he.symm

theorem jointProjection_real_gap (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∑ a : ι × κ, ‖(P a.1 * Q a.2) ξ‖ ^ 2 * (c a.1-d a.2) ^ 2) =
      ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ ^ 2 := by
  have he := jointProjection_gap_energy P Q hP hQ hPo hQo hPt hQt hc
    (fun i => (c i : ℂ)) (fun j => (d j : ℂ)) ξ
  rw [he]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_comm]

theorem finiteThresholdProjection_integral_le (c : ι → ℝ) (d : κ → ℝ) (ξ : H) :
    (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) ≤
      ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ * ‖ξ‖ := by
  rw [finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc]
  have he := weighted_threshold_energy_le (univ : Finset (ι × κ))
    (fun a => c a.1) (fun a => d a.2) (fun a => ‖(P a.1 * Q a.2) ξ‖ ^ 2)
    (fun _ _ => sq_nonneg _)
  rw [integral_weighted_thresholdDifference_sq,
    jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,
    jointProjection_vector_mass P Q hP hQ hPo hQo hPt hQt hc] at he
  simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)] using he

theorem finiteThresholdProjection_integral_lower (c : ι → ℝ) (d : κ → ℝ) (ξ : H)
    (hrange : ∀ i j, |c i-d j| ≤ 2) :
    ‖((∑ i, (c i : ℂ) • P i) - (∑ j, (d j : ℂ) • Q j)) ξ‖ ^ 2 ≤
      2 * (∫ t, ‖(finiteThresholdProjection P c t - finiteThresholdProjection Q d t) ξ‖ ^ 2) := by
  rw [finiteThresholdProjection_integrated_energy P Q hP hQ hPo hQo hPt hQt hc,
    ← jointProjection_real_gap P Q hP hQ hPo hQo hPt hQt hc,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  have h := mul_le_mul_of_nonneg_right (hrange a.1 a.2) (abs_nonneg (c a.1-d a.2))
  rw [← sq, sq_abs] at h
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg ‖(P a.1 * Q a.2) ξ‖)]

end

end KadisonKastler

end OAI
