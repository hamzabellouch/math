import Mathlib
import OAI.Analysis.AffineBernstein.ConvexGradientBound
import OAI.Analysis.AffineBernstein.TubeWeightAlgebra

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/- The source's unweighted tube mass estimate from support height and the two
actual determinant integrals. A positive angular determinant is not needed for
this upper estimate: the real square root already discards its negative part. -/
lemma lintegral_tube_mass_le {n : ℕ} {h B Q : X → ℝ}
    (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (hBp : ∀ᵐ x ∂μ, 0 ≤ B x) {r : ℝ} (hr : 0 < r)
    (hbound : ∀ᵐ x ∂μ, r ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)) ∂μ) ≤
      ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂μ) ^ (1/(2:ℝ)) *
        (∫⁻ x, ENNReal.ofReal (Q x) ∂μ) ^ (1/(2:ℝ)) := by
  let Qp := fun x => max (Q x) 0
  have hQp : AEMeasurable Qp μ := hQ.max aemeasurable_const
  have hpos : ∀ᵐ x ∂μ, 0 ≤ Qp x := Filter.Eventually.of_forall fun _ => le_max_right _ _
  have hh := lintegral_ofReal_geometric_mean_le μ (p := (1/(2:ℝ))) (by norm_num)
    (by norm_num) hB hQp hBp hpos
  have hqint : (∫⁻ x, ENNReal.ofReal (Qp x) ∂μ) = ∫⁻ x, ENNReal.ofReal (Q x) ∂μ := by
    congr 1
    funext x
    simp [Qp]
  norm_num only [show (1:ℝ)-1/2 = 1/2 by norm_num] at hh
  rw [hqint] at hh
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        ENNReal.ofReal ((B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ))) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hBp,hbound] with x hbx hhx
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      apply ENNReal.ofReal_le_ofReal
      unfold tubeMeasureCoefficient
      have hrp : (h x)^(-(n:ℝ)/2) ≤ r^(-(n:ℝ)/2) :=
        Real.rpow_le_rpow_of_nonpos hr hhx (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
      have hs : Real.sqrt (B x*Q x) ≤ (B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ)) := by
        rw [Real.sqrt_mul hbx,← Real.sqrt_eq_rpow,← Real.sqrt_eq_rpow]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (le_max_left _ _)) (Real.sqrt_nonneg _)
      exact mul_le_mul hrp hs (Real.sqrt_nonneg _) (Real.rpow_nonneg hr.le _)
    _ = ENNReal.ofReal (r ^ (-(n:ℝ)/2)) *
        ∫⁻ x, ENNReal.ofReal ((B x)^(1/(2:ℝ)) * (Qp x)^(1/(2:ℝ))) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_right hh (ENNReal.ofReal (r ^ (-(n:ℝ)/2)))

end AffineBernstein
end

end OAI
