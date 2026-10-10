import OAI.Analysis.CircleDomains.Sobolev.PolarAnnulusEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

namespace OAI

/-! Polar integration on a bounded annulus, with nonnegative measurable
integrands. The angular interval is fixed to the standard polar chart. -/
open Set MeasureTheory Metric Real
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma complex_polar_symm_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply]
  apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

lemma lintegral_circleMap_annulus (q : ℂ → ℝ≥0∞) (hq : Measurable q)
    {a b : ℝ} (ha : 0 ≤ a) :
    (∫⁻ z in {z : ℂ | a < ‖z‖ ∧ ‖z‖ < b}, q z) =
      ∫⁻ r in Ioo a b, ENNReal.ofReal r *
        ∫⁻ θ in Ioo (-Real.pi) Real.pi, q (circleMap 0 r θ) := by
  rw [lintegral_polar_annulus q hq ha]
  apply lintegral_congr
  intro r
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  apply lintegral_congr
  intro θ
  rw [complex_polar_symm_circleMap]

end CircleDomainRigidity

end

end OAI
