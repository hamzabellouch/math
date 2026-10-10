import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedRawDensity
import OAI.MathematicalPhysics.ContinuumCoulomb.Programs.CoulombNormalizationProgram

namespace OAI

/-! Uniform raw-integral bounds for certified normalization of the
finite-box numerical output. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem localizedRawCoulombBox_bound {freq ε : ℝ} (hf : 0 < freq) (hε : 0 < ε)
    (L : ℝ) (u : PlanarPosition) :
    |localizedRawCoulombBox freq ε L u| ≤ ε⁻¹ * localizedRawMass freq ^ 2 := by
  let f := localizedRawDensity freq
  let S := coulombNumericalBox L ×ˢ coulombNumericalBox L
  let F := cappedPairIntegrand ε (planarCenter u) f f
  have hfi := localizedRawDensity_integrable hf
  have hm : Integrable (fun p : Position × Position => ε⁻¹ * (f p.1 * f p.2)) := by
    have hp : Integrable (fun p : Position × Position => f p.1 * f p.2) := by
      simpa only [Measure.volume_eq_prod] using hfi.mul_prod hfi
    exact hp.const_mul _
  have hpoint (p : Position × Position) : ‖S.indicator F p‖ ≤ ε⁻¹ * (f p.1 * f p.2) := by
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Real.norm_of_nonneg (show 0 ≤ F p from
        mul_nonneg (mul_nonneg (localizedRawDensity_nonnegative _ _)
          (localizedRawDensity_nonnegative _ _)) (cappedCoulombKernel_nonnegative hε _))]
      change f p.1 * f p.2 * cappedCoulombKernel ε _ ≤ _
      calc
        _ ≤ f p.1 * f p.2 * ε⁻¹ := mul_le_mul_of_nonneg_left (cappedCoulombKernel_le hε _)
          (mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _))
        _ = _ := by ring
    · rw [Set.indicator_of_notMem hp, norm_zero]
      exact mul_nonneg (inv_nonneg.mpr hε.le)
        (mul_nonneg (localizedRawDensity_nonnegative _ _) (localizedRawDensity_nonnegative _ _))
  have hb := norm_integral_le_of_norm_le (f := S.indicator F) hm (Filter.Eventually.of_forall hpoint)
  rw [integral_indicator ((coulombNumericalBox_measurable L).prod
    (coulombNumericalBox_measurable L)), Real.norm_eq_abs] at hb
  apply hb.trans_eq
  rw [integral_const_mul, Measure.volume_eq_prod, integral_prod_mul]
  change ε⁻¹ * ((∫ x, localizedRawDensity freq x) * ∫ x, localizedRawDensity freq x) = _
  rw [localizedRawDensity_mass hf]
  ring

theorem localizedCoulombBox_eq_normalizedRaw {freq : ℝ} (hf : 0 < freq)
    (ε L : ℝ) (u : PlanarPosition) :
    localizedCoulombBoxIntegral freq ε L u =
      CoulombNormalization.coefficient freq * localizedRawCoulombBox freq ε L u := by
  rw [← localizedRawCoulombBox_quotient hf ε L u]
  unfold CoulombNormalization.coefficient
  ring

end ContinuumCoulomb

end

end OAI
