import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CappedCoulombMass
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombSymmetry

namespace OAI

/-! The actual six-coordinate bounded integrand for Coulomb quadrature,
with an explicit error to the original full singular coefficient. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedCappedIntegrand (freq ε : ℝ) (u v : PlanarPosition) (p : Position × Position) : ℝ :=
  localizedDensity freq u p.1 *
    (cappedCoulombKernel ε (p.1 - p.2) * localizedDensity freq v p.2)

def localizedCappedCoulombCoeff (freq ε : ℝ) (u v : PlanarPosition) : ℝ :=
  ∫ p, localizedCappedIntegrand freq ε u v p

theorem localizedCappedIntegrand_integrable {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) : Integrable (localizedCappedIntegrand freq ε u v) := by
  have hp : Integrable (fun p : Position × Position =>
      localizedDensity freq u p.1 * localizedDensity freq v p.2) := by
    simpa only [Measure.volume_eq_prod] using
      (localizedDensity_integrable hfreq u).mul_prod (localizedDensity_integrable hfreq v)
  have hk : Continuous (fun p : Position × Position => cappedCoulombKernel ε (p.1 - p.2)) :=
    (cappedCoulombKernel_continuous hε).comp (continuous_fst.sub continuous_snd)
  have h := hp.mul_bdd (c := ε⁻¹) hk.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => by
      rw [Real.norm_of_nonneg (cappedCoulombKernel_nonnegative hε _)]
      exact cappedCoulombKernel_le hε _))
  convert h using 1
  funext p
  unfold localizedCappedIntegrand
  ring

theorem localizedCappedCoulombCoeff_nested {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) :
    localizedCappedCoulombCoeff freq ε u v =
      ∫ x, localizedDensity freq u x * cappedCoulombPotential ε (localizedDensity freq v) x := by
  unfold localizedCappedCoulombCoeff
  rw [Measure.volume_eq_prod, integral_prod _
    (by simpa only [Measure.volume_eq_prod] using localizedCappedIntegrand_integrable hfreq hε u v)]
  simp only [localizedCappedIntegrand, integral_const_mul, cappedCoulombPotential]

theorem localizedCappedCoulombCoeff_error {freq ε : ℝ} (hfreq : 0 < freq) (hε : 0 < ε)
    (u v : PlanarPosition) :
    |localizedCoulombCoeff freq u v - localizedCappedCoulombCoeff freq ε u v| ≤
      2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2 := by
  have hic : Integrable (fun x => localizedDensity freq u x *
      cappedCoulombPotential ε (localizedDensity freq v) x) := by
    have h := (localizedCappedIntegrand_integrable hfreq hε u v).integral_prod_left
    simpa only [localizedCappedIntegrand, integral_const_mul, cappedCoulombPotential] using h
  rw [localizedCappedCoulombCoeff_nested hfreq hε, localizedCoulombCoeff,
    ← integral_sub (localizedCoulombCoeff_integrable hfreq u v) hic]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x -
      localizedDensity freq u x * cappedCoulombPotential ε (localizedDensity freq v) x)
    ((localizedDensity_integrable hfreq u).mul_const
      (2 * Real.pi * localizedAmplitudeBound freq ^ 2 * ε ^ 2))
    (Filter.Eventually.of_forall (fun x => by
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq u x),
        Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (cappedCoulombPotential_error_explicit hε (localizedDensity_integrable hfreq v)
          (localizedDensity_nonnegative freq v) (localizedDensity_bound hfreq v) x)
        (localizedDensity_nonnegative freq u x)))
  simpa only [Real.norm_eq_abs, integral_mul_const, localizedDensity_mass hfreq u, one_mul] using h

end ContinuumCoulomb

end

end OAI
