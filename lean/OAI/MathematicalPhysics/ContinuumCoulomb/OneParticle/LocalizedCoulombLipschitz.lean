import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedCoulombTranslation

namespace OAI

/-! A uniform Lipschitz estimate for the actual direct-Coulomb profile. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedCoulombLipschitzConstant (freq : ℝ) : ℝ :=
  localizedAmplitudeBound freq ^ 2 *
    (∫ y in Metric.ball (0 : Position) 1, NeutralAtom.coulombKernel y ^ 2) + 1

theorem localizedCoulombLipschitzConstant_nonnegative (freq : ℝ) :
    0 ≤ localizedCoulombLipschitzConstant freq :=
  add_nonneg (mul_nonneg (sq_nonneg _)
    (integral_nonneg (fun _ => sq_nonneg _))) zero_le_one

theorem localizedDensity_potential_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x y : Position) :
    ‖NeutralAtom.potentialOf (localizedDensity freq u) x -
      NeutralAtom.potentialOf (localizedDensity freq u) y‖ ≤
        localizedCoulombLipschitzConstant freq * ‖x - y‖ := by
  simpa only [localizedDensity_mass hfreq u, localizedCoulombLipschitzConstant] using
    NeutralAtom.potentialOf_lipschitz_bound (localizedDensity_integrable hfreq u)
      (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x y

theorem localizedCoulombProfileAt_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Integrable (fun x => localizedDensity freq 0 x *
      NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u)) := by
  apply (localizedCoulombCoeff_integrable hfreq 0 u).congr
  exact Filter.Eventually.of_forall (fun x =>
    congrArg (fun z => localizedDensity freq 0 x * z)
      (localizedDensity_potential_translate freq u x))

theorem localizedCoulombProfileAt_norm_sub {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    ‖localizedCoulombProfileAt freq u - localizedCoulombProfileAt freq v‖ ≤
      localizedCoulombLipschitzConstant freq * ‖u - v‖ := by
  have hpt (x : Position) :
      ‖localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
        localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v)‖ ≤
      (localizedCoulombLipschitzConstant freq * ‖u - v‖) * localizedDensity freq 0 x := by
    rw [← mul_sub, norm_mul, Real.norm_of_nonneg (localizedDensity_nonnegative freq 0 x)]
    have h := localizedDensity_potential_norm_sub hfreq 0 (x - planarCenter u) (x - planarCenter v)
    rw [show (x - planarCenter u) - (x - planarCenter v) = planarCenter v - planarCenter u by abel,
      norm_sub_rev (planarCenter v) (planarCenter u), planarCenter_norm_sub] at h
    calc
      _ ≤ localizedDensity freq 0 x *
          (localizedCoulombLipschitzConstant freq * ‖u - v‖) :=
        mul_le_mul_of_nonneg_left h (localizedDensity_nonnegative freq 0 x)
      _ = _ := mul_comm _ _
  unfold localizedCoulombProfileAt
  rw [← integral_sub (localizedCoulombProfileAt_integrable hfreq u)
    (localizedCoulombProfileAt_integrable hfreq v)]
  have h := norm_integral_le_of_norm_le
    (f := fun x => localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter u) -
      localizedDensity freq 0 x * NeutralAtom.potentialOf (localizedDensity freq 0) (x - planarCenter v))
    ((localizedDensity_integrable hfreq 0).const_mul
      (localizedCoulombLipschitzConstant freq * ‖u - v‖))
    (Filter.Eventually.of_forall hpt)
  simpa only [integral_const_mul, localizedDensity_mass hfreq 0, mul_one] using h

theorem localizedCoulombProfileAt_continuous {freq : ℝ} (hfreq : 0 < freq) :
    Continuous (localizedCoulombProfileAt freq) :=
  (show LipschitzWith
      ⟨localizedCoulombLipschitzConstant freq, localizedCoulombLipschitzConstant_nonnegative freq⟩
      (localizedCoulombProfileAt freq) from
    lipschitzWith_iff_norm_sub_le.mpr (localizedCoulombProfileAt_norm_sub hfreq)).continuous

theorem localizedCoulombProfile_continuous {freq : ℝ} (hfreq : 0 < freq) :
    Continuous (localizedCoulombProfile freq) :=
  (localizedCoulombProfileAt_continuous hfreq).comp (continuous_id.smul continuous_const)

end ContinuumCoulomb

end

end OAI
