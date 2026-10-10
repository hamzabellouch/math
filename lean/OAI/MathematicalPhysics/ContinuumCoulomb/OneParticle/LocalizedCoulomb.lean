import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.SplitCoordinates
import OAI.Analysis.CoulombRadii.Variational.CorrectionDensity

namespace OAI

/-! Finite actual Coulomb interactions of the localized densities. Bounded
probability densities permit the existing elementary near/far Coulomb bound;
no interaction coefficient is introduced as a spectral input. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedAmplitudeBound (freq : ℝ) : ℝ :=
  (1 / Real.sqrt (∫ r, planarResolventMode r ^ 2)) *
    (1 / Real.sqrt (Real.sqrt (Real.pi / freq)))

theorem localizedAmplitudeBound_positive {freq : ℝ} (hfreq : 0 < freq) :
    0 < localizedAmplitudeBound freq :=
  mul_pos (one_div_pos.mpr (Real.sqrt_pos.mpr planarResolventMode_square_integral_positive))
    (one_div_pos.mpr (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (div_pos Real.pi_pos hfreq))))

theorem continuumLocalizedMode_le {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    continuumLocalizedMode freq u x ≤ localizedAmplitudeBound freq := by
  have hp (r : PlanarPosition) : normalizedPlanarMode r ≤
      1 / Real.sqrt (∫ s, planarResolventMode s ^ 2) :=
    div_le_div_of_nonneg_right (planarResolventMode_le_one r) (Real.sqrt_nonneg _)
  have hv (z : ℝ) : verticalMode freq z ≤ 1 / Real.sqrt (Real.sqrt (Real.pi / freq)) := by
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  exact mul_le_mul (hp _) (hv _) (verticalMode_positive hfreq _).le
    (by positivity)

def localizedDensity (freq : ℝ) (u : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x ^ 2

theorem localizedDensity_continuous (freq : ℝ) (u : PlanarPosition) :
    Continuous (localizedDensity freq u) := (continuumLocalizedMode_C7 freq u).continuous.pow 2

theorem localizedDensity_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ localizedDensity freq u x := sq_nonneg _

theorem localizedDensity_positive {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) : 0 < localizedDensity freq u x :=
  sq_pos_of_pos (continuumLocalizedMode_positive hfreq u x)

theorem localizedDensity_integrable {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    Integrable (localizedDensity freq u) :=
  (memLp_two_iff_integrable_sq (continuumLocalizedMode_C7 freq u).continuous.aestronglyMeasurable).mp
    (continuumLocalizedMode_memLp hfreq u)

theorem localizedDensity_mass {freq : ℝ} (hfreq : 0 < freq) (u : PlanarPosition) :
    (∫ x, localizedDensity freq u x) = 1 := continuumLocalizedMode_normalized hfreq u

theorem localizedDensity_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    localizedDensity freq u x ≤ localizedAmplitudeBound freq ^ 2 :=
  (sq_le_sq₀ (continuumLocalizedMode_positive hfreq u x).le
    (localizedAmplitudeBound_positive hfreq).le).mpr (continuumLocalizedMode_le hfreq u x)

def localizedPotentialBound (freq : ℝ) : ℝ :=
  localizedAmplitudeBound freq ^ 2 * NeutralAtom.kernelBallMass 1 + 1

theorem localizedDensity_coulomb_integrable_bound {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) (x : Position) :
    Integrable (fun y => NeutralAtom.coulombKernel (x - y) * localizedDensity freq u y) ∧
      NeutralAtom.potentialOf (localizedDensity freq u) x ≤ localizedPotentialBound freq := by
  have h := NeutralAtom.bounded_density_convolution NeutralAtom.measurable_coulombKernel
    NeutralAtom.coulombKernel_nonneg (NeutralAtom.coulombKernel_integrableOn_ball 1)
    (fun _ => NeutralAtom.coulombKernel_le_one) (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u) x
  simpa only [localizedDensity_mass hfreq u, localizedPotentialBound, NeutralAtom.kernelBallMass,
    NeutralAtom.potentialOf] using h

theorem localizedDensity_potential_nonnegative (freq : ℝ) (u : PlanarPosition) (x : Position) :
    0 ≤ NeutralAtom.potentialOf (localizedDensity freq u) x :=
  integral_nonneg (fun _ => mul_nonneg (NeutralAtom.coulombKernel_nonneg _)
    (localizedDensity_nonnegative freq u _))

theorem localizedDensity_potential_continuous {freq : ℝ} (hfreq : 0 < freq)
    (u : PlanarPosition) : Continuous (NeutralAtom.potentialOf (localizedDensity freq u)) :=
  NeutralAtom.potentialOf_continuous (localizedDensity_integrable hfreq u)
    (localizedDensity_nonnegative freq u) (localizedDensity_bound hfreq u)

def localizedCoulombCoeff (freq : ℝ) (u v : PlanarPosition) : ℝ :=
  ∫ x, localizedDensity freq u x * NeutralAtom.potentialOf (localizedDensity freq v) x

theorem localizedCoulombCoeff_integrable {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) :
    Integrable (fun x => localizedDensity freq u x *
      NeutralAtom.potentialOf (localizedDensity freq v) x) := by
  apply (localizedDensity_integrable hfreq u).mul_bdd (c := localizedPotentialBound freq)
    (localizedDensity_potential_continuous hfreq v).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (localizedDensity_potential_nonnegative freq v x)]
    exact (localizedDensity_coulomb_integrable_bound hfreq v x).2)

theorem localizedCoulombCoeff_nonnegative (freq : ℝ) (u v : PlanarPosition) :
    0 ≤ localizedCoulombCoeff freq u v :=
  integral_nonneg (fun x => mul_nonneg (localizedDensity_nonnegative freq u x)
    (localizedDensity_potential_nonnegative freq v x))

theorem localizedCoulombCoeff_le {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    localizedCoulombCoeff freq u v ≤ localizedPotentialBound freq := by
  have hi := (localizedDensity_integrable hfreq u).mul_const (localizedPotentialBound freq)
  have h := integral_mono (localizedCoulombCoeff_integrable hfreq u v) hi
    (fun x => mul_le_mul_of_nonneg_left
      (localizedDensity_coulomb_integrable_bound hfreq v x).2
      (localizedDensity_nonnegative freq u x))
  simpa only [integral_mul_const, localizedDensity_mass hfreq u, one_mul,
    localizedCoulombCoeff] using h

end ContinuumCoulomb

end

end OAI
