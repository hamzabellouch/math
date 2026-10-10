import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarOverlap
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPackets

namespace OAI

/-! The actual transition densities of localized three-dimensional modes
have normalized mass bounds and exponentially small off-site L1 mass. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

def localizedTransition (freq : ℝ) (u v : PlanarPosition) (x : Position) : ℝ :=
  continuumLocalizedMode freq u x * continuumLocalizedMode freq v x

theorem localizedTransition_continuous (freq : ℝ) (u v : PlanarPosition) :
    Continuous (localizedTransition freq u v) :=
  (continuumLocalizedMode_C7 freq u).continuous.mul (continuumLocalizedMode_C7 freq v).continuous

theorem localizedTransition_nonnegative {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) : 0 ≤ localizedTransition freq u v x :=
  mul_nonneg (continuumLocalizedMode_positive hfreq u x).le (continuumLocalizedMode_positive hfreq v x).le

theorem localizedTransition_integrable {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    Integrable (localizedTransition freq u v) :=
  (continuumLocalizedMode_memLp hfreq u).integrable_mul (continuumLocalizedMode_memLp hfreq v)

theorem localizedTransition_bound {freq : ℝ} (hfreq : 0 < freq)
    (u v : PlanarPosition) (x : Position) :
    localizedTransition freq u v x ≤ localizedAmplitudeBound freq ^ 2 := by
  have h := mul_le_mul (continuumLocalizedMode_le hfreq u x) (continuumLocalizedMode_le hfreq v x)
    (continuumLocalizedMode_positive hfreq v x).le (localizedAmplitudeBound_positive hfreq).le
  simpa only [localizedTransition, pow_two] using h

theorem localizedTransition_mass {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, localizedTransition freq u v x) = planarModeOverlap u v := by
  change (∫ x, localizedMode freq u (positionSplitCoordinates x) *
    localizedMode freq v (positionSplitCoordinates x)) = _
  rw [positionSplitCoordinates_integral (fun p => localizedMode freq u p * localizedMode freq v p)]
  have he : (fun p : SplitPosition => localizedMode freq u p * localizedMode freq v p) =
      (fun p => (normalizedPlanarMode (p.1 - u) * normalizedPlanarMode (p.1 - v)) * verticalMode freq p.2 ^ 2) := by
    funext p
    unfold localizedMode
    ring
  rw [he, Measure.volume_eq_prod, integral_prod_mul
    (fun r => normalizedPlanarMode (r - u) * normalizedPlanarMode (r - v))
    (fun z => verticalMode freq z ^ 2)]
  rw [verticalMode_normalized hfreq, mul_one]
  rfl

theorem localizedTransition_mass_le_one {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, localizedTransition freq u v x) ≤ 1 := by
  have hi := ((localizedDensity_integrable hfreq u).add (localizedDensity_integrable hfreq v)).div_const 2
  have h := integral_mono (localizedTransition_integrable hfreq u v) hi (fun x => by
    simp only [Pi.add_apply, localizedTransition, localizedDensity]
    nlinarith [sq_nonneg (continuumLocalizedMode freq u x - continuumLocalizedMode freq v x)])
  simp only [Pi.add_apply] at h
  rw [integral_div, integral_add (localizedDensity_integrable hfreq u) (localizedDensity_integrable hfreq v),
    localizedDensity_mass hfreq u, localizedDensity_mass hfreq v] at h
  norm_num at h
  exact h

theorem localizedTransition_norm_mass {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, ‖localizedTransition freq u v x‖) = planarModeOverlap u v := by
  simp_rw [Real.norm_of_nonneg (localizedTransition_nonnegative hfreq u v _)]
  exact localizedTransition_mass hfreq u v

theorem localizedTransition_L1_decay {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) :
    (∫ x, ‖localizedTransition freq u v x‖) ≤
      planarOverlapConstant * Real.exp (-(9 / 10 : ℝ) * ‖u - v‖) := by
  rw [localizedTransition_norm_mass hfreq]
  exact planarModeOverlap_decay u v

def localizedTransitionPacket {freq : ℝ} (hfreq : 0 < freq) (u v : PlanarPosition) : CoulombPacket where
  value := localizedTransition freq u v
  continuous := localizedTransition_continuous freq u v
  integrable := localizedTransition_integrable hfreq u v
  bound := localizedAmplitudeBound freq ^ 2
  bound_nonnegative := sq_nonneg _
  bound_spec x := by
    rw [Real.norm_of_nonneg (localizedTransition_nonnegative hfreq u v x)]
    exact localizedTransition_bound hfreq u v x

end ContinuumCoulomb

end

end OAI
