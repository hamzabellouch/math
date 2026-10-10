import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityFourierMultiplier
import Mathlib.Analysis.Fourier.LpSpace

namespace OAI

/-! # Hilbert coordinates for the evolution transport Fourier transform -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BoltzmannNonuniqueness.Published

abbrev FourierSpace := WithLp 2 SpaceTime

def spacetimeHilbertEquiv : SpaceTime ≃ᵐ FourierSpace := MeasurableEquiv.toLp 2 _

theorem spacetimeHilbert_measurePreserving :
    MeasurePreserving spacetimeHilbertEquiv (volume : Measure SpaceTime) volume :=
  WithLp.volume_preserving_toLp ℝ Velocity

def characteristicDirection (v : Velocity) : FourierSpace := WithLp.toLp 2 (1,v)

theorem characteristicFrequency (k : FourierSpace) (v : Velocity) :
    inner ℝ k (characteristicDirection v) = (WithLp.ofLp k).1 + inner ℝ (WithLp.ofLp k).2 v := by
  simp [characteristicDirection,WithLp.prod_inner_apply,RCLike.inner_apply]

theorem spacetimeHilbert_translation (z : SpaceTime) (s : ℝ) (v : Velocity) :
    spacetimeHilbertEquiv (z.1-s,z.2-s • v) =
      spacetimeHilbertEquiv z - s • characteristicDirection v := by
  apply WithLp.ofLp_injective
  change (z.1-s,z.2-s • v) = (z.1-s*1,z.2-s • v)
  simp only [mul_one]

end BoltzmannNonuniqueness.Published

end

end OAI
