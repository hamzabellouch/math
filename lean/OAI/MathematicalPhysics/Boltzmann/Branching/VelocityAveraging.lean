import OAI.MathematicalPhysics.Boltzmann.Compactness.UniformAverageCompactness
import OAI.MathematicalPhysics.Boltzmann.Collision.FourierCompactness
import OAI.MathematicalPhysics.Boltzmann.Collision.VelocityAverageRepresentatives
import OAI.MathematicalPhysics.Boltzmann.Branching.SpacetimeAverageLimit

namespace OAI

/-! # The needed Golse–Lions–Perthame–Sentis compactness specialization

This proves the exact input from Proposition 3 (pp. 115–116) and the evolution
extension, Remark (2) (p. 119), JFA 76 (1988). The velocity measure is Lebesgue
measure on a ball. Bounded value truncations have uniformly small Fourier tails;
one common subsequence converges locally in L2. Uniform L1 approximation then
constructs the global L1 limit and yields local L1 convergence for the original
sources. No spatial tightness or extra compactness hypothesis is imposed.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Published

theorem glps1988Proposition3 : GLPS1988Proposition3 := by
  intro r R _ hs hui ψ hψ hsupport
  obtain ⟨u,hum,hue,hus⟩ := measurable_velocity_representative r hui R hs
  have huiu : UniformIntegrable u 1 volume := hui.ae_eq (fun n => (hue n).symm)
  have huif := fourierSource_uniformIntegrable u hum huiu ψ hψ.continuous hsupport
  have hui' n : Integrable (fourierSource (u n) ψ) :=
    memLp_one_iff_integrable.mp (huif.memLp n)
  have hs' n (p : Velocity × FourierSpace) (hp : R < ‖p.1‖) : fourierSource (u n) ψ p = 0 := by
    simp only [fourierSource,hus n (p.2.ofLp,p.1) hp,mul_zero,Complex.ofReal_zero]
  obtain ⟨φ,g,hφ,hg⟩ := uniform_average_compactness (fun n => fourierSource (u n) ψ)
    (fun n => fourierSource_measurable (hum n) hψ.continuous.measurable) huif R hs'
  have he n : fourierSource (r n) ψ =ᵐ[volume] fourierSource (u n) ψ :=
    fourierSource_congr_ae ψ (hue n).symm
  have hri n : Integrable (fourierSource (r n) ψ) := (hui' n).congr (he n).symm
  refine ⟨φ,fun z => (g (spacetimeHilbertEquiv z)).re,hφ,?_⟩
  apply spacetime_average_limit (fun n => r (φ n)) ψ (fun n => hri (φ n)) g
  intro K hK
  have heq n : eLpNorm (velocityLineAverage (fourierSource (r (φ n)) ψ)-(g : FourierSpace → ℂ))
      1 (volume.restrict K) =
      eLpNorm (velocityLineAverage (fourierSource (u (φ n)) ψ)-(g : FourierSpace → ℂ))
      1 (volume.restrict K) := by
    apply eLpNorm_congr_ae
    exact ae_restrict_of_ae ((velocityLineAverage_congr_ae (hri (φ n)) (hui' (φ n))
      (he (φ n))).sub ae_eq_rfl)
  simpa only [heq] using hg K hK

end BoltzmannNonuniqueness.Published

end

end OAI
