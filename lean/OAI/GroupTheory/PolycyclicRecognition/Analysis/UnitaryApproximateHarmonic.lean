import OAI.GroupTheory.PolycyclicRecognition.Algebra.UnitaryEnergyProjection
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ApproximateHarmonicLimit

namespace OAI

/-! # Almost harmonic unitary cocycles give a nonconstant harmonic function -/
noncomputable section
namespace PolycyclicRecognition
open Filter Finset
open scoped Topology
variable {G E : Type*} [Group G] [DecidableEq G]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem nonconstant_harmonic_of_almost_harmonic_cocycles
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (S : Finset G) (hne : S.Nonempty) (hS : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (ρ : ι → G →* (E ≃ₗᵢ[ℝ] E)) (b : ι → G → E)
    (hb : ∀ i, IsUnitaryCocycle (ρ i) (b i))
    (hE : ∀ i, 0 < unitaryCocycleEnergy S (b i))
    (hdefect : Tendsto (fun i => ‖∑ s ∈ S, b i s‖ /
      Real.sqrt (unitaryCocycleEnergy S (b i))) l (𝓝 0)) :
    ∃ F : polynomialHarmonicFunctions S 1, ∃ s ∈ S, F.val s ≠ F.val 1 := by
  choose f hfzero hfbound hfnorm hfdefect using
    fun i => exists_normalized_unitaryCocycleProjection (hb i) S hS hgen (hE i)
  have hc : 0 < (1 / (S.card : ℝ)) ^ 2 := by
    have hm : 0 < (S.card : ℝ) := Nat.cast_pos.mpr (card_pos.mpr hne)
    positivity
  apply exists_nonconstant_polynomial_harmonic_of_approximate (l := l)
    S hS hgen f hfbound hfzero hc hfnorm
  intro g
  apply squeeze_zero_norm (fun i => ?_) hdefect
  simpa only [Real.norm_eq_abs] using hfdefect i g

end PolycyclicRecognition

end

end OAI
