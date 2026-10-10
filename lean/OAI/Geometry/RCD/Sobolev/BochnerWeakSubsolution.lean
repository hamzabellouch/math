import OAI.Geometry.RCD.Sobolev.WeakSubsolution
import OAI.Geometry.RCD.Sobolev.BochnerCutoffIdentity

namespace OAI

/-! # The full Bochner measure implies a weak energy subsolution -/

open Set Filter Metric MeasureTheory
open scoped NNReal InnerProductSpace BoundedContinuousFunction CompactlySupported

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [ProperSpace X] in
/-- Positivity of the full Bochner measure, including any singular part,
gives the distributional inequality for its Sobolev energy density. -/
theorem LocalHarmonicEnergy.weak_subsolution
    {U : E →L[ℝ] SobolevSpace μ hQ} {M : PositiveBilinearMeasure X E}
    {κ : ℝ} {p : X} {r : ℝ} {L : ℝ≥0} {v : E}
    (G : LocalHarmonicEnergy μ hQ U M κ p r L v) :
    IsWeakSubsolutionOn μ hQ (ball p (2*r)) G.energy (2*κ) := by
  apply weakSubsolution_of_core μ hQ
  intro ψ w C hw hws hs hψ hw0
  let χ : X →ᵇ ℝ := (⟨⟨w,hw.continuous⟩,hws⟩ : C_c(X,ℝ)).toBoundedContinuousFunction
  have he := G.measure_laplacian ψ w hw.continuous hws hs hψ
  change energyForm μ hQ G.energy ψ = -(∫ᵛ x, χ x ∂<•(harmonicBochnerSource μ hQ U M κ v)) at he
  rw [integral_harmonicBochnerSource μ hQ U M κ v χ] at he
  have hM : 0 ≤ inner ℝ v (M.weightedOperator χ v) :=
    (M.weightedOperator_isPositive χ hw0).inner_nonneg_right v
  have hI : inner ℝ (SobolevSpace.toLp μ hQ G.energy) (SobolevSpace.toLp μ hQ ψ) =
      ∫ x, χ x*localGamma μ hQ (U v) (U v) x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hψ,(ae_restrict_iff' measurableSet_ball).mp G.representative] with x hx hg
    by_cases hin : x ∈ ball p (2*r)
    · rw [hg hin,hx]
      simp only [Real.inner_apply]
      change localGamma μ hQ (U v) (U v) x*w x = w x*localGamma μ hQ (U v) (U v) x
      ring
    · have hwz : w x = 0 := by
        by_contra hne
        exact hin (hs (subset_tsupport w hne))
      rw [hx,hwz]
      simp only [show χ x = 0 from hwz,inner_zero_right,zero_mul]
  rw [hI]
  linarith only [he,hM]

end RegularPointCoordinates

end

end OAI
