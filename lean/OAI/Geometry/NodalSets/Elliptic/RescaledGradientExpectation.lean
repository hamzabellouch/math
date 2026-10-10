import OAI.Geometry.NodalSets.Charts.BallGeometry
import OAI.Geometry.NodalSets.Waves.GaussianCubeExpectation
import OAI.Geometry.NodalSets.Waves.LatticeDerivativeMoments

namespace OAI

namespace Yau.Geometry
open Yau.Jets Yau.Probability MeasureTheory ProbabilityTheory Set Filter
open scoped ContDiff Topology
noncomputable section
variable {ι : Type*} [Fintype ι]

lemma rescaled_gradient_supremum_expectation (V : ι → Coord → ℂ)
    (hV : ∀ i, ContDiff ℝ ∞ (V i)) (S0 T0 S : Coord → ℝ)
    (hS0 : ContDiff ℝ ∞ S0) (hT0 : ContDiff ℝ ∞ T0)
    (N s sigma : ℝ) (x : Coord) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ v : Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → Coord, ‖dirs‖ ≤ 1 →
        (∫ coeff, (iteratedFDeriv ℝ k
          (rescaledGaussianField V S0 T0 S N s sigma x coeff) v dirs)^2 ∂gaussianPairs) ≤ B) :
    ∃ G : (ι × Fin 2 → ℝ) → ℝ,
      Continuous G ∧ Integrable G gaussianPairs ∧ (∀ coeff, 0 ≤ G coeff) ∧
      (∫ coeff, G coeff ∂gaussianPairs) ≤ 648*(B+1) ∧
      ∀ coeff C, 0 ≤ C →
        (G coeff ≤ C ↔ ∀ v : Coord, sourceEuclideanNorm v ≤ 1 →
          sourceEuclideanNorm (fun j ↦ fderiv ℝ
            (rescaledGaussianField V S0 T0 S N s sigma x coeff) v (Pi.single j 1)) ≤ C) := by
  let K := {v : Coord | sourceEuclideanNorm v ≤ 1}
  let : CompactSpace K := isCompact_iff_compactSpace.mp (sourceEuclideanBall_compact 1)
  let A := fun i ↦ normalizedRescaling (V i) S N s sigma x
  let seed := rescaledSeed S0 T0 S N s sigma x
  have hA (i : ι) : ContDiff ℝ ∞ (A i) := normalizedRescaling_smooth _ (hV i) _ _ _ _ _
  have hs : ContDiff ℝ ∞ seed := rescaledSeed_smooth _ _ _ hS0 hT0 _ _ _ _
  have he (coeff : ι × Fin 2 → ℝ) : rescaledGaussianField V S0 T0 S N s sigma x coeff =
      fun z ↦ seed z+gaussianWaveField A coeff z := by
    ext z
    exact rescaledGaussianField_decomposition _ _ _ _ _ _ _ _ _ _
  have hb' : ∀ v : Coord, sourceEuclideanNorm v ≤ 2 → ∀ k : ℕ, k ≤ 5 →
      ∀ dirs : Fin k → Coord, ‖dirs‖ ≤ 1 →
        (∫ coeff, (iteratedFDeriv ℝ k
          (fun z ↦ seed z+gaussianWaveField A coeff z) v dirs)^2 ∂gaussianPairs) ≤ B := by
    simpa only [he] using hb
  refine ⟨gaussianGradientSup A seed hA hs K,
    gaussianGradientSup_continuous _ _ _ _ _,gaussianGradientSup_integrable _ _ _ _ _,
    fun coeff ↦ norm_nonneg _,
    gaussian_gradient_expectation_of_moments A seed hA hs hB hb' K (fun _ hx ↦ hx),?_⟩
  intro coeff C hC
  rw [he coeff]
  exact gaussianGradientSup_le_iff A seed hA hs K coeff hC

end
end Yau.Geometry

end OAI
