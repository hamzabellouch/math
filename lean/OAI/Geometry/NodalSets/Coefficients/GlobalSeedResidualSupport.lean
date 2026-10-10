import OAI.Geometry.NodalSets.Elliptic.IntrinsicWeightedLift
import OAI.Geometry.NodalSets.Spectral.SphericalSeedEigenfunction

namespace OAI

namespace Yau.Target
open Manifold Matrix Set Filter
open scoped Topology
noncomputable section

lemma ambientWeightedChartOperator_coefficients_eq
    (A B : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho sigma : Base → ℝ)
    (f : Base → ℝ) (p : Base) {z : BaseModel}
    (hz : z ∈ (extChartAt (𝓡 4) p).target)
    (hA : A =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] B)
    (hr : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm z)] sigma) :
    ambientWeightedChartOperator A rho f p z = ambientWeightedChartOperator B sigma f p z := by
  have he := hA.comp_tendsto (continuousAt_extChartAt_symm'' hz)
  have hf (i : Fin 4) : roundTensorFlux A f p i =ᶠ[𝓝 z] roundTensorFlux B f p i := by
    filter_upwards [he] with y hy
    simp only [roundTensorFlux,sphereChartTensor,Function.comp_def] at *
    rw [hy]
  simp only [ambientWeightedChartOperator,hr.eq_of_nhds]
  congr 2
  funext i
  rw [(hf i).fderiv_eq]

theorem ambient_seed_residual_tsupport
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    {K : Set Base} (hK : IsClosed K)
    (hA : ∀ p ∉ K, A p = 1) (hr : ∀ p ∉ K, rho p = 1) (N : ℕ) :
    tsupport (fun p : Base ↦ ambientWeightedChartOperator A rho (sphericalSeed N) p
      (extChartAt (𝓡 4) p p)+seedEigenvalue N*sphericalSeed N p) ⊆ K := by
  apply closure_minimal _ hK
  intro p hp
  by_contra hpk
  have hAe : A =ᶠ[𝓝 p] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hpk] with q hq
    exact hA q hq
  have hre : rho =ᶠ[𝓝 p] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hpk] with q hq
    exact hr q hq
  have hinv : (extChartAt (𝓡 4) p).symm (extChartAt (𝓡 4) p p) = p := by
    rw [centeredSphereChart_value,centeredSphereChart_inverse_zero]
  have hop := ambientWeightedChartOperator_coefficients_eq A (fun _ ↦ 1) rho (fun _ ↦ 1)
    (sphericalSeed N) p ((extChartAt (𝓡 4) p).map_source (mem_extChartAt_source p))
    (by rw [hinv]; exact hAe) (by rw [hinv]; exact hre)
  apply hp
  dsimp only
  rw [hop]
  linarith [sphericalSeed_round_eigenfunction N p]

theorem intrinsic_seed_residual_tsupport
    (A : IntrinsicTensor) (rho : Base → ℝ) {K : Set Base} (hK : IsClosed K)
    (hA : ∀ p ∉ K, intrinsicAmbientMatrix A p = 1) (hr : ∀ p ∉ K, rho p = 1) (N : ℕ) :
    tsupport (fun p : Base ↦ intrinsicWeightedChartOperator A rho (sphericalSeed N) p
      (extChartAt (𝓡 4) p p)+seedEigenvalue N*sphericalSeed N p) ⊆ K := by
  simpa only [intrinsicWeightedChartOperator_eq] using
    ambient_seed_residual_tsupport (intrinsicAmbientMatrix A) rho hK hA hr N

end
end Yau.Target

end OAI
