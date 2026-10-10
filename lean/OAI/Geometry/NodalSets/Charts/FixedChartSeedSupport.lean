import OAI.Geometry.NodalSets.Charts.FixedChartSeedEquation
import OAI.Geometry.NodalSets.Coefficients.GlobalSeedResidualSupport
import OAI.Geometry.NodalSets.Coefficients.SeededResidual
import OAI.Geometry.NodalSets.Elliptic.IntrinsicRoundReference
import OAI.Geometry.NodalSets.Elliptic.IntrinsicSeedRegularity
import OAI.Geometry.NodalSets.Elliptic.SeedPatchTopology

namespace OAI

namespace Yau.Target
open Manifold Matrix Set Filter Yau.Geometry Yau.Jets
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section

lemma ambient_seed_fixed_chart_residual_zero
    (A : Base → Matrix (Fin 5) (Fin 5) ℝ) (rho : Base → ℝ)
    {K : Set Base} (hK : IsClosed K)
    (hA : ∀ p ∉ K, A p = 1) (hr : ∀ p ∉ K, rho p = 1)
    (N : ℕ) (p : Base) (y : BaseModel) (hy : (extChartAt (𝓡 4) p).symm y ∉ K) :
    ambientWeightedChartOperator A rho (sphericalSeed N) p y +
      seedEigenvalue N*sphericalSeed N ((extChartAt (𝓡 4) p).symm y) = 0 := by
  have hAe : A =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm y)] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with q hq
    exact hA q hq
  have hre : rho =ᶠ[𝓝 ((extChartAt (𝓡 4) p).symm y)] (fun _ ↦ 1) := by
    filter_upwards [hK.isOpen_compl.mem_nhds hy] with q hq
    exact hr q hq
  rw [ambientWeightedChartOperator_coefficients_eq A (fun _ ↦ 1) rho (fun _ ↦ 1)
    (sphericalSeed N) p (by rw [centeredSphereChart_target]; trivial) hAe hre]
  linarith [sphericalSeed_fixed_chart_round_eigenfunction N p y]

theorem intrinsicSeedCoord_residual_tsupport
    (A : IntrinsicTensor) (hAs : IntrinsicTensorSmooth A)
    (hs : ∀ x v w, A x v w = A x w v)
    (hp : ∀ x v, v ≠ 0 → 0 < A x v v)
    (rho : Base → ℝ) (hrp : ∀ x, 0 < rho x)
    {K : Set Base} (hK : IsClosed K)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase,
      ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
      A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫)
    (hr : ∀ x ∉ K, rho x = 1) (N : ℕ) :
    tsupport (realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho)
      (seedEigenvalue N) (seedCoordinateField N)) ⊆
      (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) ⁻¹' K := by
  have hc : Continuous (fun x ↦ (extChartAt (𝓡 4) seedPoint).symm (seedCoordEquiv x)) :=
    seedSphereChart_inverse_continuous.comp seedCoordEquiv.continuous
  apply closure_minimal _ (hK.preimage hc)
  intro x hx
  by_contra hxK
  apply hx
  rw [realSourceResidual,intrinsicSeedCoord_residual A hAs hs hp rho hrp,
    intrinsicWeightedChartOperator_eq]
  exact_mod_cast ambient_seed_fixed_chart_residual_zero (intrinsicAmbientMatrix A) rho hK
    (fun z hz ↦ intrinsicAmbientMatrix_reference A z (hA z hz)) hr N seedPoint
      (seedCoordEquiv x) hxK

lemma iteratedFDeriv_zero_off_tsupport {f : Coord → ℂ} {K : Set Coord}
    (hf : tsupport f ⊆ K) {x : Coord} (hx : x ∉ K) (k : ℕ) :
    iteratedFDeriv ℝ k f x = 0 := by
  have he : f =ᶠ[𝓝 x] (fun _ ↦ 0) :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h ↦ hx (hf h))
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  simp

end
end Yau.Target

end OAI
