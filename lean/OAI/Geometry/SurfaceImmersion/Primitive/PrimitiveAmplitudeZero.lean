import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveCoordinateData

namespace OAI

/-! Outside its original chart support the actual amplitude has zero first jet. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma correctedAmplitude_zero_coordinate
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∉ tsupport (B.weight a.1)) :
    B.correctedPrimitiveAmplitude P psi phi u a p = 0 ∧
      fderiv ℝ (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm)
        (chart (i : M) p) = 0 := by
  have hn : p ∉ tsupport (B.correctedPrimitiveAmplitude P psi phi u a) := by
    intro hp
    exact ha (hs a (tsupport_mul_subset_left hp))
  have hz := notMem_tsupport_iff_eventuallyEq.mp hn
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    have h := ((chart (i : M)).continuousOn_symm _ ((chart (i : M)).map_source hi)).continuousAt
      ((chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hi))
    simpa only [(chart (i : M)).left_inv hi] using h.tendsto
  have he : (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm) =ᶠ[𝓝 (chart (i : M) p)]
      (fun _ => 0) := hz.comp_tendsto hc
  exact ⟨hz.self_of_nhds,(he.fderiv_eq (𝕜 := ℝ)).trans (fderiv_const_apply _)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
