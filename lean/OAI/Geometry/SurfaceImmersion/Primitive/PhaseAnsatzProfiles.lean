import OAI.Geometry.SurfaceImmersion.Atlas.PhaseAnsatzNormal
import OAI.Geometry.SurfaceImmersion.Primitive.UniformPrimitiveProfiles

namespace OAI

/-! Retain the actual second jet of a supported phase-chart ansatz on the
inverse chart; this transfers the quantitative normal profile unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates

lemma primitiveJetProfile_germ {f g : Base → Euclidean} {p : Base}
    (h : f =ᶠ[𝓝 p] g) (z : ℝ) : primitiveJetProfile f z p = primitiveJetProfile g z p := by
  have hd (v : Base) : PeriodicExpansion.directionalMap f v =ᶠ[𝓝 p]
      PeriodicExpansion.directionalMap g v :=
    h.fderiv.mono (fun _ hh => congrArg (fun L : Base →L[ℝ] Euclidean => L v) hh)
  ext k a
  fin_cases k <;> simp only [primitiveJetProfile,
    PeriodicExpansion.directionalMap,h.fderiv_eq,(hd (coordinateVector 0)).fderiv_eq,
    (hd (coordinateVector 1)).fderiv_eq]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion CovarianceCorrector SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasAnsatz_jetProfile (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    primitiveJetProfile (A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm) z p =
      primitiveJetProfile (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z) z p :=
  primitiveJetProfile_germ
    (A.phaseAtlasAnsatz_inverse_germ i F e hi hχ U hK hKA hzero hone ℓ L z hp) z

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
