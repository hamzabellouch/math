import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasAnsatz
import OAI.Geometry.SurfaceImmersion.Primitive.PrimitiveNormalCoordinates

namespace OAI

/-! Retain the actual second jet of a supported phase-chart ansatz on the
inverse chart; this transfers the quantitative normal profile unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates

lemma primitiveNormalTriple_germ {f g : Base → Euclidean} {p : Base}
    (h : f =ᶠ[𝓝 p] g) : primitiveNormalTriple f p = primitiveNormalTriple g p := by
  have hd : (fun q => fderiv ℝ f q (coordinateVector 1)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (coordinateVector 1)) :=
    h.fderiv.mono (fun _ hh => congrArg (fun L : Base →L[ℝ] Euclidean => L (coordinateVector 1)) hh)
  ext k a
  fin_cases k <;> simp only [primitiveNormalTriple,h.fderiv_eq,hd.fderiv_eq]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion CovarianceCorrector SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasAnsatz_inverse_germ (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm =ᶠ[𝓝 p]
      finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z := by
  filter_upwards [e.open_target.mem_nhds hp] with y hy
  have hh := A.phaseAtlasAnsatz_coordinate i F e hi hχ U hK hKA hzero hone ℓ L z (e.map_target hy)
  apply spaceCoordinates.injective
  simpa only [jetChartMap,Function.comp_apply,e.right_inv hy] using hh

lemma phaseAtlasAnsatz_normalTriple (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    primitiveNormalTriple (A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm) p =
      primitiveNormalTriple (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z) p :=
  primitiveNormalTriple_germ
    (A.phaseAtlasAnsatz_inverse_germ i F e hi hχ U hK hKA hzero hone ℓ L z hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
