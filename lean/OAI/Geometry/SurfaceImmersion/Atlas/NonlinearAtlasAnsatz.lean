import OAI.Geometry.SurfaceImmersion.Atlas.SupportedChartPullback
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPeriodicAnsatz
import OAI.Geometry.SurfaceImmersion.Primitive.AtlasPrimitiveMapBound

namespace OAI

/-! A supported finite ansatz in a nonlinear phase chart, restored to the
original surface and retaining its exact coordinate expression. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseAtlasLocalIncrement (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (χ : JetPolynomial.Base → ℝ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) : JetPolynomial.Base → Space :=
  supportedChartPullback e χ
    (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm))

def phaseAtlasAnsatz (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base) (χ : JetPolynomial.Base → ℝ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) : M → Space :=
  F + restore (i : M) (A.outer i) (A.phaseAtlasLocalIncrement i F e χ U ℓ L z)

lemma phaseAtlasLocalIncrement_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) := by
  have hG := (A.vectorChartRead_smooth i hF).comp hi
  exact supportedChartPullback_smooth e he hχ
    ((finiteAnsatz_smooth_global hG U hK hKO (fun j x _ hx => hzero j x hx) ℓ L z).sub hG)

omit [CompactSpace M] in
lemma phaseAtlasLocalIncrement_support (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) ⊆ e.symm '' K :=
  supportedChartPullback_support e hi hK hχ
    (finiteAnsatz_tsupport_sub _ U hK.isClosed hzero ℓ L z)

lemma phaseAtlasAnsatz_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i F e χ U ℓ L z) :=
  hF.add (restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (A.phaseAtlasLocalIncrement_smooth i hF e he hi hχ U hK hKO hzero ℓ L z))

lemma phaseAtlasAnsatz_coordinate (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hχone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {x : JetPolynomial.Base} (hx : x ∈ e.source) :
    A.jetChartMap i (A.phaseAtlasAnsatz i F e χ U ℓ L z) x =
      spaceCoordinates (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z (e x)) := by
  have hs := (A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z).trans hKA
  have heq := A.jetChartMap_restored_supported i (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) hs
  rw [phaseAtlasAnsatz,A.jetChartMap_add,heq]
  change spaceCoordinates (A.vectorChartRead i F x) +
    spaceCoordinates (supportedChartPullback e χ
      (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z -
        (A.vectorChartRead i F ∘ e.symm)) x) = _
  have hpull := supportedChartPullback_eq e
    (f := finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm))
    (show tsupport (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm)) ⊆ K from
      finiteAnsatz_tsupport_sub _ U hK.isClosed hzero ℓ L z) hχone hx
  rw [hpull]
  simp only [Pi.sub_apply,Function.comp_apply,e.left_inv hx,map_sub]
  abel

lemma phaseAtlasAnsatz_eventuallyEq (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : M} (hp : p ∉ tsupport (A.weight i)) :
    A.phaseAtlasAnsatz i F e χ U ℓ L z =ᶠ[𝓝 p] F := by
  let H := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have hs : tsupport H ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) :=
    (A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z).trans hKA
  have hs' : tsupport (H ∘ planeCoordinateIsometry.symm) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    have hh := hs (tsupport_comp_preimage H planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous hx)
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have heq : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext x
    simp
  have ht := A.restore_plane_tsupport i (H ∘ planeCoordinateIsometry.symm) hs'
  rw [heq] at ht
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hp (ht h))
  filter_upwards [hz] with x hx
  change F x + restore (i : M) (A.outer i) H x = F x
  rw [hx]
  exact add_zero _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
