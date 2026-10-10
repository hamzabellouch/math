import OAI.Geometry.SurfaceImmersion.Atlas.NonlinearAtlasAnsatz

namespace OAI

/-! Preserve the actual primitive support instead of enlarging it to the
whole atlas patch. The closure also works without a Hausdorff hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

def phaseSurfaceSupport (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (K : Set JetPolynomial.Base) : Set M :=
  closure ((chart (i : M)).symm '' (e.symm '' K))

lemma phaseSurfaceSupport_subset_weight (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    {K : Set JetPolynomial.Base}
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.phaseSurfaceSupport i e K ⊆ tsupport (A.weight i) := by
  apply closure_minimal _ (isClosed_tsupport _)
  rintro _ ⟨q,hq,rfl⟩
  obtain ⟨p,hp,rfl⟩ := hKA hq
  simpa only [(chart (i : M)).left_inv (A.weight_support i hp)] using hp

omit [CompactSpace M] in
lemma phaseAtlasAnsatz_tsupport_sub (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (A.phaseAtlasAnsatz i F e χ U ℓ L z-F) ⊆ A.phaseSurfaceSupport i e K := by
  let H := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have he : A.phaseAtlasAnsatz i F e χ U ℓ L z-F = restore (i : M) (A.outer i) H := by
    funext p
    change F p+restore (i : M) (A.outer i) H p-F p = _
    abel
  rw [he]
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · have hn : H (chart (i : M) p) ≠ 0 := by
      intro hz
      apply hp
      simp only [restore,indicator_of_mem hs,hz,smul_zero]
    have hmem := A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z
      (subset_tsupport H hn)
    apply subset_closure
    exact ⟨chart (i : M) p,hmem,(chart (i : M)).left_inv hs⟩
  · exact False.elim (hp (by simp only [restore,indicator_of_notMem hs]))

omit [CompactSpace M] in
lemma phaseAtlasAnsatz_eventuallyEq_precise (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : M} (hp : p ∉ A.phaseSurfaceSupport i e K) :
    A.phaseAtlasAnsatz i F e χ U ℓ L z =ᶠ[𝓝 p] F := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp
    (fun h => hp (A.phaseAtlasAnsatz_tsupport_sub i F e hi hχ U hK hzero ℓ L z h))
  filter_upwards [hz] with q hq
  change A.phaseAtlasAnsatz i F e χ U ℓ L z q-F q = 0 at hq
  exact sub_eq_zero.mp hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
