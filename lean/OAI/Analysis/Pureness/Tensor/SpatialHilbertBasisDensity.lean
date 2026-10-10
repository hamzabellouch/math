import OAI.Analysis.Pureness.Tensor.SpatialVectorSlice
import OAI.Analysis.Pureness.GroupAlgebra.GroupRegularRepresentation

namespace OAI
noncomputable section
namespace CuntzPureness
open CuntzComparison
open scoped TensorProduct InnerProductSpace
variable {H K ι κ : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def spatialLeftVector (x : H) : K →L[ℂ] SpatialHilbert H K :=
  (spatialTensorSwap (H := K) (K := H)).toContinuousLinearMap.comp (spatialRightVector x)

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialLeftVector_apply (x : H) (y : K) :
    spatialLeftVector x y = (x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) :=
  spatialTensorSwap_tmul y x

omit [CompleteSpace H] [CompleteSpace K] in
lemma spatialTensorFamily_orthonormal (e : ι → H) (f : κ → K)
    (he : Orthonormal ℂ e) (hf : Orthonormal ℂ f) :
    Orthonormal ℂ (fun p : ι × κ =>
      ((e p.1 ⊗ₜ[ℂ] f p.2 : H ⊗[ℂ] K) : SpatialHilbert H K)) :=
  (he.tmul hf).comp_linearIsometry UniformSpace.Completion.toComplₗᵢ

omit [CompleteSpace H] [CompleteSpace K] in
theorem spatialTensorFamily_dense (e : ι → H) (f : κ → K)
    (he : Dense (Submodule.span ℂ (Set.range e) : Set H))
    (hf : Dense (Submodule.span ℂ (Set.range f) : Set K)) :
    Dense (Submodule.span ℂ (Set.range (fun p : ι × κ =>
      ((e p.1 ⊗ₜ[ℂ] f p.2 : H ⊗[ℂ] K) : SpatialHilbert H K))) : Set (SpatialHilbert H K)) := by
  let P := (Submodule.span ℂ (Set.range (fun p : ι × κ =>
    ((e p.1 ⊗ₜ[ℂ] f p.2 : H ⊗[ℂ] K) : SpatialHilbert H K)))).topologicalClosure
  have hp : IsClosed (P : Set (SpatialHilbert H K)) := Submodule.isClosed_topologicalClosure _
  have hgen (x : H) (j : κ) : (spatialRightVector (f j) x) ∈ P := by
    have hs : Submodule.span ℂ (Set.range e) ≤ P.comap (spatialRightVector (f j)).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(i,j), rfl⟩)
    exact closure_minimal hs (hp.preimage (spatialRightVector (f j)).continuous) (he x)
  have htmul (x : H) (y : K) : ((x ⊗ₜ[ℂ] y : H ⊗[ℂ] K) : SpatialHilbert H K) ∈ P := by
    have hs : Submodule.span ℂ (Set.range f) ≤ P.comap (spatialLeftVector x).toLinearMap := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change spatialLeftVector x (f j) ∈ P
      rw [spatialLeftVector_apply]
      exact hgen x j
    have hxy : spatialLeftVector x y ∈ P :=
      closure_minimal hs (hp.preimage (spatialLeftVector x).continuous) (hf y)
    simpa only [spatialLeftVector_apply] using hxy
  intro z
  change z ∈ P
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact hp
  | ih z =>
    induction z using TensorProduct.inductionOn with
    | tmul x y => exact htmul x y
    | add x y hx hy => simpa only [UniformSpace.Completion.coe_add] using P.add_mem hx hy

local instance spatialHilbertBasisDensityDecidableEq {X : Type*} : DecidableEq X :=
  Classical.decEq X

lemma groupDelta_orthonormal (G : Type*) :
    Orthonormal ℂ (fun g : G => (lp.single 2 g 1 : GroupL2 G)) :=
  (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (GroupL2 G))).orthonormal

lemma groupDelta_dense (G : Type*) :
    Dense (Submodule.span ℂ (Set.range (fun g : G => (lp.single 2 g 1 : GroupL2 G))) :
      Set (GroupL2 G)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (GroupL2 G))).dense_span
end CuntzPureness

end

end OAI
