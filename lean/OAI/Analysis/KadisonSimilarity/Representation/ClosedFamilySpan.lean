import OAI.Analysis.KadisonSimilarity.Representation.DenseFamilyIsometry
import OAI.Analysis.KadisonSimilarity.Tensor.MultiplicityClassification

namespace OAI

/-! Actual closed spans and elementary tensors of total families. -/

noncomputable section
namespace KadisonSimilarity

variable {I J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def closedFamilySpan (v : I → E) : ClosedSubmodule ℂ E :=
  (Submodule.span ℂ (Set.range v)).closure

def closedFamilyVector (v : I → E) (i : I) : closedFamilySpan v :=
  ⟨v i, (Submodule.span ℂ (Set.range v)).le_topologicalClosure (Submodule.subset_span ⟨i, rfl⟩)⟩

omit [CompleteSpace E] in
@[simp] theorem closedFamilyVector_coe (v : I → E) (i : I) :
    (closedFamilyVector v i : E) = v i := rfl

omit [CompleteSpace E] in
theorem closedFamilySpan_le (v : I → E) (S : ClosedSubmodule ℂ E)
    (h : ∀ i, v i ∈ S) : (closedFamilySpan v).toSubmodule ≤ S.toSubmodule := by
  apply (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
    (Submodule.span_le.mpr ?_) S.isClosed
  rintro _ ⟨i, rfl⟩
  exact h i

theorem closedFamilyVector_total (v : I → E) :
    (Submodule.span ℂ (Set.range (closedFamilyVector v))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  let g := f.comp (closedFamilySpan v).toSubmodule.orthogonalProjectionOnto
  have hs : Submodule.span ℂ (Set.range v) ≤ g.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change f ((closedFamilySpan v).toSubmodule.orthogonalProjectionOnto
      (closedFamilyVector v i : E)) = 0
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact hf i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs g.isClosed_ker
  ext x
  change f x = 0
  have hx := hc x.property
  change f ((closedFamilySpan v).toSubmodule.orthogonalProjectionOnto (x : E)) = 0 at hx
  simpa only [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using hx

omit [CompleteSpace E] [CompleteSpace F] in
theorem tensorFamily_total (v : I → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (hw : (Submodule.span ℂ (Set.range w)).topologicalClosure = ⊤) :
    (Submodule.span ℂ (Set.range (fun p : I × J =>
      hilbertTensorInsert (v p.1) (w p.2)))).topologicalClosure = ⊤ := by
  apply dense_span_of_scalar_tests
  intro f hf
  have hi (i : I) : f.comp (hilbertTensorInsert (v i)) = 0 := by
    apply continuousLinearMap_eq_zero_of_total w hw
    intro j
    exact hf (i, j)
  apply continuousLinearMap_ext_hilbertTensorInsert
  intro x y
  have hy : f.comp (hilbertTensorRightInsert y) = 0 := by
    apply continuousLinearMap_eq_zero_of_total v hv
    intro i
    exact congrArg (fun g => g y) (hi i)
  exact congrArg (fun g => g x) hy

omit [CompleteSpace E] in
theorem closedFamilySpan_inner_zero (v : I → E) (w : J → E)
    (h : ∀ i j, inner ℂ (v i) (w j) = 0)
    (x : closedFamilySpan v) (y : closedFamilySpan w) : inner ℂ (x : E) (y : E) = 0 := by
  have hw (i : I) : (closedFamilySpan w).toSubmodule ≤ (innerSL ℂ (v i)).ker := by
    apply (Submodule.span ℂ (Set.range w)).topologicalClosure_minimal
      (Submodule.span_le.mpr ?_) (innerSL ℂ (v i)).isClosed_ker
    rintro _ ⟨j, rfl⟩
    exact h i j
  have hv : (closedFamilySpan v).toSubmodule ≤ (innerSL ℂ (y : E)).ker := by
    apply (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal
      (Submodule.span_le.mpr ?_) (innerSL ℂ (y : E)).isClosed_ker
    rintro _ ⟨i, rfl⟩
    exact inner_eq_zero_symm.mp (hw i y.property)
  exact inner_eq_zero_symm.mp (hv x.property)

omit [CompleteSpace E] [CompleteSpace F] in
theorem map_mem_of_total (v : I → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (f : E →L[ℂ] F) (S : ClosedSubmodule ℂ F) (h : ∀ i, f (v i) ∈ S) (x : E) :
    f x ∈ S := by
  have hs : Submodule.span ℂ (Set.range v) ≤ S.toSubmodule.comap f.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs
    (S.isClosed.preimage f.continuous)
  rw [hv] at hc
  exact hc (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

end KadisonSimilarity

end

end OAI
