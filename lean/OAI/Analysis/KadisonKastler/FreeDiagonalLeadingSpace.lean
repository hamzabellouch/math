import OAI.Analysis.KadisonKastler.FreeDiagonalWordTotal

namespace OAI

/-! # Orthogonal leading-word subspaces -/

namespace KadisonKastler

noncomputable section

private theorem inner_zero_of_closed_spans
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {S T : Set E} (h : ∀ x ∈ S, ∀ y ∈ T, inner ℂ x y = 0)
    {x y : E} (hx : x ∈ (Submodule.span ℂ S).topologicalClosure)
    (hy : y ∈ (Submodule.span ℂ T).topologicalClosure) : inner ℂ x y = 0 := by
  have hy' : ∀ a ∈ S, inner ℂ a y = 0 := by
    intro a ha
    have ht : Submodule.span ℂ T ≤ (innerSL ℂ a).ker :=
      Submodule.span_le.mpr (h a ha)
    exact ((Submodule.span ℂ T).topologicalClosure_minimal ht
      (innerSL ℂ a).isClosed_ker) hy
  have hs : Submodule.span ℂ S ≤ (innerSL ℂ y).ker :=
    Submodule.span_le.mpr (fun a ha => inner_eq_zero_symm.mp (hy' a ha))
  exact inner_eq_zero_symm.mp (((Submodule.span ℂ S).topologicalClosure_minimal hs
    (innerSL ℂ y).isClosed_ker) hx)

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
  {r d : ℕ} (τ : FaithfulTracialState B) (e : Fin r → Fin d → B)

def leadingDiagonalGenerators (i : Fin r) : Set (TraceStateHilbert τ) :=
  {z | ∃ a w, ReducedDiagonalWord ((i, a) :: w) ∧
    z = traceStateVector τ (diagonalWord e ((i, a) :: w))}

def leadingDiagonalSpace (i : Fin r) : Submodule ℂ (TraceStateHilbert τ) :=
  (Submodule.span ℂ (leadingDiagonalGenerators τ e i)).topologicalClosure

instance leadingDiagonalSpace_hasOrthogonalProjection (i : Fin r) :
    (leadingDiagonalSpace τ e i).HasOrthogonalProjection := by
  unfold leadingDiagonalSpace
  infer_instance

def leadingDiagonalProjection (i : Fin r) : TraceStateHilbert τ →L[ℂ] TraceStateHilbert τ :=
  (leadingDiagonalSpace τ e i).starProjection

theorem leadingDiagonalProjection_isProjection (i : Fin r) :
    IsStarProjection (leadingDiagonalProjection τ e i) := isStarProjection_starProjection

theorem diagonalWord_mem_leadingDiagonalSpace (i : Fin r) (a : Fin d)
    {w : List (Fin r × Fin d)} (hw : ReducedDiagonalWord ((i, a) :: w)) :
    traceStateVector τ (diagonalWord e ((i, a) :: w)) ∈ leadingDiagonalSpace τ e i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, w, hw, rfl⟩)

variable [NeZero d]

theorem leadingDiagonalSpace_inner
    (hp : ∀ i a, IsStarProjection (e i a)) (hs : ∀ i, ∑ a, e i a = 1)
    (hf : ScalarFreeDiagonal τ e) {i j : Fin r} (hij : i ≠ j)
    {x y : TraceStateHilbert τ} (hx : x ∈ leadingDiagonalSpace τ e i)
    (hy : y ∈ leadingDiagonalSpace τ e j) : inner ℂ x y = 0 := by
  apply inner_zero_of_closed_spans (S := leadingDiagonalGenerators τ e i)
    (T := leadingDiagonalGenerators τ e j) ?_ hx hy
  rintro x ⟨a, w, hw, rfl⟩ y ⟨b, v, hv, rfl⟩
  rw [inner_traceStateVector]
  exact trace_diagonalWord_cross e τ hp hs hf hw hv hij

theorem leadingDiagonalProjection_mul_of_ne
    (hp : ∀ i a, IsStarProjection (e i a)) (hs : ∀ i, ∑ a, e i a = 1)
    (hf : ScalarFreeDiagonal τ e) {i j : Fin r} (hij : i ≠ j) :
    leadingDiagonalProjection τ e i * leadingDiagonalProjection τ e j = 0 := by
  apply Submodule.starProjection_comp_starProjection_eq_zero_iff.mpr
  exact fun _ hx _ hy => inner_eq_zero_symm.mp (leadingDiagonalSpace_inner τ e hp hs hf hij hx hy)

theorem leadingDiagonalSpace_vacuum_orthogonal
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e) (i : Fin r) :
    traceStateVector τ 1 ∈ (leadingDiagonalSpace τ e i)ᗮ := by
  intro x hx
  have ht : Submodule.span ℂ (leadingDiagonalGenerators τ e i) ≤
      (innerSL ℂ (traceStateVector τ 1)).ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨a, w, hw, rfl⟩
    change inner ℂ (traceStateVector τ 1)
      (traceStateVector τ (diagonalWord e ((i, a) :: w))) = 0
    rw [inner_traceStateVector, star_one, one_mul]
    exact trace_reducedDiagonalWord e τ hs hf hw (List.cons_ne_nil _ _)
  exact inner_eq_zero_symm.mp (((Submodule.span ℂ (leadingDiagonalGenerators τ e i)).topologicalClosure_minimal
    ht (innerSL ℂ (traceStateVector τ 1)).isClosed_ker) hx)

theorem leadingDiagonalProjection_vacuum
    (hs : ∀ i, ∑ a, e i a = 1) (hf : ScalarFreeDiagonal τ e) (i : Fin r) :
    leadingDiagonalProjection τ e i (traceStateVector τ 1) = 0 := by
  change traceStateVector τ 1 ∈ (leadingDiagonalSpace τ e i).starProjection.ker
  rw [Submodule.ker_starProjection]
  exact leadingDiagonalSpace_vacuum_orthogonal τ e hs hf i

theorem leadingDiagonalProjection_other
    (hp : ∀ i a, IsStarProjection (e i a)) (hs : ∀ i, ∑ a, e i a = 1)
    (hf : ScalarFreeDiagonal τ e) {i j : Fin r} (hij : i ≠ j)
    {x : TraceStateHilbert τ} (hx : x ∈ leadingDiagonalSpace τ e j) :
    leadingDiagonalProjection τ e i x = 0 := by
  change x ∈ (leadingDiagonalSpace τ e i).starProjection.ker
  rw [Submodule.ker_starProjection]
  exact fun _ hy => leadingDiagonalSpace_inner τ e hp hs hf hij hy hx

end

end KadisonKastler

end OAI
