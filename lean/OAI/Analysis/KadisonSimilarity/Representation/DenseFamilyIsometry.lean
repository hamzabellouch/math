import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI

/-! Extend a map on a total family from its Gram matrix. This construction
allows the family to have linear relations. -/

noncomputable section
namespace KadisonSimilarity

variable {J E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem dense_span_of_scalar_tests [CompleteSpace E] (v : J → E)
    (h : ∀ f : E →L[ℂ] ℂ, (∀ i, f (v i) = 0) → f = 0) :
    (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hf : innerSL ℂ x = 0 := h _ (fun i =>
    Submodule.inner_left_of_mem_orthogonal
      ((Submodule.span ℂ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span ⟨i, rfl⟩)) hx)
  exact inner_self_eq_zero.mp (congrArg (fun f : E →L[ℂ] ℂ => f x) hf)

omit [CompleteSpace F] in
theorem inner_linearCombination_eq (v : J → E) (w : J → F)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (x y : J →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ w x) (Finsupp.linearCombination ℂ w y) =
      inner ℂ (Finsupp.linearCombination ℂ v x) (Finsupp.linearCombination ℂ v y) := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, h]

omit [CompleteSpace F] in
theorem norm_linearCombination_eq (v : J → E) (w : J → F)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (x : J →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ w x‖ = ‖Finsupp.linearCombination ℂ v x‖ := by
  have he := congrArg Complex.re (inner_linearCombination_eq v w h x x)
  have hn : ‖Finsupp.linearCombination ℂ w x‖ ^ 2 =
      ‖Finsupp.linearCombination ℂ v x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
    exact he
  nlinarith [norm_nonneg (Finsupp.linearCombination ℂ w x),
    norm_nonneg (Finsupp.linearCombination ℂ v x)]

theorem denseRange_linearCombination (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤) :
    DenseRange (Finsupp.linearCombination ℂ v) := by
  change Dense (Set.range (Finsupp.linearCombination ℂ v))
  change Dense ((Finsupp.linearCombination ℂ v).range : Set E)
  rw [Finsupp.range_linearCombination]
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hv

omit [CompleteSpace F] in
theorem continuousLinearMap_eq_zero_of_total (v : J → E)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (f : E →L[ℂ] F) (hf : ∀ i, f (v i) = 0) : f = 0 := by
  have hs : Submodule.span ℂ (Set.range v) ≤ f.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hf i
  have hc := (Submodule.span ℂ (Set.range v)).topologicalClosure_minimal hs f.isClosed_ker
  rw [hv] at hc
  ext x
  exact hc (Submodule.mem_top : x ∈ (⊤ : Submodule ℂ E))

/-- The unique isometry sending a total family to a family with the same
Gram matrix, constructed through finitely supported linear combinations. -/
def denseFamilyIsometry (v : J → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) : E →ₗᵢ[ℂ] F :=
  (Finsupp.linearCombination ℂ w).extendOfIsometry
    (denseRange_linearCombination v hv) (norm_linearCombination_eq v w h)

@[simp] theorem denseFamilyIsometry_apply (v : J → E) (w : J → F)
    (hv : (Submodule.span ℂ (Set.range v)).topologicalClosure = ⊤)
    (h : ∀ i j, inner ℂ (w i) (w j) = inner ℂ (v i) (v j)) (i : J) :
    denseFamilyIsometry v w hv h (v i) = w i := by
  have he := LinearMap.extendOfIsometry_eq (Finsupp.linearCombination ℂ w)
    (denseRange_linearCombination v hv) (norm_linearCombination_eq v w h)
    (Finsupp.single i 1)
  simpa only [denseFamilyIsometry, Finsupp.linearCombination_single, one_smul] using he

end KadisonSimilarity

end

end OAI
