import OAI.Analysis.Pureness.Operators.FiniteSchurFactorization
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped InnerProductSpace
variable {E V ι : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [InnerProductSpace ℂ V]

lemma schur_inner_bound_on_span (e : ι → E) (he : Orthonormal ℂ e)
    (v w : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    (S T : E →L[ℂ] E)
    (h : ∀ i j, ⟪e i, S (e j)⟫_ℂ = ⟪e i, T (e j)⟫_ℂ * ⟪v i, w j⟫_ℂ)
    (x y : E) (hx : x ∈ Submodule.span ℂ (Set.range e))
    (hy : y ∈ Submodule.span ℂ (Set.range e)) :
    ‖⟪x, S y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
  classical
  obtain ⟨a, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hx
  obtain ⟨b, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hy
  let s := a.support ∪ b.support
  let e' : s → E := fun i => e i.val
  have he' : Orthonormal ℂ e' := he.comp Subtype.val Subtype.val_injective
  let U := finiteSchurFactorization e' (fun i => v i.val) (fun i => w i.val) T
  have hU : ‖U‖ ≤ ‖T‖ := finiteSchurFactorization_norm_le e' he'
    (fun i => v i.val) (fun i => w i.val) (fun i => hv i.val) (fun i => hw i.val) T
  have hm (i : ι) (hi : i ∈ a.support) (j : ι) (hj : j ∈ b.support) :
      ⟪e i, S (e j)⟫_ℂ = ⟪e i, U (e j)⟫_ℂ :=
    (h i j).trans (finiteSchurFactorization_entry e' he' (fun i => v i.val)
      (fun i => w i.val) T ⟨i, Finset.mem_union_left _ hi⟩
        ⟨j, Finset.mem_union_right _ hj⟩).symm
  have heq : ⟪a.sum (fun i c => c • e i), S (b.sum (fun i c => c • e i))⟫_ℂ =
      ⟪a.sum (fun i c => c • e i), U (b.sum (fun i c => c • e i))⟫_ℂ := by
    simp only [Finsupp.sum, map_sum, map_smul, sum_inner, inner_sum,
      inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    apply congrArg (fun z : ℂ => b i * z)
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm j hj i hi]
  rw [heq]
  calc
    _ ≤ ‖a.sum (fun i c => c • e i)‖ * ‖U (b.sum (fun i c => c • e i))‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖a.sum (fun i c => c • e i)‖ * (‖T‖ * ‖b.sum (fun i c => c • e i)‖) :=
      mul_le_mul_of_nonneg_left ((U.le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hU (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

theorem schur_norm_le_of_dense_orthonormal (e : ι → E) (he : Orthonormal ℂ e)
    (hd : Dense (Submodule.span ℂ (Set.range e) : Set E))
    (v w : ι → V) (hv : ∀ i, ‖v i‖ ≤ 1) (hw : ∀ i, ‖w i‖ ≤ 1)
    (S T : E →L[ℂ] E)
    (h : ∀ i j, ⟪e i, S (e j)⟫_ℂ = ⟪e i, T (e j)⟫_ℂ * ⟪v i, w j⟫_ℂ) :
    ‖S‖ ≤ ‖T‖ := by
  have hfirst (x : E) (hx : x ∈ Submodule.span ℂ (Set.range e)) (y : E) :
      ‖⟪x, S y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    have hc : IsClosed {y : E | ‖⟪x, S y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun y hy => schur_inner_bound_on_span e he v w hv hw S T h x y hx hy)
      hc (hd y)
  have hall (x y : E) : ‖⟪x, S y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖ := by
    have hc : IsClosed {x : E | ‖⟪x, S y⟫_ℂ‖ ≤ ‖T‖ * ‖x‖ * ‖y‖} :=
      isClosed_le (by fun_prop) (by fun_prop)
    exact closure_minimal (fun x hx => hfirst x hx y) hc (hd x)
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le (norm_nonneg T)
  intro x y hx hy
  apply (Complex.re_le_norm _).trans
  rw [norm_inner_symm]
  simpa only [hx, hy, mul_one] using hall y x
end CuntzPureness

end

end OAI
