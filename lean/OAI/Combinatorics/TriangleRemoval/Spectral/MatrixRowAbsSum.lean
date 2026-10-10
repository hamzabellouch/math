import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.ExtendStarApply
import OAI.Combinatorics.TriangleRemoval.Process.IncidenceDegree

namespace OAI

section
section
open Filter
open scoped BigOperators Topology
open InnerProductSpace
open scoped InnerProductSpace
open scoped BigOperators NNReal
open Matrix InnerProductSpace
open scoped BigOperators
open scoped BigOperators Matrix.Norms.L2Operator
open Matrix
open scoped BigOperators Topology NNReal Matrix.Norms.Operator
open MeasureTheory

namespace SharpTerminalLeave
open scoped Matrix.Norms.Operator

theorem matrix_row_abs_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (M : Matrix I J ℝ) (i : I) : ∑ j, |M i j| ≤ ‖M‖ := by
  rw [Matrix.linfty_opNorm_def]
  have hh : ∑ j, ‖M i j‖₊ ≤ Finset.univ.sup (fun k => ∑ j, ‖M k j‖₊) :=
    Finset.le_sup (f := fun k => ∑ j, ‖M k j‖₊) (Finset.mem_univ i)
  have hc := NNReal.coe_le_coe.mpr hh
  simpa only [NNReal.coe_sum,coe_nnnorm,Real.norm_eq_abs] using hc

theorem extendStar_row_abs_sum {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (M : Matrix S S ℝ) (i : E) :
    ∑ j, |extendStar S M i j| =
      if hi : i ∈ S then ∑ j : S, |M ⟨i,hi⟩ j| else 0 := by
  by_cases hi : i ∈ S
  · rw [dite_eq_left hi]
    have he : ∑ j : E, |extendStar S M i j| = ∑ j ∈ S, |extendStar S M i j| := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro j _ hj
      simp [extendStar_apply,hj]
    rw [he,← Finset.sum_coe_sort S]
    apply Finset.sum_congr rfl
    intro j _
    simp [extendStar_apply,hi,j.property]
  · simp [extendStar_apply,hi]

theorem sum_star_infty_norm_bound {E U : Type*} [Fintype E] [DecidableEq E] [Fintype U]
    (S : U → Finset E) (M : (u : U) → Matrix (S u) (S u) ℝ)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hM : ∀ u, ‖M u‖ ≤ ε)
    (hoverlap : ∀ e, ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) ≤ K) :
    ‖∑ u, extendStar (S u) (M u)‖ ≤ K*ε := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (mul_nonneg hK hε)
  intro e
  calc
    _ ≤ ∑ f, ∑ u, |extendStar (S u) (M u) e f| := by
      apply Finset.sum_le_sum
      intro f _
      simp only [Matrix.sum_apply]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u, ∑ f, |extendStar (S u) (M u) e f| := Finset.sum_comm
    _ ≤ ∑ u, if e ∈ S u then ε else 0 := by
      apply Finset.sum_le_sum
      intro u _
      rw [extendStar_row_abs_sum]
      by_cases he : e ∈ S u
      · simp only [he,↓reduceDIte,↓reduceIte]
        exact (matrix_row_abs_sum_le (M u) ⟨e,he⟩).trans (hM u)
      · simp [he]
    _ = ((Finset.univ.filter fun u => e ∈ S u).card : ℝ) * ε := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ K*ε := mul_le_mul_of_nonneg_right (hoverlap e) hε

theorem infty_reindex_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) (M : Matrix I I ℝ) : ‖Matrix.reindex e e M‖ ≤ ‖M‖ := by
  apply matrix_norm_le_of_row_abs_sum_le _ _ (norm_nonneg _)
  intro i
  simp only [Matrix.reindex_apply,Matrix.submatrix_apply]
  rw [e.symm.sum_comp (fun j => |M (e.symm i) j|)]
  exact matrix_row_abs_sum_le M (e.symm i)

end SharpTerminalLeave

end
end

end OAI
