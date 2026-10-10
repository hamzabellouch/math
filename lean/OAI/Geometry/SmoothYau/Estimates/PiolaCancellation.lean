import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
namespace YauCounterexamples
variable {ι : Type*} [Fintype ι]
lemma piola_cancellation (B : Matrix ι ι ℝ) (D : ι → Matrix ι ι ℝ)
    (hD : ∀ i l m, D i l m = D m l i) (k : ι) :
    ∑ i, (Matrix.trace (D i * B) * B i k - (B * D i * B) i k) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  calc
    (∑ i, ∑ l, ∑ m, D i l m * B m l * B i k) =
        ∑ i, ∑ l, ∑ m, B m l * D m l i * B i k := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro m _
      rw [hD i l m]
      ring
    _ = ∑ m, ∑ i, ∑ l, B m l * D m l i * B i k := by
      calc
        _ = ∑ i, ∑ m, ∑ l, B m l * D m l i * B i k := by
          apply Finset.sum_congr rfl
          intro i _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by rfl
end YauCounterexamples

end

end OAI
