import OAI.NumberTheory.TwoPoint.Bounds.GraphTesting
import OAI.NumberTheory.TwoPoint.Bounds.IntegerLiouville

namespace OAI

/-! A real symmetric edge test counts each retained directed edge twice. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem symmetric_kernel_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (a : V → V → ℝ) (v : EuclideanSpace ℂ V) (hv : ∀ i, star (v i) = v i) :
    inner ℂ v (matrixOperator (fun i j => ((a i j + a j i : ℝ) : ℂ)) v) =
      2 * ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
  change (∑ i, (∑ j, ((a i j + a j i : ℝ) : ℂ) * v j) * star (v i)) = _
  have hf : (∑ i, ∑ j, (a i j : ℂ) * v j * v i) =
      ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have hr : (∑ i, ∑ j, (a j i : ℂ) * v j * v i) =
      ∑ i, ∑ j, (a i j : ℂ) * v i * v j := by
    rw [sum_comm]
  calc
    _ = (∑ i, ∑ j, (a i j : ℂ) * v j * v i) +
        (∑ i, ∑ j, (a j i : ℂ) * v j * v i) := by
      simp only [hv, Complex.ofReal_add, add_mul, sum_add_distrib, sum_mul]
    _ = _ := by rw [hf, hr]; ring

lemma maskedIntegerEdgeMatrix_directed {V : Type*} [Fintype V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i) (i j : V) :
    maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate i j =
      ((if gate i j then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site i) (site j) else 0) +
       (if gate j i then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
        (site j) (site i) else 0) : ℝ) := by
  simp only [maskedIntegerEdgeMatrix, maskMatrix, integerEdgeMatrix,
    hgate i j, sum_add_distrib]
  split_ifs <;> simp

theorem maskedIntegerEdgeMatrix_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (v : EuclideanSpace ℂ V) (hv : ∀ i, star (v i) = v i) :
    inner ℂ v (matrixOperator
      (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate) v) =
      2 * ∑ i, ∑ j,
        ((if gate i j then ∑ q ∈ Q, directedIntegerEdge Q u eligible g center L K extra h d q
          (site i) (site j) else 0) : ℝ) * v i * v j := by
  have hm : maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate =
      fun i j => (((if gate i j then ∑ q ∈ Q,
          directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) else 0) +
        (if gate j i then ∑ q ∈ Q,
          directedIntegerEdge Q u eligible g center L K extra h d q (site j) (site i) else 0) : ℝ) : ℂ) := by
    funext i j
    exact maskedIntegerEdgeMatrix_directed site Q u eligible g center L K extra h d gate hgate i j
  rw [hm]
  exact symmetric_kernel_quadratic _ v hv

end TwoPointCorrelations

end OAI
