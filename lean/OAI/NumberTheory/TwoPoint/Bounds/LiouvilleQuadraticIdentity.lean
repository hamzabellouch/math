import OAI.NumberTheory.TwoPoint.Bounds.SymmetricEdgeTesting
import OAI.NumberTheory.TwoPoint.Walks.BlockEndpointSum

namespace OAI

/-! Testing the actual weighted matrix leaves twice L times the ambient
retained directed-edge correlation. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

theorem maskedLiouville_quadratic {V : Type*} [Fintype V] [DecidableEq V]
    (site : V → ℤ) (Q : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (g center : ℤ → ℝ) (L K : ℝ) (extra keep : ℤ → Prop) (h d : ℕ)
    (gate : V → V → Prop) (hgate : ∀ i j, gate i j ↔ gate j i)
    (hg : ∀ z, g z ≠ 0) :
    let v := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
    inner ℂ v (matrixOperator
      (maskedIntegerEdgeMatrix site Q u eligible g center L K extra h d gate) v) =
      (2 * (L : ℂ)) * ∑ i, ∑ j, if gate i j then
        ∑ q ∈ Q, retainedLiouvilleEdge Q u eligible g center L K extra keep h d q (site i) (site j)
      else 0 := by
  dsimp only
  let v : EuclideanSpace ℂ V := WithLp.toLp 2 (fun i => retainedLiouvilleScalar g keep (site i))
  have hv (i : V) : star (v i) = v i := retainedLiouvilleScalar_star g keep (site i)
  have hterm (i j : V) :
      ((if gate i j then ∑ q ∈ Q,
        directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j)
        else 0) : ℝ) * v i * v j =
        (L : ℂ) * (if gate i j then ∑ q ∈ Q,
          retainedLiouvilleEdge Q u eligible g center L K extra keep h d q (site i) (site j)
          else 0) := by
    by_cases hij : gate i j
    · simp only [ite_eq_left hij, Complex.ofReal_sum, sum_mul, mul_sum]
      apply sum_congr rfl
      intro q _
      have ht := retainedLiouvilleEdge_test Q u eligible g center L K extra keep h d q
        (site i) (site j) hg
      rw [retainedLiouvilleScalar_star] at ht
      calc
        _ = retainedLiouvilleScalar g keep (site i) *
            (directedIntegerEdge Q u eligible g center L K extra h d q (site i) (site j) : ℂ) *
            retainedLiouvilleScalar g keep (site j) := by dsimp [v]; ring
        _ = _ := ht
    · simp [hij]
  rw [maskedIntegerEdgeMatrix_quadratic site Q u eligible g center L K extra h d gate hgate v hv]
  simp_rw [hterm]
  simp only [← mul_sum, mul_assoc]

end TwoPointCorrelations

end OAI
