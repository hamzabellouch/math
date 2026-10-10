import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPathPolynomialBound

namespace OAI

/-! A fixed number of routed subdivisions has an explicit polynomial envelope,
with edge counts tracked separately from coefficient magnitudes. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical

def qmaPathIteratedBound (m L T : ℝ) : ℕ → ℝ
  | 0 => L
  | k+1 => qmaPathCoefficientBound (3^k*m) (qmaPathIteratedBound m L T k) T

theorem qmaPathCoefficientBound_one {m L T : ℝ} (hm : 0 ≤ m) (hL : 1 ≤ L) :
    1 ≤ qmaPathCoefficientBound m L T := by
  unfold qmaPathCoefficientBound
  have h : 0 ≤ (7*m+2)*(qmaPathRadiusBound m L T)^2 := by positivity
  linarith

theorem qmaPathIteratedBound_one {m L T : ℝ} (hm : 0 ≤ m) (hL : 1 ≤ L) (k : ℕ) :
    1 ≤ qmaPathIteratedBound m L T k := by
  induction k with
  | zero => exact hL
  | succ k ih => exact qmaPathCoefficientBound_one (by positivity) ih

namespace QMAPathSchedule
variable (W : QMAPathSchedule)

theorem iterate_coefficientBound {N : ℚ} (hN : 0 ≤ N) {m L T : ℝ}
    (hm : (Fintype.card W.graph.Edge:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : W.graph.CoefficientBound L) (k : ℕ) :
    (W.iterate N k).graph.CoefficientBound (qmaPathIteratedBound m L T k) := by
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  induction k with
  | zero => exact hc
  | succ k ih =>
    have hcount : (Fintype.card (W.iterate N k).graph.Edge:ℝ) ≤ 3^k*m := by
      have hcast : (Fintype.card (W.iterate N k).graph.Edge:ℝ) ≤
          3^k*(Fintype.card W.graph.Edge:ℝ) := by
        exact_mod_cast W.iterate_edge_count N k
      exact hcast.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    exact (W.iterate N k).graph.subdivide_coefficientBound _ _ hN hcount
      (qmaPathIteratedBound_one hm0 hL k) hT ih

end QMAPathSchedule
end ContinuumCoulomb

end

end OAI
