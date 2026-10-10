import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteOutputProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleBounds

namespace OAI

/-! The actual serialized output satisfies the source coefficient, coordinate
and inverse-gap promise using the fixed-round compiler's proved estimates. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode

theorem compiled_polynomialPromise {N : ℚ} (hN : 0 < N)
    (s : State) (hs : Valid s.1)
    (P : QMAPathEmbedding (schedule s.1 hs)) (hP : Represents s hs P)
    {D X Y : ℕ} (hD : ∀ e ∈ s.1.2.2, e.1 ≤ D) (hbox : P.Bounded X Y)
    (hn : 0 < s.1.1) (a b : ℚ) (hab : a < b)
    (n k : ℕ) (hsize : n ≤ s.1.1)
    (hx : (X:ℝ) ≤ (n+1:ℝ)^k) (hy : (Y:ℝ) ≤ (n+1:ℝ)^k)
    {m L T : ℝ} (hm : (s.1.2.2.length:ℝ) ≤ m) (hL : 1 ≤ L)
    (hT : |(N:ℝ)| ≤ T) (hc : (graph s.1 hs).CoefficientBound L)
    (hcoeff : (3^D*m)*qmaPathIteratedBound m L T D ≤ (n+1:ℝ)^k)
    (hgap : ((n+1:ℝ)^k)⁻¹ ≤ (b:ℝ)-a) :
    (latticeOutput (iterate N D s) a b).PolynomialPromise k := by
  obtain ⟨hs',Q,hQ,hQbox,hgrid,_hsize,_henergy⟩ :=
    compile_realization hN s hs P hP hD hbox
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans hm
  have hL' : 0 ≤ qmaPathIteratedBound m L T D :=
    le_trans zero_le_one (qmaPathIteratedBound_one hm0 hL D)
  have hc' : (graph (iterate N D s).1 hs').CoefficientBound
      (qmaPathIteratedBound m L T D) := by
    have ht : ∀ (t : QuantumListSchedule.State) (hv : Valid t),
        t=QuantumListSchedule.iterate N D s.1 →
        (graph t hv).CoefficientBound (qmaPathIteratedBound m L T D) := by
      intro t hv he
      subst t
      exact iterate_coefficientBound hN.le s.1 hs hm hL hT hc D
    exact ht _ hs' (iterate_state N s D)
  have hcount : ((iterate N D s).1.2.2.length:ℝ) ≤ 3^D*m := by
    have hc : (iterate N D s).1.2.2.length ≤ 3^D*s.1.2.2.length := by
      rw [iterate_state]
      exact iterate_edge_count N s.1 D
    have hr : ((iterate N D s).1.2.2.length:ℝ) ≤ 3^D*(s.1.2.2.length:ℝ) := by
      exact_mod_cast hc
    exact hr.trans (mul_le_mul_of_nonneg_left hm (by positivity))
  apply latticeOutput_polynomialPromise (iterate N D s) hs' Q hQ hgrid
    (hn.trans_le (iterate_count_le N s D)) a b hab n k
    (hsize.trans (iterate_count_le N s D)) ?_ hL' hc' ?_ hgap
  · intro v
    exact ⟨(le_of_lt (by exact_mod_cast (hQbox.1 v).1)).trans hx,
      (le_of_lt (by exact_mod_cast (hQbox.1 v).2)).trans hy⟩
  · exact (mul_le_mul_of_nonneg_right hcount hL').trans hcoeff

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
