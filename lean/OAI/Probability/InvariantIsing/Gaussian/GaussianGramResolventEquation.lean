import OAI.Probability.InvariantIsing.Gaussian.GaussianLeaveOneColumn

namespace OAI

/-! The exact finite-dimensional leave-one-column equation for the physical Gram transform. -/
noncomputable section
open Matrix
open scoped BigOperators
namespace InvariantIsing

def gaussianGramColumnQuadratic {N m : ℕ} (t : ℝ) (z : EuclideanSpace ℝ (Fin N × Fin m))
    (j : Fin m) : ℝ :=
  gaussianPatternScaledColumn z j ⬝ᵥ
    (gaussianGramLeaveResolvent t z j *ᵥ gaussianPatternScaledColumn z j)

lemma gaussianPatternCoupling_scaled_column_sum {N m : ℕ}
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    gaussianPatternCoupling 1 z = ∑ j : Fin m,
      vecMulVec (gaussianPatternScaledColumn z j) (gaussianPatternScaledColumn z j) := by
  simp_rw [gaussianPatternScaledColumn_outer]
  rw [← Finset.smul_sum,gaussianPatternCoupling_column_sum]

lemma trace_rankOne_mul {N : ℕ} (x : Fin N → ℝ) (A : Matrix (Fin N) (Fin N) ℝ) :
    (vecMulVec x x*A).trace = x ⬝ᵥ (A *ᵥ x) := by
  rw [Matrix.trace_mul_comm,Matrix.mul_vecMulVec,Matrix.trace_vecMulVec,dotProduct_comm]

lemma gaussianGramColumnQuadratic_nonneg {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) (j : Fin m) : 0 ≤ gaussianGramColumnQuadratic t z j := by
  have h := (gaussianGramLeaveShift_posDef ht z j).inv.posSemidef.dotProduct_mulVec_nonneg
    (gaussianPatternScaledColumn z j)
  simpa only [gaussianGramColumnQuadratic,gaussianGramLeaveResolvent,star_trivial] using h

lemma gaussianGramResolvent_column_trace {N m : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    t*(gaussianGramResolvent t z).trace+
      ∑ j : Fin m, gaussianGramColumnQuadratic t z j/(1+gaussianGramColumnQuadratic t z j) = N := by
  have he := gaussianGramResolvent_trace_identity ht z
  rw [gaussianPatternCoupling_scaled_column_sum,Finset.sum_mul,Matrix.trace_sum] at he
  simp_rw [trace_rankOne_mul,gaussianGramLeaveResolvent_quadratic ht z] at he
  exact he

theorem gaussianGramStieltjes_column_equation {N m : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin N × Fin m)) :
    1-t*gaussianGramStieltjes t z = (1/(N : ℝ))*
      ∑ j : Fin m, gaussianGramColumnQuadratic t z j/(1+gaussianGramColumnQuadratic t z j) := by
  have h := gaussianGramResolvent_column_trace ht z
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  unfold gaussianGramStieltjes
  rw [one_div_mul_eq_div]
  apply (eq_div_iff hn).mpr
  field_simp
  nlinarith

end InvariantIsing

end

end OAI
