import OAI.Analysis.Laughlin.Pair.NormalizedLadder
import OAI.Analysis.Laughlin.Spin.Highest2

namespace OAI

namespace Laughlin

noncomputable def raisePair (f : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  ((i : ℝ)+1)*f (i+1) j + ((j : ℝ)+1)*f i (j+1)

theorem pairPolynomialCoefficient_raising (Q i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    ((i : ℝ)+1)*pairPolynomialCoefficient Q (i+1) j +
      ((j : ℝ)+1)*pairPolynomialCoefficient Q i (j+1) =
    (2*(Q : ℝ)-i-j-1)*pairPolynomialCoefficient Q i j := by
  have hx := Spin.choose_step_real Q i hi
  have hy := Spin.choose_step_real Q j hj
  rw [Nat.cast_sub hi] at hx
  rw [Nat.cast_sub hj] at hy
  unfold pairPolynomialCoefficient
  push_cast
  linear_combination
    ((i : ℝ)+1-j)*(Q.choose j : ℝ)*hx +
    ((i : ℝ)-j-1)*(Q.choose i : ℝ)*hy

theorem rawPairState_raising (Q p i j : ℕ) (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (rawPairState Q (p+1)) i j =
      (2*(Q : ℝ)-2-p)*rawPairState Q p i j := by
  have hs : i+1+j = p+1+1 ↔ i+j=p+1 := by omega
  have ht : i+(j+1) = p+1+1 ↔ i+j=p+1 := by omega
  unfold raisePair rawPairState
  by_cases h : i+j=p+1
  · rw [ite_eq_left (hs.mpr h),ite_eq_left (ht.mpr h),ite_eq_left h]
    have hc : (i : ℝ)+j = (p : ℝ)+1 := by exact_mod_cast h
    rw [pairPolynomialCoefficient_raising Q i j hi hj]
    congr 1
    linarith
  · simp only [ite_eq_right h,ite_eq_right (mt hs.mp h),ite_eq_right (mt ht.mp h),mul_zero,add_zero]

theorem pairNormalization_raising_ratio (Q p : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2) :
    (2*(Q : ℝ)-2-p)/pairNormalization Q (p+1) =
      Spin.ladder (2*Q-2) p / pairNormalization Q p := by
  have h := Spin.sqrt_choose_step (2*Q-2) p hp
  have hc : ((2*Q-2-p : ℕ) : ℝ) = 2*(Q : ℝ)-2-p := by
    rw [Nat.cast_sub (by omega : p ≤ 2*Q-2),Nat.cast_sub (by omega : 2 ≤ 2*Q)]
    push_cast; ring
  rw [hc] at h
  have hn₀ := ne_of_gt (pairNormalization_pos Q p hQ (by omega))
  have hn₁ := ne_of_gt (pairNormalization_pos Q (p+1) hQ (by omega))
  apply (div_eq_div_iff hn₁ hn₀).mpr
  unfold pairNormalization
  simp only [Real.sqrt_mul (by positivity : 0 ≤ 2*(Q : ℝ))]
  linear_combination -(Real.sqrt (2*(Q : ℝ)))*h

theorem normalizedPairState_raising (Q p i j : ℕ) (hQ : 0 < Q) (hp : p < 2*Q-2)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    raisePair (normalizedPairState Q (p+1)) i j =
      Spin.ladder (2*Q-2) p * normalizedPairState Q p i j := by
  have hdiv : raisePair (normalizedPairState Q (p+1)) i j =
      raisePair (rawPairState Q (p+1)) i j / pairNormalization Q (p+1) := by
    unfold normalizedPairState raisePair
    ring
  rw [hdiv,rawPairState_raising Q p i j hi hj]
  unfold normalizedPairState
  calc
    _ = ((2*(Q : ℝ)-2-p)/pairNormalization Q (p+1))*rawPairState Q p i j := by ring
    _ = _ := by rw [pairNormalization_raising_ratio Q p hQ hp]; ring

end Laughlin

end OAI
