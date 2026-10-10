import OAI.Analysis.Laughlin.Pair.TensorRaise

namespace OAI

namespace Laughlin.Spin

theorem rawPairState_highest (Q i j : ℕ) :
    raisePair (rawPairState Q 0) i j = 0 := by
  by_cases h : i+j=0
  · have hi : i=0 := by omega
    have hj : j=0 := by omega
    simp [hi,hj,raisePair,rawPairState,pairPolynomialCoefficient]
  · have hi : i+1+j ≠ 0+1 := by omega
    have hj : i+(j+1) ≠ 0+1 := by omega
    simp [raisePair,rawPairState,hi,hj]

theorem normalizedPairState_highest (Q i j : ℕ) :
    raisePair (normalizedPairState Q 0) i j = 0 := by
  have he : raisePair (normalizedPairState Q 0) i j =
      raisePair (rawPairState Q 0) i j / pairNormalization Q 0 := by
    unfold raisePair normalizedPairState; ring
  rw [he,rawPairState_highest,zero_div]

theorem rawPairState_past_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    rawPairState Q (2*Q-2+1) i j = 0 := by
  by_cases h : i+j=2*Q-2+1+1
  · have he : i=j := by omega
    simp [rawPairState,pairPolynomialCoefficient,he]
  · simp [rawPairState,h]

theorem normalizedPairState_lowest (Q i j : ℕ) (hQ : 0 < Q)
    (hi : i ≤ Q) (hj : j ≤ Q) :
    lowerPair Q (normalizedPairState Q (2*Q-2)) i j = 0 := by
  unfold normalizedPairState
  rw [lowerPair_div,rawPairState_lowering Q (2*Q-2) i j hi hj,
    rawPairState_past_lowest Q i j hQ hi hj]
  simp

theorem pairCoefficient_tensor_highest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorRaise Q 0 x y = 0 := by
  have he := pairTensorRaise_weight Q 0 hQ (by omega) x y
  rw [normalizedPairState_highest] at he
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy)).resolve_right hx

theorem pairCoefficient_tensor_lowest (Q : ℕ) (hQ : 0 < Q)
    (x y : Fin (Q+1)) : pairTensorLower Q (2*Q-2) x y = 0 := by
  have he := pairTensorLower_weight Q (2*Q-2) hQ (by omega) x y
  rw [normalizedPairState_lowest Q x.val y.val hQ (by omega) (by omega)] at he
  have hx : Real.sqrt (Q.choose x.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : x.val ≤ Q)
  have hy : Real.sqrt (Q.choose y.val : ℝ) ≠ 0 := by
    apply ne_of_gt; apply Real.sqrt_pos.mpr
    exact_mod_cast Nat.choose_pos (by omega : y.val ≤ Q)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hy)).resolve_right hx

end Laughlin.Spin

end OAI
