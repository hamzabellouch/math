import OAI.Analysis.Laughlin.Pair.NormalizedLadder

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_scaled (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (x y : Fin (Q+1)) :
    pairCoefficient Q p x y * pairNormalization Q p =
      if x.val+y.val = p+1 then ((x.val : ℝ)-(y.val : ℝ))*
        Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) else 0 := by
  have hd : pairNormalization Q p ≠ 0 := ne_of_gt (pairNormalization_pos Q p hQ hp)
  rw [pairCoefficient_choose Q p hQ hp]
  unfold pairNormalization at hd ⊢
  split_ifs
  · rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity)]
    field_simp
  · simp

noncomputable def weightedPairCoordinate (Q : ℕ)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) (x y : Fin (Q+1)) : ℂ :=
  ((Real.sqrt (Q.choose x.val : ℝ)*Real.sqrt (Q.choose y.val : ℝ) : ℝ) : ℂ)*ψ x y

noncomputable def pairMoment (Q p : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) : ℂ :=
  ∑ x, ∑ y, if x.val+y.val = p+1 then
    ((x.val : ℂ)-(y.val : ℂ))*weightedPairCoordinate Q ψ x y else 0

theorem pairMoment_eq_amplitude (Q p : ℕ) (hQ : 0 < Q) (hp : p ≤ 2*Q-2)
    (ψ : Fin (Q+1) → Fin (Q+1) → ℂ) :
    pairMoment Q p ψ = (pairNormalization Q p : ℂ)*
      (∑ x, ∑ y, (pairCoefficient Q p x y : ℂ)*ψ x y) := by
  unfold pairMoment
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  have h := congrArg (fun r : ℝ => (r : ℂ)) (pairCoefficient_scaled Q p hQ hp x y)
  push_cast at h
  by_cases hs : x.val+y.val = p+1
  · rw [ite_eq_left hs] at h ⊢
    push_cast at h
    unfold weightedPairCoordinate
    push_cast
    calc
      _ = ((x.val : ℂ)-(y.val : ℂ))*(Real.sqrt (Q.choose x.val : ℝ) : ℂ)*
        (Real.sqrt (Q.choose y.val : ℝ) : ℂ)*ψ x y := by ring
      _ = _ := by rw [← h]; ring
  · rw [ite_eq_right hs]
    simp only [ite_eq_right hs, Complex.ofReal_zero] at h
    calc
      _ = ((pairCoefficient Q p x y : ℂ)*(pairNormalization Q p : ℂ))*ψ x y := by rw [h]; simp
      _ = _ := by ring

theorem weightedPairCoordinate_swap (Q : ℕ) (ψ : Fin (Q+1) → Fin (Q+1) → ℂ)
    (ha : ∀ x y, ψ y x = -ψ x y) (x y : Fin (Q+1)) :
    weightedPairCoordinate Q ψ y x = -weightedPairCoordinate Q ψ x y := by
  unfold weightedPairCoordinate
  rw [ha]
  push_cast
  ring

end Laughlin

end OAI
