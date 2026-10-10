import OAI.Analysis.Laughlin.Pair.Normalization

namespace OAI

namespace Laughlin
open scoped BigOperators

theorem pairCoefficient_orthogonal (Q p q : ℕ) (hpq : p ≠ q) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hp : x.val+y.val = p+1
  · have hq : x.val+y.val ≠ q+1 := by omega
    simp [pairCoefficient, hq]
  · simp [pairCoefficient, hp]

theorem pairCoefficient_gram (Q p q : ℕ) (hQ : 2 ≤ Q)
    (hp : p ≤ 2*Q-2) :
    (∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      pairCoefficient Q p x y * pairCoefficient Q q x y) = if p = q then 1 else 0 := by
  by_cases h : p = q
  · subst q
    simp only [ite_true]
    simpa only [pow_two] using pairCoefficient_unit_norm Q p hQ hp
  · rw [ite_eq_right h]
    exact pairCoefficient_orthogonal Q p q h

theorem pairCoefficient_swap (Q p : ℕ) (x y : Fin (Q+1)) :
    pairCoefficient Q p y x = -pairCoefficient Q p x y := by
  unfold pairCoefficient
  rw [Nat.add_comm y.val x.val]
  split_ifs
  · have hn : ((Q.descFactorial y.val : ℝ) * (Q.descFactorial x.val : ℝ) * (p.factorial : ℝ)) =
        ((Q.descFactorial x.val : ℝ) * (Q.descFactorial y.val : ℝ) * (p.factorial : ℝ)) := by ring
    have hd : ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (y.val.factorial : ℝ) * (x.val.factorial : ℝ)) =
        ((Q : ℝ) * ((2*Q-2).descFactorial p : ℝ) * (x.val.factorial : ℝ) * (y.val.factorial : ℝ)) := by ring
    rw [hn, hd]
    ring
  · simp

end Laughlin

end OAI
