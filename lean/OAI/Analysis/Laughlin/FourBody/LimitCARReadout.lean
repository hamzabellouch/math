import OAI.Analysis.Laughlin.Exterior.FourConjugation
import OAI.Analysis.Laughlin.FourBody.CARReadout

namespace OAI

namespace Laughlin

theorem pairLimitCoefficient_swap (p x y : ℕ) :
    pairLimitCoefficient p y x = -pairLimitCoefficient p x y := by
  unfold pairLimitCoefficient
  rw [Nat.add_comm y x]
  split_ifs
  · rw [show ((2 : ℕ) : ℝ)^p * y.factorial*x.factorial =
      ((2 : ℕ) : ℝ)^p*x.factorial*y.factorial by ring]
    ring
  · simp

theorem pairLimitCoefficient_difference (p x y : ℕ) :
    pairLimitCoefficient p x y / Real.sqrt 2 - pairLimitCoefficient p y x / Real.sqrt 2 =
      Real.sqrt 2 * pairLimitCoefficient p x y := by
  rw [pairLimitCoefficient_swap p x y]
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  calc
    _ = 2 * pairLimitCoefficient p x y / Real.sqrt 2 := by ring
    _ = (Real.sqrt 2 * Real.sqrt 2) * pairLimitCoefficient p x y / Real.sqrt 2 := by rw [h]
    _ = _ := by field_simp

end Laughlin

namespace Laughlin.Fock
open scoped BigOperators

theorem limitPairEnd_four_create (Q p : ℕ) (a b c d : Fin (Q+1)) :
    limitPairEnd Q p (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) • create c (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) • create b (create d (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) • create b (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) • create a (create d (1 : Space Q)) -
      ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) • create a (create c (1 : Space Q)) +
      ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) • create a (create b (1 : Space Q)) := by
  unfold limitPairEnd
  rw [pairEnd_four_create]
  have he (x y : ℕ) : ((pairLimitCoefficient p x y / Real.sqrt 2 : ℝ) : ℂ) -
      ((pairLimitCoefficient p y x / Real.sqrt 2 : ℝ) : ℂ) =
      ((Real.sqrt 2 * pairLimitCoefficient p x y : ℝ) : ℂ) := by
    rw [← Complex.ofReal_sub,pairLimitCoefficient_difference]
  simp only [he]

noncomputable def wedgeDelta (Q : ℕ) (j k a b : Fin (Q+1)) : ℂ :=
  delta j a * delta k b - delta k a * delta j b

theorem limitFourEnd_four_create (Q p : ℕ) (j k a b c d : Fin (Q+1)) :
    limitFourEnd Q p j k (create a (create b (create c (create d (1 : Space Q))))) =
      (((Real.sqrt 2*pairLimitCoefficient p a.val b.val : ℝ) : ℂ) * wedgeDelta Q j k c d -
       ((Real.sqrt 2*pairLimitCoefficient p a.val c.val : ℝ) : ℂ) * wedgeDelta Q j k b d +
       ((Real.sqrt 2*pairLimitCoefficient p a.val d.val : ℝ) : ℂ) * wedgeDelta Q j k b c +
       ((Real.sqrt 2*pairLimitCoefficient p b.val c.val : ℝ) : ℂ) * wedgeDelta Q j k a d -
       ((Real.sqrt 2*pairLimitCoefficient p b.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a c +
       ((Real.sqrt 2*pairLimitCoefficient p c.val d.val : ℝ) : ℂ) * wedgeDelta Q j k a b) • (1 : Space Q) := by
  simp only [limitFourEnd,Module.End.mul_apply,limitPairEnd_four_create,map_sub,map_add,map_smul,
    two_annihilate_two_create,smul_smul,wedgeDelta,sub_smul,add_smul,smul_sub,mul_sub]

end Laughlin.Fock

end OAI
