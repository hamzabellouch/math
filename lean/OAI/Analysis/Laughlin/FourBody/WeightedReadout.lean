import OAI.Analysis.Laughlin.FourBody.LimitCARReadout

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem sum_weighted_wedgeDelta (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) = (S a b : ℂ) := by
  simp only [wedgeDelta,delta,mul_sub,mul_ite,mul_one,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [hS a b]
  push_cast
  ring

theorem sum_weighted_wedgeDelta_factor (Q : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (c : ℂ) (a b : Fin (Q+1)) :
    (∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*(c*wedgeDelta Q j k a b)) = c*(S a b : ℂ) := by
  calc
    _ = c*(∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ)*wedgeDelta Q j k a b) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j hj
      apply Finset.sum_congr rfl; intro k hk; ring
    _ = _ := by rw [sum_weighted_wedgeDelta Q S hS a b]

noncomputable def weightedFourEnd (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ) :
    Module.End ℂ (Space Q) :=
  ∑ j, ∑ k, ((S j k / 2 : ℝ) : ℂ) • limitFourEnd Q p j k

theorem weightedFourEnd_readout (Q p : ℕ) (S : Fin (Q+1) → Fin (Q+1) → ℝ)
    (hS : ∀ j k, S k j = -S j k) (a b c d : Fin (Q+1)) :
    weightedFourEnd Q p S (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt 2*pairLimitCoefficient p a.val b.val*S c d -
        Real.sqrt 2*pairLimitCoefficient p a.val c.val*S b d +
        Real.sqrt 2*pairLimitCoefficient p a.val d.val*S b c +
        Real.sqrt 2*pairLimitCoefficient p b.val c.val*S a d -
        Real.sqrt 2*pairLimitCoefficient p b.val d.val*S a c +
        Real.sqrt 2*pairLimitCoefficient p c.val d.val*S a b : ℝ) : ℂ) • (1 : Space Q) := by
  simp only [weightedFourEnd,LinearMap.sum_apply,LinearMap.smul_apply,limitFourEnd_four_create,
    smul_smul,← Finset.sum_smul]
  congr 1
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    sum_weighted_wedgeDelta_factor Q S hS]
  push_cast
  ring

end Laughlin.Fock

end OAI
