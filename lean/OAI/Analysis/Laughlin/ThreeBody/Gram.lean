import OAI.Analysis.Laughlin.ThreeBody.PairAction

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators

theorem occupationInner_sub_right (Q : ℕ) (x y z : Space Q) :
    occupationInner Q x (y-z) = occupationInner Q x y-occupationInner Q x z := by
  simp [occupationInner,mul_sub,Finset.sum_sub_distrib]

theorem occupationInner_oneMode (Q : ℕ) (i j : Fin (Q+1)) :
    occupationInner Q (create i (1 : Space Q)) (create j (1 : Space Q)) =
      if i = j then 1 else 0 := by
  have h (k : Fin (Q+1)) : create k (1 : Space Q) = occupationBasis Q {k} := by
    rw [occupation_singleton]
    simp [create]
  rw [h i,h j]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem threeBodyColumn_gram (Q p q : ℕ) (hQ : 2 ≤ Q) (hp : p ≤ 2*Q-2)
    (i j : Fin (Q+1)) :
    occupationInner Q (threeBodyColumn Q p i) (threeBodyColumn Q q j) =
      (if p = q then (1 : ℂ) else 0)*(if i = j then (1 : ℂ) else 0) -
      2 * ∑ t, (pairCoefficient Q p j t : ℂ)*(pairCoefficient Q q i t : ℂ) := by
  rw [threeBodyColumn,sourcePairCreateEnd,pairCreate_pair_adjoint]
  change occupationInner Q (create i (1 : Space Q))
    (sourcePairEnd Q p (threeBodyColumn Q q j)) = _
  rw [sourcePair_threeBodyColumn Q p q hQ hp j,occupationInner_sub_right,
    occupationInner_smul_right,occupationInner_smul_right]
  simp only [occupationInner_sum_right,occupationInner_smul_right,occupationInner_oneMode]
  simp only [mul_ite,mul_one,mul_zero]
  congr 2
  apply Finset.sum_congr rfl
  intro t ht
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [pairCoefficient_swap Q q i t,pairCoefficient_swap Q p j t]
  push_cast
  ring

end Laughlin.Fock

end OAI
