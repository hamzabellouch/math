import OAI.Analysis.Laughlin.Fock.Bidegree
import OAI.Analysis.Laughlin.FourBody.PhysicalSlaterReadout

namespace OAI

namespace Laughlin.Fock
open scoped BigOperators
open Spin

noncomputable def limitFourColumn (Q r D : ℕ) : Space Q :=
  ∑ p ∈ Finset.range (D+1), ∑ j : Fin (Q+1), ∑ k : Fin (Q+1),
    ∑ x : Fin (Q+1), ∑ y : Fin (Q+1),
      (((limitSliceCoefficient r D p j.val k.val / 2) *
        (pairLimitCoefficient p x.val y.val / Real.sqrt 2) : ℝ) : ℂ) •
        create x (create y (create j (create k (1 : Space Q))))

theorem limitFourColumn_adjoint (Q r D : ℕ) (x : Space Q) :
    occupationInner Q (limitFourColumn Q r D) x = occupationInner Q (1 : Space Q) (limitFourCopyEnd Q r D x) := by
  simp only [limitFourColumn,limitFourCopyEnd,weightedFourEnd,limitFourEnd,limitPairEnd,pairEnd,
    LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply,map_sum,map_smul,
    occupationInner_sum_left,occupationInner_sum_right,occupationInner_smul_left,
    occupationInner_smul_right,create_annihilate_adjoint,Complex.star_def,Complex.conj_ofReal]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro j hj
  apply Finset.sum_congr rfl; intro k hk
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a ha
  apply Finset.sum_congr rfl; intro b hb
  push_cast
  ring

theorem limitFourColumn_bidegree (Q r D : ℕ) : OccupationBidegree Q 4 (D+1) (limitFourColumn Q r D) := by
  intro A hA
  simp only [limitFourColumn,map_sum,Finsupp.finsetSum_apply,map_smul,Finsupp.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero; intro p hp
  apply Finset.sum_eq_zero; intro j hj
  apply Finset.sum_eq_zero; intro k hk
  apply Finset.sum_eq_zero; intro x hx
  apply Finset.sum_eq_zero; intro y hy
  by_cases hS : p+j.val+k.val=D
  · by_cases hP : x.val+y.val=p+1
    · have hv := four_create_bidegree Q x y j k A (by
        rcases hA with hA | hA
        · exact Or.inl hA
        · exact Or.inr (by omega))
      rw [hv,mul_zero]
    · simp [pairLimitCoefficient,hP]
  · simp [limitSliceCoefficient,hS]

theorem occupationInner_vacuum (Q : ℕ) : occupationInner Q (1 : Space Q) 1 = 1 := by
  rw [← occupation_empty Q]
  simp [occupationInner,Module.Basis.repr_self,Finsupp.single_apply]

theorem limitFourColumn_physical_L (Q r D : ℕ) (hr : r ≤ D) (hor : Odd r)
    (a b c d : Fin (Q+1)) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hT : a.val+b.val+c.val+d.val=D+1) :
    occupationInner Q (limitFourColumn Q r D)
      (create a (create b (create c (create d (1 : Space Q))))) =
      ((Real.sqrt (sourceCopyWeight D r /
        ((a.val.factorial : ℝ)*b.val.factorial*c.val.factorial*d.val.factorial)) *
        (Certificate.L D r (a.val,b.val,c.val,d.val) : ℝ) : ℝ) : ℂ) := by
  rw [limitFourColumn_adjoint,source_fourBody_physical_L Q r D hr hor a b c d hab hbc hcd hT,
    occupationInner_smul_right,occupationInner_vacuum,mul_one]

end Laughlin.Fock

end OAI
