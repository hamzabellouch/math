import OAI.Analysis.Laughlin.FourBody.Coefficients

namespace OAI

namespace Laughlin.Spin
open scoped BigOperators

theorem fourBodyCopy_off (Q r D n : ℕ) (hr : r ≤ Q) (hrD : r ≤ D)
    (hA : D-r ≤ 2*Q-2) (hB : D-r ≤ genericCoupledWeight Q Q r)
    (p : Fin ((2*Q-2)+1)) (i : WedgePairIndex Q)
    (hi : p.val+i.val.1.val+i.val.2.val ≠ D+n) :
    fourBodyCopy Q r D hr hA hB n (p,i) = 0 := by
  rw [fourBodyCopy_coordinate]
  apply Finset.sum_eq_zero
  intro b hb
  by_cases hi' : i.val.1.val+i.val.2.val=r+b.val
  · rw [genericUnitDescendant_off _ _ _ _ hA hB (p,b) (by dsimp; omega),mul_zero,mul_zero]
  · rw [pairCoupledWedge_off Q r b.val hr i hi',zero_mul]

theorem source_fourBody_coefficients_norm (Q r D T : ℕ) (ho : Odd r)
    (hrD : r ≤ D) (hDT : D ≤ T) (hQT : T+2 ≤ Q) :
    (∑ p : Fin ((2*Q-2)+1), ∑ i : WedgePairIndex Q,
      if p.val+i.val.1.val+i.val.2.val=T then
        (fourBodyCoefficient Q r D T p.val i.val.1.val i.val.2.val)^2 else 0) = 1 := by
  have hn : T-D ≤ genericCoupledWeight (2*Q-2) (genericCoupledWeight Q Q r) (D-r) := by
    unfold genericCoupledWeight; omega
  have hnorm := fourBodyCopy_norm Q r D (T-D) (by omega) ho (by omega)
    (by unfold genericCoupledWeight; omega) hn
  rw [vectorNormSq,Fintype.sum_prod_type] at hnorm
  rw [← hnorm]
  apply Finset.sum_congr rfl; intro p hp
  apply Finset.sum_congr rfl; intro i hi
  by_cases he : p.val+i.val.1.val+i.val.2.val=T
  · rw [ite_eq_left he,fourBodyCopy_source_coefficient Q r D T hrD hDT hQT p i he]
  · rw [ite_eq_right he,fourBodyCopy_off Q r D (T-D) (by omega) hrD (by omega)
      (by unfold genericCoupledWeight; omega) p i (by omega),zero_pow (by omega)]

end Laughlin.Spin

end OAI
