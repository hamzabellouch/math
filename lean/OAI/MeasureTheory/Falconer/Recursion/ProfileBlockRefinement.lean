import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses

namespace OAI

namespace PlanarFalconer
open MeasureTheory

theorem RegularizedProfileData.unitBlocks {Q : DyadicSquare} {ρ : Measure Plane}
    {N B : ℕ} {δ lam : ℝ} {m : ℝ → ℝ}
    (h : RegularizedProfileData Q ρ N B δ lam m) (hB : 0 < B) :
    RegularizedProfileData Q ρ N 1 δ lam m := by
  refine ⟨h.probability,h.continuous,h.zero,h.slope,?_,h.cells,h.envelope,h.adjusted,h.packing⟩
  intro i hi
  have hiN : i ≤ N := by simpa only [Nat.div_one] using Nat.le_of_lt_succ hi
  have hj : i/B < N/B+1 := Nat.lt_succ_of_le (Nat.div_le_div_right hiN)
  obtain ⟨a,b,hab⟩ := h.affine (i/B) hj
  refine ⟨a,b,?_⟩
  intro u hlo hhi
  apply hab u
  · apply le_trans _ hlo
    apply Nat.cast_le.mpr
    simp only [blockDepth,Nat.mul_one]
    apply Nat.sub_le_sub_left
    have hh : i < (i/B+1)*B := by simpa only [Nat.mul_comm] using Nat.lt_mul_div_succ i hB
    omega
  · apply hhi.trans
    apply Nat.cast_le.mpr
    simp only [blockDepth,Nat.mul_one]
    exact Nat.sub_le_sub_left (Nat.div_mul_le_self i B) N

end PlanarFalconer

end OAI
