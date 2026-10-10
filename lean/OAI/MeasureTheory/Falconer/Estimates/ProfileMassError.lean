import OAI.MeasureTheory.Falconer.Estimates.ActualRegularizedClasses
import OAI.MeasureTheory.Falconer.Radial.RadialDistanceError

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem RegularizedProfileData.normalized_cell_mass_le
    {Q : DyadicSquare} {ρ : Measure Plane} {N B : ℕ} {δ lam : ℝ} {m : ℝ → ℝ}
    (hd : RegularizedProfileData Q ρ N B δ lam m) {a : ℕ} (ha : a ≤ N)
    {A : CellPath} (hA : A.length = a) :
    (ρ (Q.descendant A).carrier).toReal / ((2:ℝ)^N)^(-m a) ≤ ((2:ℝ)^N)^(3*lam) := by
  have hM : 0 < ((2:ℝ)^N)^(-m a) := Real.rpow_pos_of_pos (by positivity) _
  apply (div_le_iff₀ hM).mpr
  by_cases hp : 0 < ρ (Q.descendant A).carrier
  · exact (hd.cells a ha A hA hp).2
  · have hz : ρ (Q.descendant A).carrier = 0 := le_antisymm (le_of_not_gt hp) bot_le
    rw [hz, ENNReal.toReal_zero]
    positivity

theorem parent_error_power_bound {R C W l T outer : ℝ}
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hW : 0 ≤ W) (hl : 0 ≤ l) (hT : 0 ≤ T)
    (ho : 0 ≤ outer) (houter : outer ≤ R^2) (hconst : 4*W*(2*C+1) ≤ R) :
    let ε := R^(-(T+2*l+3))*R^l
    outer * (2*(C*R^l)*ε+ε^2) * (4*W) ≤ R^(-T) := by
  dsimp only
  have hRp : 0 < R := zero_lt_one.trans_le hR
  have hε : R^(-(T+2*l+3))*R^l = R^(-(T+l+3)) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  rw [hε]
  have hepos : 0 ≤ R^(-(T+l+3)) := Real.rpow_nonneg hRp.le _
  have heone : R^(-(T+l+3)) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hR (show -(T+l+3) ≤ 0 by linarith)
  have hRl : 1 ≤ R^l := Real.one_le_rpow hR hl
  have hesq : (R^(-(T+l+3)))^2 ≤ R^l*R^(-(T+l+3)) := by
    nlinarith [mul_le_mul_of_nonneg_right (heone.trans hRl) hepos]
  have hpoly : 2*(C*R^l)*R^(-(T+l+3))+(R^(-(T+l+3)))^2 ≤
      (2*C+1)*R^l*R^(-(T+l+3)) := by nlinarith
  have hid : R^2*((2*C+1)*R^l*R^(-(T+l+3)))*(4*W) =
      (4*W*(2*C+1))*R^(-T-1) := by
    have hr2 : (R^2:ℝ) = R^(2:ℝ) := (Real.rpow_natCast R 2).symm
    rw [hr2]
    have he : R^(2:ℝ)*R^l*R^(-(T+l+3)) = R^(-T-1) := by
      rw [← Real.rpow_add hRp, ← Real.rpow_add hRp]
      congr 1
      ring
    calc
      _ = (4*W*(2*C+1))*(R^(2:ℝ)*R^l*R^(-(T+l+3))) := by ring
      _ = _ := by rw [he]
  calc
    _ ≤ R^2*((2*C+1)*R^l*R^(-(T+l+3)))*(4*W) :=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hpoly ho).trans
          (mul_le_mul_of_nonneg_right houter (by positivity))) (by positivity)
    _ = (4*W*(2*C+1))*R^(-T-1) := hid
    _ ≤ R*R^(-T-1) := mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hRp.le _)
    _ = R^(-T) := by
      nth_rw 1 [← Real.rpow_one R]
      rw [← Real.rpow_add hRp]
      congr 1
      ring

end PlanarFalconer

end OAI
