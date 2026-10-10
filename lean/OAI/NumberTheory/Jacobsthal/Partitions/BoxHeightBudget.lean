import OAI.NumberTheory.Jacobsthal.Estimates.CorrectionFloorRemainder

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

open _root_.Filter
open scoped Topology
namespace ErdosInverseBoxHeight

theorem small_power_height {z Sq R Z : ℝ} (hz : 4 ≤ z)
    (hSq : 0 ≤ Sq) (hR : 0 ≤ R) (hZ : 0 ≤ Z)
    (hSqz : Sq ≤ z^((21:ℝ)/10)) (hRz : R ≤ z^((1:ℝ)/100))
    (hZz : Z ≤ z^((1:ℝ)/100)) : 2*Sq*R^2*Z^20 ≤ z^3 := by
  have hz0 : 0 ≤ z := by linarith
  have hzpos : 0 < z := by linarith
  have htwo : (2:ℝ) ≤ z^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) hz0).mpr (by norm_num; exact hz)
  have hRp : R^2 ≤ z^((2:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^2 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  have hZp : Z^20 ≤ z^((20:ℝ)/100) := by
    calc
      _ ≤ (z^((1:ℝ)/100))^20 := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hz0]; norm_num
  calc
    _ ≤ z^((1:ℝ)/2)*z^((21:ℝ)/10)*z^((2:ℝ)/100)*z^((20:ℝ)/100) := by gcongr
    _ = z^((141:ℝ)/50) := by
      rw [← Real.rpow_add hzpos,← Real.rpow_add hzpos,← Real.rpow_add hzpos]
      norm_num
    _ ≤ z^3 := by
      have h := Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ z)
        (by norm_num : (141:ℝ)/50 ≤ 3)
      norm_num at h ⊢
      exact h

theorem uniform_box_height (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ z : ℝ in atTop, 1 < z ∧ ∀ Sq R B xi q : ℝ,
      0 ≤ Sq → 0 ≤ R → 1 ≤ B → B ≤ Real.log z → 0 ≤ xi → xi ≤ 1 →
      0 < q → q ≤ z^2 → Sq/q ≤ (1+xi)^(C*Real.log B) → R ≤ z^((1:ℝ)/100) →
      2*Sq*R^2*(sourceZ z)^20 ≤ z^3 := by
  filter_upwards [uniform_bin_inflation C hC,sourceZ_le_small_power,eventually_ge_atTop (4:ℝ)]
    with z hInfl hZ hz
  refine ⟨hInfl.1,?_⟩
  intro Sq R B xi q hSq hR hB hBL hxi0 hxi1 hq hqz hinfl hRz
  have hBpow := hInfl.2 B xi hB hBL hxi0 hxi1
  have hSqz : Sq ≤ z^((21:ℝ)/10) := by
    have hSqbound := (div_le_iff₀ hq).mp (hinfl.trans hBpow)
    calc
      _ ≤ z^((1:ℝ)/10)*q := hSqbound
      _ ≤ z^((1:ℝ)/10)*z^2 :=
        mul_le_mul_of_nonneg_left hqz (Real.rpow_nonneg (by linarith) _)
      _ = _ := by
        rw [← Real.rpow_natCast z 2,← Real.rpow_add (by linarith : 0 < z)]
        norm_num
  exact small_power_height hz hSq hR hZ.2.1.le hSqz hRz hZ.2.2

end ErdosInverseBoxHeight

end

end Erdos970

end OAI
