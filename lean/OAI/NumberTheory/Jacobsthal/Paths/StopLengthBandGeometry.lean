import OAI.NumberTheory.Jacobsthal.Partitions.CrossingBandGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.StopLengthBandGeometry
open NearbyParentGeometry

theorem shifted_ratio_band {r b a : ℝ} (hb : 400 ≤ b) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hlo : 204/100 ≤ r/b) (hhi : r/b ≤ 218/100) :
    2035/1000 ≤ r/b+(a-2)/b ∧ r/b+(a-2)/b ≤ 218/100 := by
  have hbp : 0 < b := by linarith
  have hshift : -(1/200:ℝ) ≤ (a-2)/b := (le_div_iff₀ hbp).mpr (by nlinarith)
  have hshift0 : (a-2)/b ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hbp.le
  constructor <;> linarith

theorem bin_log_length_stability {Y q P R xi p p₀ : ℝ}
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (_hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hp : R ≤ p ∧ p ≤ (1+xi)*R) (hp₀ : R ≤ p₀ ∧ p₀ ≤ (1+xi)*R)
    (hlogP : 200 ≤ Real.log P) :
    |Real.log (Y/(p*q))/Real.log P-Real.log (Y/(p₀*q))/Real.log P| ≤ 1/200 := by
  have hp0 := hR.trans_le hp.1
  have hp00 := hR.trans_le hp₀.1
  have hden : 0 < Real.log P := by linarith
  have habs : |p-p₀| ≤ xi*R := abs_le.mpr ⟨by nlinarith,by nlinarith⟩
  have hlog : |Real.log p-Real.log p₀| ≤ xi := by
    have hh := log_stability hR hp.1 hp₀.1
    have hd := div_le_div_of_nonneg_right habs hR.le
    rw [mul_div_cancel_right₀ xi hR.ne'] at hd
    exact hh.trans hd
  have he : Real.log (Y/(p*q))-Real.log (Y/(p₀*q))=Real.log p₀-Real.log p := by
    rw [Real.log_div hY.ne' (mul_pos hp0 hq).ne',Real.log_div hY.ne' (mul_pos hp00 hq).ne',
      Real.log_mul hp0.ne' hq.ne',Real.log_mul hp00.ne' hq.ne']
    ring
  rw [← sub_div,he,abs_div,abs_of_pos hden,abs_sub_comm (Real.log p₀)]
  calc
    _ ≤ xi/Real.log P := div_le_div_of_nonneg_right hlog hden.le
    _ ≤ 1/Real.log P := div_le_div_of_nonneg_right hxi1 hden.le
    _ ≤ 1/200 := one_div_le_one_div_of_le (by norm_num) hlogP

theorem whole_bin_length_band {Y q P R xi p p₀ s₀ : ℝ}
    (hY : 0 < Y) (hq : 0 < q) (hR : 0 < R) (hxi : 0 ≤ xi) (hxi1 : xi ≤ 1)
    (hp : R ≤ p ∧ p ≤ (1+xi)*R) (hp₀ : R ≤ p₀ ∧ p₀ ≤ (1+xi)*R)
    (hlogP : 200 ≤ Real.log P) (hs₀ : Real.log (Y/(p₀*q))/Real.log P=s₀)
    (hband : 2035/1000 ≤ s₀ ∧ s₀ ≤ 218/100) :
    203/100 ≤ Real.log (Y/(p*q))/Real.log P ∧ Real.log (Y/(p*q))/Real.log P ≤ 219/100 := by
  have hh := bin_log_length_stability hY hq hR hxi hxi1 hp hp₀ hlogP
  rw [hs₀] at hh
  constructor <;> linarith [(abs_le.mp hh).1,(abs_le.mp hh).2]
end NumberTheoryLean.StopLengthBandGeometry


end Erdos970

end OAI
