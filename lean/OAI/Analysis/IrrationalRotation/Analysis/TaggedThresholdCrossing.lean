import OAI.Analysis.IrrationalRotation.Rotation.FloorCocycle

namespace OAI

namespace Invariant233.FloorCocycle

theorem threshold_mem_Ioo_of_abs_phase {δ t : ℝ} (hδ : 0 ≤ δ)
    (hlo : δ < |t|) (hhi : |t| < 1 - δ) :
    1 - Int.fract t ∈ Set.Ioo δ (1 - δ) := by
  by_cases ht : 0 ≤ t
  · rw [abs_of_nonneg ht] at hlo hhi
    have hf : Int.fract t = t := Int.fract_eq_self.mpr ⟨ht, by linarith⟩
    rw [hf]
    constructor <;> linarith
  · have ht' : t < 0 := lt_of_not_ge ht
    rw [abs_of_neg ht'] at hlo hhi
    have hf : Int.fract (-t) = -t :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hne : Int.fract (-t) ≠ 0 := by rw [hf]; linarith
    have hf' : Int.fract t = 1 + t := by
      simpa only [neg_neg, hf, sub_neg_eq_add] using Int.fract_neg hne
    rw [hf']
    constructor <;> linarith

theorem tagged_crossing_of_abs_phase {x y δ t : ℝ} (hδ : 0 ≤ δ)
    (hx : x < δ) (hy : 1 - δ < y)
    (hlo : δ < |t|) (hhi : |t| < 1 - δ) :
    x < 1 - Int.fract t ∧ 1 - Int.fract t ≤ y := by
  have h := threshold_mem_Ioo_of_abs_phase hδ hlo hhi
  exact ⟨hx.trans h.1, (h.2.trans hy).le⟩

theorem tagged_crossing_of_window {m K α x y : ℝ} (k : ℤ)
    (hm : 2 ≤ m) (hK : 0 < K)
    (hαlo : 1 / (m * K) < α) (hαhi : α < 2 / (m * K))
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (hx : x < 1 / m) (hy : 1 - 1 / m < y) :
    x < 1 - Int.fract ((k : ℝ) * α) ∧
      1 - Int.fract ((k : ℝ) * α) ≤ y := by
  have hm0 : 0 < m := by linarith
  have hmK : 0 < m * K := mul_pos hm0 hK
  have hα0 : 0 < α := (one_div_pos.mpr hmK).trans hαlo
  have hk0 : 0 < |(k : ℝ)| := hK.trans hklo
  have hlo : 1 / m < |(k : ℝ)| * α := by
    calc
      1 / m = K * (1 / (m * K)) := by field_simp
      _ < |(k : ℝ)| * (1 / (m * K)) :=
        mul_lt_mul_of_pos_right hklo (one_div_pos.mpr hmK)
      _ ≤ |(k : ℝ)| * α := mul_le_mul_of_nonneg_left hαlo.le hk0.le
  have hhalf : |(k : ℝ)| * α < 1 / 2 := by
    calc
      |(k : ℝ)| * α < |(k : ℝ)| * (2 / (m * K)) :=
        mul_lt_mul_of_pos_left hαhi hk0
      _ ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_right hkhi (div_nonneg (by norm_num) hmK.le)
      _ = 1 / 2 := by field_simp; ring
  have hinv : 1 / m ≤ (1 / 2 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hm
  apply tagged_crossing_of_abs_phase (one_div_pos.mpr hm0).le hx hy
  · simpa only [abs_mul, abs_of_pos hα0] using hlo
  · rw [abs_mul, abs_of_pos hα0]
    linarith

theorem tagged_crossing_of_window_closed {m K α x y : ℝ} (k : ℤ)
    (hm : 2 ≤ m) (hK : 0 < K)
    (hαlo : 1 / (m * K) ≤ α) (hαhi : α ≤ 2 / (m * K))
    (hklo : K < |(k : ℝ)|) (hkhi : |(k : ℝ)| ≤ m * K / 4)
    (hx : x < 1 / m) (hy : 1 - 1 / m ≤ y) :
    x < 1 - Int.fract ((k : ℝ) * α) ∧
      1 - Int.fract ((k : ℝ) * α) ≤ y := by
  have hm0 : 0 < m := by linarith
  have hmK : 0 < m * K := mul_pos hm0 hK
  have hα0 : 0 < α := (one_div_pos.mpr hmK).trans_le hαlo
  have hk0 : 0 < |(k : ℝ)| := hK.trans hklo
  have hlo : 1 / m < |(k : ℝ)| * α := by
    calc
      1 / m = K * (1 / (m * K)) := by field_simp
      _ < |(k : ℝ)| * (1 / (m * K)) :=
        mul_lt_mul_of_pos_right hklo (one_div_pos.mpr hmK)
      _ ≤ |(k : ℝ)| * α := mul_le_mul_of_nonneg_left hαlo hk0.le
  have hhalf : |(k : ℝ)| * α ≤ 1 / 2 := by
    calc
      |(k : ℝ)| * α ≤ |(k : ℝ)| * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_left hαhi hk0.le
      _ ≤ (m * K / 4) * (2 / (m * K)) :=
        mul_le_mul_of_nonneg_right hkhi (div_nonneg (by norm_num) hmK.le)
      _ = 1 / 2 := by field_simp; ring
  have hinv : 1 / m < (1 / 2 : ℝ) := hlo.trans_le hhalf
  have hatt : 1 - Int.fract ((k : ℝ) * α) ∈ Set.Ioo (1 / m) (1 - 1 / m) := by
    apply threshold_mem_Ioo_of_abs_phase (one_div_pos.mpr hm0).le
    · simpa only [abs_mul, abs_of_pos hα0] using hlo
    · rw [abs_mul, abs_of_pos hα0]
      linarith
  exact ⟨hx.trans hatt.1, hatt.2.le.trans hy⟩

end Invariant233.FloorCocycle

end OAI
