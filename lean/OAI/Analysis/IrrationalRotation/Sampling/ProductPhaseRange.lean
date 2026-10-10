import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection

theorem phase_threshold_mem_Icc {a t : ℝ} (ha : 0 < a)
    (ha_half : a ≤ 1 / 2) (hlower : a ≤ |t|) (hupper : |t| ≤ 1 / 2) :
    1 - Int.fract t ∈ Set.Icc a (1 - a) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht] at hlower hupper
    rw [Int.fract_eq_self.mpr ⟨ht, by linarith⟩]
    constructor <;> linarith
  · rw [abs_of_neg ht] at hlower hupper
    have hf : Int.fract (-t) = -t :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hn : Int.fract t = 1 + t := by
      simpa only [neg_neg, hf, sub_neg_eq_add] using
        (Int.fract_neg (x := -t) (by rw [hf]; linarith))
    rw [hn]
    constructor <;> linarith

theorem product_phase_range {m K G θ k : ℝ}
    (hm : 0 < m) (hK : 0 < K) (hG : 0 < G) (hwidth : G / m ≤ 1 / 4)
    (hθlower : 1 / (m * K) ≤ θ) (hθupper : θ ≤ 2 / (m * K))
    (hklower : G * K ≤ |k|) (hkupper : |k| ≤ (m * K) / 4) :
    1 - Int.fract (k * θ) ∈ Set.Icc (G / m) (1 - G / m) := by
  have hN : 0 < m * K := mul_pos hm hK
  have hθ : 0 < θ := lt_of_lt_of_le (one_div_pos.mpr hN) hθlower
  have hlower : G / m ≤ |k * θ| := by
    rw [abs_mul, abs_of_pos hθ]
    calc
      G / m = (G * K) * (1 / (m * K)) := by
        field_simp
      _ ≤ |k| * (1 / (m * K)) :=
        mul_le_mul_of_nonneg_right hklower (le_of_lt (one_div_pos.mpr hN))
      _ ≤ |k| * θ := mul_le_mul_of_nonneg_left hθlower (abs_nonneg k)
  have hupper : |k * θ| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hθ]
    calc
      |k| * θ ≤ ((m * K) / 4) * (2 / (m * K)) :=
        mul_le_mul hkupper hθupper (le_of_lt hθ) (by positivity)
      _ = 1 / 2 := by field_simp; norm_num
  exact phase_threshold_mem_Icc (div_pos hG hm) (by linarith) hlower hupper

theorem product_phase_range_integer {m K G θ : ℝ} (k : ℤ)
    (hm : 0 < m) (hK : 0 < K) (hG : 0 < G) (hwidth : G / m ≤ 1 / 4)
    (hθlower : 1 / (m * K) ≤ θ) (hθupper : θ ≤ 2 / (m * K))
    (hklower : G * K ≤ |(k : ℝ)|) (hkupper : |(k : ℝ)| ≤ (m * K) / 4) :
    1 - Int.fract ((k : ℝ) * θ) ∈ Set.Icc (G / m) (1 - G / m) :=
  product_phase_range hm hK hG hwidth hθlower hθupper hklower hkupper

end InvariantProjection

end OAI
