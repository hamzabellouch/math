import OAI.NumberTheory.JointDickman.Counting.ComplexShortIntegrability
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! # Mean-square control of short windows by a nonnegative long mean -/
namespace JointDickman
open Finset Filter MeasureTheory Classical

noncomputable def shortWindowEnergy (E : ℕ → ℝ) (H : ℝ) (N : ℕ) (z : ℝ) : ℝ :=
  ∑ n ∈ range N, (Set.Ico ((n : ℝ)-H) n).indicator (fun _ => E n) z

theorem shortWindowEnergy_integrable (E : ℕ → ℝ) (H : ℝ) (N : ℕ) (a b : ℝ) :
    IntervalIntegrable (shortWindowEnergy E H N) volume a b := by
  have hi (n : ℕ) : IntervalIntegrable
      ((Set.Ico ((n : ℝ)-H) n).indicator (fun _ => E n)) volume a b :=
    intervalIntegrable_iff.mpr ((intervalIntegrable_const (c := E n)).def'.indicator measurableSet_Ico)
  convert (IntervalIntegrable.sum (range N) (fun n _ => hi n)) using 1
  ext z
  simp only [shortWindowEnergy,Finset.sum_apply]

theorem shortWindowEnergy_integral_le (E : ℕ → ℝ) (hE : ∀ n, 0 ≤ E n)
    {H a b : ℝ} (hH : 0 ≤ H) (hab : a ≤ b) (N : ℕ) :
    (∫ z in a..b, shortWindowEnergy E H N z) ≤ H*∑ n ∈ range N, E n := by
  unfold shortWindowEnergy
  rw [intervalIntegral.integral_finsetSum]
  · rw [mul_sum]
    apply sum_le_sum
    intro n _
    rw [intervalIntegral.integral_of_le hab,integral_indicator measurableSet_Ico,
      Measure.restrict_restrict measurableSet_Ico,setIntegral_const,smul_eq_mul]
    have hm := measureReal_mono (μ := volume)
      (show Set.Ico ((n : ℝ)-H) n ∩ Set.Ioc a b ⊆ Set.Ico ((n : ℝ)-H) n from Set.inter_subset_left)
      (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    rw [Real.volume_real_Ico_of_le (by linarith)] at hm
    convert mul_le_mul_of_nonneg_right hm (hE n) using 1
    ring
  · intro n _
    apply intervalIntegrable_iff.mpr
    exact (intervalIntegrable_const (c := E n)).def'.indicator measurableSet_Ico

theorem shortWindowEnergy_eq (E : ℕ → ℝ) {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z)
    {N : ℕ} (hN : ⌊z+H⌋₊ < N) :
    shortWindowEnergy E H N z = ∑ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊, E n := by
  have he (n : ℕ) : z ∈ Set.Ico ((n : ℝ)-H) n ↔ n ∈ Ioc ⌊z⌋₊ ⌊z+H⌋₊ := by
    rw [Set.mem_Ico,mem_Ioc,Nat.floor_lt hz,Nat.le_floor_iff (by linarith : 0 ≤ z+H)]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  unfold shortWindowEnergy
  simp only [Set.indicator_apply,he]
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter,mem_range,mem_Ioc]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨lt_of_le_of_lt h.2 hN,h⟩

theorem short_interval_card_le {H z : ℝ} (hH : 0 ≤ H) (hz : 0 ≤ z) :
    ((Ioc ⌊z⌋₊ ⌊z+H⌋₊).card : ℝ) ≤ H+1 := by
  rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono (by linarith : z ≤ z+H))]
  have hu := Nat.floor_le (by linarith : 0 ≤ z+H)
  have hl := Nat.lt_floor_add_one z
  linarith

theorem complexShortAverage_sq_le_window (f : ArithmeticFunction ℂ) (E : ℕ → ℝ)
    (hE : ∀ n, ‖f n‖^2 ≤ E n) {H z : ℝ} (hH : 1 ≤ H) (hz : 0 ≤ z)
    {N : ℕ} (hN : ⌊z+H⌋₊ < N) :
    ‖PublishedInputs.complexShortAverage f H z‖^2 ≤ (2/H)*shortWindowEnergy E H N z := by
  have hH0 : 0 < H := by linarith
  rw [shortWindowEnergy_eq E hH0.le hz hN]
  let S := Ioc ⌊z⌋₊ ⌊z+H⌋₊
  have hn := norm_sum_le S (fun n => f n)
  have hc := sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun n => ‖f n‖)
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  have hs := (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hc
  have he := sum_le_sum (s := S) (fun n _ => hE n)
  have hEn : 0 ≤ ∑ n ∈ S, E n := sum_nonneg (fun n _ => (sq_nonneg ‖f n‖).trans (hE n))
  have hcard : (S.card : ℝ) ≤ 2*H := (short_interval_card_le hH0.le hz).trans (by linarith)
  have hb : ‖∑ n ∈ S, f n‖^2 ≤ 2*H*∑ n ∈ S, E n :=
    hs.trans ((mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hcard hEn))
  rw [PublishedInputs.complexShortAverage,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hH0,div_pow]
  change ‖∑ n ∈ S, f n‖^2 / H^2 ≤ (2/H)*∑ n ∈ S, E n
  apply (div_le_iff₀ (sq_pos_of_pos hH0)).mpr
  convert hb using 1
  field_simp


theorem complexShortAverage_energy_le_prefix (f : ArithmeticFunction ℂ) (E : ℕ → ℝ)
    (hE : ∀ n, ‖f n‖^2 ≤ E n) {H X : ℝ} (hH : 1 ≤ H) (hX : 0 < X) (hHX : H ≤ X) :
    (1/X)*(∫ z in X..2*X, ‖PublishedInputs.complexShortAverage f H z‖^2) ≤
      2*(∑ n ∈ range (⌊3*X⌋₊+1), E n)/X := by
  have hH0 : 0 < H := by linarith
  have hE0 n : 0 ≤ E n := (sq_nonneg ‖f n‖).trans (hE n)
  have hi := intervalIntegral.integral_mono_on (by linarith : X ≤ 2*X)
    (PublishedInputs.complexShortAverage_sq_integrable_any f hH0 X (2*X))
    ((shortWindowEnergy_integrable E H (⌊3*X⌋₊+1) X (2*X)).const_mul (2/H))
    (fun z hz => complexShortAverage_sq_le_window f E hE hH (by linarith [hz.1])
      (show ⌊z+H⌋₊ < ⌊3*X⌋₊+1 from Nat.lt_succ_of_le (Nat.floor_mono (by linarith [hz.2]))))
  rw [intervalIntegral.integral_const_mul] at hi
  have he := shortWindowEnergy_integral_le E hE0 hH0.le (by linarith : X ≤ 2*X) (⌊3*X⌋₊+1)
  have h := hi.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2/H))
  have hh := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/X)
  convert hh using 1
  field_simp

end JointDickman

end OAI
