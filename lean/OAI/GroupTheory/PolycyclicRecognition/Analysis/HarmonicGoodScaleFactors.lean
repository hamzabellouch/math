import OAI.GroupTheory.PolycyclicRecognition.Analysis.HarmonicVolumeDeterminant

namespace OAI

/-! # Separate volume and determinant bounds from a good scale -/
noncomputable section
namespace PolycyclicRecognition

theorem positive_product_power_first_factor {a b c d K : ℝ} {k : ℕ}
    (ha : 0 < a) (hb : 0 ≤ b) (hc : 0 < c) (hd : c ≤ d) (hK : 0 ≤ K) (hk : 0 < k)
    (h : b ^ k * d ≤ K ^ k * (a ^ k * c)) : b ≤ K * a := by
  have hp : b ^ k * c ≤ (K * a) ^ k * c := by
    calc
      _ ≤ b ^ k * d := mul_le_mul_of_nonneg_left hd (pow_nonneg hb _)
      _ ≤ K ^ k * (a ^ k * c) := h
      _ = _ := by rw [mul_pow]; ring
  exact (pow_le_pow_iff_left₀ hb (mul_nonneg hK ha.le) hk.ne').mp
    ((mul_le_mul_iff_left₀ hc).mp hp)

theorem positive_product_power_second_factor {a b c d K : ℝ} {k : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hd : 0 ≤ d)
    (h : b ^ k * d ≤ K ^ k * (a ^ k * c)) : d ≤ K ^ k * c := by
  apply (mul_le_mul_iff_right₀ (pow_pos ha k)).mp
  calc
    a ^ k * d ≤ b ^ k * d := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le hab k) hd
    _ ≤ K ^ k * (a ^ k * c) := h
    _ = _ := by ring

variable {G : Type*} [Group G] [DecidableEq G]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem wordBall_good_scale_volume_bound (S : Finset G) (F : ι → G → ℝ)
    {m n : ℕ} (hmn : m ≤ n) (hpos : (wordBallGram S m F).PosDef)
    (hk : 0 < Fintype.card ι) (K : ℝ) (hK : 0 ≤ K)
    (hscale : wordBallVolumeDeterminant S F n ≤
      K ^ Fintype.card ι * wordBallVolumeDeterminant S F m) :
    ((wordBall S n).card : ℝ) ≤ K * (wordBall S m).card := by
  exact positive_product_power_first_factor
    (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨1, one_mem_wordBall S m⟩))
    (Nat.cast_nonneg _) hpos.det_pos (wordBallGram_det_monotone S F hmn) hK hk hscale

theorem wordBall_good_scale_determinant_bound (S : Finset G) (F : ι → G → ℝ)
    {m n : ℕ} (hmn : m ≤ n) (K : ℝ)
    (hscale : wordBallVolumeDeterminant S F n ≤
      K ^ Fintype.card ι * wordBallVolumeDeterminant S F m) :
    (wordBallGram S n F).det ≤ K ^ Fintype.card ι * (wordBallGram S m F).det := by
  exact positive_product_power_second_factor
    (Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨1, one_mem_wordBall S m⟩))
    (Nat.cast_le.mpr (Finset.card_le_card (wordBall_mono S hmn)))
    (wordBallGram_posSemidef S n F).det_nonneg hscale

def harmonicScaleConstant (b d : ℕ) : ℝ := 2 * (16 : ℝ) ^ (3 * (2 * b + 2 * d))

theorem harmonicScaleConstant_gt_one (b d : ℕ) : 1 < harmonicScaleConstant b d := by
  have h : (1 : ℝ) ≤ 16 ^ (3 * (2 * b + 2 * d)) := one_le_pow₀ (by norm_num)
  dsimp [harmonicScaleConstant]
  linarith

theorem harmonic_good_scale_factor_bound (b d k : ℕ) (hk : 0 < k) :
    2 * ((16 : ℝ) ^ ((2 * b + 2 * d) * k)) ^ 3 ≤ harmonicScaleConstant b d ^ k := by
  have ht : (2 : ℝ) ≤ 2 ^ k := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
  have he : ((2 * b + 2 * d) * k) * 3 = (3 * (2 * b + 2 * d)) * k := by ring
  rw [harmonicScaleConstant, mul_pow, ← pow_mul, ← pow_mul, he]
  exact mul_le_mul_of_nonneg_right ht (by positivity)

end PolycyclicRecognition

end

end OAI
