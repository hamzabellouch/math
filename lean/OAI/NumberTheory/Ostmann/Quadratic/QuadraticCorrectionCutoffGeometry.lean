import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSecondCutoffs

namespace OAI

/-! # The actual frequency-dependent cutoffs lie in fixed divisor bands -/

namespace Ostmann

noncomputable def quadraticCorrectionBase (M H : ℝ) (e b : ℕ) : ℝ :=
  Real.sqrt ((e : ℝ) * H ^ 2 / (M * b))

theorem quadraticCorrectionBase_pos {M H : ℝ} {e b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hb : 0 < b) :
    0 < quadraticCorrectionBase M H e b := by
  unfold quadraticCorrectionBase
  positivity

theorem quadratic_correction_base_formula {M H : ℝ} {e b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (_hb : 0 < b) :
    quadraticCorrectionBase M H e b =
      H * Real.sqrt e / (Real.sqrt M * Real.sqrt b) := by
  unfold quadraticCorrectionBase
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity : (0 : ℝ) ≤ e),
    Real.sqrt_sq_eq_abs, abs_of_pos hH, Real.sqrt_mul hM.le]
  ring

theorem quadratic_correction_base_band {M H : ℝ} {e B b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B)
    (hb : B ≤ b) (hb' : b ≤ 2 * B) :
    quadraticCorrectionBase M H e B / 2 ≤ quadraticCorrectionBase M H e b ∧
      quadraticCorrectionBase M H e b ≤ quadraticCorrectionBase M H e B := by
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hbR : (0 : ℝ) < b := by exact_mod_cast hB.trans_le hb
  have hb₁ : (B : ℝ) ≤ b := by exact_mod_cast hb
  have hb₂ : (b : ℝ) ≤ 2 * B := by exact_mod_cast hb'
  have hn : 0 ≤ (e : ℝ) * H ^ 2 := by positivity
  have hlo : (e : ℝ) * H ^ 2 / (M * B) ≤
      2 * ((e : ℝ) * H ^ 2 / (M * b)) := by
    calc
      _ = 2 * ((e : ℝ) * H ^ 2 / (M * (2 * B))) := by ring
      _ ≤ _ := by gcongr
  have hhi : (e : ℝ) * H ^ 2 / (M * b) ≤ (e : ℝ) * H ^ 2 / (M * B) := by gcongr
  unfold quadraticCorrectionBase
  constructor
  · have h₁ := Real.sq_sqrt (div_nonneg hn (by positivity : 0 ≤ M * B))
    have h₂ := Real.sq_sqrt (div_nonneg hn (by positivity : 0 ≤ M * b))
    have h₁₀ := Real.sqrt_nonneg ((e : ℝ) * H ^ 2 / (M * B))
    have h₂₀ := Real.sqrt_nonneg ((e : ℝ) * H ^ 2 / (M * b))
    nlinarith
  · exact Real.sqrt_le_sqrt hhi

theorem quadratic_correction_cutoff_band {M H J : ℝ} {e B b : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B)
    (hJ : 1 ≤ J) (hb : B ≤ b) (hb' : b ≤ 2 * B) :
    quadraticCorrectionBase M H e B / (4 * J) ≤
        quadraticSecondLower (quadraticCorrectionBase M H e b) J ∧
      quadraticSecondLower (quadraticCorrectionBase M H e b) J ≤
        quadraticCorrectionBase M H e B / (2 * J) ∧
      quadraticCorrectionBase M H e B * J ≤
        quadraticSecondUpper (quadraticCorrectionBase M H e b) J ∧
      quadraticSecondUpper (quadraticCorrectionBase M H e b) J ≤
        2 * quadraticCorrectionBase M H e B * J := by
  obtain ⟨hlo, hhi⟩ := quadratic_correction_base_band hM hH he hB hb hb'
  have hJ₀ : 0 < J := zero_lt_one.trans_le hJ
  unfold quadraticSecondLower quadraticSecondUpper
  refine ⟨?_, div_le_div_of_nonneg_right hhi (by positivity), ?_, ?_⟩
  · have hh := div_le_div_of_nonneg_right hlo (by positivity : 0 ≤ 2 * J)
    convert hh using 1
    ring
  · nlinarith [mul_le_mul_of_nonneg_right hlo hJ₀.le]
  · nlinarith [mul_le_mul_of_nonneg_right hhi hJ₀.le]

theorem quadratic_correction_divisor_band {M H J : ℝ} {e B b D d : ℕ}
    (hM : 0 < M) (hH : 0 < H) (he : 0 < e) (hB : 0 < B)
    (hJ : 1 ≤ J) (hb : B ≤ b) (hb' : b ≤ 2 * B) (hd : D < d) (hd' : d ≤ 2 * D) :
    ((d : ℝ) ≤ quadraticSecondUpper (quadraticCorrectionBase M H e b) J →
      (D : ℝ) < 2 * quadraticCorrectionBase M H e B * J) ∧
    (quadraticSecondLower (quadraticCorrectionBase M H e b) J < (d : ℝ) →
      quadraticCorrectionBase M H e B / (8 * J) < (D : ℝ)) := by
  obtain ⟨hlo, _, _, hhi⟩ := quadratic_correction_cutoff_band hM hH he hB hJ hb hb'
  have hdR : (D : ℝ) < d := by exact_mod_cast hd
  have hdR' : (d : ℝ) ≤ 2 * D := by exact_mod_cast hd'
  constructor
  · intro h
    exact hdR.trans_le (h.trans hhi)
  · intro h
    have hh : quadraticCorrectionBase M H e B / (4 * J) < 2 * D := hlo.trans_lt (h.trans_le hdR')
    have hid : quadraticCorrectionBase M H e B / (8 * J) =
        (quadraticCorrectionBase M H e B / (4 * J)) / 2 := by ring
    rw [hid]
    linarith

end Ostmann

end OAI
