import OAI.NumberTheory.JointDickman.Analysis.CharacterDistanceEuler
import OAI.NumberTheory.JointDickman.Analysis.DirichletGrowth

namespace OAI

/-! # Character distance on polynomial logarithmic frequency ranges

This proves the small-frequency part of KMT Lemma 7.8 directly from the
classical Dirichlet-series growth estimate. The full input has a larger
frequency range and is not asserted here.
-/
namespace JointDickman
open Complex

lemma character_log_frequency_norm {A : ℝ} (hA : 0 ≤ A)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, Real.exp 1 ≤ X → ∀ t : ℝ,
      |t| ≤ (Real.log X)^A →
      ‖χ.LFunction (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
        K*(Real.log X)^(1/4:ℝ) := by
  let ε : ℝ := 1/(8*(A+1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε ≤ 1/2 := by
    dsimp [ε]
    apply (div_le_iff₀ (by positivity : 0<8*(A+1))).mpr
    linarith
  have hAε : A*(2*ε) ≤ (1/4:ℝ) := by
    dsimp [ε]
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<4)).mpr
    have he : A*(2*(1/(8*(A+1))))*4 = A/(A+1) := by
      field_simp
      ring
    rw [he]
    exact (div_le_one (by positivity : 0<A+1)).mpr (by linarith)
  obtain ⟨K,hK,hbound⟩ := LargePrimeGaps.LFunction_norm_small_power hε hε1
  refine ⟨K*(5*(q+2:ℝ))^(2*ε),by positivity,?_⟩
  intro X hX t ht
  have hlog1 : 1 ≤ Real.log X := by
    simpa using Real.log_le_log (Real.exp_pos 1) hX
  have hlog : 0 < Real.log X := by linarith
  have hp : 1 ≤ (Real.log X)^A := Real.one_le_rpow hlog1 hA
  have hσ : 0 < 1+1/Real.log X := by positivity
  have hσ2 : 1+1/Real.log X ≤ 2 := by
    have h := (div_le_one hlog).mpr hlog1
    linarith
  have hs : 1-ε ≤ (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hnorm : ‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2 ≤ 5*(Real.log X)^A := by
    have h := norm_add_le (((1+1/Real.log X:ℝ):ℂ)) ((t:ℂ)*I)
    rw [norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hσ,Complex.norm_real,Real.norm_eq_abs] at h
    linarith
  calc
    _ ≤ K*((q+2)*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) :=
      hbound q χ hχ _ hs
    _ ≤ K*((5*(q+2:ℝ))*(Real.log X)^A)^(2*ε) := by
      apply mul_le_mul_of_nonneg_left _ hK.le
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith
    _ = (K*(5*(q+2:ℝ))^(2*ε))*(Real.log X)^(A*(2*ε)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hlog.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 hAε) (by positivity)

/-- This is an unconditional bound on every fixed polynomial logarithmic
frequency range. It does not replace the full KMT range `|t| ≤ X`. -/
theorem characterDistance_log_frequency {A : ℝ} (hA : 0 ≤ A)
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ X : ℝ, max 2 (Real.exp 1) ≤ X → ∀ t : ℝ,
      |t| ≤ (Real.log X)^A →
      (3/4:ℝ)*Real.log (Real.log X)-C ≤
        PublishedInputs.primeDistanceSquared (characterArithmetic χ) X t := by
  obtain ⟨B,hB⟩ := characterDistance_ge_log_sub_L
  obtain ⟨K,hK,hbound⟩ := character_log_frequency_norm hA χ hχ
  refine ⟨B+Real.log K,?_⟩
  intro X hX t ht
  have hXe : Real.exp 1 ≤ X := (le_max_right _ _).trans hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hlog : 0 < Real.log X := Real.log_pos (by linarith)
  have hs : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,sub_zero,zero_mul,add_zero]
    linarith [one_div_pos.mpr hlog]
  have hn : 0 < ‖χ.LFunction (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ :=
    norm_pos_iff.mpr (by
      rw [χ.LFunction_eq_LSeries hs]
      exact χ.LSeries_ne_zero_of_one_lt_re hs)
  have hl := Real.log_le_log hn (hbound X hXe t ht)
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hlog _).ne',Real.log_rpow hlog] at hl
  have hd := hB q χ X hX t
  linarith

end JointDickman

end OAI
