import OAI.NumberTheory.JointDickman.Analysis.ZetaCutoff
import OAI.NumberTheory.JointDickman.Analysis.DirichletGrowth

namespace OAI

/-! # Zeta growth on polynomial logarithmic frequency ranges away from the pole

The regularized Dirichlet series has small power growth, and the pole term
is bounded when the frequency has absolute value at least one.
-/
namespace JointDickman
open Complex

lemma zeta_log_frequency_norm {A : ℝ} (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, Real.exp 1 ≤ X → ∀ t : ℝ,
      1 ≤ |t| → |t| ≤ (Real.log X)^A →
      ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
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
  obtain ⟨K,hK,hbound⟩ := LargePrimeGaps.regularSeries_norm_small_power hε hε1
  refine ⟨(K+1)*(10:ℝ)^(2*ε),by positivity,?_⟩
  intro X hX t htlo ht
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
  have hs1 : 1 < (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I).re := by
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im,
      mul_zero, sub_zero, zero_mul, add_zero]
    linarith [one_div_pos.mpr hlog]
  have hreg := hbound (LargePrimeGaps.positiveCoefficients (fun _ => 1)) 1 1
    (LargePrimeGaps.positiveCoefficients_zero _)
    (LargePrimeGaps.positiveCoefficients_norm_le (by intro n; simp))
    (by simp) (by norm_num) (fun u hu => LargePrimeGaps.discrepancy_constant_bound hu)
    (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I) hs
  have hpole : ‖(1 : ℂ) / ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    have hh := Complex.abs_im_le_norm ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1)
    have hn : 1 ≤ ‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1‖ :=
      htlo.trans (by simpa using hh)
    exact (div_le_one (lt_of_lt_of_le zero_lt_one hn)).mpr hn
  have hpower : 1 ≤ (2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) :=
    Real.one_le_rpow (by nlinarith [norm_nonneg (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)])
      (by positivity)
  have hzeta : ‖riemannZeta (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖ ≤
      (K+1)*(2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) := by
    have he := regularSeries_constant_eq hs1
    have htri := norm_add_le
      (LargePrimeGaps.regularSeries (LargePrimeGaps.positiveCoefficients (fun _ => 1)) 1
        (((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I))
      (1 / ((((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)-1))
    rw [he, sub_add_cancel] at htri
    norm_num only [one_add_one_eq_two] at hreg
    rw [he] at hreg
    nlinarith
  calc
    _ ≤ (K+1)*(2*(‖(((1+1/Real.log X:ℝ):ℂ)+(t:ℂ)*I)‖+2))^(2*ε) := hzeta
    _ ≤ (K+1)*((10:ℝ)*(Real.log X)^A)^(2*ε) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      linarith
    _ = ((K+1)*(10:ℝ)^(2*ε))*(Real.log X)^(A*(2*ε)) := by
      rw [Real.mul_rpow (by positivity) (by positivity),←Real.rpow_mul hlog.le]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hlog1 hAε) (by positivity)

end JointDickman

end OAI
