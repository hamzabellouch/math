import Mathlib
import OAI.Geometry.PrescribedPotential.GlobalSobolev

namespace OAI

/-! Parameter Resolvent. -/

section

 

noncomputable section
open MeasureTheory FourierTransform TemperedDistribution LineDeriv
open scoped SchwartzMap BoundedContinuousFunction ComplexOrder MatrixOrder Real

namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ}

 
def parameterSymbol (H : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) (ξ : EC n) : ℂ :=
  ((m^2 + symbol H ξ)⁻¹ : ℝ)

lemma parameterSymbol_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) : (parameterSymbol H m).HasTemperateGrowth := by
  obtain ⟨B, _, hB⟩ := posDef_factor H⁻¹ hH.inv
  have he : parameterSymbol H m = fun ξ =>
      (m^2 : ℂ)⁻¹ * (Complex.ofReal ∘
        ((fun y : EC n => (1 + ‖y‖^2)^(-1 : ℝ)) ∘
          ((m⁻¹ : ℝ) • factorMap B))) ξ := by
    funext ξ
    simp only [parameterSymbol, Function.comp_apply, Real.rpow_neg_one,
      _root_.smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hm), mul_pow, symbol_eq_factorMap H B hB,
      ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
    congr 1
    field_simp
  rw [he]
  have hg := (Function.hasTemperateGrowth_one_add_norm_sq_rpow (EC n) (-1)).comp
    ((m⁻¹ : ℝ) • factorMap B).hasTemperateGrowth
  exact (Function.HasTemperateGrowth.const _).mul
    (Complex.hasTemperateGrowth_ofReal.comp hg)

lemma elliptic_symbol_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (ξ : EC n) :
    1 + ‖ξ‖^2 ≤ ellipticBound H hH * (1 + symbol H ξ) := by
  have hp := symbol_nonneg H hH ξ
  have h := gainSymbol_bound H hH ξ
  simp only [gainSymbol, inverseSymbol, ← Complex.ofReal_mul,
    Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by linarith [symbol_nonneg H hH ξ])] at h
  exact h

lemma parameter_gain_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 1 ≤ m) (ξ : EC n) :
    ‖(1 + ‖ξ‖^2 : ℝ) * parameterSymbol H m ξ‖ ≤ ellipticBound H hH := by
  have hm2 : 1 ≤ m^2 := by nlinarith
  have hp := symbol_nonneg H hH ξ
  simp only [parameterSymbol, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity), mul_inv_le_iff₀ (by positivity)]
  exact (elliptic_symbol_bound H hH ξ).trans
    (mul_le_mul_of_nonneg_left (by linarith) (ellipticBound_pos H hH).le)

lemma parameter_zero_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) (ξ : EC n) :
    ‖parameterSymbol H m ξ‖ ≤ (m^2)⁻¹ := by
  have hp := symbol_nonneg H hH ξ
  simp only [parameterSymbol, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (show 0 < m^2 + symbol H ξ by positivity))]
  exact inv_anti₀ (by positivity) (by linarith)

lemma parameter_first_weight (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 1 ≤ m) (ξ : EC n) :
    ‖ξ‖ * (m^2 + symbol H ξ)⁻¹ ≤ ellipticBound H hH / m := by
  let C := ellipticBound H hH
  let D := m^2 + symbol H ξ
  have hC : 1 ≤ C := le_max_left _ _
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hm2 : 1 ≤ m^2 := by nlinarith
  have hp := symbol_nonneg H hH ξ
  have hD : 0 < D := by dsimp [D]; positivity
  have hDm : m^2 ≤ D := by dsimp [D]; linarith
  have hξ : ‖ξ‖^2 ≤ C * D := by
    have hb := elliptic_symbol_bound H hH ξ
    dsimp [D, C]
    nlinarith [mul_nonneg (ellipticBound_pos H hH).le (sub_nonneg.mpr hm2)]
  have hsq : (‖ξ‖ * m)^2 ≤ (C * D)^2 := by
    calc
      _ = ‖ξ‖^2 * m^2 := mul_pow _ _ _
      _ ≤ (C * D) * m^2 := mul_le_mul_of_nonneg_right hξ (sq_nonneg _)
      _ ≤ (C * D) * D := mul_le_mul_of_nonneg_left hDm (by positivity)
      _ ≤ (C * D)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hC) (show 0 ≤ C * D^2 by positivity)]
  have hlin : ‖ξ‖ * m ≤ C * D := (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  change ‖ξ‖ * D⁻¹ ≤ C / m
  rw [le_div_iff₀ hm0]
  rw [mul_right_comm, mul_inv_le_iff₀ hD]
  exact hlin

 
def parameterResolvent (H : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) := fourierMultiplierCLM ℂ (parameterSymbol H m)

def parameterForward (H : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) :
    𝓢'(EC n, ℂ) →L[ℂ] 𝓢'(EC n, ℂ) :=
  fourierMultiplierCLM ℂ (fun ξ => ((m^2 + symbol H ξ : ℝ) : ℂ))

lemma parameterForward_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) (m : ℝ) :
    (fun ξ => ((m^2 + symbol H ξ : ℝ) : ℂ)).HasTemperateGrowth :=
  Complex.hasTemperateGrowth_ofReal.comp
    ((Function.HasTemperateGrowth.const _).add (symbol_temperate H hH))

lemma parameterForward_eq (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (u : 𝓢'(EC n, ℂ)) :
    parameterForward H m u = (m^2 : ℂ) • u - frozenDifferential H u := by
  rw [frozenDifferential_fourier]
  have hn : (fun ξ => ((-symbol H ξ : ℝ) : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (symbol_temperate H hH).neg
  have he := multiplier_sub (Function.HasTemperateGrowth.const (m^2 : ℂ)) hn u
  simpa only [Pi.sub_def, Complex.ofReal_neg, sub_neg_eq_add, parameterForward,
    Complex.ofReal_add, Complex.ofReal_pow, fourierMultiplierCLM_const,
    _root_.smul_apply, ContinuousLinearMap.id_apply] using he

lemma parameterForward_resolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) (u : 𝓢'(EC n, ℂ)) :
    parameterForward H m (parameterResolvent H m u) = u := by
  rw [parameterForward, parameterResolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (parameterSymbol_temperate H hH hm)
      (parameterForward_temperate H hH m)]
  have he : parameterSymbol H m * (fun ξ => ((m^2 + symbol H ξ : ℝ) : ℂ)) =
      fun _ => (1 : ℂ) := by
    funext ξ
    simp only [Pi.mul_apply, parameterSymbol, ← Complex.ofReal_mul]
    have hp := symbol_nonneg H hH ξ
    rw [inv_mul_cancel₀ (by positivity : m^2 + symbol H ξ ≠ 0), Complex.ofReal_one]
  rw [he, fourierMultiplierCLM_const]
  simp

end FrozenPoisson

namespace FrozenPoisson
open EllipticKernel SobolevChart
variable {n : ℕ}

def parameterGain (H : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) (ξ : EC n) : ℂ :=
  (1 + ‖ξ‖^2 : ℝ) * parameterSymbol H m ξ

lemma parameterGain_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) : (parameterGain H m).HasTemperateGrowth := by
  have hi := parameterSymbol_temperate H hH hm
  unfold parameterGain
  fun_prop

def parameterGainBCF (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) : EC n →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (parameterGain H m)
    (parameterGain_temperate H hH (lt_of_lt_of_le zero_lt_one hm)).1.continuous
    (ellipticBound H hH) (parameter_gain_bound H hH hm)

lemma parameterGainBCF_norm (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) : ‖parameterGainBCF H hH m hm‖ ≤ ellipticBound H hH :=
  (BoundedContinuousFunction.norm_le (ellipticBound_pos H hH).le).mpr
    (parameter_gain_bound H hH hm)

def parameterHilbert (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) : L2 (EC n) →L[ℂ] L2 (EC n) :=
  multiplier (parameterGainBCF H hH m hm)

lemma parameterHilbert_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (u : L2 (EC n)) :
    ‖parameterHilbert H hH m hm u‖ ≤ ellipticBound H hH * ‖u‖ :=
  (multiplier_norm_le (parameterGainBCF H hH m hm) u).trans
    (mul_le_mul_of_nonneg_right (parameterGainBCF_norm H hH m hm) (norm_nonneg u))

lemma bessel_two_parameterResolvent (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) (u : 𝓢'(EC n, ℂ)) :
    besselPotential (EC n) ℂ 2 (parameterResolvent H m u) =
      fourierMultiplierCLM ℂ (parameterGain H m) u := by
  rw [besselPotential, parameterResolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (parameterSymbol_temperate H hH hm)
      (by fun_prop)]
  congr 2
  ext ξ
  simp [parameterGain, mul_comm]

lemma parameterHilbert_realize (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (s : ℝ) (u : L2 (EC n)) :
    realize (s + 2) (parameterHilbert H hH m hm u) =
      parameterResolvent H m (realize s u) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  change besselPotential (EC n) ℂ (-(s + 2))
    (Lp.toTemperedDistributionCLM ℂ MeasureTheory.volume 2 (parameterHilbert H hH m hm u)) = _
  rw [besselPotential_neg_apply_eq_iff]
  have hc : parameterResolvent H m (realize s u) = besselPotential (EC n) ℂ (-s)
      (parameterResolvent H m (Lp.toTemperedDistributionCLM ℂ MeasureTheory.volume 2 u)) :=
    (bessel_multiplier_comm (parameterSymbol_temperate H hH hm0) (-s) _).symm
  rw [hc, besselPotential_besselPotential_apply]
  have hs : -s + (s + 2) = 2 := by ring
  rw [hs, bessel_two_parameterResolvent H hH hm0]
  exact (multiplier_distribution (parameterGainBCF H hH m hm)
    (parameterGain_temperate H hH hm0) u).symm

lemma parameterHilbert_equation (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (f : L2 (EC n)) :
    (m^2 : ℂ) • realize 2 (parameterHilbert H hH m hm f) -
      frozenDifferential H (realize 2 (parameterHilbert H hH m hm f)) =
        (f : 𝓢'(EC n, ℂ)) := by
  rw [← parameterForward_eq H hH]
  have hr := parameterHilbert_realize H hH m hm 0 f
  simp only [zero_add] at hr
  rw [hr, parameterForward_resolvent H hH (lt_of_lt_of_le zero_lt_one hm)]
  simp [realize]

def parameterZeroBCF (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 0 < m) : EC n →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (parameterSymbol H m)
    (parameterSymbol_temperate H hH hm).1.continuous (m^2)⁻¹ (parameter_zero_bound H hH hm)

def parameterZero (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 0 < m) : L2 (EC n) →L[ℂ] L2 (EC n) :=
  multiplier (parameterZeroBCF H hH m hm)

lemma parameterZero_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 0 < m) (f : L2 (EC n)) :
    ‖parameterZero H hH m hm f‖ ≤ (m^2)⁻¹ * ‖f‖ := by
  apply (multiplier_norm_le _ f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (BoundedContinuousFunction.norm_le (by positivity)).mpr (parameter_zero_bound H hH hm)

lemma parameterZero_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 0 < m) (f : L2 (EC n)) :
    (parameterZero H hH m hm f : 𝓢'(EC n, ℂ)) = parameterResolvent H m (f : 𝓢'(EC n, ℂ)) :=
  multiplier_distribution _ (parameterSymbol_temperate H hH hm) f

def parameterFirstSymbol (H : Matrix (Fin n) (Fin n) ℂ) (m : ℝ) (v ξ : EC n) : ℂ :=
  (2 * Real.pi * Complex.I) * (inner ℝ ξ v : ℂ) * parameterSymbol H m ξ

lemma parameterFirstSymbol_temperate (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 0 < m) (v : EC n) : (parameterFirstSymbol H m v).HasTemperateGrowth := by
  have hi := parameterSymbol_temperate H hH hm
  unfold parameterFirstSymbol
  fun_prop

lemma parameterFirstSymbol_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    {m : ℝ} (hm : 1 ≤ m) (v ξ : EC n) :
    ‖parameterFirstSymbol H m v ξ‖ ≤ (2 * Real.pi * ‖v‖ * ellipticBound H hH) / m := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hp := symbol_nonneg H hH ξ
  have hi := abs_real_inner_le_norm ξ v
  have hw := parameter_first_weight H hH hm ξ
  simp only [parameterFirstSymbol, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    parameterSymbol, abs_of_pos (inv_pos.mpr (show 0 < m^2 + symbol H ξ by positivity))]
  calc
    _ ≤ (2 * Real.pi) * (‖ξ‖ * ‖v‖) * (m^2 + symbol H ξ)⁻¹ := by gcongr
    _ = (2 * Real.pi * ‖v‖) * (‖ξ‖ * (m^2 + symbol H ξ)⁻¹) := by ring
    _ ≤ (2 * Real.pi * ‖v‖) * (ellipticBound H hH / m) := by gcongr
    _ = _ := by ring

def parameterFirstBCF (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : EC n) : EC n →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (parameterFirstSymbol H m v)
    (parameterFirstSymbol_temperate H hH (lt_of_lt_of_le zero_lt_one hm) v).1.continuous
    ((2 * Real.pi * ‖v‖ * ellipticBound H hH) / m) (parameterFirstSymbol_bound H hH hm v)

def parameterFirst (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : EC n) : L2 (EC n) →L[ℂ] L2 (EC n) :=
  multiplier (parameterFirstBCF H hH m hm v)

lemma parameterFirst_bound (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : EC n) (f : L2 (EC n)) :
    ‖parameterFirst H hH m hm v f‖ ≤ ((2 * Real.pi * ‖v‖ * ellipticBound H hH) / m) * ‖f‖ := by
  apply (multiplier_norm_le _ f).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (BoundedContinuousFunction.norm_le (by positivity [ellipticBound_pos H hH])).mpr
    (parameterFirstSymbol_bound H hH hm v)

lemma parameterFirst_distribution (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef)
    (m : ℝ) (hm : 1 ≤ m) (v : EC n) (f : L2 (EC n)) :
    (parameterFirst H hH m hm v f : 𝓢'(EC n, ℂ)) =
      ∂_{v} (parameterResolvent H m (f : 𝓢'(EC n, ℂ))) := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  rw [lineDeriv_eq_fourierMultiplierCLM, parameterResolvent,
    fourierMultiplierCLM_fourierMultiplierCLM_apply (parameterSymbol_temperate H hH hm0)
      (by fun_prop)]
  have ht : (parameterSymbol H m * (fun ξ => (inner ℝ ξ v : ℂ))).HasTemperateGrowth := by
    apply (parameterSymbol_temperate H hH hm0).mul
    fun_prop
  rw [← _root_.smul_apply, ← fourierMultiplierCLM_smul ht, parameterFirst,
    multiplier_distribution _ (parameterFirstSymbol_temperate H hH hm0 v)]
  congr 2
  ext ξ
  change parameterFirstSymbol H m v ξ =
    (2 * Real.pi * Complex.I) * (parameterSymbol H m ξ * (inner ℝ ξ v : ℂ))
  unfold parameterFirstSymbol
  ring

end FrozenPoisson

end
end

end OAI
