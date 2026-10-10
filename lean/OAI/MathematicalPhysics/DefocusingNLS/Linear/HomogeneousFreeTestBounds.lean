import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeTestDerivative

namespace OAI

/-! # A uniform integrable bound for the differentiated Fourier tests -/

open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousFreeDualDerivative (a b t : ℝ)
    (φ : 𝓢(E, ℂ)) (ξ : E) : ℂ :=
  let y := Real.exp (-t / 2) • ξ
  homogeneousPhysicalAmplitude a b t * homogeneousSchrodingerPhase (1 - Real.exp (-t)) ξ *
    (((-(a : ℂ) + Complex.I * (b : ℂ)) - Complex.I * (‖y‖ ^ 2 : ℝ)) * φ y -
      (1 / 2 : ℝ) • fderiv ℝ φ y y)

theorem hasDerivAt_homogeneousFreeDualTest (a b t : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    HasDerivAt (fun s : ℝ => homogeneousFreeDualTest a b s φ ξ)
      (homogeneousFreeDualDerivative a b t φ ξ) t := by
  let R := Real.exp (-t / 2)
  let y := R • ξ
  have hR : HasDerivAt (fun s : ℝ => Real.exp (-s / 2)) (-(R / 2)) t := by
    convert (Real.hasDerivAt_exp (-t / 2)).comp t
      (((hasDerivAt_id t).neg).div_const 2) using 1
    · rfl
    · dsimp only [R]
      ring
  have hdir : (-(R / 2)) • ξ = (-(1 / 2 : ℝ)) • y := by
    simp only [y, smul_smul]
    congr 1
    ring
  have hφ : HasDerivAt (fun s : ℝ => φ (Real.exp (-s / 2) • ξ))
      (-(1 / 2 : ℝ) • fderiv ℝ φ y y) t := by
    have h := (φ.hasFDerivAt y).comp_hasDerivAt t (hR.smul_const ξ)
    simpa only [Function.comp_def, hdir, map_smul] using h
  have hy : Real.exp (-t) * ‖ξ‖ ^ 2 = ‖y‖ ^ 2 := by
    simp only [y, R, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
    rw [← Real.exp_nat_mul]
    congr 1
    congr 1
    ring
  have hreal : HasDerivAt (fun s : ℝ => -(1 - Real.exp (-s)) * ‖ξ‖ ^ 2)
      (-‖y‖ ^ 2) t := by
    have h := (((hasDerivAt_const t (1 : ℝ)).sub
      ((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg)).neg).mul_const (‖ξ‖ ^ 2)
    convert h using 1
    · rfl
    · rw [← hy]
      ring
  have hp : HasDerivAt
      (fun s : ℝ => homogeneousSchrodingerPhase (1 - Real.exp (-s)) ξ)
      (homogeneousSchrodingerPhase (1 - Real.exp (-t)) ξ *
        (-((‖y‖ ^ 2 : ℝ) : ℂ) * Complex.I)) t := by
    simpa only [homogeneousSchrodingerPhase, Complex.ofReal_neg] using
      (hreal.ofReal_comp.mul_const Complex.I).cexp
  have h := ((hasDerivAt_homogeneousPhysicalAmplitude a b t).mul hp).mul hφ
  convert h using 1
  · funext s
    exact homogeneousFreeDualTest_apply a b s φ ξ
  · dsimp only [homogeneousFreeDualDerivative, y, R, Pi.mul_apply]
    simp only [Complex.real_smul, Complex.ofReal_neg]
    ring

noncomputable def homogeneousFreeTestBound (a b : ℝ) (φ : 𝓢(E, ℂ)) : ℝ :=
  ‖-(a : ℂ) + Complex.I * (b : ℂ)‖ * SchwartzMap.seminorm ℂ 0 0 φ +
    SchwartzMap.seminorm ℂ 2 0 φ + (1 / 2 : ℝ) * SchwartzMap.seminorm ℂ 1 1 φ

theorem homogeneousFreeTestBound_nonneg (a b : ℝ) (φ : 𝓢(E, ℂ)) :
    0 ≤ homogeneousFreeTestBound a b φ := by
  unfold homogeneousFreeTestBound
  positivity

theorem homogeneousFreeDualDerivative_norm_le (a b t : ℝ) (φ : 𝓢(E, ℂ)) (ξ : E) :
    ‖homogeneousFreeDualDerivative a b t φ ξ‖ ≤
      Real.exp (-a * t) * homogeneousFreeTestBound a b φ := by
  let y := Real.exp (-t / 2) • ξ
  have hgrad : ‖fderiv ℝ φ y y‖ ≤ SchwartzMap.seminorm ℂ 1 1 φ := by
    apply (ContinuousLinearMap.le_opNorm _ _).trans
    have h := φ.le_seminorm ℂ 1 1 y
    simpa only [pow_one, norm_iteratedFDeriv_one, mul_comm] using h
  have hnorm : ‖((-(a : ℂ) + Complex.I * (b : ℂ)) - Complex.I * (‖y‖ ^ 2 : ℝ)) * φ y -
      (1 / 2 : ℝ) • fderiv ℝ φ y y‖ ≤ homogeneousFreeTestBound a b φ := by
    calc
      _ ≤ ‖(-(a : ℂ) + Complex.I * (b : ℂ)) * φ y‖ +
          ‖(Complex.I * (‖y‖ ^ 2 : ℝ)) * φ y‖ +
          ‖(1 / 2 : ℝ) • fderiv ℝ φ y y‖ := by
        rw [sub_mul]
        exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ homogeneousFreeTestBound a b φ := by
        simp only [norm_mul, Complex.norm_I, one_mul, norm_smul, Real.norm_eq_abs,
          Complex.norm_real, abs_of_nonneg (sq_nonneg ‖y‖),
          show |(1 / 2 : ℝ)| = 1 / 2 by norm_num]
        unfold homogeneousFreeTestBound
        exact add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (φ.norm_le_seminorm ℂ y) (norm_nonneg _))
          (φ.norm_pow_mul_le_seminorm ℂ 2 y))
          (mul_le_mul_of_nonneg_left hgrad (by positivity))
  dsimp only [homogeneousFreeDualDerivative]
  rw [norm_mul, norm_mul, homogeneousPhysicalAmplitude_norm,
    homogeneousSchrodingerPhase_norm, mul_one]
  exact mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _)

theorem continuous_homogeneousFreeDualDerivative (a b t : ℝ) (φ : 𝓢(E, ℂ)) :
    Continuous (homogeneousFreeDualDerivative a b t φ) := by
  have hd : Continuous (fun y : E => fderiv ℝ φ y) :=
    (SchwartzMap.fderivCLM ℂ E ℂ φ).continuous
  have hgrad : Continuous (fun y : E => fderiv ℝ φ y y) :=
    Continuous.clm_apply (𝕜 := ℝ) hd continuous_id
  have hy : Continuous (fun ξ : E => Real.exp (-t / 2) • ξ) :=
    continuous_const_smul _
  have hn : Continuous (fun ξ : E => ((‖Real.exp (-t / 2) • ξ‖ ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hy.norm.pow 2)
  have hc : Continuous (fun ξ : E => (-(a : ℂ) + Complex.I * (b : ℂ)) -
      Complex.I * ((‖Real.exp (-t / 2) • ξ‖ ^ 2 : ℝ) : ℂ)) :=
    continuous_const.sub (hn.const_mul Complex.I)
  have hb : Continuous (fun ξ : E =>
      (((-(a : ℂ) + Complex.I * (b : ℂ)) -
        Complex.I * ((‖Real.exp (-t / 2) • ξ‖ ^ 2 : ℝ) : ℂ)) *
        φ (Real.exp (-t / 2) • ξ) -
        (1 / 2 : ℝ) • fderiv ℝ φ (Real.exp (-t / 2) • ξ) (Real.exp (-t / 2) • ξ))) :=
    (hc.mul (φ.continuous.comp hy)).sub ((hgrad.comp hy).const_smul (1 / 2 : ℝ))
  exact (continuous_const.mul (homogeneousSchrodingerPhase_continuous _)).mul hb

end DefocusingNLS

end OAI
