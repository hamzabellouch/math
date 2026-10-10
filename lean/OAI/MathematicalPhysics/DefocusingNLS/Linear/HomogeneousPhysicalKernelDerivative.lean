import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalFreeKernel
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFreeTestDerivative

namespace OAI

/-! # Differentiating the exact physical free kernel

The estimates are on the scalar kernel itself. They require only the second
Fourier moment, already proved for every vector in the manuscript's Y space.
-/

open Set
open scoped RealInnerProductSpace

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

noncomputable def homogeneousPhysicalFreeKernelDerivative (a b t : ℝ) (y ξ : E) : ℂ :=
  homogeneousPhysicalFreeKernel a b t y ξ *
    ((-(a : ℂ) + Complex.I * (b : ℂ)) +
      ((-Real.exp (-t) * ‖ξ‖ ^ 2 - Real.exp (-t / 2) / 2 * ⟪ξ, y⟫ : ℝ) : ℂ) * Complex.I)

private theorem physicalPhase_hasDerivAt (t : ℝ) (y ξ : E) :
    HasDerivAt (fun s : ℝ => -(1 - Real.exp (-s)) * ‖ξ‖ ^ 2 +
      Real.exp (-s / 2) * ⟪ξ, y⟫)
      (-Real.exp (-t) * ‖ξ‖ ^ 2 - Real.exp (-t / 2) / 2 * ⟪ξ, y⟫) t := by
  have he := ((hasDerivAt_id t).neg).exp
  have hr := (((hasDerivAt_id t).neg).div_const 2).exp
  have h := ((((hasDerivAt_const t (1 : ℝ)).sub he).neg).mul_const (‖ξ‖ ^ 2)).add
    (hr.mul_const ⟪ξ, y⟫)
  convert h using 1
  · rfl
  · simp only [Pi.neg_apply, id_eq]
    ring

@[simp] theorem homogeneousPhysicalFreeKernel_norm (a b t : ℝ) (y ξ : E) :
    ‖homogeneousPhysicalFreeKernel a b t y ξ‖ = Real.exp (-a * t) := by
  simp only [homogeneousPhysicalFreeKernel, norm_mul, homogeneousPhysicalAmplitude_norm,
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero, Real.exp_zero, mul_one]

theorem hasDerivAt_homogeneousPhysicalFreeKernel (a b t : ℝ) (y ξ : E) :
    HasDerivAt (fun s : ℝ => homogeneousPhysicalFreeKernel a b s y ξ)
      (homogeneousPhysicalFreeKernelDerivative a b t y ξ) t := by
  have hp := (((physicalPhase_hasDerivAt t y ξ).ofReal_comp).mul_const Complex.I).cexp
  have h := (hasDerivAt_homogeneousPhysicalAmplitude a b t).mul hp
  convert h using 1
  · rfl
  · unfold homogeneousPhysicalFreeKernelDerivative homogeneousPhysicalFreeKernel
    ring

theorem homogeneousPhysicalFreeKernelDerivative_norm_le (a b t : ℝ) (y ξ : E) :
    ‖homogeneousPhysicalFreeKernelDerivative a b t y ξ‖ ≤ Real.exp (-a * t) *
      (‖-(a : ℂ) + Complex.I * (b : ℂ)‖ +
        Real.exp (-t) * ‖ξ‖ ^ 2 + Real.exp (-t / 2) / 2 * ‖ξ‖ * ‖y‖) := by
  have hreal : |(-Real.exp (-t) * ‖ξ‖ ^ 2 - Real.exp (-t / 2) / 2 * ⟪ξ, y⟫ : ℝ)| ≤
      Real.exp (-t) * ‖ξ‖ ^ 2 + Real.exp (-t / 2) / 2 * ‖ξ‖ * ‖y‖ := by
    calc
      _ ≤ |-Real.exp (-t) * ‖ξ‖ ^ 2| + |Real.exp (-t / 2) / 2 * ⟪ξ, y⟫| := by
        simpa only [Real.norm_eq_abs] using
          norm_sub_le (-Real.exp (-t) * ‖ξ‖ ^ 2) (Real.exp (-t / 2) / 2 * ⟪ξ, y⟫)
      _ = Real.exp (-t) * ‖ξ‖ ^ 2 + Real.exp (-t / 2) / 2 * |⟪ξ, y⟫| := by
        rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _), abs_of_nonneg (sq_nonneg _),
          abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.exp (-t / 2) / 2)]
      _ ≤ _ := by
        simpa only [mul_assoc] using add_le_add (le_refl (Real.exp (-t) * ‖ξ‖ ^ 2))
          (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm ξ y)
            (show 0 ≤ Real.exp (-t / 2) / 2 by positivity))
  unfold homogeneousPhysicalFreeKernelDerivative
  rw [norm_mul, homogeneousPhysicalFreeKernel_norm]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
  apply (norm_add_le _ _).trans
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simpa only [add_assoc] using add_le_add (le_refl ‖-(a : ℂ) + Complex.I * (b : ℂ)‖) hreal

theorem homogeneousPhysicalFreeKernelDerivative_local_bound (a b t : ℝ) (ha : 0 < a)
    (ht : t ∈ Ioo (-1 : ℝ) 1) (y ξ : E) :
    ‖homogeneousPhysicalFreeKernelDerivative a b t y ξ‖ ≤
      (Real.exp a * (‖-(a : ℂ) + Complex.I * (b : ℂ)‖ +
        Real.exp 1 * (1 + ‖y‖))) * (1 + ‖ξ‖ ^ 2) := by
  have hA : Real.exp (-a * t) ≤ Real.exp a := Real.exp_le_exp.mpr (by nlinarith [ht.1])
  have hE : Real.exp (-t) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith [ht.1])
  have hR : Real.exp (-t / 2) / 2 ≤ Real.exp 1 := by
    have h := Real.exp_le_exp.mpr (show -t / 2 ≤ (1 : ℝ) by linarith [ht.1])
    linarith [Real.exp_pos (-t / 2)]
  have hξ : ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg (‖ξ‖ - 1), norm_nonneg ξ]
  have h₁ : ‖-(a : ℂ) + Complex.I * (b : ℂ)‖ + Real.exp (-t) * ‖ξ‖ ^ 2 +
      Real.exp (-t / 2) / 2 * ‖ξ‖ * ‖y‖ ≤
      (‖-(a : ℂ) + Complex.I * (b : ℂ)‖ + Real.exp 1 * (1 + ‖y‖)) *
        (1 + ‖ξ‖ ^ 2) := by
    calc
      _ ≤ ‖-(a : ℂ) + Complex.I * (b : ℂ)‖ + Real.exp 1 * ‖ξ‖ ^ 2 +
          Real.exp 1 * (1 + ‖ξ‖ ^ 2) * ‖y‖ := by gcongr
      _ ≤ _ := by
        nlinarith [mul_nonneg (norm_nonneg (-(a : ℂ) + Complex.I * (b : ℂ)))
          (sq_nonneg ‖ξ‖), Real.exp_pos (1 : ℝ)]
  exact (homogeneousPhysicalFreeKernelDerivative_norm_le a b t y ξ).trans
    ((mul_le_mul hA h₁ (by positivity) (Real.exp_nonneg _)).trans_eq (by ring))

end DefocusingNLS

end OAI
