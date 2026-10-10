import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingDuhamelRestart
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Fourier-mode variation of constants on the moving torus

The normalized Hilbert-space Duhamel construction has the exact physical
Fourier integrating factor.  The Fourier modes refer to fixed `y/L_s`, as
in the manuscript's interpretation of the expanding-torus equation.
-/

open Set MeasureTheory

namespace DefocusingNLS

noncomputable def expandingFreeMode (a b L s : ℝ) (n : frequencyLattice) : ℂ :=
  expandingFreeAmplitude a b s * schrodingerMultiplier (expandingFreeTime L s) n

theorem expandingFreeMode_ne_zero (a b L s : ℝ) (n : frequencyLattice) :
    expandingFreeMode a b L s n ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _)
    (Complex.exp_ne_zero _)

theorem expandingFreeMode_add (a b L s t : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingFreeMode a b L (s + t) n =
      expandingFreeMode a b L s n * expandingFreeMode a b (expandingRadius L s) t n := by
  unfold expandingFreeMode
  rw [expandingFreeAmplitude_add, expandingFreeTime_add L s t hL, schrodingerMultiplier_add]
  ring

theorem expandingFreeMode_kernel (a b L s τ : ℝ) (hL : 1 ≤ L) (n : frequencyLattice) :
    expandingFreeMode a b (expandingRadius L τ) (s - τ) n =
      expandingFreeMode a b L s n * (expandingFreeMode a b L τ n)⁻¹ := by
  have h := expandingFreeMode_add a b L τ (s - τ) hL n
  rw [add_sub_cancel] at h
  apply (eq_mul_inv_iff_mul_eq₀ (expandingFreeMode_ne_zero a b L τ n)).2
  rw [mul_comm, ← h]

/-- Physical coefficient evaluation at a fixed radius is continuous linear. -/
noncomputable def expandingCoefficientCLM (a k L : ℝ) (n : frequencyLattice) :
    FourierL2 →L[ℂ] ℂ :=
  (((expandingSobolevWeight a k L n)⁻¹ : ℝ) : ℂ) •
    lp.evalCLM ℂ (fun _ : frequencyLattice => ℂ) 2 n

@[simp] theorem expandingCoefficientCLM_apply (a k L : ℝ)
    (n : frequencyLattice) (f : FourierL2) :
    expandingCoefficientCLM a k L n f = expandingFourierCoefficient a k L f n := rfl

/-- The physical Fourier coefficient of Duhamel is its scalar variation of constants. -/
theorem expandingDuhamel_coefficient (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (r : ℝ → FourierL2)
    (hr : ContinuousOn r (Icc 0 t)) (n : frequencyLattice) :
    expandingFourierCoefficient a k (expandingRadius L t)
        (expandingDuhamel a b k L ha hk hL t r) n =
      expandingFreeMode a b L t n * ∫ τ in Icc 0 t,
        (expandingFreeMode a b L τ n)⁻¹ *
          expandingFourierCoefficient a k (expandingRadius L τ) (r τ) n := by
  let E := expandingCoefficientCLM a k (expandingRadius L t) n
  have hI := integrableOn_expandingDuhamelIntegrand a b k L ha hk hL t r hr
  calc
    _ = ∫ τ in Icc 0 t, E (expandingDuhamelIntegrand a b k L ha hk hL t r τ) :=
      (E.integral_comp_comm hI).symm
    _ = ∫ τ in Icc 0 t, expandingFreeMode a b L t n *
        ((expandingFreeMode a b L τ n)⁻¹ *
          expandingFourierCoefficient a k (expandingRadius L τ) (r τ) n) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      change expandingFourierCoefficient a k (expandingRadius L t)
        (expandingDuhamelIntegrand a b k L ha hk hL t r τ) n = _
      rw [expandingDuhamelIntegrand_of_mem _ _ _ _ _ _ _ _ _ _ hτ]
      have h := expandingFreeStep_coefficient a b k (expandingRadius L τ) (t - τ)
        ha hk (hL.trans (expandingRadius_ge L τ hL hτ.1)) (sub_nonneg.mpr hτ.2) (r τ) n
      rw [expandingDuhamel_destination] at h
      rw [h]
      change expandingFreeMode a b (expandingRadius L τ) (t - τ) n * _ = _
      rw [expandingFreeMode_kernel a b L t τ hL n, mul_assoc]
    _ = _ := integral_const_mul _ _

/-- Every continuous mild trajectory satisfies the exact modewise integral equation. -/
theorem expandingMild_coefficient (a b k L t : ℝ)
    (ha : 0 < a) (hk : 8 < k) (hL : 1 ≤ L) (ht : 0 ≤ t)
    (r : ℝ → FourierL2) (hr : ContinuousOn r (Icc 0 t))
    (u₀ : FourierL2) (n : frequencyLattice) :
    expandingFourierCoefficient a k (expandingRadius L t)
      (expandingFreeStep a b k L t ha hk hL ht u₀ +
        expandingDuhamel a b k L ha hk hL t r) n =
      expandingFreeMode a b L t n *
        (expandingFourierCoefficient a k L u₀ n + ∫ τ in Icc 0 t,
          (expandingFreeMode a b L τ n)⁻¹ *
            expandingFourierCoefficient a k (expandingRadius L τ) (r τ) n) := by
  rw [← expandingCoefficientCLM_apply, map_add, expandingCoefficientCLM_apply,
    expandingCoefficientCLM_apply, expandingDuhamel_coefficient a b k L t ha hk hL r hr n,
    expandingFreeStep_coefficient a b k L t ha hk hL ht u₀ n]
  change expandingFreeMode a b L t n * _ + expandingFreeMode a b L t n * _ = _
  exact (mul_add _ _ _).symm

end DefocusingNLS

end OAI
