import Mathlib

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory

namespace OrdinaryCorrelations.SourcePrimeReciprocal

def kernel (x : ℝ) : ℝ := (Real.log x + 1) / (x * Real.log x)^2

def primitive (x : ℝ) : ℝ := Real.log (Real.log x) - (Real.log x)⁻¹

lemma reciprocal_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t : ℝ => (t * Real.log t)⁻¹) (-kernel x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)).inv (mul_ne_zero hx0 hl)
  convert h using 1 <;> (first | rfl | (simp only [kernel,Pi.mul_apply,id_eq,one_mul,mul_inv_cancel₀ hx0]; ring))

lemma primitive_deriv {x : ℝ} (hx : 1 < x) :
    HasDerivAt primitive (x * kernel x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have h := ((Real.hasDerivAt_log hl).comp x (Real.hasDerivAt_log hx0)).sub
    ((Real.hasDerivAt_log hx0).inv hl)
  convert h using 1 <;> (first | rfl | (simp only [kernel]; field_simp; ring))

lemma kernel_continuousOn {b : ℝ} : ContinuousOn kernel (Set.Icc 2 b) := by
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hx.1]
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith [hx.1]))
  have hden : (x * Real.log x)^2 ≠ 0 := pow_ne_zero 2 (mul_ne_zero hx0 hl)
  have : ContinuousAt kernel x := by unfold kernel; fun_prop
  exact this.continuousWithinAt

lemma theta_kernel_integrable (b : ℝ) :
    IntegrableOn (fun t => Chebyshev.theta t * kernel t) (Set.Icc 2 b) := by
  have h := integrableOn_mul_sum_Icc
    (fun n : ℕ => if n.Prime then Real.log n else 0) (m := 0) (by norm_num : (0:ℝ) ≤ 2)
    (kernel_continuousOn.integrableOn_Icc (b := b))
  simpa only [Chebyshev.theta_eq_sum_Icc,Finset.sum_filter,mul_comm] using h

lemma reciprocal_abel {b : ℝ} (hb : 2 ≤ b) :
    (∑ n ∈ (Finset.Icc 0 ⌊b⌋₊).filter Nat.Prime, (n:ℝ)⁻¹) =
      Chebyshev.theta b / (b * Real.log b) +
        ∫ t in 2..b, Chebyshev.theta t * kernel t := by
  let a : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hf : ∀ t ∈ Set.Icc 2 b, DifferentiableAt ℝ (fun t : ℝ => (t*Real.log t)⁻¹) t := by
    intro t ht
    exact (reciprocal_deriv (by linarith [ht.1])).differentiableAt
  have hd : ∀ t ∈ Set.Icc 2 b, deriv (fun t : ℝ => (t*Real.log t)⁻¹) t = -kernel t := by
    intro t ht
    exact (reciprocal_deriv (by linarith [ht.1])).deriv
  have hi : IntegrableOn (deriv (fun t : ℝ => (t*Real.log t)⁻¹)) (Set.Icc 2 b) := by
    exact (kernel_continuousOn.neg.integrableOn_Icc).congr_fun (fun t ht => (hd t ht).symm) measurableSet_Icc
  have h := sum_mul_eq_sub_integral_mul₁ a (f := fun t : ℝ => (t*Real.log t)⁻¹)
    (by simp [a]) (by simp [a]) b hf hi
  rw [← intervalIntegral.integral_of_le hb] at h
  have he : (∑ k ∈ Icc 0 ⌊b⌋₊, (↑k*Real.log k)⁻¹ * a k) =
       ∑ n ∈ (Finset.Icc 0 ⌊b⌋₊).filter Nat.Prime, (n:ℝ)⁻¹ := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn : n.Prime
    · have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
      have hl : Real.log (n:ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by exact_mod_cast hn.pos) (by exact_mod_cast hn.ne_one)
      simp only [a,ite_eq_left hn]
      field_simp
    · simp [a,hn]
  rw [he] at h
  have ht (t : ℝ) : (∑ k ∈ Icc 0 ⌊t⌋₊, a k) = Chebyshev.theta t := by
    simp only [a,Chebyshev.theta_eq_sum_Icc,Finset.sum_filter]
  simp only [ht] at h
  have hei : (∫ t in 2..b, deriv (fun t : ℝ => (t*Real.log t)⁻¹) t * Chebyshev.theta t) =
      -(∫ t in 2..b, Chebyshev.theta t * kernel t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hb] at ht
    dsimp only
    rw [hd t ht]
    ring
  rw [hei] at h
  simpa [div_eq_mul_inv,mul_comm] using h

theorem reciprocal_bound {b : ℝ} (hb : 2 ≤ b) :
    (∑ n ∈ (Finset.Icc 0 ⌊b⌋₊).filter Nat.Prime, (n:ℝ)⁻¹) ≤
      Real.log 4 * (Real.log (Real.log b) - primitive 2) := by
  have hi : IntervalIntegrable (fun t => Chebyshev.theta t * kernel t) volume 2 b := by
    rw [intervalIntegrable_iff,Set.uIoc_of_le hb,← integrableOn_Icc_iff_integrableOn_Ioc]
    exact theta_kernel_integrable b
  have hk : IntervalIntegrable (fun t => t * kernel t) volume 2 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb]
    exact continuousOn_id.mul kernel_continuousOn
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => primitive_deriv (by rw [Set.uIcc_of_le hb] at ht; linarith [ht.1])) hk
  have hm : (∫ t in 2..b, Chebyshev.theta t * kernel t) ≤
      Real.log 4 * (primitive b - primitive 2) := by
    calc
      _ ≤ ∫ t in 2..b, Real.log 4 * (t * kernel t) := by
        apply intervalIntegral.integral_mono_on hb hi (hk.const_mul _)
        intro t ht
        have hkp : 0 ≤ kernel t := by
          unfold kernel
          have := (Real.log_pos (show 1<t by linarith [ht.1])).le
          positivity
        calc
          _ ≤ (Real.log 4 * t) * kernel t :=
            mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (by linarith [ht.1])) hkp
          _ = _ := mul_assoc _ _ _
      _ = _ := by rw [intervalIntegral.integral_const_mul,he]
  have hlog : 0 < Real.log b := Real.log_pos (by linarith)
  have hb0 : 0 < b := by linarith
  rw [reciprocal_abel hb]
  calc
    _ ≤ (Real.log 4*b)/(b*Real.log b) + Real.log 4*(primitive b-primitive 2) :=
      _root_.add_le_add (div_le_div_of_nonneg_right (Chebyshev.theta_le_log4_mul_x hb0.le) (by positivity)) hm
    _ = _ := by
      unfold primitive
      field_simp
      ring

end OrdinaryCorrelations.SourcePrimeReciprocal

end

end OAI
