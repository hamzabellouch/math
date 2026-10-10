import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import PrimeNumberTheoremAnd.Erdos970.Consequences
import OAI.NumberTheory.Jacobsthal.Primes.HighPrimeRemoval

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace ErdosPrimeInputs.PrimeCountingPrimitive

open _root_.Set _root_.Filter _root_.MeasureTheory _root_.Asymptotics
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory _root_.Erdos970.Asymptotics
open scoped Topology
open PrimeErrorDecay StrongChebyshev

noncomputable def scale (c x : ℝ) : ℝ := x * decay c x / Real.log x
noncomputable def kernel (c x : ℝ) : ℝ := decay c x / Real.log x ^ 2
noncomputable def slope (c x : ℝ) : ℝ := decay c x / Real.log x *
  (1 - 1 / Real.log x - c / (2 * Real.sqrt (Real.log x)))

lemma scale_nonneg {c x : ℝ} (hx : 1 ≤ x) : 0 ≤ scale c x :=
  div_nonneg (mul_nonneg (by linarith) (decay_pos c x).le) (Real.log_nonneg hx)

lemma hasDerivAt_scale {c x : ℝ} (hx : 1 < x) :
    HasDerivAt (scale c) (slope c x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (by linarith)
  have hl0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hs0 : Real.sqrt (Real.log x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos hx))
  convert! ((hasDerivAt_id x).mul (hasDerivAt_decay hx)).div (Real.hasDerivAt_log hx0) hl0 using 1
  simp only [slope, tailKernel, id_eq, Pi.mul_apply]
  field_simp
  ring

lemma kernel_le_slope {c x : ℝ} (hc : 0 ≤ c)
    (hx : 1 < x) (hl : 4 ≤ Real.log x) (hc2 : 4*c^2 ≤ Real.log x) :
    kernel c x ≤ slope c x := by
  have hl0 := Real.log_pos hx
  have hs := Real.sqrt_nonneg (Real.log x)
  have hs0 := Real.sqrt_pos.mpr hl0
  have hs2 := Real.sq_sqrt hl0.le
  have hcS : 2*c ≤ Real.sqrt (Real.log x) := by nlinarith
  have hi : 1 / Real.log x ≤ 1/4 := (div_le_iff₀ hl0).mpr (by linarith)
  have hj : c / (2 * Real.sqrt (Real.log x)) ≤ 1/4 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  have h : 1 / Real.log x ≤ 1 - 1 / Real.log x - c / (2 * Real.sqrt (Real.log x)) := by linarith
  calc
    kernel c x = (decay c x / Real.log x) * (1 / Real.log x) := by unfold kernel; ring
    _ ≤ slope c x := mul_le_mul_of_nonneg_left h (div_nonneg (decay_pos c x).le hl0.le)

lemma continuousOn_kernel {c a b : ℝ} (ha : 1 < a) :
    ContinuousOn (kernel c) (Icc a b) := by
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt (by linarith [ht.1])
  have hlt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
  apply ContinuousAt.continuousWithinAt
  unfold kernel decay
  fun_prop (disch := simp [hlt0])

lemma continuousOn_slope {c a b : ℝ} (ha : 1 < a) :
    ContinuousOn (slope c) (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  have hst0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht1))
  apply ContinuousAt.continuousWithinAt
  unfold slope decay
  fun_prop (disch := simp [hst0])

theorem integral_kernel_le {c a b : ℝ} (hc : 0 ≤ c) (ha : 1 < a)
    (hl : 4 ≤ Real.log a) (hc2 : 4*c^2 ≤ Real.log a) (hab : a ≤ b) :
    (∫ t in a..b, kernel c t) ≤ scale c b := by
  have hi : IntervalIntegrable (kernel c) volume a b := (continuousOn_kernel (c:=c) (b:=b) ha).intervalIntegrable_of_Icc hab
  have hj : IntervalIntegrable (slope c) volume a b := (continuousOn_slope (c:=c) (b:=b) ha).intervalIntegrable_of_Icc hab
  have hle : (∫ t in a..b, kernel c t) ≤ ∫ t in a..b, slope c t := by
    apply intervalIntegral.integral_mono_on hab hi hj
    intro t ht
    have hlog := Real.log_le_log (show 0 < a by linarith) ht.1
    exact kernel_le_slope hc (lt_of_lt_of_le ha ht.1) (hl.trans hlog) (hc2.trans hlog)
  have hfund : (∫ t in a..b, slope c t) = scale c b - scale c a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hab] at ht
      exact hasDerivAt_scale (lt_of_lt_of_le ha ht.1)
    · exact hj
  exact hle.trans (hfund.trans_le (sub_le_self _ (scale_nonneg ha.le)))

theorem eventually_one_le_scale {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ scale c x := by
  have hlog := (isLittleO_log_rpow_atTop (show (0:ℝ)<1/2 by norm_num)).bound (show (0:ℝ)<1 by norm_num)
  filter_upwards [sqrt_le_errorScale hc, hlog, eventually_gt_atTop (1:ℝ)] with x hs hl hx
  have hl0 := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hslog : Real.log x ≤ Real.sqrt x := by
    simpa only [Real.norm_eq_abs, one_mul, Real.sqrt_eq_rpow, abs_of_pos hl0,
      abs_of_nonneg (Real.rpow_nonneg hx0.le _)] using hl
  change 1 ≤ x * decay c x / Real.log x
  apply (le_div_iff₀ hl0).mpr
  simp only [one_mul]
  exact hslog.trans hs

end ErdosPrimeInputs.PrimeCountingPrimitive

end

section

namespace ErdosPrimeInputs.PrimeCountAbel

open _root_.Set _root_.Filter _root_.MeasureTheory
open _root_.Erdos970.Set _root_.Erdos970.Filter _root_.Erdos970.MeasureTheory
open scoped Topology

noncomputable def logarithmicIntegral (x : ℝ) : ℝ := ∫ t in 2..x, 1 / Real.log t
noncomputable def primeError (x : ℝ) : ℝ := (Nat.primeCounting ⌊x⌋₊ : ℝ) - logarithmicIntegral x
noncomputable def endpoint (x : ℝ) : ℝ := (Chebyshev.theta x - x) / Real.log x
noncomputable def thetaKernel (t : ℝ) : ℝ := Chebyshev.theta t / (t * Real.log t ^ 2)
noncomputable def mainKernel (t : ℝ) : ℝ := 1 / Real.log t ^ 2
noncomputable def errorKernel (t : ℝ) : ℝ := thetaKernel t - mainKernel t

lemma mainKernel_continuous {a b : ℝ} (ha : 2 ≤ a) : ContinuousOn mainKernel (Icc a b) := by
  intro t ht
  have ht1 : 1 < t := by linarith [ht.1]
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlt0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  apply ContinuousAt.continuousWithinAt
  unfold mainKernel
  fun_prop (disch := simp [hlt0])

lemma mainKernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable mainKernel volume a b :=
  (mainKernel_continuous ha).intervalIntegrable_of_Icc hab

lemma thetaKernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable thetaKernel volume a b := by
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set (fun t ht => ⟨ha.trans ht.1,ht.2⟩)

lemma errorKernel_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable errorKernel volume a b :=
  (thetaKernel_integrable ha hab).sub (mainKernel_integrable ha hab)

lemma errorKernel_eq {t : ℝ} (ht : 0 < t) :
    errorKernel t = (Chebyshev.theta t - t) / (t * Real.log t ^ 2) := by
  unfold errorKernel thetaKernel mainKernel
  field_simp

theorem primeError_eq {x : ℝ} (hx : 2 ≤ x) :
    primeError x = 2 / Real.log 2 + endpoint x + ∫ t in 2..x, errorKernel t := by
  have hli := _root_.Erdos970.integral_log_inv 2 x (by norm_num) hx
  have herr : (∫ t in 2..x, errorKernel t) =
      (∫ t in 2..x, thetaKernel t) - (∫ t in 2..x, mainKernel t) :=
    intervalIntegral.integral_sub (thetaKernel_integrable (by norm_num) hx)
      (mainKernel_integrable (by norm_num) hx)
  unfold primeError logarithmicIntegral endpoint
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx, herr]
  simp only [one_div]
  rw [hli]
  unfold thetaKernel mainKernel
  simp only [one_div]
  ring

theorem primeError_increment {a x : ℝ} (ha : 2 ≤ a) (hax : a ≤ x) :
    primeError x = primeError a - endpoint a + endpoint x + ∫ t in a..x, errorKernel t := by
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (errorKernel_integrable (by norm_num) ha) (errorKernel_integrable ha hax)
  rw [primeError_eq (ha.trans hax), primeError_eq ha]
  linarith

end ErdosPrimeInputs.PrimeCountAbel

end

end Erdos970

end OAI
