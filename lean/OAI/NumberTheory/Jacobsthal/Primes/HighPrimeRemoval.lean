import Mathlib.Data.Finset.Sort
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import PrimeNumberTheoremAnd.Erdos970.MertensClassical
import StrongPNT.Erdos970.PNT5_Strong
import OAI.NumberTheory.Jacobsthal.Primes.PrimeBinCounting

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace ErdosPrimeInputs.StrongChebyshev

open _root_.Filter Asymptotics
open scoped Topology

noncomputable def errorScale (c x : ℝ) : ℝ :=
  x * Real.exp (-c * Real.sqrt (Real.log x))

theorem errorScale_nonneg (c : ℝ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ errorScale c x := by
  exact mul_nonneg hx (Real.exp_pos _).le

theorem psi_eq_original {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x = _root_.Erdos970.ChebyshevPsi x := by
  rw [Chebyshev.psi_eq_sum_Icc, _root_.Erdos970.ChebyshevPsi, Nat.floor_add_one hx,
    Nat.range_succ_eq_Icc_zero]

theorem sqrt_le_errorScale {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, Real.sqrt x ≤ errorScale c x := by
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop ((2 * c) ^ 2))] with x hx hlog
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hy0 := Real.sqrt_nonneg (Real.log x)
  have hy2 := Real.sq_sqrt hl0
  have hy : 2 * c ≤ Real.sqrt (Real.log x) := by nlinarith
  have hmul := mul_nonneg hy0 (sub_nonneg.mpr hy)
  have hlin : Real.log x * (1 / 2) ≤ Real.log x - c * Real.sqrt (Real.log x) := by
    nlinarith
  calc
    Real.sqrt x = Real.exp (Real.log x * (1 / 2)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0]
    _ ≤ Real.exp (Real.log x - c * Real.sqrt (Real.log x)) := Real.exp_le_exp.mpr hlin
    _ = errorScale c x := by
      rw [Real.exp_sub, Real.exp_log hx0, errorScale, neg_mul, Real.exp_neg]
      ring

theorem sqrt_isBigO_errorScale {c : ℝ} (hc : 0 < c) :
    Real.sqrt =O[atTop] errorScale c := by
  apply IsBigO.of_bound 1
  filter_upwards [sqrt_le_errorScale hc, eventually_ge_atTop (0 : ℝ)] with x hb hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x),
    abs_of_nonneg (errorScale_nonneg c hx), one_mul] using hb

theorem psi_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.psi x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, h⟩ := _root_.Erdos970.Strong_PNT
  refine ⟨c, hc, h.congr' ?_ ?_⟩
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    simp only [Pi.sub_apply, id_eq, psi_eq_original hx]
  · filter_upwards [] with x
    simp only [errorScale, Real.sqrt_eq_rpow]

theorem theta_strong : ∃ c : ℝ, 0 < c ∧
    (fun x : ℝ => Chebyshev.theta x - x) =O[atTop] errorScale c := by
  obtain ⟨c, hc, hpsi⟩ := psi_strong
  have hdiff := Chebyshev.isBigO_psi_sub_theta_sqrt.trans (sqrt_isBigO_errorScale hc)
  refine ⟨c, hc, (hpsi.sub hdiff).congr_left ?_⟩
  intro x
  simp only [Pi.sub_apply]
  ring

end ErdosPrimeInputs.StrongChebyshev



namespace ErdosPrimeInputs.PrimeAbel

open _root_.Set _root_.Finset _root_.MeasureTheory
open scoped Topology

noncomputable def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0
noncomputable def reciprocalPrimes (a b : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (n : ℝ)⁻¹
noncomputable def invLogWeight (t : ℝ) : ℝ := 1 / (t * Real.log t)
noncomputable def errorKernel (t : ℝ) : ℝ := (Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)

theorem prefix_primeLogWeight (x : ℝ) :
    ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, primeLogWeight n = Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  rfl

theorem reciprocal_eq_weighted (a b : ℝ) :
    reciprocalPrimes a b = ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, invLogWeight n * primeLogWeight n := by
  rw [reciprocalPrimes, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hnl : Real.log (n : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt))
    simp only [primeLogWeight, hp, ite_true, invLogWeight]
    field_simp
  · simp [primeLogWeight, hp]

theorem hasDerivAt_invLogWeight {t : ℝ} (ht : 1 < t) :
    HasDerivAt invLogWeight (-errorKernel t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)).inv (mul_ne_zero ht0 hl0) using 1
  · ext x
    simp [invLogWeight, one_div]
  · dsimp [errorKernel]
    field_simp

theorem deriv_invLogWeight {t : ℝ} (ht : 1 < t) : deriv invLogWeight t = -errorKernel t :=
  (hasDerivAt_invLogWeight ht).deriv

theorem invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn invLogWeight (Set.Icc a b) := by
  intro t ht
  exact (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt

theorem deriv_invLogWeight_continuousOn {a b : ℝ} (ha : 1 < a) :
    ContinuousOn (deriv invLogWeight) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t => -errorKernel t) (Set.Icc a b) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
    have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
    apply ContinuousAt.continuousWithinAt
    unfold errorKernel
    fun_prop (disch := simp [ht0, hl0])
  apply hc.congr
  intro t ht
  exact deriv_invLogWeight (lt_of_lt_of_le ha ht.1)

theorem abel_theta {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b = invLogWeight b * Chebyshev.theta b - invLogWeight a * Chebyshev.theta a -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t := by
  rw [reciprocal_eq_weighted]
  have h := sum_mul_eq_sub_sub_integral_mul primeLogWeight (le_of_lt (lt_trans zero_lt_one ha)) hab
    (fun t ht => (hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).differentiableAt)
    (deriv_invLogWeight_continuousOn ha).integrableOn_Icc
  simpa only [prefix_primeLogWeight] using h

theorem error_identity {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    reciprocalPrimes a b - (∫ t in Set.Ioc a b, invLogWeight t) =
      invLogWeight b * (Chebyshev.theta b - b) - invLogWeight a * (Chebyshev.theta a - a) -
      ∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t) := by
  have hf : IntegrableOn invLogWeight (Set.Ioc a b) :=
    (invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hfd : ContinuousOn (deriv invLogWeight) (Set.Icc a b) := deriv_invLogWeight_continuousOn ha
  have hlin : IntegrableOn (fun t => deriv invLogWeight t * t) (Set.Ioc a b) :=
    (hfd.mul continuousOn_id).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have htheta : IntegrableOn (fun t => deriv invLogWeight t * Chebyshev.theta t) (Set.Ioc a b) := by
    have h := integrableOn_mul_sum_Icc primeLogWeight (m := 0)
      (le_of_lt (lt_trans zero_lt_one ha)) hfd.integrableOn_Icc
    simp only [prefix_primeLogWeight] at h
    exact h.mono_set Set.Ioc_subset_Icc_self
  have hmain : (∫ t in Set.Ioc a b, deriv invLogWeight t * t) +
      (∫ t in Set.Ioc a b, invLogWeight t) = invLogWeight b * b - invLogWeight a * a := by
    rw [← integral_add hlin hf, ← intervalIntegral.integral_of_le hab]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      rw [deriv_invLogWeight (lt_of_lt_of_le ha ht.1)]
      simpa only [one_mul, mul_one] using!
        ((hasDerivAt_invLogWeight (lt_of_lt_of_le ha ht.1)).mul (hasDerivAt_id t))
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (hlin.add hf)
  have hrem : (∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)) =
      (∫ t in Set.Ioc a b, deriv invLogWeight t * Chebyshev.theta t) -
      (∫ t in Set.Ioc a b, deriv invLogWeight t * t) := by
    simp_rw [mul_sub]
    exact integral_sub htheta hlin
  have hAbel := abel_theta ha hab
  linear_combination hAbel - hmain + hrem

theorem hasDerivAt_loglog {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun x => Real.log (Real.log x)) (invLogWeight t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  convert! (Real.hasDerivAt_log hl0).comp t (Real.hasDerivAt_log ht0) using 1
  simp [invLogWeight, one_div, mul_inv_rev, mul_comm]

theorem integral_invLogWeight {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, invLogWeight t) = Real.log (Real.log b) - Real.log (Real.log a) := by
  rw [← intervalIntegral.integral_of_le hab]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact hasDerivAt_loglog (lt_of_lt_of_le ha ht.1)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((invLogWeight_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

end ErdosPrimeInputs.PrimeAbel



namespace ErdosPrimeInputs.PrimeEndpoints

open _root_.Finset
open PrimeAbel

noncomputable def intervalGuard (leftClosed rightClosed : Bool) (a b t : ℝ) : Prop :=
  (if leftClosed then a ≤ t else a < t) ∧ (if rightClosed then t ≤ b else t < b)

noncomputable def intervalSum (leftClosed rightClosed : Bool) (a b : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ Nat.primesLE ⌊b⌋₊,
    if intervalGuard leftClosed rightClosed a b (n : ℝ) then (n : ℝ)⁻¹ else 0

lemma reciprocal_eq_core {a b : ℝ} (ha : 0 ≤ a) (_hab : a ≤ b) :
    reciprocalPrimes a b = ∑ n ∈ Nat.primesLE ⌊b⌋₊, if a < (n : ℝ) then (n : ℝ)⁻¹ else 0 := by
  rw [reciprocalPrimes, ← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.mem_primesLE]
  rw [Nat.floor_lt ha]
  tauto

lemma selection_difference_bound (p q : Prop) [Decidable p] [Decidable q] {w : ℝ} (hw : 0 ≤ w) :
    |(if p then w else 0) - (if q then w else 0)| ≤ w := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq, abs_of_nonneg hw, hw]

lemma fiber_sum_le (s : Finset ℕ) (x : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (∑ n ∈ s, if (n : ℝ) = x then w else 0) ≤ w := by
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hc : (s.filter (fun n : ℕ => (n : ℝ) = x)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro n hn m hm
    have h := (Finset.mem_filter.mp hn).2.trans (Finset.mem_filter.mp hm).2.symm
    exact_mod_cast h
  have hr : ((s.filter (fun n : ℕ => (n : ℝ) = x)).card : ℝ) ≤ 1 := by exact_mod_cast hc
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hr hw

theorem endpoint_difference {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (lc rc : Bool) : |intervalSum lc rc a b - reciprocalPrimes a b| ≤ 2 / a := by
  classical
  have hw : 0 ≤ a⁻¹ := inv_nonneg.mpr ha.le
  rw [intervalSum, reciprocal_eq_core ha.le hab, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        |(if intervalGuard lc rc a b (n : ℝ) then (n : ℝ)⁻¹ else 0) -
          (if a < (n : ℝ) then (n : ℝ)⁻¹ else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Nat.primesLE ⌊b⌋₊,
        ((if (n : ℝ) = a then a⁻¹ else 0) + (if (n : ℝ) = b then a⁻¹ else 0)) := by
      apply Finset.sum_le_sum
      intro n hn
      have hp : n.Prime := (Nat.mem_primesLE.mp hn).2
      have hn0 : 0 < (n : ℝ) := by exact_mod_cast hp.pos
      have hnw : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr hn0.le
      have hnb : (n : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha.le hab)).mp (Nat.mem_primesLE.mp hn).1
      by_cases hna : (n : ℝ) = a
      · have hd := selection_difference_bound (intervalGuard lc rc a b (n : ℝ)) (a < (n : ℝ)) hnw
        calc
          _ ≤ (n : ℝ)⁻¹ := hd
          _ ≤ _ := by rw [hna]; split_ifs <;> simp_all
      · by_cases hneqb : (n : ℝ) = b
        · calc
            _ ≤ (n : ℝ)⁻¹ := selection_difference_bound _ _ hnw
            _ ≤ a⁻¹ := by rw [hneqb]; exact inv_anti₀ ha hab
            _ = _ := by rw [ite_eq_right hna, ite_eq_left hneqb, zero_add]
        · have hguard : intervalGuard lc rc a b (n : ℝ) ↔ a < (n : ℝ) := by
            have hne : a ≠ (n : ℝ) := Ne.symm hna
            cases lc <;> cases rc <;> simp_all [intervalGuard, le_iff_lt_or_eq]
          simp [hguard, hna, hneqb]
    _ ≤ a⁻¹ + a⁻¹ := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (fiber_sum_le _ _ hw) (fiber_sum_le _ _ hw)
    _ = 2 / a := by ring

end ErdosPrimeInputs.PrimeEndpoints



namespace ErdosPrimeInputs.PrimeErrorDecay

open _root_.Set _root_.MeasureTheory _root_.Filter Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel

noncomputable def decay (c t : ℝ) : ℝ := Real.exp (-c * Real.sqrt (Real.log t))
noncomputable def tailKernel (c t : ℝ) : ℝ := decay c t / (t * Real.sqrt (Real.log t))

lemma decay_pos (c t : ℝ) : 0 < decay c t := Real.exp_pos _

lemma decay_antitone {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hab : a ≤ b) :
    decay c b ≤ decay c a := by
  apply Real.exp_le_exp.mpr
  have h := Real.sqrt_le_sqrt (Real.log_le_log ha hab)
  nlinarith

lemma hasDerivAt_decay {c t : ℝ} (ht : 1 < t) :
    HasDerivAt (decay c) (-(c / 2) * tailKernel c t) t := by
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht)
  have hl0 : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht))
  have h := (((Real.hasDerivAt_sqrt hl0).comp t (Real.hasDerivAt_log ht0)).const_mul (-c)).exp
  convert! h using 1
  dsimp [tailKernel, decay]
  field_simp

lemma tailKernel_continuousOn {c a b : ℝ} (ha : 1 < a) :
    ContinuousOn (tailKernel c) (Set.Icc a b) := by
  intro t ht
  have ht1 := lt_of_lt_of_le ha ht.1
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans zero_lt_one ht1)
  have hs0 : Real.sqrt (Real.log t) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (Real.log_pos ht1))
  apply ContinuousAt.continuousWithinAt
  unfold tailKernel decay
  fun_prop (disch := simp [ht0, hs0])

lemma hasDerivAt_tailPrimitive {c t : ℝ} (hc : 0 < c) (ht : 1 < t) :
    HasDerivAt (fun t => -(2 / c) * decay c t) (tailKernel c t) t := by
  convert! (hasDerivAt_decay ht).const_mul (-(2 / c)) using 1
  field_simp

lemma tailIntegral {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) = (2 / c) * (decay c a - decay c b) := by
  have h : (∫ t in a..b, tailKernel c t) = -(2 / c) * decay c b - (-(2 / c) * decay c a) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact hasDerivAt_tailPrimitive hc (lt_of_lt_of_le ha ht.1)
    · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
        ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  rw [intervalIntegral.integral_of_le hab] at h
  rw [h]
  ring

lemma tailIntegral_le {c a b : ℝ} (hc : 0 < c) (ha : 1 < a) (hab : a ≤ b) :
    (∫ t in Set.Ioc a b, tailKernel c t) ≤ (2 / c) * decay c a := by
  rw [tailIntegral hc ha hab]
  exact mul_le_mul_of_nonneg_left (sub_le_self _ (decay_pos c b).le) (by positivity)

lemma kernel_comparison {t : ℝ} (ht : 1 < t) (hl : 1 ≤ Real.log t) :
    errorKernel t * t ≤ 2 / (t * Real.sqrt (Real.log t)) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  have hs0 : 0 < Real.sqrt (Real.log t) := Real.sqrt_pos.mpr hl0
  have hsle : Real.sqrt (Real.log t) ≤ Real.log t := by
    have hs2 := Real.sq_sqrt hl0.le
    have hs := Real.sqrt_nonneg (Real.log t)
    nlinarith
  calc
    errorKernel t * t = (Real.log t + 1) / (t * Real.log t ^ 2) := by
      unfold errorKernel
      field_simp
    _ ≤ (2 * Real.log t) / (t * Real.log t ^ 2) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    _ = 2 / (t * Real.log t) := by field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (mul_pos ht0 hs0)
      (mul_le_mul_of_nonneg_left hsle ht0.le)

lemma endpoint_error_bound {c C t : ℝ} (hC : 0 ≤ C) (ht : 1 < t) (hl : 1 ≤ Real.log t)
    (hθ : |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |invLogWeight t * (Chebyshev.theta t - t)| ≤ C * decay c t := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hl0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hl
  rw [abs_mul, abs_of_nonneg (show 0 ≤ invLogWeight t by unfold invLogWeight; positivity)]
  calc
    _ ≤ invLogWeight t * (C * errorScale c t) :=
      mul_le_mul_of_nonneg_left hθ (by unfold invLogWeight; positivity)
    _ = C * decay c t / Real.log t := by unfold invLogWeight errorScale decay; field_simp
    _ ≤ C * decay c t := div_le_self (mul_nonneg hC (decay_pos c t).le) hl

lemma integral_error_bound {c C a b : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (ha : 1 < a) (hla : 1 ≤ Real.log a) (hab : a ≤ b)
    (hθ : ∀ t ∈ Set.Icc a b, |Chebyshev.theta t - t| ≤ C * errorScale c t) :
    |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| ≤
      (4 * C / c) * decay c a := by
  have hi : IntegrableOn (fun t => (2 * C) * tailKernel c t) (Set.Ioc a b) :=
    ((tailKernel_continuousOn ha).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).const_mul _
  have hb : ∀ t ∈ Set.Ioc a b,
      ‖deriv invLogWeight t * (Chebyshev.theta t - t)‖ ≤ (2 * C) * tailKernel c t := by
    intro t ht
    have ht1 : 1 < t := lt_trans ha ht.1
    have ht0 : 0 < t := lt_trans zero_lt_one ht1
    have hlt : 1 ≤ Real.log t := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) ht.1.le)
    have hk0 : 0 ≤ errorKernel t := by unfold errorKernel; positivity
    rw [deriv_invLogWeight ht1, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hk0]
    calc
      _ ≤ errorKernel t * (C * errorScale c t) := mul_le_mul_of_nonneg_left (hθ t ⟨ht.1.le, ht.2⟩) hk0
      _ = (errorKernel t * t) * (C * decay c t) := by unfold errorScale decay; ring
      _ ≤ (2 / (t * Real.sqrt (Real.log t))) * (C * decay c t) :=
        mul_le_mul_of_nonneg_right (kernel_comparison ht1 hlt) (mul_nonneg hC (decay_pos c t).le)
      _ = _ := by unfold tailKernel; ring
  have hint := norm_integral_le_of_norm_le hi (ae_restrict_of_forall_mem measurableSet_Ioc hb)
  rw [integral_const_mul] at hint
  calc
    _ ≤ (2 * C) * ∫ t in Set.Ioc a b, tailKernel c t := hint
    _ ≤ (2 * C) * ((2 / c) * decay c a) :=
      mul_le_mul_of_nonneg_left (tailIntegral_le hc ha hab) (by positivity)
    _ = _ := by ring

theorem uniform_prime_interval_error : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧
    1 < a₀ ∧ 1 ≤ Real.log a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b →
      |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  obtain ⟨c, hc, hstrong⟩ := theta_strong
  obtain ⟨K, hK, hbound⟩ := hstrong.exists_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hbound.bound
  let a₀ := max x₀ (Real.exp 1)
  have ha₀ : 1 < a₀ := by
    have he : 1 < Real.exp 1 := by linarith [Real.exp_one_gt_two]
    exact lt_of_lt_of_le he (le_max_right x₀ (Real.exp 1))
  have hlog₀ : 1 ≤ Real.log a₀ := by
    have h := Real.log_le_log (Real.exp_pos 1) (le_max_right x₀ (Real.exp 1))
    simpa only [Real.log_exp] using h
  refine ⟨c, 2 * K + 4 * K / c, a₀, hc, by positivity, ha₀, hlog₀, ?_⟩
  intro a b haa hab
  have ha : 1 < a := lt_of_lt_of_le ha₀ haa
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hla : 1 ≤ Real.log a := le_trans hlog₀ (Real.log_le_log (lt_trans zero_lt_one ha₀) haa)
  have hlb : 1 ≤ Real.log b := le_trans hla (Real.log_le_log (lt_trans zero_lt_one ha) hab)
  have hθ : ∀ t, a₀ ≤ t → |Chebyshev.theta t - t| ≤ K * errorScale c t := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le (lt_trans zero_lt_one ha₀) ht)
    have h := hx₀ t (le_trans (le_max_left _ _) ht)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (errorScale_nonneg c ht0)] using h
  rw [← integral_invLogWeight ha hab, error_identity ha hab]
  calc
    _ ≤ |invLogWeight b * (Chebyshev.theta b - b)| + |invLogWeight a * (Chebyshev.theta a - a)| +
        |∫ t in Set.Ioc a b, deriv invLogWeight t * (Chebyshev.theta t - t)| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ K * decay c a + K * decay c a + (4 * K / c) * decay c a := by
      apply add_le_add
      · apply add_le_add
        · exact (endpoint_error_bound hK.le hb hlb (hθ b (le_trans haa hab))).trans
            (mul_le_mul_of_nonneg_left (decay_antitone hc.le (lt_trans zero_lt_one ha) hab) hK.le)
        · exact endpoint_error_bound hK.le ha hla (hθ a haa)
      · exact integral_error_bound hc hK.le ha hla hab (fun t ht => hθ t (le_trans haa ht.1))
    _ = _ := by ring

end ErdosPrimeInputs.PrimeErrorDecay



namespace ErdosPrimeInputs.HarmonicPrimeMeasure

open _root_.Filter Asymptotics
open scoped Topology
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay

lemma reciprocal_le_decay {c : ℝ} (hc : 0 < c) :
    ∀ᶠ a : ℝ in atTop, a⁻¹ ≤ decay c a := by
  filter_upwards [sqrt_le_errorScale hc, eventually_ge_atTop (1 : ℝ)] with a hs ha
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have h := le_trans (Real.one_le_sqrt.mpr ha) hs
  rw [inv_eq_one_div]
  apply (div_le_iff₀ ha0).mpr
  simpa only [errorScale, decay, mul_comm] using h

theorem uniform_all_endpoints : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a b : ℝ, a₀ ≤ a → a ≤ b → ∀ lc rc : Bool,
      |intervalSum lc rc a b - (Real.log (Real.log b) - Real.log (Real.log a))| ≤ C * decay c a := by
  obtain ⟨c, C, a₀, hc, hC, ha₀, hlog₀, h⟩ := uniform_prime_interval_error
  obtain ⟨A, hA⟩ := eventually_atTop.mp (reciprocal_le_decay hc)
  refine ⟨c, C + 2, max a₀ A, hc, by positivity, lt_of_lt_of_le ha₀ (le_max_left _ _), ?_⟩
  intro a b haa hab lc rc
  have ha : 1 < a := lt_of_lt_of_le ha₀ (le_trans (le_max_left _ _) haa)
  have herr := h a b (le_trans (le_max_left _ _) haa) hab
  have hend := endpoint_difference (lt_trans zero_lt_one ha) hab lc rc
  have hinv := hA a (le_trans (le_max_right _ _) haa)
  calc
    _ ≤ |intervalSum lc rc a b - reciprocalPrimes a b| +
        |reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a))| := abs_sub_le _ _ _
    _ ≤ 2 / a + C * decay c a := add_le_add hend herr
    _ ≤ 2 * decay c a + C * decay c a := add_le_add (by simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
    _ = _ := by ring

noncomputable def primeExponent (w : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log w

noncomputable def harmonicMass (w : ℝ) (lc rc : Bool) (u v : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ Nat.primesLE ⌊w ^ v⌋₊,
    if intervalGuard lc rc u v (primeExponent w p) then (p : ℝ)⁻¹ else 0

lemma exponent_le_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    Real.log p / Real.log w ≤ t ↔ p ≤ w ^ t := by
  rw [div_le_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_le_log_iff hp (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t)]

lemma exponent_lt_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    Real.log p / Real.log w < t ↔ p < w ^ t := by
  rw [div_lt_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_lt_log_iff hp (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t)]

lemma le_exponent_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    t ≤ Real.log p / Real.log w ↔ w ^ t ≤ p := by
  rw [le_div_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_le_log_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t) hp]

lemma lt_exponent_iff {w p t : ℝ} (hw : 1 < w) (hp : 0 < p) :
    t < Real.log p / Real.log w ↔ w ^ t < p := by
  rw [lt_div_iff₀ (Real.log_pos hw), ← Real.log_rpow (lt_trans zero_lt_one hw) t,
    Real.log_lt_log_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) t) hp]

lemma harmonicMass_eq_intervalSum {w : ℝ} (hw : 1 < w) (lc rc : Bool) (u v : ℝ) :
    harmonicMass w lc rc u v = intervalSum lc rc (w ^ u) (w ^ v) := by
  classical
  unfold harmonicMass intervalSum
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hg : intervalGuard lc rc u v (primeExponent w p) ↔
      intervalGuard lc rc (w ^ u) (w ^ v) (p : ℝ) := by
    cases lc <;> cases rc <;>
      simp only [intervalGuard, primeExponent, Bool.false_eq_true, ite_true, ite_false,
        exponent_le_iff hw hp0, exponent_lt_iff hw hp0, le_exponent_iff hw hp0, lt_exponent_iff hw hp0]
  simp only [hg]

theorem harmonic_prime_measure : ∃ c C w₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ u v : ℝ, 1 / 2 ≤ u → u ≤ v → ∀ lc rc : Bool,
      |harmonicMass w lc rc u v - (Real.log v - Real.log u)| ≤
        C * Real.exp (-c * Real.sqrt (u * Real.log w)) := by
  obtain ⟨c, C, a₀, hc, hC, ha₀, h⟩ := uniform_all_endpoints
  refine ⟨c, C, max 2 (a₀ ^ 2), hc, hC, lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro w hw u v hu huv lc rc
  have hw1 : 1 < w := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_trans (le_max_left _ _) hw)
  have hw0 : 0 < w := lt_trans zero_lt_one hw1
  have hu0 : 0 < u := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2) hu
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  have hlogw : 0 < Real.log w := Real.log_pos hw1
  have hsqrt : a₀ ≤ Real.sqrt w := by
    have hs2 := Real.sq_sqrt hw0.le
    have hs0 := Real.sqrt_nonneg w
    have haw : a₀ ^ 2 ≤ w := le_trans (le_max_right _ _) hw
    nlinarith
  have hau : a₀ ≤ w ^ u := le_trans hsqrt (by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hw1.le hu)
  have huvpow : w ^ u ≤ w ^ v := Real.rpow_le_rpow_of_exponent_le hw1.le huv
  have hmain : Real.log (Real.log (w ^ v)) - Real.log (Real.log (w ^ u)) =
      Real.log v - Real.log u := by
    rw [Real.log_rpow hw0, Real.log_rpow hw0,
      Real.log_mul (ne_of_gt hv0) (ne_of_gt hlogw), Real.log_mul (ne_of_gt hu0) (ne_of_gt hlogw)]
    ring
  have hp := h (w ^ u) (w ^ v) hau huvpow lc rc
  rw [hmain] at hp
  rw [harmonicMass_eq_intervalSum hw1]
  simpa only [decay, Real.log_rpow hw0] using hp

end ErdosPrimeInputs.HarmonicPrimeMeasure



namespace ErdosPrimeInputs.MertensStrong

open _root_.Filter Asymptotics _root_.Finset
open scoped Topology
open PrimeAbel PrimeErrorDecay

lemma second_error_difference {a b : ℝ} (hab : a ≤ b) :
    _root_.Erdos970.Mertens.E₂p b - _root_.Erdos970.Mertens.E₂p a =
      reciprocalPrimes a b - (Real.log (Real.log b) - Real.log (Real.log a)) := by
  have h := Finset.sum_Ioc_consecutive
    (fun p : ℕ => if p.Prime then (p : ℝ)⁻¹ else 0) (Nat.zero_le ⌊a⌋₊) (Nat.floor_mono hab)
  unfold _root_.Erdos970.Mertens.E₂p reciprocalPrimes
  simp only [Finset.sum_filter, one_div] at *
  linarith

theorem second_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 1 < a₀ ∧
    ∀ a : ℝ, a₀ ≤ a → |_root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,_,h⟩ := uniform_prime_interval_error
  refine ⟨c,C,a₀,hc,hC,ha₀,?_⟩
  intro a ha
  have ht : Tendsto _root_.Erdos970.Mertens.E₂p atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₂p.bound'
  have hb : |0 - _root_.Erdos970.Mertens.E₂p a| ≤ C * decay c a := by
    apply le_of_tendsto (ht.sub_const (_root_.Erdos970.Mertens.E₂p a)).abs
    filter_upwards [eventually_ge_atTop a] with b hab
    rw [second_error_difference hab]
    exact h a b ha hab
  simpa only [zero_sub, abs_neg] using hb

lemma reciprocal_le_decay {c x : ℝ} (hc : c ≤ 1) (hx : 0 < x) (hlog : 1 ≤ Real.log x) :
    1 / x ≤ decay c x := by
  have hs := Real.sqrt_nonneg (Real.log x)
  have hs2 := Real.sq_sqrt (show 0 ≤ Real.log x by linarith)
  have hsmall : Real.sqrt (Real.log x) ≤ Real.log x := by nlinarith
  have hexp : -Real.log x ≤ -c * Real.sqrt (Real.log x) := by nlinarith
  calc
    1 / x = Real.exp (-Real.log x) := by rw [Real.exp_neg, Real.exp_log hx, one_div]
    _ ≤ decay c x := Real.exp_le_exp.mpr hexp

lemma third_error_identity (x : ℝ) :
    _root_.Erdos970.Mertens.E₃ x =
      (∑ n ∈ Ioc 0 ⌊x⌋₊, _root_.Erdos970.Mertens.M_eq_summand n - 0) - (_root_.Erdos970.Mertens.M - _root_.Erdos970.Mertens.γ) - _root_.Erdos970.Mertens.E₂p x := by
  unfold _root_.Erdos970.Mertens.E₃ _root_.Erdos970.Mertens.E₂p
  have h (n : ℕ) : _root_.Erdos970.Mertens.M_eq_summand n =
      (if n.Prime then Real.log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
    unfold _root_.Erdos970.Mertens.M_eq_summand
    split_ifs <;> ring
  simp_rw [sub_zero, h]
  rw [sum_filter, sum_filter, sum_add_distrib, _root_.Erdos970.Mertens.γ.eq_eulerMascheroni]
  ring

theorem third_error_strong : ∃ c C a₀ : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ a₀ ∧
    ∀ x : ℝ, a₀ ≤ x → |_root_.Erdos970.Mertens.E₃ x| ≤ C * decay c x := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,h⟩ := second_error_strong
  let c' := min c 1
  let x₀ := max a₀ (Real.exp 1)
  have hc' : 0 < c' := lt_min hc zero_lt_one
  have hx₀ : 2 ≤ x₀ := (le_of_lt Real.exp_one_gt_two).trans (le_max_right _ _)
  refine ⟨c',C+4,x₀,hc',by positivity,hx₀,?_⟩
  intro x hx
  have hx2 : 2 ≤ x := hx₀.trans hx
  have hx0 : 0 < x := by linarith
  have hlog : 1 ≤ Real.log x := by
    have h' := Real.log_le_log (Real.exp_pos 1) ((le_max_right a₀ (Real.exp 1)).trans hx)
    simpa only [Real.log_exp] using h'
  have hd : decay c x ≤ decay c' x := by
    apply Real.exp_le_exp.mpr
    have := min_le_left c (1:ℝ)
    have := Real.sqrt_nonneg (Real.log x)
    dsimp [c']
    nlinarith
  rw [third_error_identity]
  simp only [sub_zero]
  calc
    _ ≤ |(∑ n ∈ Ioc 0 ⌊x⌋₊, _root_.Erdos970.Mertens.M_eq_summand n) - (_root_.Erdos970.Mertens.M - _root_.Erdos970.Mertens.γ)| + |_root_.Erdos970.Mertens.E₂p x| := abs_sub _ _
    _ ≤ 4 / x + C * decay c x := add_le_add (_root_.Erdos970.Mertens.sum_M_eq_summand_le' hx2) (h x ((le_max_left _ _).trans hx))
    _ ≤ 4 * decay c' x + C * decay c' x := by
      apply add_le_add
      · have hrec := reciprocal_le_decay (min_le_right c 1) hx0 hlog
        calc
          4 / x = 4 * (1/x) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hrec (by norm_num)
      · exact mul_le_mul_of_nonneg_left hd hC.le
    _ = (C+4) * decay c' x := by ring

noncomputable def primeProduct (x : ℝ) : ℝ :=
  ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1:ℝ) / p)

theorem prime_product_strong : ∃ c C x₀ : ℝ, 0 < c ∧ 0 < C ∧ 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x →
      |primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) - 1| ≤
        C * Real.exp (-c * Real.sqrt (Real.log x)) := by
  obtain ⟨c,C,a₀,hc,hC,ha₀,h⟩ := third_error_strong
  have ht : Tendsto _root_.Erdos970.Mertens.E₃ atTop (𝓝 0) := (isLittleO_one_iff ℝ).mp _root_.Erdos970.Mertens.E₃.bound'
  have hs : ∀ᶠ x : ℝ in atTop, |_root_.Erdos970.Mertens.E₃ x| < 1 :=
    ht.abs.eventually (gt_mem_nhds (show |(0:ℝ)| < 1 by norm_num))
  obtain ⟨x₁,hx₁⟩ := eventually_atTop.mp hs
  refine ⟨c,2*C,max a₀ x₁,hc,by positivity,ha₀.trans (le_max_left _ _),?_⟩
  intro x hx
  have hxa := (le_max_left a₀ x₁).trans hx
  have hxx := (le_max_right a₀ x₁).trans hx
  have hx2 : 2 ≤ x := ha₀.trans hxa
  have hx1 : 1 < x := by linarith
  have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  have he : primeProduct x / (Real.exp (-Real.eulerMascheroniConstant) / Real.log x) =
      Real.exp (_root_.Erdos970.Mertens.E₃ x) := by
    rw [primeProduct, _root_.Erdos970.Mertens.prod_one_minus_div_prime_eq hx1]
    field_simp
  rw [he]
  calc
    _ ≤ 2 * |_root_.Erdos970.Mertens.E₃ x| := Real.abs_exp_sub_one_le (hx₁ x hxx).le
    _ ≤ 2 * (C * decay c x) := mul_le_mul_of_nonneg_left (h x hxa) (by norm_num)
    _ = _ := by unfold decay; ring

end ErdosPrimeInputs.MertensStrong



namespace ErdosInversePrimeBin
open _root_.Filter Asymptotics
open scoped Topology
open ErdosPrimeInputs.StrongChebyshev ErdosPrimeInputs.PrimeErrorDecay

theorem prime_bin_theta_error : ∃ c C R₀ : ℝ,0 < c ∧ 0 < C ∧ 2 ≤ R₀ ∧
    ∀ R : ℝ,R₀ ≤ R → ∀ xi : ℝ,0 ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ 3*C*R*decay c R := by
  obtain ⟨c,hc,hstrong⟩ := theta_strong
  obtain ⟨C,hC,hbig⟩ := hstrong.exists_pos
  obtain ⟨A,hA⟩ := eventually_atTop.mp hbig.bound
  refine ⟨c,C,max A 2,hc,hC,le_max_right _ _,?_⟩
  intro R hR xi hxi hxi1
  have hR2 : 2 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := by linarith
  have hRA : A ≤ R := (le_max_left _ _).trans hR
  have hbR : R ≤ (1+xi)*R := by nlinarith
  have hb2 : (1+xi)*R ≤ 2*R := by nlinarith
  have htheta (x : ℝ) (hx : A ≤ x) (hx0 : 0 ≤ x) :
      |Chebyshev.theta x-x| ≤ C*(x*decay c x) := by
    have h := hA x hx
    simp only [Real.norm_eq_abs] at h
    rw [abs_of_nonneg (errorScale_nonneg c hx0)] at h
    exact h
  have hr := htheta R hRA hR0.le
  have hb : |Chebyshev.theta ((1+xi)*R)-(1+xi)*R| ≤ 2*C*R*decay c R := by
    calc
      _ ≤ C*(((1+xi)*R)*decay c ((1+xi)*R)) := htheta _ (hRA.trans hbR) (hR0.le.trans hbR)
      _ ≤ C*((2*R)*decay c R) := mul_le_mul_of_nonneg_left
        (mul_le_mul hb2 (decay_antitone hc.le hR0 hbR) (decay_pos _ _).le (by positivity)) hC.le
      _ = _ := by ring
  have he : Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R =
      (Chebyshev.theta ((1+xi)*R)-(1+xi)*R)-(Chebyshev.theta R-R) := by ring
  rw [he]
  exact (abs_sub _ _).trans (by nlinarith only [hb,hr])

theorem decay_tendsto_zero {c : ℝ} (hc : 0 < c) : Tendsto (decay c) atTop (𝓝 0) := by
  have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    (Tendsto.const_mul_atTop hc (Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop))
  convert h using 1
  funext x
  simp only [Function.comp_apply,decay,neg_mul]

theorem uniform_bin_theta_error {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ R : ℝ in atTop,2 ≤ R ∧ ∀ xi : ℝ,eta ≤ xi → xi ≤ 1 →
      |Chebyshev.theta ((1+xi)*R)-Chebyshev.theta R-xi*R| ≤ xi*R/2 := by
  obtain ⟨c,C,R₀,hc,hC,hR₀,hbound⟩ := prime_bin_theta_error
  have hdec : Tendsto (fun R : ℝ => 3*C*decay c R) atTop (𝓝 0) := by
    simpa only [mul_zero] using (decay_tendsto_zero hc).const_mul (3*C)
  filter_upwards [eventually_ge_atTop R₀,
    hdec.eventually (eventually_le_nhds (show 0 < eta/2 by positivity))] with R hR hd
  have hR2 := hR₀.trans hR
  refine ⟨hR2,?_⟩
  intro xi hxi hxi1
  have hxi0 : 0 ≤ xi := heta.le.trans hxi
  have he := hbound R hR xi hxi0 hxi1
  have hm := mul_le_mul_of_nonneg_right hd (show 0 ≤ R by linarith)
  have hwidth := mul_le_mul_of_nonneg_right hxi (show 0 ≤ R by linarith)
  exact he.trans (by nlinarith only [hm,hwidth])

end ErdosInversePrimeBin



namespace ErdosPrimeInputs.PrimePrefixMass

open _root_.Finset
open StrongChebyshev PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure

noncomputable def primesBetween (a b : ℝ) : Finset ℕ :=
  (Nat.primesLE ⌊b⌋₊).filter (fun p => a < (p : ℝ))

def decreasingPrefixes (s : Finset ℕ) : Finset (List ℕ) :=
  s.powerset.image (fun t => t.sort (· ≥ ·))

noncomputable def prefixWeight (l : List ℕ) : ℝ := (l.map (fun p : ℕ => (p : ℝ)⁻¹)).prod

lemma mem_decreasingPrefixes {s : Finset ℕ} {l : List ℕ} :
    l ∈ decreasingPrefixes s ↔ l.Pairwise (· > ·) ∧ ∀ p ∈ l, p ∈ s := by
  constructor
  · intro hl
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hl
    refine ⟨t.sortedGT_sort.pairwise, ?_⟩
    intro p hp
    apply (Finset.mem_powerset.mp ht)
    simpa using hp
  · rintro ⟨hp, hs⟩
    have hn : l.Nodup := hp.imp (fun h => ne_of_gt h)
    have hge : l.Pairwise (· ≥ ·) := hp.imp (fun h => le_of_lt h)
    apply Finset.mem_image.mpr
    refine ⟨l.toFinset, Finset.mem_powerset.mpr ?_, (List.toFinset_sort (· ≥ ·) hn).mpr hge⟩
    intro p hp
    exact hs p (List.mem_toFinset.mp hp)

lemma prefixWeight_sort (s : Finset ℕ) :
    prefixWeight (s.sort (· ≥ ·)) = ∏ p ∈ s, (p : ℝ)⁻¹ := by
  have h := List.prod_toFinset (fun p : ℕ => (p : ℝ)⁻¹) (s.sort_nodup (· ≥ ·))
  simpa only [Finset.sort_toFinset, prefixWeight] using h.symm

lemma sum_prefixWeights (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, prefixWeight l) = ∏ p ∈ s, (1 + (p : ℝ)⁻¹) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · simp_rw [prefixWeight_sort]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    have h' := congrArg List.toFinset h
    simpa only [Finset.sort_toFinset] using h'

lemma prefix_mass_le_exp (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, prefixWeight l) ≤ Real.exp (∑ p ∈ s, (p : ℝ)⁻¹) := by
  rw [sum_prefixWeights, Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    positivity
  · intro p hp
    simpa only [add_comm] using Real.add_one_le_exp (p : ℝ)⁻¹

lemma sum_primesBetween {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∑ p ∈ primesBetween a b, (p : ℝ)⁻¹) = reciprocalPrimes a b := by
  rw [primesBetween, Finset.sum_filter]
  exact (reciprocal_eq_core ha hab).symm

lemma interval_open_closed {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    intervalSum false true a b = reciprocalPrimes a b := by
  classical
  rw [intervalSum, reciprocal_eq_core ha hab]
  apply Finset.sum_congr rfl
  intro p hp
  have hpb : (p : ℝ) ≤ b := (Nat.le_floor_iff (le_trans ha hab)).mp (Nat.mem_primesLE.mp hp).1
  simp [intervalGuard, hpb]

theorem total_prime_prefix_mass : ∃ M w₀ : ℝ, 0 < M ∧ 1 < w₀ ∧
    ∀ w : ℝ, w₀ ≤ w → ∀ ell B : ℝ, 1 ≤ ell → ell ≤ B →
      (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) ≤ M * B / ell := by
  obtain ⟨c, C, w₀, hc, hC, hw₀, h⟩ := harmonic_prime_measure
  refine ⟨Real.exp C, w₀, Real.exp_pos C, hw₀, ?_⟩
  intro w hw ell B hell hB
  have hw1 := lt_of_lt_of_le hw₀ hw
  have hwpos : 0 < w := lt_trans zero_lt_one hw1
  have hellpos : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hBpos : 0 < B := lt_of_lt_of_le hellpos hB
  have hab : w ^ ell ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have ha : 0 ≤ w ^ ell := (Real.rpow_pos_of_pos hwpos ell).le
  have hh := h w hw ell B (by linarith) hB false true
  rw [harmonicMass_eq_intervalSum hw1, interval_open_closed ha hab] at hh
  have hexp : Real.exp (-c * Real.sqrt (ell * Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hs : reciprocalPrimes (w ^ ell) (w ^ B) ≤ Real.log B - Real.log ell + C := by
    have hu := (abs_le.mp hh).2
    have he := mul_le_mul_of_nonneg_left hexp hC.le
    linarith
  calc
    _ ≤ Real.exp (∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) := prefix_mass_le_exp _
    _ ≤ Real.exp (Real.log B - Real.log ell + C) := by
      apply Real.exp_le_exp.mpr
      simpa only [sum_primesBetween ha hab] using hs
    _ = Real.exp C * B / ell := by
      rw [Real.exp_add, Real.exp_sub, Real.exp_log hBpos, Real.exp_log hellpos]
      ring

end ErdosPrimeInputs.PrimePrefixMass



namespace ErdosPrimeInputs.PrimePrefixTail

open _root_.Finset
open PrimePrefixMass

noncomputable def longPrefixMass (s : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ l ∈ (decreasingPrefixes s).filter (fun l => m ≤ l.length), prefixWeight l

lemma prefixWeight_nonneg (l : List ℕ) : 0 ≤ prefixWeight l := by
  unfold prefixWeight
  apply List.prod_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  positivity

lemma tilted_weight (l : List ℕ) :
    ((l.map (fun p : ℕ => 2 * (p : ℝ)⁻¹)).prod) = (2 : ℝ) ^ l.length * prefixWeight l := by
  induction l with
  | nil => simp [prefixWeight]
  | cons p l ih => simp only [List.map_cons, List.prod_cons, List.length_cons, pow_succ, prefixWeight] at ih ⊢; rw [ih]; ring

lemma sum_sorted_products (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ l ∈ decreasingPrefixes s, (l.map f).prod) = ∏ p ∈ s, (1 + f p) := by
  rw [decreasingPrefixes, Finset.sum_image]
  · have hp (t : Finset ℕ) : ((t.sort (· ≥ ·)).map f).prod = ∏ p ∈ t, f p := by
      simpa only [Finset.sort_toFinset] using (List.prod_toFinset f (t.sort_nodup (· ≥ ·))).symm
    simp_rw [hp]
    exact (Finset.prod_one_add s).symm
  · intro t ht u hu h
    simpa only [Finset.sort_toFinset] using congrArg List.toFinset h

lemma sum_tilted_weights (s : Finset ℕ) :
    (∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l) =
      ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := by
  simp_rw [← tilted_weight]
  exact sum_sorted_products s _

theorem longPrefixMass_le (s : Finset ℕ) (m : ℕ) :
    longPrefixMass s m ≤ Real.exp (2 * ∑ p ∈ s, (p : ℝ)⁻¹) / (2 : ℝ) ^ m := by
  apply (le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) m)).mpr
  rw [mul_comm, longPrefixMass, Finset.mul_sum]
  calc
    _ ≤ ∑ l ∈ (decreasingPrefixes s).filter (fun l => m ≤ l.length),
        (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum
      intro l hl
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Finset.mem_filter.mp hl).2) (prefixWeight_nonneg l)
    _ ≤ ∑ l ∈ decreasingPrefixes s, (2 : ℝ) ^ l.length * prefixWeight l := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro l hl hnot
      exact mul_nonneg (pow_nonneg (by norm_num) _) (prefixWeight_nonneg l)
    _ = ∏ p ∈ s, (1 + 2 * (p : ℝ)⁻¹) := sum_tilted_weights s
    _ ≤ ∏ p ∈ s, Real.exp (2 * (p : ℝ)⁻¹) := by
      apply Finset.prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        simpa only [add_comm] using Real.add_one_le_exp (2 * (p : ℝ)⁻¹)
    _ = _ := by rw [← Real.exp_sum, ← Finset.mul_sum]

end ErdosPrimeInputs.PrimePrefixTail



namespace ErdosPrimeInputs.LongPrimePaths

open _root_.Filter Asymptotics
open scoped Topology
open PrimeAbel PrimeEndpoints PrimeErrorDecay HarmonicPrimeMeasure PrimePrefixMass PrimePrefixTail

lemma fixed_tilt_tail (C A : ℝ) : ∀ᶠ B : ℝ in atTop, ∀ m : ℕ,
    (Real.log B) ^ 2 / 2 ≤ m →
      Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m ≤ B ^ (-A) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 * (A + 2 + 2 * |C|) / Real.log 2)))] with B hB hL
  intro m hm
  have hb0 : 0 < B := lt_trans zero_lt_one hB
  have hl1 : 1 ≤ Real.log B := le_trans (le_max_left _ _) hL
  have hl0 : 0 ≤ Real.log B := le_trans zero_le_one hl1
  have ht : 2 * (A + 2 + 2 * |C|) ≤ Real.log B * Real.log 2 :=
    (div_le_iff₀ hlog2).mp (le_trans (le_max_right _ _) hL)
  have ht' := mul_le_mul_of_nonneg_right ht hl0
  have hm' := mul_le_mul_of_nonneg_right hm hlog2.le
  have hC' := mul_le_mul_of_nonneg_left hl1 (abs_nonneg C)
  have he : 2 * (Real.log B + C) - (m : ℝ) * Real.log 2 ≤ Real.log B * (-A) := by
    nlinarith [le_abs_self C]
  have hpow : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [hpow, ← Real.exp_sub, Real.rpow_def_of_pos hb0]
  exact Real.exp_le_exp.mpr he

theorem long_prime_paths_superpolynomial : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ A : ℝ, ∀ᶠ B : ℝ in atTop, ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ,
      1 ≤ ell → ell ≤ B → ∀ m : ℕ, (Real.log B) ^ 2 / 2 ≤ m →
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) m ≤ B ^ (-A) := by
  obtain ⟨c, C, w₀, hc, hC, hw₀, h⟩ := harmonic_prime_measure
  refine ⟨w₀, hw₀, ?_⟩
  intro A
  filter_upwards [fixed_tilt_tail C A] with B htail
  intro w hw ell hell hB m hm
  have hw1 := lt_of_lt_of_le hw₀ hw
  have hwpos : 0 < w := lt_trans zero_lt_one hw1
  have hab : w ^ ell ≤ w ^ B := Real.rpow_le_rpow_of_exponent_le hw1.le hB
  have ha : 0 ≤ w ^ ell := (Real.rpow_pos_of_pos hwpos ell).le
  have hh := h w hw ell B (by linarith) hB false true
  rw [harmonicMass_eq_intervalSum hw1, interval_open_closed ha hab] at hh
  have hexp : Real.exp (-c * Real.sqrt (ell * Real.log w)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))
  have hsum : (∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) ≤ Real.log B + C := by
    rw [sum_primesBetween ha hab]
    have hu := (abs_le.mp hh).2
    have he := mul_le_mul_of_nonneg_left hexp hC.le
    have hl := Real.log_nonneg hell
    linarith
  calc
    _ ≤ Real.exp (2 * ∑ p ∈ primesBetween (w ^ ell) (w ^ B), (p : ℝ)⁻¹) / (2 : ℝ) ^ m := longPrefixMass_le _ _
    _ ≤ Real.exp (2 * (Real.log B + C)) / (2 : ℝ) ^ m :=
      div_le_div_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum (by norm_num))) (by positivity)
    _ ≤ _ := htail m hm

end ErdosPrimeInputs.LongPrimePaths



namespace ErdosPrimeInputs.HighPrimeGeometry

open _root_.Finset
open HarmonicPrimeMeasure PrimePrefixMass

noncomputable def remainingGap (r₀ w : ℝ) (l : List ℕ) : ℝ :=
  r₀ - (l.map (primeExponent w)).sum

def cutoff (x : ℕ → ℝ) : ℝ → List ℕ → ℝ
  | B, [] => B
  | _, p :: ps => cutoff x (x p) ps

noncomputable def primeCutoff (w B : ℝ) (l : List ℕ) : ℝ := cutoff (primeExponent w) B l

lemma cutoff_append (x : ℕ → ℝ) (B : ℝ) (pre suf : List ℕ) :
    cutoff x B (pre ++ suf) = cutoff x (cutoff x B pre) suf := by
  induction pre generalizing B with
  | nil => rfl
  | cons p pre ih => exact ih (x p)

lemma cutoff_eq_lastD (x : ℕ → ℝ) (B : ℝ) (l : List ℕ) :
    cutoff x B l = (l.map x).getLastD B := by
  induction l generalizing B with
  | nil => rfl
  | cons p l ih =>
    cases l with
    | nil => rfl
    | cons q l => simpa [cutoff, List.getLastD] using ih (x p)

lemma remainingGap_append (r₀ w : ℝ) (pre suf : List ℕ) :
    remainingGap r₀ w (pre ++ suf) = remainingGap (remainingGap r₀ w pre) w suf := by
  simp only [remainingGap, List.map_append, List.sum_append]
  ring

lemma exponent_monotone {w : ℝ} (hw : 1 < w) : Monotone (primeExponent w) := by
  intro p q hpq
  have hlogw : 0 ≤ Real.log w := (Real.log_pos hw).le
  by_cases hp : p = 0
  · subst p
    simp only [primeExponent, Nat.cast_zero, Real.log_zero, zero_div]
    exact div_nonneg (Real.log_natCast_nonneg q) hlogw
  · have hp0 : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    exact div_le_div_of_nonneg_right (Real.log_le_log hp0 (by exact_mod_cast hpq)) hlogw

lemma cutoff_lower (x : ℕ → ℝ) {ell B : ℝ} (hB : ell ≤ B) (l : List ℕ)
    (hl : ∀ p ∈ l, ell ≤ x p) : ell ≤ cutoff x B l := by
  induction l generalizing B with
  | nil => exact hB
  | cons p l ih =>
    exact ih (hl p (by simp)) (fun q hq => hl q (by simp [hq]))

lemma suffix_le_cutoff (x : ℕ → ℝ) (hx : Monotone x) (B : ℝ) (pre suf : List ℕ)
    (hdec : (pre ++ suf).Pairwise (· > ·))
    (hB : ∀ p ∈ pre ++ suf, x p ≤ B) :
    ∀ p ∈ suf, x p ≤ cutoff x B pre := by
  induction pre generalizing B with
  | nil => exact hB
  | cons q pre ih =>
    have hp := List.pairwise_cons.mp hdec
    apply ih (x q) hp.2
    intro p hmem
    exact hx (le_of_lt (hp.1 p hmem))

lemma sum_exponents_le (x : ℕ → ℝ) (l : List ℕ) (b : ℝ)
    (hl : ∀ p ∈ l, x p ≤ b) : (l.map x).sum ≤ (l.length : ℝ) * b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have ht := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

lemma prime_exponent_bounds {w ell B : ℝ} (hw : 1 < w) {p : ℕ}
    (hp : p ∈ primesBetween (w ^ ell) (w ^ B)) :
    ell < primeExponent w p ∧ primeExponent w p ≤ B := by
  obtain ⟨hp, hlow⟩ := Finset.mem_filter.mp hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
  have hhigh : (p : ℝ) ≤ w ^ B :=
    (Nat.le_floor_iff (Real.rpow_pos_of_pos (lt_trans zero_lt_one hw) B).le).mp (Nat.mem_primesLE.mp hp).1
  exact ⟨(lt_exponent_iff hw hp0).mpr hlow, (exponent_le_iff hw hp0).mpr hhigh⟩

noncomputable def hasHighState (r₀ w B S : ℝ) (l : List ℕ) : Prop :=
  ∃ pre suf : List ℕ, l = pre ++ suf ∧
    S < remainingGap r₀ w pre / primeCutoff w B pre

theorem high_short_gap {r₀ w B ell S : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) {l : List ℕ}
    (hl : l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)))
    (hhigh : hasHighState r₀ w B S l) (hshort : (l.length : ℝ) < S / 2) :
    S * ell / 2 < remainingGap r₀ w l := by
  obtain ⟨pre, suf, rfl, hh⟩ := hhigh
  obtain ⟨hdec, hmem⟩ := mem_decreasingPrefixes.mp hl
  have hB : ∀ p ∈ pre ++ suf, primeExponent w p ≤ B := fun p hp =>
    (prime_exponent_bounds hw (hmem p hp)).2
  have hlow : ∀ p ∈ pre, ell ≤ primeExponent w p := fun p hp =>
    (prime_exponent_bounds hw (hmem p (List.mem_append_left _ hp))).1.le
  have hb : ell ≤ primeCutoff w B pre := cutoff_lower (primeExponent w) hellB pre hlow
  have hb0 : 0 < primeCutoff w B pre := lt_of_lt_of_le hell hb
  have hcut := suffix_le_cutoff (primeExponent w) (exponent_monotone hw) B pre suf hdec hB
  have hsum := sum_exponents_le (primeExponent w) suf (primeCutoff w B pre) hcut
  have hlen : (suf.length : ℝ) ≤ (List.length (pre ++ suf) : ℝ) := by
    simp only [List.length_append, Nat.cast_add]
    linarith [Nat.cast_nonneg (α := ℝ) pre.length]
  have hmul := mul_le_mul_of_nonneg_right hlen hb0.le
  have hshortmul := mul_lt_mul_of_pos_right hshort hb0
  have hbase := mul_le_mul_of_nonneg_left hb hS
  have hh := (lt_div_iff₀ hb0).mp hh
  rw [remainingGap_append]
  unfold remainingGap
  change S * primeCutoff w B pre < r₀ - (pre.map (primeExponent w)).sum at hh
  nlinarith

theorem high_small_gap_long {r₀ w B ell S K : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hK : K ≤ S * ell / 2) {l : List ℕ}
    (hl : l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)))
    (hhigh : hasHighState r₀ w B S l) (hgap : remainingGap r₀ w l ≤ K) :
    S / 2 ≤ (l.length : ℝ) := by
  by_contra h
  have hs := high_short_gap hw hell hellB hS hl hhigh (lt_of_not_ge h)
  linarith

end ErdosPrimeInputs.HighPrimeGeometry



namespace ErdosPrimeInputs.HighPrimeMass

open _root_.Finset
open PrimePrefixMass PrimePrefixTail HighPrimeGeometry

noncomputable def lowGapHighMass (r₀ w B ell S K : ℝ) : ℝ := by
  classical
  exact ∑ l ∈ (decreasingPrefixes (primesBetween (w ^ ell) (w ^ B))).filter
    (fun l => remainingGap r₀ w l ≤ K ∧ hasHighState r₀ w B S l), prefixWeight l

noncomputable def rewardedHighMass (r₀ w B ell S c : ℝ) : ℝ := by
  classical
  exact ∑ l ∈ (decreasingPrefixes (primesBetween (w ^ ell) (w ^ B))).filter
    (fun l => hasHighState r₀ w B S l ∧ 0 ≤ remainingGap r₀ w l),
      prefixWeight l * Real.exp (-c * remainingGap r₀ w l)

theorem lowGapHighMass_le_long {r₀ w B ell S K : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hK : K ≤ S * ell / 2) :
    lowGapHighMass r₀ w B ell S K ≤
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈S / 2⌉₊ := by
  classical
  unfold lowGapHighMass longPrefixMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro l hl
    obtain ⟨hl, hgap, hhigh⟩ := Finset.mem_filter.mp hl
    exact Finset.mem_filter.mpr ⟨hl, Nat.ceil_le.mpr
      (high_small_gap_long hw hell hellB hS hK hl hhigh hgap)⟩
  · intro l hl hnot
    exact prefixWeight_nonneg l

theorem rewardedHighMass_le {r₀ w B ell S c : ℝ} (hw : 1 < w) (hell : 0 < ell)
    (hellB : ell ≤ B) (hS : 0 ≤ S) (hc : 0 < c) :
    rewardedHighMass r₀ w B ell S c ≤
      longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈S / 2⌉₊ +
      (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) *
        Real.exp (-c * (S * ell / 2)) := by
  classical
  simp only [rewardedHighMass, longPrefixMass, Finset.sum_filter]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro l hl
  have hwgt := prefixWeight_nonneg l
  have he := (Real.exp_pos (-c * (S * ell / 2))).le
  by_cases hcond : hasHighState r₀ w B S l ∧ 0 ≤ remainingGap r₀ w l
  · rw [ite_eq_left hcond]
    by_cases hlong : ⌈S / 2⌉₊ ≤ l.length
    · rw [ite_eq_left hlong]
      have hexp : Real.exp (-c * remainingGap r₀ w l) ≤ 1 :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hcond.2)
      have hmul := mul_le_mul_of_nonneg_left hexp hwgt
      have hn := mul_nonneg hwgt he
      linarith
    · rw [ite_eq_right hlong, zero_add]
      have hshort : (l.length : ℝ) < S / 2 := Nat.lt_ceil.mp (lt_of_not_ge hlong)
      have hgap := high_short_gap hw hell hellB hS hl hcond.1 hshort
      apply mul_le_mul_of_nonneg_left _ hwgt
      apply Real.exp_le_exp.mpr
      nlinarith
  · rw [ite_eq_right hcond]
    apply add_nonneg
    · split_ifs <;> positivity
    · exact mul_nonneg hwgt he

end ErdosPrimeInputs.HighPrimeMass



namespace ErdosPrimeInputs.HighPrimeRemoval

open _root_.Filter Asymptotics
open scoped Topology
open PrimePrefixMass PrimePrefixTail LongPrimePaths HighPrimeGeometry HighPrimeMass

lemma lowGapHighMass_nonneg (r₀ w B ell S K : ℝ) : 0 ≤ lowGapHighMass r₀ w B ell S K := by
  classical
  unfold lowGapHighMass
  exact Finset.sum_nonneg (fun l _ => prefixWeight_nonneg l)

lemma rewardedHighMass_nonneg (r₀ w B ell S c : ℝ) : 0 ≤ rewardedHighMass r₀ w B ell S c := by
  classical
  unfold rewardedHighMass
  exact Finset.sum_nonneg (fun l _ => mul_nonneg (prefixWeight_nonneg l) (Real.exp_pos _).le)

lemma large_gap_saving {c : ℝ} (hc : 0 < c) (A : ℝ) : ∀ᶠ B : ℝ in atTop,
    B * Real.exp (-c * ((Real.log B) ^ 2 / 2)) ≤ B ^ (-A) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (2 * (A + 1) / c)))] with B hB hL
  have hb0 : 0 < B := lt_trans zero_lt_one hB
  have hl0 : 0 ≤ Real.log B := le_trans zero_le_one (le_trans (le_max_left _ _) hL)
  have ht : 2 * (A + 1) ≤ Real.log B * c :=
    (div_le_iff₀ hc).mp (le_trans (le_max_right _ _) hL)
  have hm := mul_le_mul_of_nonneg_right ht hl0
  have he : Real.log B + (-c * ((Real.log B) ^ 2 / 2)) ≤ Real.log B * (-A) := by nlinarith
  calc
    _ = Real.exp (Real.log B + (-c * ((Real.log B) ^ 2 / 2))) := by
      rw [Real.exp_add, Real.exp_log hb0]
    _ ≤ Real.exp (Real.log B * (-A)) := Real.exp_le_exp.mpr he
    _ = _ := (Real.rpow_def_of_pos hb0 (-A)).symm

theorem low_gap_high_removal : ∃ w₀ : ℝ, 1 < w₀ ∧
    ∀ K : ℝ, 0 < K → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ r₀ : ℝ,
        lowGapHighMass r₀ w B ell ((Real.log B) ^ 2) K ≤ B ^ (-A) := by
  obtain ⟨w₀, hw₀, htail⟩ := long_prime_paths_superpolynomial
  refine ⟨w₀, hw₀, ?_⟩
  intro K hK A
  filter_upwards [htail A,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2 * K + 1))] with B hB hlog
  intro w hw ell hell hellB r₀
  have hw1 : 1 < w := lt_of_lt_of_le hw₀ hw
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hsmall : K ≤ (Real.log B) ^ 2 / 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hell (sq_nonneg (Real.log B))
  have hsmall' : K ≤ (Real.log B) ^ 2 * ell / 2 := by nlinarith
  exact (lowGapHighMass_le_long hw1 hell0 hellB (sq_nonneg _) hsmall').trans
    (hB w hw ell hell hellB _ (Nat.le_ceil _))

theorem rewarded_high_removal : ∃ M w₀ : ℝ, 0 < M ∧ 1 < w₀ ∧
    ∀ c : ℝ, 0 < c → ∀ A : ℝ, ∀ᶠ B : ℝ in atTop,
      ∀ w : ℝ, w₀ ≤ w → ∀ ell : ℝ, 1 ≤ ell → ell ≤ B → ∀ r₀ : ℝ,
        rewardedHighMass r₀ w B ell ((Real.log B) ^ 2) c ≤ M * B ^ (-A) := by
  obtain ⟨M, wMass, hM, hwMass, hmass⟩ := total_prime_prefix_mass
  obtain ⟨wTail, hwTail, htail⟩ := long_prime_paths_superpolynomial
  refine ⟨1 + M, max wMass wTail, by positivity, lt_of_lt_of_le hwMass (le_max_left _ _), ?_⟩
  intro c hc A
  filter_upwards [htail A, large_gap_saving hc A] with B htailB hrewardB
  intro w hw ell hell hellB r₀
  have hwM : wMass ≤ w := le_trans (le_max_left _ _) hw
  have hwT : wTail ≤ w := le_trans (le_max_right _ _) hw
  have hw1 : 1 < w := lt_of_lt_of_le hwMass hwM
  have hell0 : 0 < ell := lt_of_lt_of_le zero_lt_one hell
  have hB0 : 0 < B := lt_of_lt_of_le hell0 hellB
  have hmassB : (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) ≤ M * B :=
    (hmass w hwM ell B hell hellB).trans (div_le_self (mul_nonneg hM.le hB0.le) hell)
  have hE : Real.exp (-c * ((Real.log B) ^ 2 * ell / 2)) ≤
      Real.exp (-c * ((Real.log B) ^ 2 / 2)) := by
    have hp := mul_le_mul_of_nonneg_left hell (sq_nonneg (Real.log B))
    apply Real.exp_le_exp.mpr
    nlinarith
  calc
    _ ≤ longPrefixMass (primesBetween (w ^ ell) (w ^ B)) ⌈(Real.log B) ^ 2 / 2⌉₊ +
        (∑ l ∈ decreasingPrefixes (primesBetween (w ^ ell) (w ^ B)), prefixWeight l) *
          Real.exp (-c * ((Real.log B) ^ 2 * ell / 2)) :=
      rewardedHighMass_le hw1 hell0 hellB (sq_nonneg _) hc
    _ ≤ B ^ (-A) + (M * B) * Real.exp (-c * ((Real.log B) ^ 2 / 2)) := by
      apply add_le_add
      · exact htailB w hwT ell hell hellB _ (Nat.le_ceil _)
      · exact mul_le_mul hmassB hE (Real.exp_pos _).le (mul_nonneg hM.le hB0.le)
    _ ≤ B ^ (-A) + M * B ^ (-A) := by
      apply add_le_add le_rfl
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hrewardB hM.le
    _ = (1 + M) * B ^ (-A) := by ring

end ErdosPrimeInputs.HighPrimeRemoval


end Erdos970

end OAI
