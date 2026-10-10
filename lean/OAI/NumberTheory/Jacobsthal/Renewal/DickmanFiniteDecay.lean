import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.DelayConstruction

open MeasureTheory Filter
open scoped Topology

noncomputable def kernel (f : ℝ → ℝ) (t : ℝ) : ℝ := f (t - 1) / max 1 t

theorem kernel_continuous {f : ℝ → ℝ} (hf : Continuous f) : Continuous (kernel f) := by
  apply Continuous.div (hf.comp (continuous_id.sub continuous_const)) (continuous_const.max continuous_id)
  intro t
  change max (1 : ℝ) t ≠ 0
  have h := le_max_left (1 : ℝ) t
  linarith

noncomputable def stepApprox (σ : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n + 1 => fun u => 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t

theorem stepApprox_continuous (σ : ℝ) (n : ℕ) : Continuous (stepApprox σ n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
      have hk := kernel_continuous ih
      have hInt : Continuous (fun u : ℝ => ∫ t in (1 : ℝ)..u, kernel (stepApprox σ n) t) :=
        (intervalIntegral.differentiable_integral_of_continuous hk).continuous
      exact continuous_const.add (continuous_const.mul (hInt.comp (continuous_const.max continuous_id)))

theorem stepApprox_initial (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ 1) : stepApprox σ n u = 1 := by
  cases n <;> simp [stepApprox, max_eq_left hu]

theorem stepApprox_succ_stable (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    stepApprox σ (n + 1) u = stepApprox σ n u := by
  induction n generalizing u with
  | zero => simp only [Nat.cast_zero, zero_add] at hu; simp [stepApprox, max_eq_left hu]
  | succ n ih =>
      change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ (n + 1)) t) =
        1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t)
      apply congrArg (fun I : ℝ => 1 + σ * I)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
      have hmax : max 1 u ≤ (n : ℝ) + 2 := by
        apply max_le
        · have hn0 := Nat.cast_nonneg (α := ℝ) n
          linarith
        · push_cast at hu
          linarith
      have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
      unfold kernel
      rw [ih htbound]

theorem stepApprox_stable (σ : ℝ) {n m : ℕ} (hnm : n ≤ m) {u : ℝ}
    (hu : u ≤ (n : ℝ) + 1) : stepApprox σ m u = stepApprox σ n u := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
      rw [stepApprox_succ_stable σ m, ih]
      have hcast : (n : ℝ) ≤ m := by exact_mod_cast hm
      linarith

noncomputable def delay (σ u : ℝ) : ℝ := stepApprox σ ⌈u⌉₊ u

theorem delay_eq_stepApprox (σ : ℝ) (n : ℕ) {u : ℝ} (hu : u ≤ (n : ℝ) + 1) :
    delay σ u = stepApprox σ n u := by
  unfold delay
  have hceil : u ≤ (⌈u⌉₊ : ℝ) + 1 := by have h := Nat.le_ceil u; linarith
  rcases le_total n ⌈u⌉₊ with h | h
  · exact stepApprox_stable σ h hu
  · exact (stepApprox_stable σ h hceil).symm

theorem delay_continuous (σ : ℝ) : Continuous (delay σ) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  let n := ⌈u⌉₊ + 1
  have hu : u < (n : ℝ) + 1 := by have h := Nat.le_ceil u; dsimp [n]; push_cast; linarith
  have heq : delay σ =ᶠ[𝓝 u] stepApprox σ n := by
    filter_upwards [Iio_mem_nhds hu] with x hx
    exact delay_eq_stepApprox σ n hx.le
  exact (continuousAt_congr heq).mpr (stepApprox_continuous σ n).continuousAt

theorem delay_initial (σ : ℝ) {u : ℝ} (hu : u ≤ 1) : delay σ u = 1 := by
  rw [delay_eq_stepApprox σ 0 (by simpa using hu)]
  rfl

theorem delay_integral (σ u : ℝ) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..max 1 u, kernel (delay σ) t := by
  let n := ⌈u⌉₊
  have hu : u ≤ (n : ℝ) := Nat.le_ceil u
  rw [delay_eq_stepApprox σ (n + 1) (by push_cast; linarith)]
  change 1 + σ * (∫ t in (1 : ℝ)..max 1 u, kernel (stepApprox σ n) t) = _
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (le_max_left (1 : ℝ) u)] at ht
  have hmax : max 1 u ≤ (n : ℝ) + 1 := max_le (by have hn0 := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith)
  have htbound : t - 1 ≤ (n : ℝ) + 1 := by linarith [ht.2]
  unfold kernel
  rw [delay_eq_stepApprox σ n htbound]

theorem delay_integral_of_one_le (σ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    delay σ u = 1 + σ * ∫ t in (1 : ℝ)..u, delay σ (t - 1) / t := by
  rw [delay_integral σ u, max_eq_right hu]
  apply congrArg (fun I : ℝ => 1 + σ * I)
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hu] at ht
  simp only [kernel, max_eq_right ht.1]

theorem delay_hasDerivAt (σ : ℝ) {u : ℝ} (hu : 1 < u) :
    HasDerivAt (delay σ) (σ * delay σ (u - 1) / u) u := by
  have hk := kernel_continuous (delay_continuous σ)
  have hInt := intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable 1 u)
    hk.aestronglyMeasurable.stronglyMeasurableAtFilter hk.continuousAt
  have hPrim := (hInt.const_mul σ).const_add 1
  have heq : delay σ =ᶠ[𝓝 u] (fun x => 1 + σ * ∫ t in (1 : ℝ)..x, kernel (delay σ) t) := by
    filter_upwards [Ioi_mem_nhds hu] with x hx
    rw [delay_integral σ x, max_eq_right hx.le]
  have hD := hPrim.congr_of_eventuallyEq heq
  simpa only [kernel, max_eq_right hu.le, mul_div_assoc] using hD

end NumberTheoryLean.DelayConstruction

end

section

namespace NumberTheoryLean.DelayUniqueness

theorem shifted_unique_upto (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    (n : ℕ) : ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → F u = G u := by
  induction n with
  | zero =>
      intro u hu1 hu2
      have hu : u ≤ 2 := by simpa only [Nat.cast_zero, zero_add] using hu2
      rw [hFinit u hu1 hu, hGinit u hu1 hu]
  | succ n ih =>
      intro u hu1 hun
      by_cases hu2 : u ≤ 2
      · rw [hFinit u hu1 hu2, hGinit u hu1 hu2]
      · have hu : 2 < u := lt_of_not_ge hu2
        rw [hFrec u hu, hGrec u hu]
        apply congrArg (fun I : ℝ => 1 + σ * I)
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
        change F t / t = G t / t
        rw [ih t ht.1 (by push_cast at hun; linarith [ht.2])]

theorem shifted_unique (σ : ℝ) (F G : ℝ → ℝ)
    (hFinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → F u = 1)
    (hGinit : ∀ u : ℝ, 1 ≤ u → u ≤ 2 → G u = 1)
    (hFrec : ∀ u : ℝ, 2 < u → F u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, F t / t)
    (hGrec : ∀ u : ℝ, 2 < u → G u = 1 + σ * ∫ t in (1 : ℝ)..u - 1, G t / t)
    {u : ℝ} (hu : 1 ≤ u) : F u = G u := by
  apply shifted_unique_upto σ F G hFinit hGinit hFrec hGrec ⌈u⌉₊ u hu
  have h := Nat.le_ceil u
  linarith

end NumberTheoryLean.DelayUniqueness

end

section

namespace NumberTheoryLean.Dickman

open MeasureTheory Filter
open scoped Topology

noncomputable def rho : ℝ → ℝ := DelayConstruction.delay (-1)

theorem rho_continuous : Continuous rho := DelayConstruction.delay_continuous (-1)

theorem rho_initial {u : ℝ} (hu : u ≤ 1) : rho u = 1 := DelayConstruction.delay_initial (-1) hu

theorem rho_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt rho (-rho (u - 1) / u) u := by
  simpa only [rho, neg_one_mul] using DelayConstruction.delay_hasDerivAt (-1) hu

theorem rho_delay_equation {u : ℝ} (hu : 1 < u) : u * deriv rho u = -rho (u - 1) := by
  rw [(rho_hasDerivAt hu).deriv]
  field_simp

theorem rho_integral {u : ℝ} (hu : 1 ≤ u) :
    rho u = 1 - ∫ t in (1 : ℝ)..u, rho (t - 1) / t := by
  simpa only [rho, neg_one_mul, sub_eq_add_neg] using DelayConstruction.delay_integral_of_one_le (-1) hu

theorem rho_first_interval {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) : rho u = 1 - Real.log u := by
  rw [rho_integral hu1]
  have hInt : (∫ t in (1 : ℝ)..u, rho (t - 1) / t) = ∫ t in (1 : ℝ)..u, 1 / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hu1] at ht
    change rho (t - 1) / t = 1 / t
    rw [rho_initial (by linarith [ht.2])]
  rw [hInt, integral_one_div_of_pos (by norm_num) (by linarith), div_one]

noncomputable def primitive (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, rho t

theorem primitive_continuous : Continuous primitive :=
  (intervalIntegral.differentiable_integral_of_continuous rho_continuous).continuous

theorem primitive_hasDerivAt (u : ℝ) : HasDerivAt primitive (rho u) u :=
  intervalIntegral.integral_hasDerivAt_right (rho_continuous.intervalIntegrable 0 u)
    rho_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter rho_continuous.continuousAt

noncomputable def identityDifference (u : ℝ) : ℝ := u * rho u - (primitive u - primitive (u - 1))

theorem identityDifference_continuous : Continuous identityDifference :=
  (continuous_id.mul rho_continuous).sub (primitive_continuous.sub
    (primitive_continuous.comp (continuous_id.sub continuous_const)))

theorem identityDifference_hasDerivAt {u : ℝ} (hu : 1 < u) :
    HasDerivAt identityDifference 0 u := by
  have hProd := (hasDerivAt_id u).mul (rho_hasDerivAt hu)
  have hShift := (primitive_hasDerivAt (u - 1)).comp u ((hasDerivAt_id u).sub_const 1)
  have hDiff := hProd.sub ((primitive_hasDerivAt u).sub hShift)
  have hvalue : (1 * rho u + id u * (-rho (u - 1) / u) - (rho u - rho (u - 1) * 1)) = 0 := by
    dsimp only [id_eq]
    field_simp
    ring
  rw [hvalue] at hDiff
  convert! hDiff using 1

theorem identityDifference_one : identityDifference 1 = 0 := by
  have hp1 : primitive 1 = 1 := by
    unfold primitive
    calc
      (∫ t in (0 : ℝ)..1, rho t) = ∫ _t in (0 : ℝ)..1, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        exact rho_initial ht.2
      _ = 1 := by simp
  have hp0 : primitive 0 = 0 := by simp [primitive]
  simp only [identityDifference, rho_initial (le_refl 1), one_mul, sub_self, hp1, hp0, sub_zero]

theorem rho_unit_integral {u : ℝ} (hu : 1 ≤ u) :
    u * rho u = ∫ t in u - 1..u, rho t := by
  have hzero : identityDifference u = 0 := by
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu
      identityDifference_continuous.continuousOn
      (fun x hx => identityDifference_hasDerivAt hx.1)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 1 u)
    simpa only [intervalIntegral.integral_zero, identityDifference_one, sub_zero] using hFTC.symm
  have hInt := intervalIntegral.integral_add_adjacent_intervals
    (rho_continuous.intervalIntegrable (μ := volume) 0 (u - 1)) (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  change primitive (u - 1) + (∫ t in u - 1..u, rho t) = primitive u at hInt
  unfold identityDifference at hzero
  linarith

theorem rho_antitone_segment (b : ℝ)
    (hprev : ∀ t : ℝ, 0 ≤ t → t ≤ b - 1 → 0 ≤ rho t) : AntitoneOn rho (Set.Icc 1 b) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 1 b) rho_continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (rho_hasDerivAt hx.1).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(rho_hasDerivAt hx.1).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hprev (x - 1) (by linarith [hx.1])
      (by linarith [hx.2]))) (by linarith [hx.1])

theorem rho_nonneg_upto (n : ℕ) : ∀ u : ℝ, 0 ≤ u → u ≤ (n : ℝ) + 1 → 0 ≤ rho u := by
  induction n with
  | zero =>
      intro u _ hu
      rw [rho_initial (by simpa only [Nat.cast_zero, zero_add] using hu)]
      norm_num
  | succ n ih =>
      intro u hu0 hu
      have hub : u ≤ (n : ℝ) + 2 := by push_cast at hu; linarith
      have hmono : AntitoneOn rho (Set.Icc 1 ((n : ℝ) + 2)) :=
        rho_antitone_segment _ (fun t ht0 htb => ih t ht0 (by linarith))
      by_cases hu1 : u ≤ 1
      · rw [rho_initial hu1]; norm_num
      · have hu1' : 1 < u := lt_of_not_ge hu1
        have hpoint : ∀ t ∈ Set.Icc (u - 1) u, rho u ≤ rho t := by
          intro t ht
          by_cases ht1 : 1 ≤ t
          · exact hmono ⟨ht1, ht.2.trans hub⟩ ⟨hu1'.le, hub⟩ ht.2
          · rw [rho_initial (le_of_not_ge ht1)]
            have h := hmono ⟨le_rfl, by linarith⟩ ⟨hu1'.le, hub⟩ hu1'.le
            simpa only [rho_initial (le_refl 1)] using h
        have hint := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
          (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho u) volume (u - 1) u)
          (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u) hpoint
        have hconst : (∫ _t in u - 1..u, rho u) = rho u := by simp
        rw [hconst, ← rho_unit_integral hu1'.le] at hint
        have hprod : 0 ≤ (u - 1) * rho u := by nlinarith
        exact nonneg_of_mul_nonneg_right hprod (by linarith)

theorem rho_nonneg (u : ℝ) : 0 ≤ rho u := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]; norm_num
  · apply rho_nonneg_upto ⌈u⌉₊ u (by linarith)
    have h := Nat.le_ceil u
    linarith

theorem rho_antitone : Antitone rho := by
  intro x y hxy
  by_cases hy : y ≤ 1
  · rw [rho_initial hy, rho_initial (hxy.trans hy)]
  · have hy1 : 1 < y := lt_of_not_ge hy
    have hmono := rho_antitone_segment y (fun t _ _ => rho_nonneg t)
    by_cases hx : x ≤ 1
    · rw [rho_initial hx]
      have h := hmono ⟨le_rfl, hy1.le⟩ ⟨hy1.le, le_rfl⟩ hy1.le
      simpa only [rho_initial (le_refl 1)] using h
    · exact hmono ⟨le_of_not_ge hx, hxy⟩ ⟨hy1.le, le_rfl⟩ hxy

theorem rho_half_step {u : ℝ} (hu : 1 ≤ u) : rho (u - 1 / 2) ≤ 2 * u * rho u := by
  have hconst := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u - 1 / 2)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1 / 2)) volume (u - 1) (u - 1 / 2))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) (u - 1 / 2))
    (fun t ht => rho_antitone ht.2)
  have hvalue : (∫ _t in u - 1..u - 1 / 2, rho (u - 1 / 2)) = (1 / 2 : ℝ) * rho (u - 1 / 2) := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  rw [hvalue] at hconst
  have hsub := intervalIntegral.integral_mono_interval (μ := volume)
    (a := u - 1) (b := u - 1 / 2) (c := u - 1) (d := u)
    le_rfl (by linarith) (by linarith)
    (Filter.Eventually.of_forall (fun t => rho_nonneg t))
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
  rw [← rho_unit_integral hu] at hsub
  nlinarith

theorem rho_lower_comparison {u : ℝ} (hu : 2 ≤ u) : rho (u - 1) ≤ 4 * u ^ 2 * rho u := by
  have h1 := rho_half_step (u := u) (by linarith)
  have h2 := rho_half_step (u := u - 1 / 2) (by linarith)
  have harg : u - 1 / 2 - 1 / 2 = u - 1 := by ring
  rw [harg] at h2
  calc
    rho (u - 1) ≤ 2 * (u - 1 / 2) * rho (u - 1 / 2) := h2
    _ ≤ 2 * (u - 1 / 2) * (2 * u * rho u) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = (4 * u * (u - 1 / 2)) * rho u := by ring
    _ ≤ 4 * u ^ 2 * rho u := mul_le_mul_of_nonneg_right (by nlinarith) (rho_nonneg u)

theorem rho_pos_initial {u : ℝ} (hu : u ≤ 2) : 0 < rho u := by
  by_cases hu1 : u ≤ 1
  · rw [rho_initial hu1]; norm_num
  · have hu1' : 1 < u := lt_of_not_ge hu1
    rw [rho_first_interval hu1'.le hu]
    have hlog2 : Real.log 2 < 1 := by
      have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) Real.exp_one_gt_two
      simpa only [Real.log_exp] using h
    have hlogu := Real.log_le_log (show 0 < u by linarith) hu
    linarith

theorem rho_pos_upto (n : ℕ) : ∀ u : ℝ, u ≤ (n : ℝ) + 2 → 0 < rho u := by
  induction n with
  | zero => intro u hu; exact rho_pos_initial (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      by_cases hu2 : u ≤ 2
      · exact rho_pos_initial hu2
      · have hu2' : 2 < u := lt_of_not_ge hu2
        have hprev : 0 < rho (u - 1) := ih (u - 1) (by push_cast at hu; linarith)
        have hbound := rho_lower_comparison hu2'.le
        by_contra hnot
        have hnonpos : rho u ≤ 0 := le_of_not_gt hnot
        have hprod := mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ 4 * u ^ 2 by positivity) hnonpos
        linarith

theorem rho_pos (u : ℝ) : 0 < rho u := by
  apply rho_pos_upto ⌈u⌉₊ u
  have h := Nat.le_ceil u
  linarith

theorem rho_upper_comparison {u : ℝ} (hu : 1 ≤ u) : u * rho u ≤ rho (u - 1) := by
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => rho (u - 1)) volume (u - 1) u)
    (fun t ht => rho_antitone ht.1)
  have hconst : (∫ _t in u - 1..u, rho (u - 1)) = rho (u - 1) := by simp
  rw [hconst, ← rho_unit_integral hu] at hInt
  exact hInt

theorem rho_ratio_bounds {u : ℝ} (hu : 2 ≤ u) :
    1 / (4 * u ^ 2) ≤ rho u / rho (u - 1) ∧ rho u / rho (u - 1) ≤ 1 / u := by
  have hprev : 0 < rho (u - 1) := rho_pos _
  have hu0 : 0 < u := by linarith
  constructor
  · apply (div_le_div_iff₀ (show 0 < 4 * u ^ 2 by positivity) hprev).mpr
    have h := rho_lower_comparison hu
    nlinarith
  · apply (div_le_div_iff₀ hprev hu0).mpr
    have h := rho_upper_comparison (u := u) (by linarith)
    nlinarith

end NumberTheoryLean.Dickman

end

section

namespace NumberTheoryLean.DickmanDecay

open MeasureTheory Filter
open scoped Topology
open Dickman

noncomputable def hazard (u : ℝ) : ℝ := rho (u - 1) / (u * rho u)

theorem hazard_eq_neg_deriv {u : ℝ} (hu : 1 < u) : hazard u = -deriv rho u / rho u := by
  rw [(rho_hasDerivAt hu).deriv]
  unfold hazard
  field_simp

theorem hazard_ge_one {u : ℝ} (hu : 2 ≤ u) : 1 ≤ hazard u := by
  unfold hazard
  apply (le_div_iff₀ (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  simpa only [one_mul] using rho_upper_comparison (u := u) (by linarith)

theorem deriv_le_of_hazard {u rate : ℝ} (hu : 1 < u) (hrate : rate ≤ hazard u) :
    deriv rho u ≤ -rate * rho u := by
  rw [hazard_eq_neg_deriv hu] at hrate
  have h := (le_div_iff₀ (rho_pos u)).mp hrate
  linarith

theorem rho_exponential_comparison (T rate a b : ℝ) (hT : 2 ≤ T)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (ha : T ≤ a) (hab : a ≤ b) :
    rho b ≤ rho a * Real.exp (-rate * (b - a)) := by
  let H : ℝ → ℝ := fun t => Real.exp (rate * t) * rho t
  have hCont : Continuous H :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul rho_continuous
  have hDeriv : ∀ t ∈ Set.Ioo a b,
      HasDerivAt H (Real.exp (rate * t) * (deriv rho t + rate * rho t)) t := by
    intro t ht
    have ht1 : 1 < t := by linarith [ht.1]
    have hExp := ((hasDerivAt_id t).const_mul rate).exp
    have hRho := (rho_hasDerivAt ht1).differentiableAt.hasDerivAt
    have hProd := hExp.mul hRho
    convert! hProd using 1
    simp only [id_eq, mul_one]
    ring
  have hMono : AntitoneOn H (Set.Icc a b) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc a b) hCont.continuousOn
    · intro t ht
      rw [interior_Icc] at ht
      exact (hDeriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hDeriv t ht).deriv]
      apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
      have hd := deriv_le_of_hazard (u := t) (rate := rate) (by linarith [ht.1]) (htail t (by linarith [ht.1]))
      linarith
  have hHb : H b ≤ H a := hMono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  have hQ : rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := by
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    dsimp [H] at hHb
    nlinarith
  calc
    rho b ≤ Real.exp (rate * a) * rho a / Real.exp (rate * b) := hQ
    _ = rho a * (Real.exp (rate * a) / Real.exp (rate * b)) := by ring
    _ = rho a * Real.exp (-rate * (b - a)) := by rw [← Real.exp_sub]; congr 1; congr 1; ring

theorem unit_exponential_integral (rate u : ℝ) (hrate : rate ≠ 0) :
    (∫ t in u - 1..u, Real.exp (-rate * (t - (u - 1)))) = (1 - Real.exp (-rate)) / rate := by
  rw [intervalIntegral.integral_comp_sub_right (fun t : ℝ => Real.exp (-rate * t)) (u - 1)]
  simp only [sub_self, sub_sub_cancel]
  rw [intervalIntegral.integral_comp_mul_left Real.exp (neg_ne_zero.mpr hrate), integral_exp]
  simp only [mul_zero, mul_one, Real.exp_zero, smul_eq_mul]
  field_simp
  ring

theorem hazard_bootstrap (T rate u : ℝ) (hT : 2 ≤ T) (hrate : 0 < rate)
    (htail : ∀ t : ℝ, T ≤ t → rate ≤ hazard t) (hu : T + 1 ≤ u) :
    rate / (1 - Real.exp (-rate)) ≤ hazard u := by
  have hu1 : 1 ≤ u := by linarith
  have hcomp : ∀ t ∈ Set.Icc (u - 1) u,
      rho t ≤ rho (u - 1) * Real.exp (-rate * (t - (u - 1))) := by
    intro t ht
    exact rho_exponential_comparison T rate (u - 1) t hT htail (by linarith) ht.1
  have hCont : Continuous (fun t : ℝ => rho (u - 1) * Real.exp (-rate * (t - (u - 1)))) := by fun_prop
  have hInt := intervalIntegral.integral_mono_on (by linarith : u - 1 ≤ u)
    (rho_continuous.intervalIntegrable (μ := volume) (u - 1) u)
    (hCont.intervalIntegrable (μ := volume) (u - 1) u) hcomp
  rw [← rho_unit_integral hu1, intervalIntegral.integral_const_mul,
    unit_exponential_integral rate u (ne_of_gt hrate)] at hInt
  have he : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  unfold hazard
  apply (div_le_div_iff₀ he (mul_pos (show 0 < u by linarith) (rho_pos u))).mpr
  rw [← mul_div_assoc] at hInt
  have hmul := (le_div_iff₀ hrate).mp hInt
  nlinarith

theorem bootstrap_uniform_gain (L rate : ℝ) (hrate1 : 1 ≤ rate) (hrateL : rate ≤ L) :
    rate + Real.exp (-L) ≤ rate / (1 - Real.exp (-rate)) := by
  have hrate0 : 0 < rate := by linarith
  have he0 : 0 < Real.exp (-rate) := Real.exp_pos _
  have hd0 : 0 < Real.exp (-L) := Real.exp_pos _
  have hle : Real.exp (-L) ≤ Real.exp (-rate) := Real.exp_le_exp.mpr (by linarith)
  have hden : 0 < 1 - Real.exp (-rate) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  apply (le_div_iff₀ hden).mpr
  nlinarith [mul_nonneg (show 0 ≤ rate - 1 by linarith) he0.le, mul_nonneg hd0.le he0.le]

theorem hazard_step_bound (L : ℝ) (hL : 1 ≤ L) (n : ℕ) :
    ∀ u : ℝ, (n : ℝ) + 2 ≤ u →
      min L (1 + (n : ℝ) * Real.exp (-L)) ≤ hazard u := by
  induction n with
  | zero =>
      intro u hu
      simp only [Nat.cast_zero, zero_mul, add_zero, min_eq_right hL]
      exact hazard_ge_one (by simpa only [Nat.cast_zero, zero_add] using hu)
  | succ n ih =>
      intro u hu
      let d := Real.exp (-L)
      let rate := min L (1 + (n : ℝ) * d)
      have hd : 0 < d := Real.exp_pos _
      have hr1 : 1 ≤ rate := le_min hL (by have hn := Nat.cast_nonneg (α := ℝ) n; nlinarith)
      have hrL : rate ≤ L := min_le_left _ _
      have htail : ∀ t : ℝ, (n : ℝ) + 2 ≤ t → rate ≤ hazard t := fun t ht => ih t ht
      have hboost := hazard_bootstrap ((n : ℝ) + 2) rate u
        (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by linarith) htail
        (by push_cast at hu; linarith)
      have hgain := bootstrap_uniform_gain L rate hr1 hrL
      have hstep : min L (1 + ((n + 1 : ℕ) : ℝ) * d) ≤ rate + d := by
        by_cases hcase : L ≤ 1 + (n : ℝ) * d
        · have hr : rate = L := min_eq_left hcase
          rw [hr]
          exact (min_le_left _ _).trans (by linarith)
        · have hr : rate = 1 + (n : ℝ) * d := min_eq_right (le_of_not_ge hcase)
          rw [hr]
          have hm := min_le_right L (1 + ((n + 1 : ℕ) : ℝ) * d)
          push_cast at hm ⊢
          linarith
      exact hstep.trans (hgain.trans hboost)

theorem exists_hazard_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ hazard u := by
  let L := max 1 rate
  let d := Real.exp (-L)
  have hL : 1 ≤ L := le_max_left _ _
  have hd : 0 < d := Real.exp_pos _
  obtain ⟨n, hn⟩ := exists_nat_ge ((L - 1) / d)
  have hreach : L ≤ 1 + (n : ℝ) * d := by
    have h := (div_le_iff₀ hd).mp hn
    linarith
  refine ⟨(n : ℝ) + 2, by have h := Nat.cast_nonneg (α := ℝ) n; linarith, ?_⟩
  intro u hu
  have h := hazard_step_bound L hL n u hu
  rw [min_eq_left hreach] at h
  exact (le_max_right 1 rate).trans h

theorem negative_logDeriv_tail (rate : ℝ) :
    ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u → rate ≤ -deriv rho u / rho u := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨T, hT, ?_⟩
  intro u hu
  rw [← hazard_eq_neg_deriv (by linarith : 1 < u)]
  exact htail u hu

theorem hazard_tendsto_atTop : Tendsto hazard atTop atTop := by
  apply tendsto_atTop.mpr
  intro rate
  obtain ⟨T, _, htail⟩ := exists_hazard_tail rate
  exact eventually_atTop.mpr ⟨T, htail⟩

theorem rho_exponential_majorant (rate : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 2 ≤ T ∧ ∀ u : ℝ, T ≤ u →
      rho u ≤ C * Real.exp (-rate * u) := by
  obtain ⟨T, hT, htail⟩ := exists_hazard_tail rate
  refine ⟨rho T * Real.exp (rate * T), mul_pos (rho_pos T) (Real.exp_pos _), T, hT, ?_⟩
  intro u hu
  have h := rho_exponential_comparison T rate T u hT htail le_rfl hu
  have heq : Real.exp (-rate * (u - T)) = Real.exp (rate * T) * Real.exp (-rate * u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq] at h
  simpa only [mul_assoc] using h

theorem rho_faster_than_exponential (rate : ℝ) :
    Tendsto (fun u : ℝ => Real.exp (rate * u) * rho u) atTop (𝓝 0) := by
  obtain ⟨C, hC, T, _, hbound⟩ := rho_exponential_majorant (rate + 1)
  have hUpper : (fun u : ℝ => Real.exp (rate * u) * rho u) ≤ᶠ[atTop]
      (fun u => C * Real.exp (-u)) := by
    apply eventually_atTop.mpr
    refine ⟨T, ?_⟩
    intro u hu
    have h := mul_le_mul_of_nonneg_left (hbound u hu) (Real.exp_pos (rate * u)).le
    have heq : Real.exp (rate * u) * (C * Real.exp (-(rate + 1) * u)) = C * Real.exp (-u) := by
      calc
        _ = C * (Real.exp (rate * u) * Real.exp (-(rate + 1) * u)) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 1; congr 1; ring
    rw [heq] at h
    exact h
  have hLower : (0 : ℝ → ℝ) ≤ᶠ[atTop] (fun u : ℝ => Real.exp (rate * u) * rho u) :=
    Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (rho_nonneg u))
  have hLimit : Tendsto (fun u : ℝ => C * Real.exp (-u)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C
  exact squeeze_zero' hLower hUpper hLimit

theorem rho_tendsto_zero : Tendsto rho atTop (𝓝 0) := by
  simpa only [zero_mul, Real.exp_zero, one_mul] using rho_faster_than_exponential 0

end NumberTheoryLean.DickmanDecay

end

section

namespace NumberTheoryLean.DickmanFiniteDecay

open Dickman

theorem rho_le_one (u : ℝ) : rho u ≤ 1 := by
  by_cases hu : u ≤ 1
  · rw [rho_initial hu]
  · have h := rho_antitone (le_of_lt (lt_of_not_ge hu))
    simpa only [rho_initial (le_refl (1:ℝ))] using h

theorem rho_step_power {t u : ℝ} (ht : 1 ≤ t) (htu : t ≤ u) (n : ℕ) :
    t^n*rho (u+(n:ℝ)) ≤ rho u := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
    have hh := rho_upper_comparison (u := u+(n:ℝ)+1) (by linarith)
    have hs : t*rho (u+(n:ℝ)+1) ≤ rho (u+(n:ℝ)) := by
      have hm := mul_le_mul_of_nonneg_right (show t ≤ u+(n:ℝ)+1 by linarith)
        (rho_nonneg (u+(n:ℝ)+1))
      simp only [add_sub_cancel_right] at hh
      exact hm.trans hh
    have hmul := mul_le_mul_of_nonneg_left hs (pow_nonneg (by linarith : 0 ≤ t) n)
    push_cast
    rw [pow_succ]
    simpa only [add_assoc,mul_assoc] using hmul.trans ih

theorem rho_half_power {u : ℝ} (hu : 2 ≤ u) :
    rho u ≤ 1/(u/2)^⌊u/2⌋₊ := by
  have hu0 : 0 < u := by linarith
  have hf := Nat.floor_le (by linarith : 0 ≤ u/2)
  have hh := rho_step_power (t := u/2) (u := u-(⌊u/2⌋₊:ℝ))
    (by linarith) (by linarith) ⌊u/2⌋₊
  simp only [sub_add_cancel] at hh
  apply (le_div_iff₀ (pow_pos (by linarith : 0 < u/2) _)).mpr
  rw [mul_comm]
  exact hh.trans (rho_le_one _)

theorem rho_log_decay {u : ℝ} (hu : 8 ≤ u) :
    rho u ≤ Real.exp (-(1/16:ℝ)*u*Real.log (u+2)) := by
  have hu0 : 0 < u := by linarith
  have ht0 : 0 < u/2 := by linarith
  have hn : u/4 ≤ (⌊u/2⌋₊:ℝ) := by
    have hf := Nat.lt_floor_add_one (u/2)
    linarith
  have hl0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
  have hlh : Real.log u/2 ≤ Real.log (u/2) := by
    have hm := Real.log_le_log hu0 (show u ≤ (u/2)^2 by nlinarith)
    rw [Real.log_pow] at hm
    norm_num only [Nat.cast_ofNat] at hm
    linarith
  have hl2 : Real.log (u+2) ≤ 2*Real.log u := by
    have hm := Real.log_le_log (show 0 < u+2 by linarith) (show u+2 ≤ u^2 by nlinarith)
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hpow : (1/16:ℝ)*u*Real.log (u+2) ≤ (⌊u/2⌋₊:ℝ)*Real.log (u/2) := by
    have hm := mul_le_mul hn hlh (by linarith : 0 ≤ Real.log u/2) (Nat.cast_nonneg ⌊u/2⌋₊)
    nlinarith [mul_le_mul_of_nonneg_left hl2 hu0.le]
  calc
    _ ≤ 1/(u/2)^⌊u/2⌋₊ := rho_half_power (by linarith)
    _ = Real.exp (-(⌊u/2⌋₊:ℝ)*Real.log (u/2)) := by
      rw [neg_mul,Real.exp_neg,Real.exp_nat_mul,Real.exp_log ht0]
      exact one_div _
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)

end NumberTheoryLean.DickmanFiniteDecay

end

end Erdos970

end OAI
