import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Renewal.DickmanFiniteDecay

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.LinearSieveFunctions

open MeasureTheory Filter
open scoped Topology

noncomputable def plus : ℝ → ℝ := DelayConstruction.delay 1

theorem plus_continuous : Continuous plus := DelayConstruction.delay_continuous 1

theorem plus_initial {u : ℝ} (hu : u ≤ 1) : plus u = 1 := DelayConstruction.delay_initial 1 hu

noncomputable def f (A s : ℝ) : ℝ :=
  if s ≤ 2 then 0 else A * (plus (s - 1) - Dickman.rho (s - 1)) / (2 * s)

noncomputable def F (A s : ℝ) : ℝ :=
  A * (plus (s - 1) + Dickman.rho (s - 1)) / (2 * s)

noncomputable def startingExtension (A s : ℝ) : ℝ := A * Real.log (s - 1) / s

theorem f_initial (A : ℝ) {s : ℝ} (hs : s ≤ 2) : f A s = 0 := by simp only [f, ite_eq_left hs]

theorem f_eq_difference (A s : ℝ) :
    f A s = A * (plus (s - 1) - Dickman.rho (s - 1)) / (2 * s) := by
  by_cases hs : s ≤ 2
  · rw [f_initial A hs, plus_initial (by linarith), Dickman.rho_initial (by linarith)]
    simp
  · simp only [f, ite_eq_right hs]

theorem plus_add_rho_initial {u : ℝ} (hu : u ≤ 2) : plus u + Dickman.rho u = 2 := by
  change DelayConstruction.delay 1 u + DelayConstruction.delay (-1) u = 2
  rw [DelayConstruction.delay_eq_stepApprox 1 1 (by norm_num; exact hu),
    DelayConstruction.delay_eq_stepApprox (-1) 1 (by norm_num; exact hu)]
  simp only [DelayConstruction.stepApprox, DelayConstruction.kernel, one_mul, neg_one_mul]
  ring

theorem mass_f (A : ℝ) {s : ℝ} (hs : s ≠ 0) :
    s * f A s = (A / 2) * (plus (s - 1) - Dickman.rho (s - 1)) := by
  rw [f_eq_difference]
  field_simp

theorem mass_F (A : ℝ) {s : ℝ} (hs : s ≠ 0) :
    s * F A s = (A / 2) * (plus (s - 1) + Dickman.rho (s - 1)) := by
  unfold F
  field_simp

theorem F_initial (A : ℝ) {s : ℝ} (hs0 : 0 < s) (hs3 : s ≤ 3) : F A s = A / s := by
  unfold F
  rw [plus_add_rho_initial (by linarith)]
  field_simp

theorem f_continuousAt_of_ne_zero (A : ℝ) {s : ℝ} (hs : s ≠ 0) : ContinuousAt (f A) s := by
  have hnum : Continuous (fun x : ℝ => A * (plus (x - 1) - Dickman.rho (x - 1))) :=
    continuous_const.mul ((plus_continuous.comp (continuous_id.sub continuous_const)).sub
      (Dickman.rho_continuous.comp (continuous_id.sub continuous_const)))
  have hraw : ContinuousAt (fun x : ℝ => A * (plus (x - 1) - Dickman.rho (x - 1)) / (2 * x)) s :=
    hnum.continuousAt.div (continuous_const.mul continuous_id).continuousAt (by exact mul_ne_zero (by norm_num) hs)
  exact (continuousAt_congr (Filter.Eventually.of_forall (f_eq_difference A))).mpr hraw

theorem f_continuous (A : ℝ) : Continuous (f A) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  by_cases hs : s = 0
  · subst s
    have heq : f A =ᶠ[𝓝 0] (fun _ => 0) := by
      filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2)] with x hx
      exact f_initial A hx.le
    exact (continuousAt_congr heq).mpr continuous_const.continuousAt
  · exact f_continuousAt_of_ne_zero A hs

theorem F_continuousAt (A : ℝ) {s : ℝ} (hs : s ≠ 0) : ContinuousAt (F A) s := by
  have hnum : Continuous (fun x : ℝ => A * (plus (x - 1) + Dickman.rho (x - 1))) :=
    continuous_const.mul ((plus_continuous.comp (continuous_id.sub continuous_const)).add
      (Dickman.rho_continuous.comp (continuous_id.sub continuous_const)))
  exact hnum.continuousAt.div (continuous_const.mul continuous_id).continuousAt (mul_ne_zero (by norm_num) hs)

theorem gap_identity (A : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    F A s - f A s = A * Dickman.rho (s - 1) / s := by
  rw [f_eq_difference]
  unfold F
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

theorem mass_f_hasDerivAt (A : ℝ) {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * f A x) (F A (s - 1)) s := by
  have hp : HasDerivAt plus (plus (s - 1 - 1) / (s - 1)) (s - 1) := by
    simpa only [plus, one_mul] using DelayConstruction.delay_hasDerivAt 1 (u := s - 1) (by linarith)
  have hpShift := hp.comp s ((hasDerivAt_id s).sub_const 1)
  have hrShift := (Dickman.rho_hasDerivAt (u := s - 1) (by linarith)).comp s ((hasDerivAt_id s).sub_const 1)
  have hraw := (hpShift.sub hrShift).const_mul (A / 2)
  have heq : (fun x => x * f A x) =ᶠ[𝓝 s]
      (fun x => (A / 2) * (plus (x - 1) - Dickman.rho (x - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 0 < s by linarith)] with x hx
    exact mass_f A (ne_of_gt hx)
  have hd := hraw.congr_of_eventuallyEq heq
  convert! hd using 1
  unfold F
  field_simp
  ring

theorem mass_F_hasDerivAt (A : ℝ) {s : ℝ} (hs : 2 < s) :
    HasDerivAt (fun x => x * F A x) (f A (s - 1)) s := by
  have hp : HasDerivAt plus (plus (s - 1 - 1) / (s - 1)) (s - 1) := by
    simpa only [plus, one_mul] using DelayConstruction.delay_hasDerivAt 1 (u := s - 1) (by linarith)
  have hpShift := hp.comp s ((hasDerivAt_id s).sub_const 1)
  have hrShift := (Dickman.rho_hasDerivAt (u := s - 1) (by linarith)).comp s ((hasDerivAt_id s).sub_const 1)
  have hraw := (hpShift.add hrShift).const_mul (A / 2)
  have heq : (fun x => x * F A x) =ᶠ[𝓝 s]
      (fun x => (A / 2) * (plus (x - 1) + Dickman.rho (x - 1))) := by
    filter_upwards [Ioi_mem_nhds (show 0 < s by linarith)] with x hx
    exact mass_F A (ne_of_gt hx)
  have hd := hraw.congr_of_eventuallyEq heq
  convert! hd using 1
  rw [f_eq_difference]
  field_simp
  ring

theorem F_continuousOn (A : ℝ) : ContinuousOn (F A) (Set.Ioi 0) := by
  intro s hs
  exact (F_continuousAt A (ne_of_gt hs)).continuousWithinAt

theorem mass_F_initial (A : ℝ) {s : ℝ} (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : s * F A s = A := by
  rw [F_initial A (by linarith) hs3]
  field_simp

theorem mass_f_integral (A : ℝ) {s : ℝ} (hs : 2 ≤ s) :
    s * f A s = ∫ t in (2 : ℝ)..s, F A (t - 1) := by
  have hInt : IntervalIntegrable (fun t : ℝ => F A (t - 1)) volume 2 s := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [Set.uIcc_of_le hs] at ht
    have hF := F_continuousAt A (s := t - 1) (by linarith [ht.1])
    have hshift : ContinuousAt (fun x : ℝ => x - 1) t := (continuous_id.sub continuous_const).continuousAt
    exact (hF.comp (f := fun x : ℝ => x - 1) (x := t) hshift).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
    (continuous_id.mul (f_continuous A)).continuousOn
    (fun t ht => mass_f_hasDerivAt A ht.1) hInt
  simpa only [Pi.mul_apply, id_eq, f_initial A (le_refl 2), mul_zero, sub_zero] using hFTC.symm

theorem mass_F_integral (A : ℝ) {s : ℝ} (hs : 3 ≤ s) :
    s * F A s = A + ∫ t in (3 : ℝ)..s, f A (t - 1) := by
  have hcont : ContinuousOn (fun t : ℝ => t * F A t) (Set.Icc 3 s) := by
    intro t ht
    exact (continuousAt_id.mul (F_continuousAt A (by linarith [ht.1]))).continuousWithinAt
  have hshift : Continuous (fun x : ℝ => x - 1) := continuous_id.sub continuous_const
  have hInt : IntervalIntegrable (fun t : ℝ => f A (t - 1)) volume 3 s :=
    ((f_continuous A).comp hshift).intervalIntegrable 3 s
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs hcont
    (fun t ht => mass_F_hasDerivAt A (by linarith [ht.1])) hInt
  rw [mass_F_initial A (s := 3) (by norm_num) (le_refl 3)] at hFTC
  linarith

theorem f_first_formula (A : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    f A s = A * Real.log (s - 1) / s := by
  have hMass := mass_f_integral A hs2
  have hInt : (∫ t in (2 : ℝ)..s, F A (t - 1)) = A * Real.log (s - 1) := by
    calc
      (∫ t in (2 : ℝ)..s, F A (t - 1)) = ∫ t in (2 : ℝ)..s, A / (t - 1) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le hs2] at ht
        change F A (t - 1) = A / (t - 1)
        exact F_initial A (by linarith [ht.1]) (by linarith [ht.2])
      _ = ∫ t in (1 : ℝ)..s - 1, A / t := by
        simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
          intervalIntegral.integral_comp_sub_right (fun t : ℝ => A / t) 1 (a := 2) (b := s)
      _ = A * ∫ t in (1 : ℝ)..s - 1, 1 / t := by
        simp only [div_eq_mul_inv, one_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [integral_one_div_of_pos (by norm_num) (by linarith), div_one]
  rw [hInt] at hMass
  apply (eq_div_iff (show s ≠ 0 by linarith)).mpr
  nlinarith

theorem startingExtension_eq_f (A : ℝ) {s : ℝ} (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    startingExtension A s = f A s := (f_first_formula A hs2 hs4).symm

theorem gap_pos {A s : ℝ} (hA : 0 < A) (hs : 1 ≤ s) : 0 < F A s - f A s := by
  rw [gap_identity A hs]
  exact div_pos (mul_pos hA (Dickman.rho_pos _)) (by linarith)

end NumberTheoryLean.LinearSieveFunctions

end

end Erdos970

end OAI
