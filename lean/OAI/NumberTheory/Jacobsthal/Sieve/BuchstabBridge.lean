import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.RoughRecursion
import OAI.NumberTheory.Jacobsthal.Renewal.LaplaceODE
import OAI.NumberTheory.Jacobsthal.Sieve.LinearSieveFunctions

namespace OAI

namespace Erdos970

section

open scoped Interval
open MeasureTheory
open Filter

namespace ErdosAverageCertificates

noncomputable section

noncomputable def buchstabStage : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, u =>
      if u ≤ 2 then 1
      else 1 + ∫ t in 1..u - 1, buchstabStage n t / t

@[simp] theorem buchstabStage_zero (u : ℝ) : buchstabStage 0 u = 1 := rfl

theorem buchstabStage_succ_eq_one {n : ℕ} {u : ℝ} (hu : u ≤ 2) :
    buchstabStage (n + 1) u = 1 := by
  simp [buchstabStage, hu]

theorem buchstabStage_succ_eq_integral {n : ℕ} {u : ℝ} (hu : 2 < u) :
    buchstabStage (n + 1) u =
      1 + ∫ t in 1..u - 1, buchstabStage n t / t := by
  rw [buchstabStage, ite_eq_right (not_le_of_gt hu)]

theorem buchstabStage_succ_eq_stage {n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hun : u ≤ n + 2) :
    buchstabStage (n + 1) u = buchstabStage n u := by
  induction n generalizing u with
  | zero =>
      have hu2 : u ≤ 2 := by simpa using hun
      simp [buchstabStage, hu2]
  | succ n ih =>
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · have hu2' : 2 < u := lt_of_not_ge hu2
        rw [buchstabStage_succ_eq_integral hu2',
          buchstabStage_succ_eq_integral hu2']
        congr 1
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
          simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
        have htupper : t ≤ n + 2 := by
          norm_num at hun ⊢
          linarith [ht'.2]
        change buchstabStage (n + 1) t / t = buchstabStage n t / t
        rw [ih ht'.1 htupper]

theorem buchstabStage_eq_of_le {m n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hum : u ≤ m + 2) (hmn : m ≤ n) :
    buchstabStage n u = buchstabStage m u := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      have hun : u ≤ n + 2 := by
        exact hum.trans (by exact_mod_cast Nat.add_le_add_right hmn 2)
      rw [buchstabStage_succ_eq_stage hu1 hun, ih]

noncomputable def buchstabAux (u : ℝ) : ℝ :=
  if u < 1 then 0 else buchstabStage ⌈u⌉₊ u

noncomputable def buchstabFunction (u : ℝ) : ℝ :=
  if u < 1 then 0 else buchstabAux u / u

theorem buchstabAux_eq_stage {n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hun : u ≤ n + 2) :
    buchstabAux u = buchstabStage n u := by
  rw [buchstabAux, ite_eq_right (not_lt_of_ge hu1)]
  let k : ℕ := max ⌈u⌉₊ n
  have huceil : u ≤ (⌈u⌉₊ : ℝ) + 2 :=
    (Nat.le_ceil u).trans (by norm_num)
  have hceilk : ⌈u⌉₊ ≤ k := le_max_left _ _
  have hnk : n ≤ k := le_max_right _ _
  calc
    buchstabStage ⌈u⌉₊ u = buchstabStage k u :=
      (buchstabStage_eq_of_le hu1 huceil hceilk).symm
    _ = buchstabStage n u := buchstabStage_eq_of_le hu1 hun hnk

theorem buchstabFunction_eq_aux_div {u : ℝ} (hu : 1 ≤ u) :
    buchstabFunction u = buchstabAux u / u := by
  rw [buchstabFunction, ite_eq_right (not_lt_of_ge hu)]

theorem buchstabFunction_eq_stage_div {n : ℕ} {u : ℝ}
    (hu1 : 1 ≤ u) (hun : u ≤ n + 2) :
    buchstabFunction u = buchstabStage n u / u := by
  rw [buchstabFunction_eq_aux_div hu1, buchstabAux_eq_stage hu1 hun]

theorem buchstabAux_eq_one {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    buchstabAux u = 1 := by
  simpa using buchstabAux_eq_stage (n := 0) hu1 (by simpa using hu2)

theorem buchstabFunction_eq_inv {u : ℝ} (hu1 : 1 ≤ u) (hu2 : u ≤ 2) :
    buchstabFunction u = u⁻¹ := by
  rw [buchstabFunction_eq_aux_div hu1, buchstabAux_eq_one hu1 hu2]
  exact one_div u

theorem mul_buchstabFunction {u : ℝ} (hu : 1 ≤ u) :
    u * buchstabFunction u = buchstabAux u := by
  rw [buchstabFunction_eq_aux_div hu]
  field_simp [show u ≠ 0 by linarith]

theorem buchstabAux_eq_one_add_integral {u : ℝ} (hu : 2 < u) :
    buchstabAux u = 1 + ∫ t in 1..u - 1, buchstabFunction t := by
  let n : ℕ := ⌈u⌉₊
  have hu1 : 1 ≤ u := by linarith
  have hun : u ≤ ((n + 1 : ℕ) : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    norm_num at hceil ⊢
    linarith
  rw [buchstabAux_eq_stage hu1 hun,
    buchstabStage_succ_eq_integral hu]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  have htn : t ≤ (n : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    linarith [ht'.2]
  change buchstabStage n t / t = buchstabFunction t
  rw [← buchstabAux_eq_stage ht'.1 htn,
    ← buchstabFunction_eq_aux_div ht'.1]

theorem mul_buchstabFunction_eq_one_add_integral {u : ℝ} (hu : 2 < u) :
    u * buchstabFunction u =
      1 + ∫ t in 1..u - 1, buchstabFunction t := by
  rw [mul_buchstabFunction (by linarith), buchstabAux_eq_one_add_integral hu]

private noncomputable def buchstabStageIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  buchstabStage n (max t 1) / max t 1

private theorem integral_buchstabStageIntegrand_eq {n : ℕ} {u : ℝ}
    (hu : 2 ≤ u) :
    (∫ t in 1..u - 1, buchstabStageIntegrand n t) =
      ∫ t in 1..u - 1, buchstabStage n t / t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  simp [buchstabStageIntegrand, max_eq_left ht'.1]

private theorem continuous_buchstabStage : ∀ n : ℕ,
    Continuous (buchstabStage n)
  | 0 => by exact continuous_const
  | n + 1 => by
      have hstage := continuous_buchstabStage n
      have hmax : Continuous (fun t : ℝ ↦ max t 1) :=
        continuous_id.max continuous_const
      have hmax0 : ∀ t : ℝ, max t 1 ≠ 0 := fun t ↦ by
        have : (1 : ℝ) ≤ max t 1 := le_max_right _ _
        linarith
      have hint : Continuous (buchstabStageIntegrand n) := by
        unfold buchstabStageIntegrand
        exact (hstage.comp hmax).div hmax (hmax0)
      have hright : Continuous (fun u : ℝ ↦
          1 + ∫ t in 1..u - 1, buchstabStageIntegrand n t) := by
        have hprimitive : Continuous (fun v : ℝ ↦
            ∫ t in 1..v, buchstabStageIntegrand n t) :=
          (intervalIntegral.differentiable_integral_of_continuous hint).continuous
        exact continuous_const.add
          (hprimitive.comp (continuous_id.sub continuous_const))
      rw [show buchstabStage (n + 1) = fun u : ℝ ↦
          if u ≤ 2 then 1
          else 1 + ∫ t in 1..u - 1, buchstabStageIntegrand n t by
        funext u
        by_cases hu : u ≤ 2
        · simp [buchstabStage, hu]
        · rw [buchstabStage, ite_eq_right hu,
            integral_buchstabStageIntegrand_eq (le_of_not_ge hu)]
          simp [hu] ]
      apply continuous_if_le continuous_id continuous_const
      · exact continuous_const.continuousOn
      · exact hright.continuousOn
      · rintro u rfl
        norm_num

theorem continuousOn_buchstabAux : ContinuousOn buchstabAux (Set.Ici 1) := by
  intro u hu
  let n : ℕ := ⌈u⌉₊
  have huBound : u < (n : ℝ) + 2 := by
    dsimp [n]
    have hceil := Nat.le_ceil u
    linarith
  have hlocal : ∀ᶠ v in nhdsWithin u (Set.Ici (1 : ℝ)),
      buchstabAux v = buchstabStage n v := by
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds huBound),
      eventually_mem_nhdsWithin] with v hvBound hv1
    exact buchstabAux_eq_stage hv1 hvBound.le
  exact (continuous_buchstabStage n).continuousAt.continuousWithinAt.congr_of_eventuallyEq
    hlocal (buchstabAux_eq_stage hu huBound.le)

theorem continuousOn_buchstabFunction :
    ContinuousOn buchstabFunction (Set.Ici 1) := by
  have hdiv : ContinuousOn (fun u ↦ buchstabAux u / u) (Set.Ici (1 : ℝ)) :=
    continuousOn_buchstabAux.div continuousOn_id fun u hu ↦ by
      change 1 ≤ u at hu
      linarith
  exact hdiv.congr fun u hu ↦ buchstabFunction_eq_aux_div hu

private noncomputable def buchstabContinuousExtension (t : ℝ) : ℝ :=
  buchstabFunction (max t 1)

private theorem continuous_buchstabContinuousExtension :
    Continuous buchstabContinuousExtension := by
  have hmax : Continuous (fun t : ℝ ↦ max t 1) :=
    continuous_id.max continuous_const
  unfold buchstabContinuousExtension
  simpa only [Function.comp_def] using
    continuousOn_buchstabFunction.comp_continuous hmax
      (fun t ↦ le_max_right t 1)

private theorem integral_buchstabContinuousExtension_eq {u : ℝ} (hu : 2 ≤ u) :
    (∫ t in 1..u - 1, buchstabContinuousExtension t) =
      ∫ t in 1..u - 1, buchstabFunction t := by
  apply intervalIntegral.integral_congr
  intro t ht
  have ht' : t ∈ Set.Icc (1 : ℝ) (u - 1) := by
    simpa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] using ht
  simp [buchstabContinuousExtension, max_eq_left ht'.1]

theorem hasDerivAt_buchstabAux {u : ℝ} (hu : 2 < u) :
    HasDerivAt buchstabAux (buchstabFunction (u - 1)) u := by
  have hext := continuous_buchstabContinuousExtension
  have hprim := intervalIntegral.integral_hasDerivAt_right
    (a := (1 : ℝ)) (b := u - 1)
    (hext.intervalIntegrable _ _)
    hext.aestronglyMeasurable.stronglyMeasurableAtFilter hext.continuousAt
  have hcomp := hprim.comp u ((hasDerivAt_id u).sub_const 1)
  have hright : HasDerivAt
      (fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t)
      (buchstabContinuousExtension (u - 1)) u := by
    have h := hcomp.const_add 1
    change HasDerivAt
      (fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t)
      (buchstabContinuousExtension (u - 1) * 1) u at h
    simpa only [mul_one] using h
  have heq : buchstabAux =ᶠ[nhds u]
      fun v : ℝ ↦ 1 + ∫ t in 1..v - 1, buchstabContinuousExtension t := by
    filter_upwards [Ioi_mem_nhds hu] with v hv
    rw [buchstabAux_eq_one_add_integral hv,
      integral_buchstabContinuousExtension_eq hv.le]
  have h := hright.congr_of_eventuallyEq heq
  simpa [buchstabContinuousExtension, max_eq_left (by linarith : (1 : ℝ) ≤ u - 1)] using h

theorem hasDerivAt_mul_buchstabFunction {u : ℝ} (hu : 2 < u) :
    HasDerivAt (fun v ↦ v * buchstabFunction v)
      (buchstabFunction (u - 1)) u := by
  have heq : (fun v : ℝ ↦ v * buchstabFunction v) =ᶠ[nhds u] buchstabAux := by
    filter_upwards [Ioi_mem_nhds (show 1 < u by linarith)] with v hv
    exact mul_buchstabFunction hv.le
  exact (hasDerivAt_buchstabAux hu).congr_of_eventuallyEq heq

theorem hasDerivAt_buchstabFunction {u : ℝ} (hu : 2 < u) :
    HasDerivAt buchstabFunction
      ((buchstabFunction (u - 1) - buchstabFunction u) / u) u := by
  have hu0 : u ≠ 0 := by linarith
  have hquot := (hasDerivAt_buchstabAux hu).div (hasDerivAt_id u) hu0
  have hEq : ∀ᶠ v in nhds u, buchstabFunction v = buchstabAux v / v := by
    filter_upwards [Ioi_mem_nhds (show 1 < u by linarith)] with v hv
    exact buchstabFunction_eq_aux_div hv.le
  have h := hquot.congr_of_eventuallyEq hEq
  apply h.congr_deriv
  dsimp only [id_eq, one_mul]
  rw [← mul_buchstabFunction (show 1 ≤ u by linarith)]
  field_simp

private theorem buchstabStage_nonneg : ∀ n : ℕ, ∀ {u : ℝ}, 1 ≤ u →
    0 ≤ buchstabStage n u
  | 0, _, _ => by simp [buchstabStage]
  | n + 1, u, hu => by
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · rw [buchstabStage_succ_eq_integral (lt_of_not_ge hu2)]
        have hInt : 0 ≤ ∫ t in 1..u - 1, buchstabStage n t / t := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro t ht
          have ht1 : 1 ≤ t := by linarith [ht.1]
          exact div_nonneg (buchstabStage_nonneg n ht1) (by linarith)
        linarith

private theorem buchstabStage_one_le : ∀ n : ℕ, ∀ {u : ℝ}, 1 ≤ u →
    1 ≤ buchstabStage n u
  | 0, _, _ => by simp [buchstabStage]
  | n + 1, u, hu => by
      by_cases hu2 : u ≤ 2
      · simp [buchstabStage, hu2]
      · rw [buchstabStage_succ_eq_integral (lt_of_not_ge hu2)]
        have hInt : 0 ≤ ∫ t in 1..u - 1, buchstabStage n t / t := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro t ht
          have ht1 : 1 ≤ t := by linarith [ht.1]
          exact div_nonneg (buchstabStage_nonneg n ht1) (by linarith)
        linarith

theorem buchstabAux_one_le {u : ℝ} (hu : 1 ≤ u) :
    1 ≤ buchstabAux u := by
  rw [buchstabAux_eq_stage (n := ⌈u⌉₊) hu
    ((Nat.le_ceil u).trans (by norm_num))]
  exact buchstabStage_one_le _ hu

theorem buchstabFunction_nonneg {u : ℝ} (hu : 1 ≤ u) :
    0 ≤ buchstabFunction u := by
  rw [buchstabFunction_eq_aux_div hu]
  exact div_nonneg (buchstabAux_one_le hu |>.trans' zero_le_one) (by linarith)

theorem inv_le_buchstabFunction {u : ℝ} (hu : 1 ≤ u) :
    u⁻¹ ≤ buchstabFunction u := by
  rw [buchstabFunction_eq_aux_div hu, inv_eq_one_div]
  exact div_le_div_of_nonneg_right (buchstabAux_one_le hu) (by linarith)

private theorem buchstabFunction_le_one_induction : ∀ n : ℕ,
    ∀ {u : ℝ}, 1 ≤ u → u ≤ n + 2 → buchstabFunction u ≤ 1
  | 0, u, hu1, hu2 => by
      rw [buchstabFunction_eq_inv hu1 (by simpa using hu2)]
      exact inv_le_one_of_one_le₀ hu1
  | n + 1, u, hu1, huN => by
      by_cases hu2 : u ≤ 2
      · rw [buchstabFunction_eq_inv hu1 hu2]
        exact inv_le_one_of_one_le₀ hu1
      · have hu2' : 2 < u := lt_of_not_ge hu2
        rw [buchstabFunction_eq_aux_div hu1,
          buchstabAux_eq_one_add_integral hu2']
        rw [div_le_iff₀ (by linarith : 0 < u)]
        have hInt : (∫ t in 1..u - 1, buchstabFunction t) ≤ u - 2 := by
          have hcont : ContinuousOn buchstabFunction (Set.Icc (1 : ℝ) (u - 1)) :=
            continuousOn_buchstabFunction.mono (by
              intro t ht
              exact ht.1)
          calc
            (∫ t in 1..u - 1, buchstabFunction t) ≤
                ∫ _t in 1..u - 1, (1 : ℝ) := by
              apply intervalIntegral.integral_mono_on (by linarith)
              · exact ContinuousOn.intervalIntegrable (by
                  rwa [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)])
              · exact continuousOn_const.intervalIntegrable
              · intro t ht
                have ht1 : 1 ≤ t := ht.1
                have htu : t ≤ n + 2 := by
                  norm_num at huN ⊢
                  linarith [ht.2]
                exact buchstabFunction_le_one_induction n ht1 htu
            _ = u - 2 := by simp; ring
        linarith

theorem buchstabFunction_le_one {u : ℝ} (hu : 1 ≤ u) :
    buchstabFunction u ≤ 1 := by
  let n : ℕ := ⌈u⌉₊
  apply buchstabFunction_le_one_induction n hu
  dsimp [n]
  exact (Nat.le_ceil u).trans (by norm_num)

theorem abs_buchstabFunction_le_one {u : ℝ} (hu : 1 ≤ u) :
    |buchstabFunction u| ≤ 1 := by
  rw [abs_of_nonneg (buchstabFunction_nonneg hu)]
  exact buchstabFunction_le_one hu

theorem norm_deriv_mul_buchstabFunction_le_one {u : ℝ} (hu : 2 < u) :
    ‖deriv (fun v ↦ v * buchstabFunction v) u‖ ≤ 1 := by
  rw [(hasDerivAt_mul_buchstabFunction hu).deriv]
  simpa only [Real.norm_eq_abs] using
    abs_buchstabFunction_le_one (show 1 ≤ u - 1 by linarith)

theorem abs_deriv_buchstabFunction_le_two_div {u : ℝ} (hu : 2 < u) :
    |deriv buchstabFunction u| ≤ 2 / u := by
  rw [(hasDerivAt_buchstabFunction hu).deriv, abs_div,
    abs_of_pos (by linarith : 0 < u)]
  have hnum : |buchstabFunction (u - 1) - buchstabFunction u| ≤ 2 := by
    calc
      |buchstabFunction (u - 1) - buchstabFunction u| ≤
          |buchstabFunction (u - 1)| + |buchstabFunction u| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add
        (abs_buchstabFunction_le_one (by linarith))
        (abs_buchstabFunction_le_one (by linarith))
      _ = 2 := by norm_num
  exact div_le_div_of_nonneg_right hnum (by linarith)

theorem abs_buchstabFunction_sub_shift_le_two_div {u : ℝ} (hu : 3 < u) :
    |buchstabFunction u - buchstabFunction (u - 1)| ≤ 2 / (u - 1) := by
  have hdiff : ∀ x ∈ Set.Icc (u - 1) u,
      DifferentiableAt ℝ buchstabFunction x := by
    intro x hx
    exact (hasDerivAt_buchstabFunction (by linarith [hx.1])).differentiableAt
  have hbound : ∀ x ∈ Set.Icc (u - 1) u,
      ‖deriv buchstabFunction x‖ ≤ 2 / (u - 1) := by
    intro x hx
    rw [Real.norm_eq_abs]
    calc
      |deriv buchstabFunction x| ≤ 2 / x :=
        abs_deriv_buchstabFunction_le_two_div (by linarith [hx.1])
      _ ≤ 2 / (u - 1) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by linarith) hx.1
  have hmv := (convex_Icc (u - 1) u).norm_image_sub_le_of_norm_deriv_le
    hdiff hbound (Set.left_mem_Icc.mpr (by linarith))
      (Set.right_mem_Icc.mpr (by linarith))
  convert hmv using 1; norm_num

theorem abs_deriv_buchstabFunction_le_two_div_mul_sub_one {u : ℝ}
    (hu : 3 < u) :
    |deriv buchstabFunction u| ≤ 2 / (u * (u - 1)) := by
  rw [(hasDerivAt_buchstabFunction (by linarith)).deriv, abs_div,
    abs_of_pos (by linarith : 0 < u)]
  have h := abs_buchstabFunction_sub_shift_le_two_div hu
  rw [abs_sub_comm] at h
  calc
    |buchstabFunction (u - 1) - buchstabFunction u| / u ≤
        (2 / (u - 1)) / u :=
      div_le_div_of_nonneg_right h (by linarith)
    _ = 2 / (u * (u - 1)) := by
      field_simp [show u ≠ 0 by linarith, show u - 1 ≠ 0 by linarith]

theorem continuousOn_deriv_buchstabFunction :
    ContinuousOn (deriv buchstabFunction) (Set.Ioi 2) := by
  have hω : ContinuousOn buchstabFunction (Set.Ioi (2 : ℝ)) :=
    continuousOn_buchstabFunction.mono (Set.Ioi_subset_Ici_self.trans
      (Set.Ici_subset_Ici.mpr (by norm_num)))
  have hshift : ContinuousOn (fun u : ℝ ↦ buchstabFunction (u - 1))
      (Set.Ioi 2) := by
    apply continuousOn_buchstabFunction.comp
      (continuousOn_id.sub continuousOn_const)
    intro u hu
    change 1 ≤ u - 1
    linarith [Set.mem_Ioi.mp hu]
  have hformula : ContinuousOn
      (fun u : ℝ ↦ (buchstabFunction (u - 1) - buchstabFunction u) / u)
      (Set.Ioi 2) :=
    (hshift.sub hω).div continuousOn_id fun u hu ↦ by
      exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu])
  exact hformula.congr fun u hu ↦
    (hasDerivAt_buchstabFunction (Set.mem_Ioi.mp hu)).deriv

theorem integrableOn_deriv_buchstabFunction :
    IntegrableOn (deriv buchstabFunction) (Set.Ioi 3) := by
  have hmodel : IntegrableOn
      (fun x : ℝ ↦ 2 * (x + (-1)) ^ (-2 : ℝ)) (Set.Ioi 3) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (3 : ℝ))
      (m := (-1 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  apply hmodel.mono'
  · exact (continuousOn_deriv_buchstabFunction.mono
      (Set.Ioi_subset_Ioi (by norm_num))).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx3 : 3 < x := Set.mem_Ioi.mp hx
    rw [Real.norm_eq_abs]
    calc
      |deriv buchstabFunction x| ≤ 2 / (x * (x - 1)) :=
        abs_deriv_buchstabFunction_le_two_div_mul_sub_one hx3
      _ ≤ 2 / ((x - 1) * (x - 1)) := by
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (by linarith) (by linarith))
          (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      _ = 2 * (x + (-1)) ^ (-2 : ℝ) := by
        rw [show x + (-1) = x - 1 by ring,
          show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num,
          Real.rpow_intCast]
        norm_num [div_eq_mul_inv, zpow_neg]
        field_simp [show x - 1 ≠ 0 by linarith]

noncomputable def buchstabLimit : ℝ :=
  limUnder atTop buchstabFunction

theorem tendsto_buchstabFunction_atTop :
    Tendsto buchstabFunction atTop (nhds buchstabLimit) := by
  exact tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
    (a := (3 : ℝ))
    (fun x hx ↦ ((hasDerivAt_buchstabFunction
      (by linarith [Set.mem_Ioi.mp hx])).differentiableAt).hasDerivAt)
    integrableOn_deriv_buchstabFunction

theorem buchstabLimit_nonneg : 0 ≤ buchstabLimit := by
  apply ge_of_tendsto tendsto_buchstabFunction_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  exact buchstabFunction_nonneg hu

theorem buchstabLimit_le_one : buchstabLimit ≤ 1 := by
  apply le_of_tendsto tendsto_buchstabFunction_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
  exact buchstabFunction_le_one hu

theorem abs_buchstabFunction_sub_le_two_div_sub_one {u v : ℝ}
    (hu : 3 < u) (huv : u ≤ v) :
    |buchstabFunction v - buchstabFunction u| ≤ 2 / (u - 1) := by
  let g : ℝ → ℝ := fun t ↦ 2 / ((t - 1) * (t - 1))
  let G : ℝ → ℝ := fun t ↦ -2 / (t - 1)
  have hderivCont : ContinuousOn (deriv buchstabFunction) (Set.Icc u v) :=
    continuousOn_deriv_buchstabFunction.mono (by
      intro t ht
      exact Set.mem_Ioi.mpr (by linarith [ht.1]))
  have hderivInt : IntervalIntegrable (deriv buchstabFunction) volume u v := by
    rw [← Set.uIcc_of_le huv] at hderivCont
    exact hderivCont.intervalIntegrable
  have hFTC : (∫ t in u..v, deriv buchstabFunction t) =
      buchstabFunction v - buchstabFunction u := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      have ht' : t ∈ Set.Icc u v := by simpa [Set.uIcc_of_le huv] using ht
      exact ((hasDerivAt_buchstabFunction
        (by linarith [ht'.1])).differentiableAt).hasDerivAt
    · exact hderivInt
  have hgCont : ContinuousOn g (Set.Icc u v) := by
    unfold g
    apply continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).mul
        (continuousOn_id.sub continuousOn_const))
    intro t ht
    change (t - 1) * (t - 1) ≠ 0
    exact mul_ne_zero (by linarith [ht.1]) (by linarith [ht.1])
  have hgInt : IntervalIntegrable g volume u v := by
    rw [← Set.uIcc_of_le huv] at hgCont
    exact hgCont.intervalIntegrable
  have hmono : (∫ t in u..v, |deriv buchstabFunction t|) ≤
      ∫ t in u..v, g t := by
    apply intervalIntegral.integral_mono_on huv hderivInt.norm hgInt
    intro t ht
    have ht3 : 3 < t := by linarith [ht.1]
    calc
      |deriv buchstabFunction t| ≤ 2 / (t * (t - 1)) :=
        abs_deriv_buchstabFunction_le_two_div_mul_sub_one ht3
      _ ≤ 2 / ((t - 1) * (t - 1)) := by
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (by linarith) (by linarith))
          (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      _ = g t := rfl
  have hGderiv : ∀ t ∈ Set.uIcc u v, HasDerivAt G (g t) t := by
    intro t ht
    have ht' : t ∈ Set.Icc u v := by simpa [Set.uIcc_of_le huv] using ht
    have ht0 : t - 1 ≠ 0 := by linarith [ht'.1]
    dsimp only [G, g]
    have h := (hasDerivAt_const t (-2 : ℝ)).div
      ((hasDerivAt_id t).sub_const 1) ht0
    have hfun : HasDerivAt (fun x : ℝ ↦ -2 / (x - 1))
        ((0 * (t - 1) - -2 * 1) / (t - 1) ^ 2) t := by
      apply h.congr_of_eventuallyEq
      filter_upwards with x
      rfl
    apply hfun.congr_deriv
    norm_num [pow_two]
  have hgEval : (∫ t in u..v, g t) = G v - G u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hGderiv hgInt
  calc
    |buchstabFunction v - buchstabFunction u| =
        |∫ t in u..v, deriv buchstabFunction t| := by rw [hFTC]
    _ ≤ ∫ t in u..v, |deriv buchstabFunction t| :=
      intervalIntegral.abs_integral_le_integral_abs huv
    _ ≤ ∫ t in u..v, g t := hmono
    _ = G v - G u := hgEval
    _ ≤ 2 / (u - 1) := by
      dsimp [G]
      have hv : 0 ≤ 2 / (v - 1) := div_nonneg (by norm_num) (by linarith)
      calc
        -2 / (v - 1) - -2 / (u - 1) =
            2 / (u - 1) - 2 / (v - 1) := by ring
        _ ≤ 2 / (u - 1) := sub_le_self _ hv

theorem abs_buchstabFunction_sub_limit_le_two_div_sub_one {u : ℝ}
    (hu : 3 < u) :
    |buchstabFunction u - buchstabLimit| ≤ 2 / (u - 1) := by
  have ht : Tendsto (fun v : ℝ ↦
      |buchstabFunction v - buchstabFunction u|) atTop
      (nhds |buchstabLimit - buchstabFunction u|) :=
    (tendsto_buchstabFunction_atTop.sub tendsto_const_nhds).abs
  have hle : |buchstabLimit - buchstabFunction u| ≤ 2 / (u - 1) := by
    apply le_of_tendsto ht
    filter_upwards [eventually_ge_atTop u] with v hv
    exact abs_buchstabFunction_sub_le_two_div_sub_one hu hv
  simpa only [abs_sub_comm] using hle

theorem integrableOn_buchstabFunction_sub_limit_div :
    IntegrableOn (fun u : ℝ ↦
      (buchstabFunction u - buchstabLimit) / u) (Set.Ioi 3) := by
  have hmodel : IntegrableOn
      (fun x : ℝ ↦ 2 * (x + (-1)) ^ (-2 : ℝ)) (Set.Ioi 3) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := (-2 : ℝ)) (c := (3 : ℝ))
      (m := (-1 : ℝ)) (by norm_num) (by norm_num)).const_mul 2
  apply hmodel.mono'
  · have hω : ContinuousOn buchstabFunction (Set.Ioi (3 : ℝ)) :=
      continuousOn_buchstabFunction.mono (by
        intro u hu
        exact Set.mem_Ici.mpr (by linarith [Set.mem_Ioi.mp hu]))
    have hcont : ContinuousOn (fun u : ℝ ↦
        (buchstabFunction u - buchstabLimit) / u) (Set.Ioi 3) := by
      apply (hω.sub continuousOn_const).div continuousOn_id
      intro u hu
      change u ≠ 0
      exact ne_of_gt (by linarith [Set.mem_Ioi.mp hu])
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx3 : 3 < x := Set.mem_Ioi.mp hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by linarith : 0 < x)]
    calc
      |buchstabFunction x - buchstabLimit| / x ≤
          (2 / (x - 1)) / x :=
        div_le_div_of_nonneg_right
          (abs_buchstabFunction_sub_limit_le_two_div_sub_one hx3)
          (by linarith)
      _ ≤ 2 / ((x - 1) * (x - 1)) := by
        rw [div_div]
        exact div_le_div_of_nonneg_left (by norm_num)
          (mul_pos (by linarith) (by linarith))
          (mul_le_mul_of_nonneg_left (by linarith) (by linarith))
      _ = 2 * (x + (-1)) ^ (-2 : ℝ) := by
        rw [show x + (-1) = x - 1 by ring,
          show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num,
          Real.rpow_intCast]
        norm_num [div_eq_mul_inv, zpow_neg]
        field_simp [show x - 1 ≠ 0 by linarith]

noncomputable def buchstabLaplace (s : ℝ) : ℝ :=
  ∫ u in Set.Ioi (1 : ℝ), buchstabFunction u * Real.exp (-s * u)

theorem measurable_buchstabFunction : Measurable buchstabFunction := by
  have hlow : ContinuousOn buchstabFunction (Set.Iio (1 : ℝ)) := by
    have hz : ∀ u ∈ Set.Iio (1 : ℝ), buchstabFunction u = 0 := by
      intro u hu
      rw [buchstabFunction, ite_eq_left (Set.mem_Iio.mp hu)]
    exact continuousOn_const.congr fun u hu ↦ hz u hu
  have hhigh : ContinuousOn buchstabFunction (Set.Ici (1 : ℝ)) :=
    continuousOn_buchstabFunction
  have hpiece : buchstabFunction = (Set.Ici (1 : ℝ)).piecewise
      buchstabFunction (fun _ ↦ 0) := by
    funext u
    by_cases hu : 1 ≤ u
    · simp [hu]
    · simp [Set.piecewise, hu, buchstabFunction, lt_of_not_ge hu]
  rw [hpiece]
  exact hhigh.measurable_piecewise
    (continuousOn_const.mono (by
      intro u hu
      exact Set.mem_Iio.mpr (lt_of_not_ge hu))) measurableSet_Ici

theorem integrableOn_buchstabLaplace_integrand {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      buchstabFunction u * Real.exp (-s * u)) (Set.Ioi 1) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u)) (Set.Ioi 1) :=
    exp_neg_integrableOn_Ioi 1 hs
  apply hexp.mono'
  · have hprod : Measurable (fun u : ℝ ↦
        buchstabFunction u * Real.exp (-s * u)) :=
      measurable_buchstabFunction.mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hprod.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (abs_buchstabFunction_le_one (Set.mem_Ioi.mp hu).le)

private theorem integrableOn_id_mul_exp_neg_mul {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦ u * Real.exp (-s * u)) (Set.Ioi 1) := by
  let f : ℝ → ℝ := fun t ↦ Real.exp (-t) * t
  have hf : IntegrableOn f (Set.Ioi 0) := by
    have h := Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num)
    convert h using 1
    funext u
    norm_num [f, Real.rpow_one, mul_comm]
  have hcomp : IntegrableOn (fun u : ℝ ↦ f (s * u)) (Set.Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff f 0 hs).mpr (by simpa using hf)
  have hscaled : IntegrableOn (fun u : ℝ ↦ s⁻¹ * f (s * u)) (Set.Ioi 0) :=
    Integrable.const_mul hcomp s⁻¹
  have htarget : IntegrableOn (fun u : ℝ ↦
      u * Real.exp (-s * u)) (Set.Ioi 0) := by
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp [f]
    field_simp [hs.ne']
  exact htarget.mono_set (Set.Ioi_subset_Ioi (by norm_num))

private theorem integrableOn_buchstabLaplace_deriv_integrand {s : ℝ}
    (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      -u * buchstabFunction u * Real.exp (-s * u)) (Set.Ioi 1) := by
  have hmodel := integrableOn_id_mul_exp_neg_mul hs
  apply hmodel.mono'
  · have hm : Measurable (fun u : ℝ ↦
        -u * buchstabFunction u * Real.exp (-s * u)) :=
      (measurable_id.neg.mul measurable_buchstabFunction).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_neg, abs_of_pos (by linarith : 0 < u)]
    calc
      u * |buchstabFunction u| * Real.exp (-s * u) ≤
          u * 1 * Real.exp (-s * u) := by
        gcongr
        exact abs_buchstabFunction_le_one hu1
      _ = u * Real.exp (-s * u) := by ring

theorem hasDerivAt_buchstabLaplace {s : ℝ} (hs : 0 < s) :
    HasDerivAt buchstabLaplace
      (∫ u in Set.Ioi (1 : ℝ),
        -(u * buchstabFunction u * Real.exp (-s * u))) s := by
  let P : ℝ → ℝ → ℝ := fun x u ↦
    buchstabFunction u * Real.exp (-x * u)
  let P' : ℝ → ℝ → ℝ := fun x u ↦
    -u * buchstabFunction u * Real.exp (-x * u)
  let b : ℝ → ℝ := fun u ↦
    u * Real.exp (-(s / 2) * u)
  have hsHalf : 0 < s / 2 := by linarith
  have hnhds : Set.Ioi (s / 2) ∈ nhds s := Ioi_mem_nhds (by linarith)
  have hPmeas : ∀ᶠ x in nhds s,
      AEStronglyMeasurable (P x) (volume.restrict (Set.Ioi 1)) := by
    filter_upwards with x
    have hm : Measurable (P x) := by
      unfold P
      exact measurable_buchstabFunction.mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -x * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  have hPint : Integrable (P s) (volume.restrict (Set.Ioi 1)) := by
    change IntegrableOn (P s) (Set.Ioi 1)
    simpa [P] using integrableOn_buchstabLaplace_integrand hs
  have hP'meas : AEStronglyMeasurable (P' s)
      (volume.restrict (Set.Ioi 1)) := by
    have hm : Measurable (P' s) := by
      unfold P'
      exact (measurable_id.neg.mul measurable_buchstabFunction).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  have hbint : Integrable b (volume.restrict (Set.Ioi 1)) := by
    change IntegrableOn b (Set.Ioi 1)
    simpa [b] using integrableOn_id_mul_exp_neg_mul hsHalf
  have hbound : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ∀ x ∈ Set.Ioi (s / 2), ‖P' x u‖ ≤ b u := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    intro x hx
    have hu1 : 1 ≤ u := (Set.mem_Ioi.mp hu).le
    have hu0 : 0 ≤ u := zero_le_one.trans hu1
    have hexp : Real.exp (-x * u) ≤ Real.exp (-(s / 2) * u) := by
      apply Real.exp_le_exp.mpr
      nlinarith [Set.mem_Ioi.mp hx]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg hu0, abs_of_pos (Real.exp_pos _)]
    dsimp [P', b]
    calc
      u * |buchstabFunction u| * Real.exp (-x * u) ≤
          u * 1 * Real.exp (-x * u) := by
        gcongr
        exact abs_buchstabFunction_le_one hu1
      _ ≤ u * Real.exp (-(s / 2) * u) := by
        simpa using mul_le_mul_of_nonneg_left hexp hu0
  have hdiff : ∀ᵐ u ∂(volume.restrict (Set.Ioi 1)),
      ∀ x ∈ Set.Ioi (s / 2), HasDerivAt (P · u) (P' x u) x := by
    filter_upwards with u
    intro x hx
    have hexp : HasDerivAt (fun y : ℝ ↦ Real.exp (-y * u))
        (-u * Real.exp (-x * u)) x := by
      have hinner : HasDerivAt (fun y : ℝ ↦ -y * u) (-u) x := by
        simpa [mul_neg, neg_mul] using (hasDerivAt_id x).mul_const (-u)
      apply hinner.exp.congr_deriv
      ring
    dsimp [P, P']
    have hc := hexp.const_mul (buchstabFunction u)
    apply hc.congr_deriv
    ring
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := P) (x₀ := s) (s := Set.Ioi (s / 2)) (bound := b)
    hnhds hPmeas hPint hP'meas hbound hbint hdiff
  change HasDerivAt
    (fun n : ℝ ↦ ∫ u in Set.Ioi (1 : ℝ),
      buchstabFunction u * Real.exp (-n * u))
    (∫ u in Set.Ioi (1 : ℝ),
      -(u * buchstabFunction u * Real.exp (-s * u))) s
  simpa [P, P'] using hmain.2

theorem differentiableOn_buchstabLaplace :
    DifferentiableOn ℝ buchstabLaplace (Set.Ioi 0) := by
  intro s hs
  exact DifferentiableAt.differentiableWithinAt
    (hasDerivAt_buchstabLaplace (Set.mem_Ioi.mp hs)).differentiableAt

private theorem integrableOn_buchstabShift_mul_exp {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      buchstabFunction (u - 1) * Real.exp (-s * u)) (Set.Ioi 2) := by
  have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u)) (Set.Ioi 2) :=
    exp_neg_integrableOn_Ioi 2 hs
  apply hexp.mono'
  · have hm : Measurable (fun u : ℝ ↦
        buchstabFunction (u - 1) * Real.exp (-s * u)) :=
      (measurable_buchstabFunction.comp
        (measurable_id.sub measurable_const)).mul
        ((Real.continuous_exp.comp
          (show Continuous (fun u : ℝ ↦ -s * u) from
            continuous_const.mul continuous_id)).measurable)
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu1 : 1 ≤ u - 1 := by linarith [Set.mem_Ioi.mp hu]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (abs_buchstabFunction_le_one hu1)

private theorem integrableOn_mul_buchstab_mul_exp_deriv {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 2) := by
  have hbase := integrableOn_buchstabLaplace_deriv_integrand hs
  have hscaled : IntegrableOn (fun u : ℝ ↦
      s * (-u * buchstabFunction u * Real.exp (-s * u))) (Set.Ioi 1) :=
    Integrable.const_mul hbase s
  have hcongr : IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 1) := by
    apply hscaled.congr_fun _ measurableSet_Ioi
    intro u hu
    ring
  exact hcongr.mono_set (Set.Ioi_subset_Ioi (by norm_num))

theorem integral_mul_buchstab_mul_exp_Ioi_two {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Ioi (2 : ℝ),
      (u * buchstabFunction u) * Real.exp (-s * u)) =
      Real.exp (-s * 2) / s +
        (1 / s) * ∫ u in Set.Ioi (2 : ℝ),
          buchstabFunction (u - 1) * Real.exp (-s * u) := by
  let g : ℝ → ℝ := fun u ↦ u * buchstabFunction u
  let g' : ℝ → ℝ := fun u ↦ buchstabFunction (u - 1)
  let e : ℝ → ℝ := fun u ↦ Real.exp (-s * u)
  let e' : ℝ → ℝ := fun u ↦ -s * Real.exp (-s * u)
  have hg : ∀ u ∈ Set.Ioi (2 : ℝ), HasDerivAt g (g' u) u := by
    intro u hu
    exact hasDerivAt_mul_buchstabFunction (Set.mem_Ioi.mp hu)
  have he : ∀ u ∈ Set.Ioi (2 : ℝ), HasDerivAt e (e' u) u := by
    intro u hu
    dsimp [e, e']
    have hinner : HasDerivAt (fun x : ℝ ↦ -s * x) (-s) u := by
      simpa only [id_eq, mul_one] using (hasDerivAt_id u).const_mul (-s)
    apply hinner.exp.congr_deriv
    ring
  have hge' : IntegrableOn (g * e') (Set.Ioi (2 : ℝ)) := by
    change IntegrableOn (fun u : ℝ ↦
      (u * buchstabFunction u) * (-s * Real.exp (-s * u))) (Set.Ioi 2)
    exact integrableOn_mul_buchstab_mul_exp_deriv hs
  have hg'e : IntegrableOn (g' * e) (Set.Ioi (2 : ℝ)) := by
    change IntegrableOn (fun u : ℝ ↦
      buchstabFunction (u - 1) * Real.exp (-s * u)) (Set.Ioi 2)
    exact integrableOn_buchstabShift_mul_exp hs
  have hzero : Tendsto (g * e) (nhdsWithin 2 (Set.Ioi 2))
      (nhds (Real.exp (-s * 2))) := by
    have hω2 : ContinuousAt buchstabFunction 2 :=
      continuousOn_buchstabFunction.continuousAt
        (Ici_mem_nhds (by norm_num))
    have hprod : ContinuousAt (fun u : ℝ ↦
        (u * buchstabFunction u) * Real.exp (-s * u)) 2 :=
      (continuousAt_id.mul hω2).mul
        (Real.continuous_exp.continuousAt.comp
          ((continuousAt_const.mul continuousAt_id)))
    have ht : Tendsto (fun u : ℝ ↦
        (u * buchstabFunction u) * Real.exp (-s * u))
        (nhdsWithin 2 (Set.Ioi 2))
        (nhds ((2 * buchstabFunction 2) * Real.exp (-s * 2))) :=
      hprod.tendsto.mono_left inf_le_left
    change Tendsto (fun u : ℝ ↦
      (u * buchstabFunction u) * Real.exp (-s * u))
      (nhdsWithin 2 (Set.Ioi 2)) (nhds (Real.exp (-s * 2)))
    simpa [buchstabFunction_eq_inv (u := (2 : ℝ))
      (by norm_num) (by norm_num)] using ht
  have hinfty : Tendsto (g * e) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (g := fun u : ℝ ↦
      u ^ (1 : ℝ) * Real.exp (-s * u))
    · filter_upwards with u
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with u hu
      have hu0 : 0 ≤ u := zero_le_one.trans hu
      change ‖(u * buchstabFunction u) * Real.exp (-s * u)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg hu0, abs_of_pos (Real.exp_pos _)]
      calc
        u * |buchstabFunction u| * Real.exp (-s * u) ≤
            u * 1 * Real.exp (-s * u) := by
          gcongr
          exact abs_buchstabFunction_le_one hu
        _ = u ^ (1 : ℝ) * Real.exp (-s * u) := by
          rw [Real.rpow_one, mul_one]
    · exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 s hs
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul
    hg he hge' hg'e hzero hinfty
  have hleft : (∫ u in Set.Ioi (2 : ℝ), g u * e' u) =
      -s * ∫ u in Set.Ioi (2 : ℝ), g u * e u := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp [e']
    ring
  rw [hleft] at hibp
  dsimp [g, g', e] at hibp ⊢
  have hs0 : s ≠ 0 := hs.ne'
  let A := ∫ u in Set.Ioi (2 : ℝ),
    u * buchstabFunction u * Real.exp (-s * u)
  let B := ∫ u in Set.Ioi (2 : ℝ),
    buchstabFunction (u - 1) * Real.exp (-s * u)
  let E := Real.exp (-s * 2)
  have hAB : s * A = E + B := by
    dsimp [A, B, E]
    linarith [hibp]
  change A = E / s + (1 / s) * B
  calc
    A = (E + B) / s := (eq_div_iff hs0).2 (by simpa [mul_comm] using hAB)
    _ = E / s + (1 / s) * B := by field_simp [hs0]

theorem integral_buchstabShift_mul_exp_Ioi_two {s : ℝ} :
    (∫ u in Set.Ioi (2 : ℝ),
      buchstabFunction (u - 1) * Real.exp (-s * u)) =
      Real.exp (-s) * buchstabLaplace s := by
  let h : ℝ → ℝ := fun u ↦
    buchstabFunction (u - 1) * Real.exp (-s * u)
  calc
    (∫ u in Set.Ioi (2 : ℝ),
        buchstabFunction (u - 1) * Real.exp (-s * u)) =
        ∫ u : ℝ, (Set.Ioi (2 : ℝ)).indicator h u := by
      rw [integral_indicator measurableSet_Ioi]
    _ = ∫ v : ℝ, (Set.Ioi (2 : ℝ)).indicator h (v + 1) := by
      rw [integral_add_right_eq_self]
    _ = ∫ v : ℝ, (Set.Ioi (1 : ℝ)).indicator
        (fun v ↦ Real.exp (-s) *
          (buchstabFunction v * Real.exp (-s * v))) v := by
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : 1 < v
      · rw [Set.indicator_of_mem (show v + 1 ∈ Set.Ioi (2 : ℝ) by
            exact Set.mem_Ioi.mpr (by linarith)),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hv)]
        dsimp [h]
        rw [show v + 1 - 1 = v by ring,
          show -s * (v + 1) = -s + (-s * v) by ring, Real.exp_add]
        ring_nf
      · rw [Set.indicator_of_notMem (show v + 1 ∉ Set.Ioi (2 : ℝ) by
            intro hv'
            exact hv (by linarith [Set.mem_Ioi.mp hv'])),
          Set.indicator_of_notMem (show v ∉ Set.Ioi (1 : ℝ) by exact hv)]
    _ = ∫ v in Set.Ioi (1 : ℝ), Real.exp (-s) *
          (buchstabFunction v * Real.exp (-s * v)) := by
      rw [integral_indicator measurableSet_Ioi]
    _ = Real.exp (-s) * buchstabLaplace s := by
      rw [integral_const_mul]
      rfl

theorem integral_mul_buchstab_mul_exp_Ioi_one {s : ℝ} (hs : 0 < s) :
    (∫ u in Set.Ioi (1 : ℝ),
      (u * buchstabFunction u) * Real.exp (-s * u)) =
      (Real.exp (-s) / s) * (1 + buchstabLaplace s) := by
  let q : ℝ → ℝ := fun u ↦
    (u * buchstabFunction u) * Real.exp (-s * u)
  have hq1 : IntegrableOn q (Set.Ioi (1 : ℝ)) := by
    have h := (integrableOn_buchstabLaplace_deriv_integrand hs).neg
    apply h.congr_fun _ measurableSet_Ioi
    intro u hu
    dsimp [q]
    ring
  have hq2 : IntegrableOn q (Set.Ioi (2 : ℝ)) :=
    hq1.mono_set (Set.Ioi_subset_Ioi (by norm_num))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hq1 hq2
  have hfinite : (∫ u in (1 : ℝ)..2, q u) =
      ∫ u in (1 : ℝ)..2, Real.exp (-s * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc (1 : ℝ) 2 := by
      simpa [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)] using hu
    dsimp [q]
    rw [buchstabFunction_eq_inv hu'.1 hu'.2]
    have hu0 : u ≠ 0 := ne_of_gt (zero_lt_one.trans_le hu'.1)
    field_simp [hu0]
  have hexp1 : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
      (Set.Ioi 1) := exp_neg_integrableOn_Ioi 1 hs
  have hexp2 : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
      (Set.Ioi 2) := exp_neg_integrableOn_Ioi 2 hs
  have hexpSplit := intervalIntegral.integral_interval_add_Ioi hexp1 hexp2
  have hexpTail (c : ℝ) :
      (∫ u in Set.Ioi c, Real.exp (-s * u)) = Real.exp (-s * c) / s := by
    have h := integral_exp_mul_Ioi (a := -s) (by linarith) c
    rw [h]
    field_simp [hs.ne']
  rw [hexpTail 1, hexpTail 2] at hexpSplit
  rw [hfinite] at hsplit
  have htail := integral_mul_buchstab_mul_exp_Ioi_two hs
  rw [integral_buchstabShift_mul_exp_Ioi_two] at htail
  dsimp [q] at hsplit ⊢
  rw [htail] at hsplit
  have hs0 : s ≠ 0 := hs.ne'
  field_simp [hs0] at hexpSplit hsplit ⊢
  nlinarith [hsplit, hexpSplit]

theorem buchstabLaplace_nonneg {s : ℝ} : 0 ≤ buchstabLaplace s := by
  apply setIntegral_nonneg measurableSet_Ioi
  intro u hu
  exact mul_nonneg
    (buchstabFunction_nonneg (Set.mem_Ioi.mp hu).le)
    (Real.exp_pos _).le

theorem buchstabLaplace_ode {s : ℝ} (hs : 0 < s) :
    s * deriv buchstabLaplace s +
      Real.exp (-s) * (1 + buchstabLaplace s) = 0 := by
  have hd := (hasDerivAt_buchstabLaplace hs).deriv
  rw [integral_neg] at hd
  have htotal := integral_mul_buchstab_mul_exp_Ioi_one hs
  rw [hd, htotal]
  field_simp [hs.ne']
  ring

theorem tendsto_buchstabLaplace_atTop :
    Tendsto buchstabLaplace atTop (nhds 0) := by
  apply squeeze_zero' (g := fun s : ℝ ↦ Real.exp (-s))
  · filter_upwards with s
    exact buchstabLaplace_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs1
    have hs : 0 < s := zero_lt_one.trans_le hs1
    have hFint := integrableOn_buchstabLaplace_integrand hs
    have hexp : IntegrableOn (fun u : ℝ ↦ Real.exp (-s * u))
        (Set.Ioi 1) := exp_neg_integrableOn_Ioi 1 hs
    have hle : buchstabLaplace s ≤
        ∫ u in Set.Ioi (1 : ℝ), Real.exp (-s * u) := by
      apply setIntegral_mono_on hFint hexp measurableSet_Ioi
      intro u hu
      exact mul_le_of_le_one_left (Real.exp_pos _).le
        (buchstabFunction_le_one (Set.mem_Ioi.mp hu).le)
    have heval : (∫ u in Set.Ioi (1 : ℝ), Real.exp (-s * u)) =
        Real.exp (-s) / s := by
      have h := integral_exp_mul_Ioi (a := -s) (by linarith) 1
      rw [h]
      field_simp [hs.ne']
    rw [heval] at hle
    exact hle.trans (div_le_self (Real.exp_pos _).le hs1)
  · exact Real.tendsto_exp_neg_atTop_nhds_zero

theorem one_add_buchstabLaplace_eq_exponentialIntegral {s : ℝ} (hs : 0 < s) :
    1 + buchstabLaplace s = Real.exp
      (∫ t in Set.Ioi s, Real.exp (-t) / t) := by
  exact laplace_ode_solution differentiableOn_buchstabLaplace
    (fun x hx ↦ by linarith [buchstabLaplace_nonneg (s := x)])
    (fun x hx ↦ buchstabLaplace_ode hx)
    tendsto_buchstabLaplace_atTop s hs

theorem buchstabLimit_eq_exp_neg_eulerMascheroniConstant :
    buchstabLimit = Real.exp (-Real.eulerMascheroniConstant) := by
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hzero : Tendsto (fun s : ℝ ↦ s) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hleft : Tendsto (fun s : ℝ ↦
      s * (1 + buchstabLaplace s)) l (nhds buchstabLimit) := by
    have hab : Tendsto (fun s : ℝ ↦ s * buchstabLaplace s) l
        (nhds buchstabLimit) :=
      laplace_final_value_of_tendsto buchstabFunction buchstabLimit 1
        measurable_buchstabFunction (by norm_num)
        (fun u hu ↦ abs_buchstabFunction_le_one hu)
        tendsto_buchstabFunction_atTop
    have hsum := hzero.add hab
    simpa [mul_add] using hsum
  have hright : Tendsto (fun s : ℝ ↦
      s * (1 + buchstabLaplace s)) l
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
    apply exponentialIntegral_exp_limit.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [one_add_buchstabLaplace_eq_exponentialIntegral hs]
  exact tendsto_nhds_unique hleft hright

theorem abs_buchstabFunction_sub_exp_neg_eulerMascheroni_le {u : ℝ}
    (hu : 3 < u) :
    |buchstabFunction u - Real.exp (-Real.eulerMascheroniConstant)| ≤
      2 / (u - 1) := by
  rw [← buchstabLimit_eq_exp_neg_eulerMascheroniConstant]
  exact abs_buchstabFunction_sub_limit_le_two_div_sub_one hu

theorem integrableOn_buchstabFunction_sub_exp_neg_eulerMascheroni_div :
    IntegrableOn (fun u : ℝ ↦
      (buchstabFunction u - Real.exp (-Real.eulerMascheroniConstant)) / u)
      (Set.Ioi 3) := by
  rw [← buchstabLimit_eq_exp_neg_eulerMascheroniConstant]
  exact integrableOn_buchstabFunction_sub_limit_div

theorem tendsto_mul_buchstabLaplace_zero_right :
    Tendsto (fun s : ℝ ↦ s * buchstabLaplace s)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds buchstabLimit) := by
  exact laplace_final_value_of_tendsto buchstabFunction buchstabLimit 1
    measurable_buchstabFunction (by norm_num)
    (fun u hu ↦ abs_buchstabFunction_le_one hu)
    tendsto_buchstabFunction_atTop

end

end ErdosAverageCertificates

end

section

namespace NumberTheoryLean.BuchstabBridge

open MeasureTheory Filter
open scoped Topology
open LinearSieveFunctions

theorem plus_eq_buchstabAux {s : ℝ} (hs : 1 ≤ s) :
    plus (s - 1) = ErdosAverageCertificates.buchstabAux s := by
  apply DelayUniqueness.shifted_unique 1 (fun u => plus (u - 1)) ErdosAverageCertificates.buchstabAux
  · intro u _ hu2
    exact plus_initial (by linarith)
  · intro u hu1 hu2
    exact ErdosAverageCertificates.buchstabAux_eq_one hu1 hu2
  · intro u hu
    simpa only [plus, one_mul] using
      DelayConstruction.delay_integral_of_one_le 1 (u := u - 1) (by linarith)
  · intro u hu
    rw [ErdosAverageCertificates.buchstabAux_eq_one_add_integral hu, one_mul]
    apply congrArg (fun I : ℝ => 1 + I)
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ u - 1)] at ht
    exact ErdosAverageCertificates.buchstabFunction_eq_aux_div ht.1
  · exact hs

theorem plus_div_eq_buchstabFunction {s : ℝ} (hs : 1 ≤ s) :
    plus (s - 1) / s = ErdosAverageCertificates.buchstabFunction s := by
  rw [plus_eq_buchstabAux hs]
  exact (ErdosAverageCertificates.buchstabFunction_eq_aux_div hs).symm

theorem pair_sum_eq_buchstab (A : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    F A s + f A s = A * ErdosAverageCertificates.buchstabFunction s := by
  rw [← plus_div_eq_buchstabFunction hs, f_eq_difference]
  unfold F
  have hs0 : s ≠ 0 := by linarith
  field_simp
  ring

noncomputable def sieveA : ℝ := 2 * Real.exp Real.eulerMascheroniConstant

theorem sieveA_pos : 0 < sieveA := by unfold sieveA; positivity

theorem sieveA_gt_two : 2 < sieveA := by
  have hgamma : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hexp : 1 < Real.exp Real.eulerMascheroniConstant := Real.one_lt_exp_iff.mpr hgamma
  unfold sieveA
  linarith

theorem sieveA_normalization : sieveA * Real.exp (-Real.eulerMascheroniConstant) = 2 := by
  unfold sieveA
  rw [mul_assoc, ← Real.exp_add]
  simp

theorem normalized_pair_sum_tendsto_two :
    Tendsto (fun s : ℝ => F sieveA s + f sieveA s) atTop (𝓝 2) := by
  have hlim := ErdosAverageCertificates.tendsto_buchstabFunction_atTop.const_mul sieveA
  rw [ErdosAverageCertificates.buchstabLimit_eq_exp_neg_eulerMascheroniConstant,
    sieveA_normalization] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  exact (pair_sum_eq_buchstab sieveA hs).symm

theorem pair_gap_tendsto_zero (A : ℝ) :
    Tendsto (fun s : ℝ => F A s - f A s) atTop (𝓝 0) := by
  have hshift : Tendsto (fun s : ℝ => s - 1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b + 1, fun s hs => by linarith⟩
  have hrho := DickmanDecay.rho_tendsto_zero.comp hshift
  have hlim := (hrho.const_mul A).mul (tendsto_inv_atTop_zero : Tendsto (fun s : ℝ => s⁻¹) atTop (𝓝 0))
  simp only [mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  rw [gap_identity A hs, div_eq_mul_inv]
  rfl

theorem normalized_F_tendsto_one : Tendsto (F sieveA) atTop (𝓝 1) := by
  have hlim := (normalized_pair_sum_tendsto_two.add (pair_gap_tendsto_zero sieveA)).div_const 2
  norm_num at hlim
  apply hlim.congr
  intro s
  ring

theorem normalized_f_tendsto_one : Tendsto (f sieveA) atTop (𝓝 1) := by
  have hlim := (normalized_pair_sum_tendsto_two.sub (pair_gap_tendsto_zero sieveA)).div_const 2
  norm_num at hlim
  apply hlim.congr
  intro s
  ring

end NumberTheoryLean.BuchstabBridge

end

end Erdos970

end OAI
