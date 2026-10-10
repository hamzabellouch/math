import OAI.Analysis.CircleDomains.Sobolev.ScalarFlattening
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Smooth primitives approximating the flattening map, with bounded
derivatives converging at every scalar value to the complement indicator. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal Interval
noncomputable section
namespace CircleDomainRigidity

 theorem exists_flattenValues_smooth_approximation {O : Set ℝ} (hO : IsOpen O) :
    ∃ F : ℕ → ℝ → ℝ,
      (∀ n, ContDiff ℝ 1 (F n) ∧ F n 0 = 0 ∧ LipschitzWith 1 (F n)) ∧
      (∀ t, Tendsto (fun n => F n t) atTop (𝓝 (flattenValues O t))) ∧
      (∀ n t, deriv (F n) t ∈ Icc (0 : ℝ) 1) ∧
      (∀ t, Tendsto (fun n => deriv (F n) t) atTop
        (𝓝 (Oᶜ.indicator (fun _ => (1 : ℝ)) t))) := by
  obtain ⟨b, hbs, hbc, hb⟩ := hO.exists_contDiff_support_eq (n := (⊤ : ℕ∞))
  let a : ℕ → ℝ → ℝ := fun n t => 1 - Real.smoothTransition (((n : ℝ)+1)*b t-1)
  have haSmooth (n : ℕ) : ContDiff ℝ 1 (a n) :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul hbc).sub contDiff_const)) |>.of_le (by simp)
  have haUnit (n : ℕ) (t : ℝ) : a n t ∈ Icc (0 : ℝ) 1 := by
    dsimp only [a]
    constructor <;> linarith [Real.smoothTransition.nonneg (((n : ℝ)+1)*b t-1),
      Real.smoothTransition.le_one (((n : ℝ)+1)*b t-1)]
  have haLim (t : ℝ) : Tendsto (fun n => a n t) atTop
      (𝓝 (Oᶜ.indicator (fun _ => (1 : ℝ)) t)) := by
    by_cases ht : t ∈ O
    · have hbpos : 0 < b t := by
        have hn : b t ≠ 0 := by simpa only [← hbs, mem_support] using ht
        exact lt_of_le_of_ne (hb (mem_range_self t)).1 (Ne.symm hn)
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / b t)
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hlarge : 2 ≤ ((n : ℝ)+1)*b t := by
        have hN' : 2 < (N : ℝ)*b t := (div_lt_iff₀ hbpos).mp hN
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith
      simp only [a, Real.smoothTransition.one_of_one_le (by linarith :
        1 ≤ ((n : ℝ)+1)*b t-1), sub_self, indicator_of_notMem (show t ∉ Oᶜ by simpa only [mem_compl_iff, not_not] using ht)]
    · have hbzero : b t = 0 := by
        by_contra hn
        exact ht (hbs ▸ (show t ∈ support b from hn))
      have heq : ∀ n, a n t = Oᶜ.indicator (fun _ => (1 : ℝ)) t := by
        intro n
        simp [a, hbzero, ht, Real.smoothTransition.zero_of_nonpos]
      simpa only [heq] using (tendsto_const_nhds : Tendsto
        (fun _ : ℕ => Oᶜ.indicator (fun _ => (1 : ℝ)) t) atTop _)
  let F : ℕ → ℝ → ℝ := fun n t => ∫ s in (0 : ℝ)..t, a n s
  have hderiv (n : ℕ) (t : ℝ) : HasDerivAt (F n) (a n t) t :=
    intervalIntegral.integral_hasDerivAt_right
      ((haSmooth n).continuous.intervalIntegrable 0 t)
      (haSmooth n).continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      (haSmooth n).continuous.continuousAt
  have hFderiv (n : ℕ) : deriv (F n) = a n := funext fun t => (hderiv n t).deriv
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro n
    refine ⟨contDiff_one_iff_deriv.mpr ⟨fun t => (hderiv n t).differentiableAt,
      by rw [hFderiv]; exact (haSmooth n).continuous⟩, by simp [F], ?_⟩
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have hinc := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      ((haSmooth n).continuous.intervalIntegrable 0 y)
      ((haSmooth n).continuous.intervalIntegrable y x)
    have he : F n x - F n y = ∫ s in y..x, a n s := by dsimp only [F]; linarith
    simp only [Real.dist_eq, NNReal.coe_one, one_mul, he]
    simpa only [Real.norm_eq_abs, one_mul] using
      intervalIntegral.norm_integral_le_of_norm_le_const (f := a n) (a := y) (b := x) (C := 1)
        (fun s _ => by rw [Real.norm_eq_abs, abs_of_nonneg (haUnit n s).1]; exact (haUnit n s).2)
  · intro t
    let : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) t)) :=
      isFiniteMeasure_restrict.mpr (by simp [uIoc, Real.volume_Ioc])
    have hlim := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ι (0 : ℝ) t)) (bound := fun _ => (1 : ℝ))
      (fun n => (haSmooth n).continuous.aestronglyMeasurable)
      (integrable_const (1 : ℝ))
      (fun n => Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg (haUnit n s).1]; exact (haUnit n s).2)
      (Eventually.of_forall haLim)
    dsimp only [F, flattenValues]
    simp_rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    exact hlim.const_smul _
  · intro n t
    rw [hFderiv]
    exact haUnit n t
  · intro t
    simp only [hFderiv]
    exact haLim t

end CircleDomainRigidity

end

end OAI
