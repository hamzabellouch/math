import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Topology
import Mathlib.Tactic

namespace OAI

open MeasureTheory Filter Set
open scoped Topology

namespace Balanced
open scoped _root_.Balanced

lemma analytic_equality_null {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {U : Set ℝ} (hf : AnalyticOnNhd ℝ f U)
    (hg : AnalyticOnNhd ℝ g U) (hU : IsPreconnected U) (hmU : MeasurableSet U)
    (hne : ¬ Set.EqOn f g U) :
    volume.restrict U {x | f x = g x} = 0 := by
  have hc := (hf.eqOn_or_eventually_ne_of_preconnected hg hU).resolve_left hne
  have ha : ∀ᵐ x ∂volume.restrict U, f x ≠ g x :=
    ae_restrict_le_codiscreteWithin hmU hc
  simpa only [ae_iff, not_not] using ha

lemma analytic_complex_exponential_series {ι : Type*} (a : ι → ℂ) (rate : ι → ℝ)
    (ha : Summable fun i ↦ ‖a i‖) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' i, a i * Complex.exp (-(rate i : ℂ) * z))
      {z : ℂ | 0 < z.re} := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  apply Complex.differentiableOn_tsum_of_summable_norm ha
  · intro i
    fun_prop
  · exact hopen
  · intro i z hz
    rw [norm_mul, Complex.norm_exp]
    have he : (-(rate i : ℂ) * z).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
        Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hrate i)) hz.le
    have hb : Real.exp (-(rate i : ℂ) * z).re ≤ 1 := Real.exp_le_one_iff.mpr he
    simpa using mul_le_mul_of_nonneg_left hb (norm_nonneg (a i))

lemma analytic_real_exponential_series {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℝ (fun s : ℝ ↦ ∑' i, a i * Real.exp (-rate i * s)) (Ioi 0) := by
  have hc := analytic_complex_exponential_series (fun i ↦ (a i : ℂ)) rate
    (by simpa using ha) hrate
  intro s hs
  have hh : AnalyticAt ℝ
      (fun z : ℂ ↦ ∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * z)) (s : ℂ) :=
    (hc (s : ℂ) (by exact hs)).restrictScalars
  have hh' := hh.comp (Complex.ofRealCLM.analyticAt s)
  have hh'' := (Complex.reCLM.analyticAt _).comp hh'
  have heq : (fun s : ℝ ↦
      (∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * (s : ℂ))).re) =
      (fun s : ℝ ↦ ∑' i, a i * Real.exp (-rate i * s)) := by
    funext s
    simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_tsum, Complex.ofReal_re]
  change AnalyticAt ℝ (fun s : ℝ ↦
    (∑' i, (a i : ℂ) * Complex.exp (-(rate i : ℂ) * (s : ℂ))).re) s at hh''
  rwa [heq] at hh''

lemma analytic_real_power_series {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i) :
    AnalyticOnNhd ℝ (fun z : ℝ ↦ ∑' i, a i * z ^ rate i) (Ioo 0 1) := by
  intro z hz
  have hs : 0 < -Real.log z := neg_pos.mpr (Real.log_neg hz.1 hz.2)
  have h := (analytic_real_exponential_series a rate ha hrate (-Real.log z) hs).comp
    (f := fun x : ℝ ↦ -Real.log x) (x := z) (analyticAt_log hz.1).neg
  apply h.congr
  filter_upwards [eventually_gt_nhds hz.1] with x hx
  simp only [Function.comp_apply]
  apply tsum_congr
  intro i
  rw [Real.rpow_def_of_pos hx]
  congr 2
  ring

lemma power_series_at_exp_neg {ι : Type*} (a rate : ι → ℝ) (s : ℝ) :
    (∑' i, a i * (Real.exp (-s)) ^ rate i) =
      ∑' i, a i * Real.exp (-rate i * s) := by
  apply tsum_congr
  intro i
  rw [← Real.exp_mul]
  congr 2
  ring

lemma power_series_zero_null_of_laplace_nonzero {ι : Type*} (a rate : ι → ℝ)
    (ha : Summable fun i ↦ |a i|) (hrate : ∀ i, 0 ≤ rate i)
    (hne : ∃ s : ℝ, 0 < s ∧ (∑' i, a i * Real.exp (-rate i * s)) ≠ 0) :
    volume.restrict (Ioo (0 : ℝ) 1) {z | (∑' i, a i * z ^ rate i) = 0} = 0 := by
  apply analytic_equality_null (analytic_real_power_series a rate ha hrate)
    analyticOnNhd_const isPreconnected_Ioo measurableSet_Ioo
  intro hzero
  obtain ⟨s, hs, hne⟩ := hne
  have hz : Real.exp (-s) ∈ Ioo (0 : ℝ) 1 :=
    ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (by linarith)⟩
  have heq := hzero hz
  change (∑' i, a i * (Real.exp (-s)) ^ rate i) = 0 at heq
  rw [power_series_at_exp_neg] at heq
  exact hne heq

end Balanced

end OAI
