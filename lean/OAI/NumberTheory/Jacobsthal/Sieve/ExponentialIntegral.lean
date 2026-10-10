import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic
import OAI.NumberTheory.Jacobsthal.Estimates.PVIdentity

namespace OAI

namespace Erdos970

section

open Real Set MeasureTheory Filter Topology
open scoped Interval

namespace ErdosAverageCertificates

noncomputable section

theorem exponentialIntegral_log_limit :
    Tendsto
      (fun s : ℝ ↦ Real.log s +
        ∫ t in Set.Ioi s, Real.exp (-t) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-Real.eulerMascheroniConstant)) := by
  have hbase := tendsto_integral_one_sub_exp_neg_div
  have htail : Tendsto
      (fun _s : ℝ ↦ ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t)) :=
    tendsto_const_nhds
  have hlim := hbase.neg.add htail
  have htarget :
      -(∫ t in (0 : ℝ)..1, (1 - Real.exp (-t)) / t) +
          ∫ t in Set.Ioi (1 : ℝ), Real.exp (-t) / t =
        -Real.eulerMascheroniConstant := by
    rw [eulerMascheroni_eq_integral]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with s hs0 hs1
  have hs : 0 < s := hs0
  have hsle : s ≤ 1 := hs1.le
  have hfinite : IntervalIntegrable
      (fun t : ℝ ↦ Real.exp (-t) / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div
    · exact (continuous_exp.comp continuous_neg).continuousOn
    · exact continuousOn_id
    · intro t ht
      have ht' := Set.mem_uIcc.mp ht
      rcases ht' with ht' | ht'
      · change t ≠ 0
        linarith
      · change t ≠ 0
        linarith
  have hone : IntervalIntegrable (fun t : ℝ ↦ 1 / t) volume s 1 := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro t ht
    have ht' := Set.mem_uIcc.mp ht
    rcases ht' with ht' | ht'
    · change t ≠ 0
      linarith
    · change t ≠ 0
      linarith
  have hsplitSet : Set.Ioi s = Set.Ioc s 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi hsle).symm
  have hdisj : Disjoint (Set.Ioc s 1) (Set.Ioi 1) :=
    Set.Ioc_disjoint_Ioi_same
  have htailInt : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-t) / t) (Set.Ioi 1) :=
    integrableOn_exp_neg_div_Ioi
  have hfiniteOn : IntegrableOn
      (fun t : ℝ ↦ Real.exp (-t) / t) (Set.Ioc s 1) := by
    rwa [← intervalIntegrable_iff_integrableOn_Ioc_of_le hsle]
  rw [hsplitSet, setIntegral_union hdisj measurableSet_Ioi hfiniteOn htailInt]
  have hlog : (∫ t in s..1, (1 : ℝ) / t) = -Real.log s := by
    simp_rw [one_div]
    rw [integral_inv_of_pos hs one_pos]
    rw [Real.log_div one_ne_zero hs.ne']
    simp
  have hsub :
      (∫ t in s..1, (1 - Real.exp (-t)) / t) =
        (∫ t in s..1, (1 : ℝ) / t) -
          ∫ t in s..1, Real.exp (-t) / t := by
    rw [← intervalIntegral.integral_sub hone hfinite]
    congr 1
    funext t
    ring
  rw [hsub, hlog]
  rw [← intervalIntegral.integral_of_le hsle]
  ring

theorem exponentialIntegral_exp_limit :
    Tendsto
      (fun s : ℝ ↦ s * Real.exp
        (∫ t in Set.Ioi s, Real.exp (-t) / t))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp (-Real.eulerMascheroniConstant))) := by
  have h := (continuous_exp.tendsto
    (-Real.eulerMascheroniConstant)).comp exponentialIntegral_log_limit
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  change Real.exp (Real.log s +
      ∫ t in Set.Ioi s, Real.exp (-t) / t) = _
  rw [Real.exp_add, Real.exp_log hs]

theorem laplace_final_value_of_tendsto
    (f : ℝ → ℝ) (L C : ℝ)
    (hf : Measurable f) (hC : 0 ≤ C)
    (hbound : ∀ u : ℝ, 1 ≤ u → |f u| ≤ C)
    (hlim : Tendsto f atTop (nhds L)) :
    Tendsto
      (fun s : ℝ ↦ s * ∫ u in Set.Ioi 1, f u * Real.exp (-s * u))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
  let F : ℝ → ℝ → ℝ := fun s t ↦
    (Set.Ioi s).indicator (fun t ↦ f (t / s) * Real.exp (-t)) t
  let G : ℝ → ℝ := fun t ↦
    (Set.Ioi (0 : ℝ)).indicator (fun t ↦ L * Real.exp (-t)) t
  let B : ℝ → ℝ := fun t ↦
    (Set.Ioi (0 : ℝ)).indicator (fun t ↦ C * Real.exp (-t)) t
  have hBint : Integrable B := by
    have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-t)) (Set.Ioi 0) :=
      integrableOn_exp_neg_Ioi 0
    have hmul : IntegrableOn (fun t : ℝ ↦ C * Real.exp (-t)) (Set.Ioi 0) :=
      hexp.const_mul C
    simpa [B, integrable_indicator_iff measurableSet_Ioi] using hmul
  have hFmeas : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      AEStronglyMeasurable (F s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    have hcomp : Measurable (fun t : ℝ ↦ f (t / s)) :=
      hf.comp (measurable_id.div_const s)
    have hprod : Measurable (fun t : ℝ ↦
        f (t / s) * Real.exp (-t)) :=
      hcomp.mul ((continuous_exp.comp continuous_neg).measurable)
    exact hprod.aestronglyMeasurable.indicator measurableSet_Ioi
  have hFbound : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0),
      ∀ᵐ t : ℝ, ‖F s t‖ ≤ B t := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    filter_upwards with t
    by_cases hst : s < t
    · have hs0 : 0 < s := hs
      have ht0 : 0 < t := hs0.trans hst
      have hratio : 1 ≤ t / s := by
        rw [le_div_iff₀ hs0]
        simpa using hst.le
      have hfC := hbound (t / s) hratio
      have hstmem : t ∈ Set.Ioi s := hst
      have htmem : t ∈ Set.Ioi (0 : ℝ) := ht0
      change ‖(Set.Ioi s).indicator
          (fun v ↦ f (v / s) * Real.exp (-v)) t‖ ≤
        (Set.Ioi 0).indicator (fun v ↦ C * Real.exp (-v)) t
      rw [Set.indicator_of_mem hstmem, Set.indicator_of_mem htmem]
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hfC (Real.exp_pos _).le
    · have hnot : t ∉ Set.Ioi s := hst
      change ‖(Set.Ioi s).indicator
          (fun v ↦ f (v / s) * Real.exp (-v)) t‖ ≤
        (Set.Ioi 0).indicator (fun v ↦ C * Real.exp (-v)) t
      rw [Set.indicator_of_notMem hnot, norm_zero]
      by_cases ht0 : 0 < t
      · have htmem : t ∈ Set.Ioi (0 : ℝ) := ht0
        rw [Set.indicator_of_mem htmem]
        positivity
      · have htmem : t ∉ Set.Ioi (0 : ℝ) := ht0
        rw [Set.indicator_of_notMem htmem]
  have hFlim : ∀ᵐ t : ℝ,
      Tendsto (fun s : ℝ ↦ F s t) (nhdsWithin 0 (Set.Ioi 0)) (nhds (G t)) := by
    filter_upwards with t
    by_cases ht : 0 < t
    · have hevent : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), s < t :=
        nhdsWithin_le_nhds (Iio_mem_nhds ht)
      have hratio : Tendsto (fun s : ℝ ↦ t / s)
          (nhdsWithin 0 (Set.Ioi 0)) atTop := by
        simpa [div_eq_mul_inv] using
          tendsto_const_nhds.pos_mul_atTop ht tendsto_inv_nhdsGT_zero
      have hfpart := hlim.comp hratio
      have hconst : Tendsto (fun _s : ℝ ↦ Real.exp (-t))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-t))) :=
        tendsto_const_nhds
      have hprod := hfpart.mul hconst
      have hprod' : Tendsto
          (fun s : ℝ ↦ f (t / s) * Real.exp (-t))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (L * Real.exp (-t))) := hprod
      have hG : G t = L * Real.exp (-t) := by simp [G, ht]
      rw [hG]
      apply hprod'.congr'
      filter_upwards [hevent] with s hst
      simp [F, hst]
    · have ht0 : t ≤ 0 := le_of_not_gt ht
      have hevent : ∀ᶠ s : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < s :=
        self_mem_nhdsWithin
      have hzero : Tendsto (fun _s : ℝ ↦ (0 : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
      have hzero' : G t = 0 := by simp [G, ht]
      rw [hzero']
      apply hzero.congr'
      filter_upwards [hevent] with s hs
      have hnot : ¬s < t := by linarith
      simp [F, hnot]
  have hint := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    B hFmeas hFbound hBint hFlim
  have hGint : (∫ t : ℝ, G t) = L := by
    have hGset : (∫ t : ℝ, G t) =
        ∫ t in Set.Ioi (0 : ℝ), L * Real.exp (-t) := by
      rw [← integral_indicator measurableSet_Ioi]
    rw [hGset, integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [hGint] at hint
  refine hint.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs0 : 0 < s := hs
  have hsne : s ≠ 0 := hs0.ne'
  have hscale := integral_comp_mul_left_Ioi
    (fun t : ℝ ↦ f (t / s) * Real.exp (-t)) 1 hs0
  have hscale' :
      (∫ u in Set.Ioi (1 : ℝ), f u * Real.exp (-s * u)) =
        s⁻¹ * ∫ t in Set.Ioi s, f (t / s) * Real.exp (-t) := by
    simpa [hsne, smul_eq_mul] using hscale
  have hFset : (∫ t : ℝ, F s t) =
      ∫ t in Set.Ioi s, f (t / s) * Real.exp (-t) := by
    rw [← integral_indicator measurableSet_Ioi]
  rw [hFset]
  rw [hscale']
  simp [hsne]

end

end ErdosAverageCertificates

end

end Erdos970

end OAI
