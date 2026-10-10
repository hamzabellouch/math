import Mathlib
import OAI.Probability.Ballisticity.Estimates.GridLinear
import OAI.Probability.Ballisticity.Estimates.CappedExp

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
namespace DirectionalTransience

lemma dominated_translation_bounded {μ ν : ℕ → ProbabilityMeasure ℝ}
    {M N : ProbabilityMeasure ℝ} (hμ : Tendsto μ atTop (𝓝 M)) (hν : Tendsto ν atTop (𝓝 N))
    {p : ℝ≥0∞} (hp : p ≠ 0) (hptop : p ≠ ∞) (c : ℕ → ℝ)
    (hdom : ∀ i, p • ((μ i : Measure ℝ).map (fun x => x-c i)) ≤ (ν i : Measure ℝ)) :
    ∃ R > 0, ∀ i, |c i| ≤ R := by
  obtain ⟨K,hK,hKb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (weak_sequence_tight hμ) (1/2) (by norm_num)
  obtain ⟨L,hL,hLb⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (weak_sequence_tight hν) (p/4) (ENNReal.div_pos hp (by norm_num))
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨S,hS,hLS⟩ := hL.isBounded.exists_pos_norm_le
  refine ⟨R+S,by positivity,?_⟩
  intro i
  by_contra hi
  have hc : R+S < |c i| := lt_of_not_ge hi
  have hsub : K ⊆ (fun x => x-c i) ⁻¹' Lᶜ := by
    intro x hx hxl
    have hr := hKR x hx
    have hs := hLS (x-c i) hxl
    have he : c i = x-(x-c i) := by ring
    have hab := norm_sub_le x (x-c i)
    rw [← he,Real.norm_eq_abs] at hab
    linarith
  have hKm : (1/2 : ℝ≥0∞) ≤ (μ i : Measure ℝ) K := by
    have hh := hKb _ ⟨i,rfl⟩
    have he := measure_add_measure_compl hK.measurableSet (μ := (μ i : Measure ℝ))
    rw [measure_univ] at he
    have hh' : (1:ℝ≥0∞) ≤ (μ i : Measure ℝ) K+1/2 := by
      calc _ = (μ i : Measure ℝ) K+(μ i : Measure ℝ) Kᶜ := he.symm
        _ ≤ _ := add_le_add le_rfl hh
    exact (ENNReal.le_of_add_le_add_right (by norm_num : (1/2:ℝ≥0∞) ≠ ∞)) (by
      simpa only [ENNReal.add_halves] using hh')
  have hh : p*(1/2) ≤ p/4 := by
    calc _ ≤ p*(μ i : Measure ℝ) K := by gcongr
      _ ≤ p*((μ i : Measure ℝ).map (fun x => x-c i)) Lᶜ := by
        rw [Measure.map_apply (by fun_prop) hL.measurableSet.compl]
        gcongr
      _ = (p • ((μ i : Measure ℝ).map (fun x => x-c i))) Lᶜ := rfl
      _ ≤ (ν i : Measure ℝ) Lᶜ := hdom i Lᶜ
      _ ≤ p/4 := hLb _ ⟨i,rfl⟩
  have hlt : p/4 < p*(1/2) := by
    convert ENNReal.mul_lt_mul_left (a := p) hp hptop (show (1/4:ℝ≥0∞) < 1/2 by norm_num) using 1 <;> simp [div_eq_mul_inv,mul_comm]
  exact not_le_of_gt hlt hh

lemma weak_gaussian_domination_center {μ ν : ℕ → ProbabilityMeasure ℝ} (v : ℝ≥0)
    (hμ : Tendsto μ atTop (𝓝 ⟨gaussianReal 0 v,inferInstance⟩))
    (hν : Tendsto ν atTop (𝓝 ⟨gaussianReal 0 v,inferInstance⟩))
    {p : ℝ} (hp : 0 < p) (c : ℕ → ℝ)
    (hdom : ∀ i, ENNReal.ofReal p • ((μ i : Measure ℝ).map (fun x => x-c i)) ≤ (ν i : Measure ℝ)) :
    Tendsto c atTop (𝓝 0) := by
  obtain ⟨R,hR,hc⟩ := dominated_translation_bounded hμ hν
    (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top c hdom
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push Not at hn
  choose n hn hbad using hn
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hic : ∀ i, c (n i) ∈ Set.Icc (-R) R := fun i => abs_le.mp (hc (n i))
  obtain ⟨b,_,k,hk,hkb⟩ := isCompact_Icc.tendsto_subseq hic
  have hlim := weak_sub_const_tendsto (hμ.comp (hnlim.comp hk.tendsto_atTop)) hkb
  have hmap : ProbabilityMeasure.map (⟨gaussianReal 0 v,inferInstance⟩ : ProbabilityMeasure ℝ)
      (fun x : ℝ => x-b) =
      ⟨gaussianReal (-b) v,inferInstance⟩ := by
    apply Subtype.ext
    change (gaussianReal 0 v).map (fun x => x-b) = gaussianReal (-b) v
    have hh := gaussianReal_map_add_const (μ := (0:ℝ)) (v := v) (-b)
    simpa only [sub_eq_add_neg,zero_add] using hh
  rw [hmap] at hlim
  have hb : -b = 0 := gaussian_mean_eq_of_test_domination (-b) 0 v hp (fun f hf =>
    weak_test_domination hlim (hν.comp (hnlim.comp hk.tendsto_atTop)) hp.le
      (fun i => hdom (n (k i))) f hf)
  have hb0 : b = 0 := neg_eq_zero.mp hb
  have he := (hkb.abs).eventually (gt_mem_nhds (show |b| < ε by simpa [hb0] using hε))
  obtain ⟨i,hi⟩ := he.exists
  exact not_lt_of_ge (by simpa [Real.dist_eq] using hbad (k i)) hi

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
