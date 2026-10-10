import Mathlib
import OAI.Probability.Ballisticity.Estimates.IidDifferenceCenteredHalf

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
namespace DirectionalTransience

lemma weak_path_eval_tendsto {μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)}
    {ν : ProbabilityMeasure C(unitInterval,ℝ)} (hμ : Tendsto μ atTop (𝓝 ν))
    {t : ℕ → unitInterval} {s : unitInterval} (ht : Tendsto t atTop (𝓝 s)) :
    Tendsto (fun n => (μ n).map (fun path => path (t n)))
      atTop (𝓝 (ν.map (fun path => path s))) := by
  have he : Continuous (fun p : C(unitInterval,ℝ) × unitInterval => p.1 p.2) := continuous_eval
  have hh := (ProbabilityMeasure.continuous_map he).tendsto
    (ν.prod (diracProba s)) |>.comp
    (ProbabilityMeasure.continuous_prod.tendsto (ν,diracProba s) |>.comp
      (hμ.prodMk_nhds (continuous_diracProba.tendsto s |>.comp ht)))
  have hid (V : ProbabilityMeasure C(unitInterval,ℝ)) (u : unitInterval) :
      (V.prod (diracProba u)).map (fun pair => pair.1 pair.2) =
        V.map (fun path => path u) := by
    apply Subtype.ext
    change ((V : Measure C(unitInterval,ℝ)).prod (Measure.dirac u)).map _ = _
    rw [Measure.prod_dirac,Measure.map_map he.measurable (by fun_prop)]
    rfl
  change Tendsto (fun n => ((μ n).prod (diracProba (t n))).map (fun pair => pair.1 pair.2))
    atTop (𝓝 ((ν.prod (diracProba s)).map (fun pair => pair.1 pair.2))) at hh
  simpa only [hid] using hh

lemma gaussian_median_nonstrict (m : ℝ) (v : ℝ≥0) :
    (1/2 : ℝ≥0∞) ≤ gaussianReal m v (Set.Iic m) ∧
    (1/2 : ℝ≥0∞) ≤ gaussianReal m v (Set.Ici m) := by
  by_cases hv : v = 0
  · subst v; simp [gaussianReal_zero_var]
  · exact ⟨(gaussian_median_half m v hv).1.ge,(gaussian_median_half m v hv).2.ge⟩

lemma continuous_gaussian_path_mean (G : ProbabilityMeasure C(unitInterval,ℝ))
    (m : unitInterval → ℝ) (v : unitInterval → ℝ≥0)
    (hg : ∀ t, (G : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal (m t) (v t)) :
    Continuous m := by
  apply continuous_iff_seqContinuous.mpr
  intro t s ht
  apply median_tendsto_of_weak (weak_path_eval_tendsto tendsto_const_nhds ht)
  · intro n
    change (1/2 : ℝ≥0∞) ≤ ((G : Measure C(unitInterval,ℝ)).map (fun g => g (t n))) (Set.Iic (m (t n))) ∧
      (1/2 : ℝ≥0∞) ≤ ((G : Measure C(unitInterval,ℝ)).map (fun g => g (t n))) (Set.Ici (m (t n)))
    rw [hg]
    exact gaussian_median_nonstrict _ _
  · intro ε hε
    change (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Iio (m s+ε)) ∧
      (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Ioi (m s-ε))
    rw [hg]
    exact gaussian_median_strict _ _ hε

lemma weak_path_grid_medians_uniform {μ : ℕ → ProbabilityMeasure C(unitInterval,ℝ)}
    {G : ProbabilityMeasure C(unitInterval,ℝ)} (hμ : Tendsto μ atTop (𝓝 G))
    (m : unitInterval → ℝ) (v : unitInterval → ℝ≥0)
    (hg : ∀ t, (G : Measure C(unitInterval,ℝ)).map (fun g => g t) = gaussianReal (m t) (v t))
    (grid : ℕ → Set unitInterval) (b : ℕ → unitInterval → ℝ)
    (hb : ∀ n t, t ∈ grid n →
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Iic (b n t)) ∧
      (1/2 : ℝ≥0∞) ≤ ((μ n : Measure C(unitInterval,ℝ)).map (fun g => g t)) (Set.Ici (b n t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t ∈ grid n, |b n t-m t| < ε := by
  by_contra hn
  simp only [eventually_atTop,not_exists,not_forall] at hn
  have hex : ∀ N : ℕ, ∃ n ≥ N, ∃ t ∈ grid n, ε ≤ |b n t-m t| := by
    intro N
    obtain ⟨n,hn⟩ := hn N
    push Not at hn
    obtain ⟨t,ht,hb⟩ := hn.2
    exact ⟨n,hn.1,t,ht,hb⟩
  choose n hn t htg hbad using hex
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  obtain ⟨s,_,k,hk,ht⟩ := isCompact_univ.tendsto_subseq (fun n => Set.mem_univ (t n))
  have hm := continuous_gaussian_path_mean G m v hg |>.tendsto s |>.comp ht
  have hl := weak_path_eval_tendsto (hμ.comp (hnlim.comp hk.tendsto_atTop)) ht
  have hb' : Tendsto (fun i => b (n (k i)) (t (k i))) atTop (𝓝 (m s)) := by
    apply median_tendsto_of_weak hl
    · intro i; exact hb _ _ (htg _)
    · intro δ hδ
      change (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Iio (m s+δ)) ∧
        (1/2 : ℝ≥0∞) < ((G : Measure C(unitInterval,ℝ)).map (fun g => g s)) (Set.Ioi (m s-δ))
      rw [hg]
      exact gaussian_median_strict _ _ hδ
  have hz := (hb'.sub hm).abs
  have he := hz.eventually (gt_mem_nhds (show |m s-m s| < ε by simpa using hε))
  obtain ⟨i,hi⟩ := he.exists
  exact not_lt_of_ge (hbad (k i)) hi

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
