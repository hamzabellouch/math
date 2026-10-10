import Mathlib
import OAI.Probability.Ballisticity.Geometry.HeightPolygonTranslateApply
import OAI.Probability.Ballisticity.Walk.CompactPathModulus

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
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

lemma heightPolygon_random_shift_small {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → ℕ → Ω → ℝ)
    (hF : ∀ i k, Measurable (F i k)) (r n : ℕ → ℝ) (hn : Tendsto n atTop atTop)
    (H : Ω → ℕ) (hH : Measurable H) (c : ℕ → Ω → ℝ)
    (hc : TendstoInMeasure μ (fun i ω => c i ω/r i) atTop 0)
    {T : ℝ} (hT : 0 ≤ T)
    (ht : IsTightMeasureSet (Set.range (fun i => μ.map
      (fun ω => heightPolygon (fun k => F i k ω) (r i) (n i) (T+1))))) :
    TendstoInMeasure μ (fun i ω =>
      heightPolygon (fun k => F i (k+H ω) ω+c i ω) (r i) (n i) T-
        heightPolygon (fun k => F i k ω) (r i) (n i) T) atTop 0 := by
  have hhn : TendstoInMeasure μ (fun i ω => (H ω:ℝ)/n i) atTop 0 := by
    apply tendstoInMeasure_of_tendsto_ae
      (fun i => (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp hH).div_const _).aestronglyMeasurable)
    exact ae_of_all _ (fun _ => tendsto_const_nhds.div_atTop hn)
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  simp only [Pi.zero_apply,sub_zero]
  apply Metric.tendsto_nhds.2
  intro β hβ
  obtain ⟨δ,hδ,hmod⟩ := tight_path_modulus _ ht (by positivity : 0 < ε/4)
    (by positivity : 0 < β/4)
  have hht := (tendstoInMeasure_iff_measureReal_norm.1 hhn) (min δ 1) (by positivity)
  have hct := (tendstoInMeasure_iff_measureReal_norm.1 hc) (ε/4) (by positivity)
  simp only [Pi.zero_apply,sub_zero,Real.norm_eq_abs] at hht hct
  filter_upwards [hn.eventually (eventually_gt_atTop (0:ℝ)),
    hht.eventually_lt_const (by positivity : 0 < β/4),
    hct.eventually_lt_const (by positivity : 0 < β/4)] with i hni hhi hci
  let A := {ω | min δ 1 ≤ |(H ω:ℝ)/n i|}
  let B := {ω | heightPolygon (fun k => F i k ω) (r i) (n i) (T+1) ∈ ContinuousOscillation (ε/4) δ}
  let C := {ω | ε/4 ≤ |c i ω/r i|}
  have hb : μ.real B ≤ β/4 := by
    have hm := hmod i
    rw [Measure.map_apply (measurable_heightPolygon _ (hF i) _ _ _)
      (isOpen_continuousOscillation _ _).measurableSet] at hm
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hm
  have hs : {ω | ε ≤ ‖heightPolygon (fun k => F i (k+H ω) ω+c i ω) (r i) (n i) T-
        heightPolygon (fun k => F i k ω) (r i) (n i) T‖} ⊆ A ∪ B ∪ C := by
    intro ω hω
    by_contra hh
    have ha : ω ∉ A := fun h => hh (Or.inl (Or.inl h))
    have hb' : ω ∉ B := fun h => hh (Or.inl (Or.inr h))
    have hc' : ω ∉ C := fun h => hh (Or.inr h)
    have ha' : (H ω:ℝ)/n i < min δ 1 := by
      simpa only [A,Set.mem_ofPred_eq,not_le,abs_of_nonneg
        (div_nonneg (Nat.cast_nonneg _) hni.le)] using ha
    have hHi : (H ω:ℝ) ≤ n i := ((div_lt_one hni).mp (ha'.trans_le (min_le_right _ _))).le
    have hnorm := heightPolygon_translate_norm_le (fun k => F i k ω) (r i) (n i) T
      hni hT (H ω) hHi (c i ω) (ε/4) δ (ha'.le.trans (min_le_left _ _)) hb'
    have hcc : |c i ω/r i| < ε/4 := lt_of_not_ge hc'
    simp only [Set.mem_ofPred_eq] at hω
    linarith
  have hm := (measureReal_mono (μ := μ) hs (measure_ne_top _ _)).trans
    ((measureReal_union_le (μ := μ) (s₁ := A ∪ B) (s₂ := C)).trans
      (add_le_add (measureReal_union_le (μ := μ) (s₁ := A) (s₂ := B)) le_rfl))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg measureReal_nonneg]
  dsimp only [A,C] at hm
  linarith

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
