import OAI.Analysis.LipschitzHilbert.Trees.SourceWeightedBadPath
import OAI.Analysis.LipschitzHilbert.Trees.SourceStopCostBudget

namespace OAI

/-! The source good set controls the pointwise total bad-top mass.
Its measure estimate follows from the full weighted bad-path integral. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace LipschitzHilbert
attribute [local instance] Classical.propDecidable
variable {ι X : Type*} [MeasurableSpace X]

def sourceBadPathMass (tops : Finset ι) (weight : ι → X → ℝ) (bad : ι → Set X) (x : X) : ℝ :=
  ∑ t ∈ tops, (bad t).indicator (weight t) x

def sourceGoodPathSet (base : Set X) (tops : Finset ι) (weight : ι → X → ℝ)
    (bad : ι → Set X) (L : ℝ) : Set X :=
  base ∩ {x | sourceBadPathMass tops weight bad x ≤ Real.exp (-L)}

omit [MeasurableSpace X] in
theorem sourceBadPathMass_eq_filter (tops : Finset ι) (weight : ι → X → ℝ)
    (bad : ι → Set X) (x : X) :
    sourceBadPathMass tops weight bad x = ∑ t ∈ tops.filter (fun t => x ∈ bad t), weight t x := by
  simp only [sourceBadPathMass,Finset.sum_filter,indicator_apply]

theorem source_good_path_set_area (μ : Measure X) (base : Set X) (hbase : MeasurableSet base)
    (tops : Finset ι) (weight : ι → X → ℝ) (bad : ι → Set X)
    (hw : ∀ t ∈ tops, Measurable (weight t)) (hw0 : ∀ t x, 0 ≤ weight t x)
    (hbad : ∀ t ∈ tops, MeasurableSet (bad t)) (L S : ℝ)
    (hint : Integrable (sourceBadPathMass tops weight bad) μ)
    (hbound : (∫ x, sourceBadPathMass tops weight bad x ∂μ) ≤ S*Real.exp (-10*L)) :
    MeasurableSet (sourceGoodPathSet base tops weight bad L) ∧
      sourceGoodPathSet base tops weight bad L ⊆ base ∧
      μ (base \ sourceGoodPathSet base tops weight bad L) ≤ ENNReal.ofReal (S*Real.exp (-9*L)) := by
  let f := sourceBadPathMass tops weight bad
  have hf : Measurable f := Finset.measurable_sum _ (fun t ht => (hw t ht).indicator (hbad t ht))
  have hf0 (x : X) : 0 ≤ f x := Finset.sum_nonneg fun t _ =>
    indicator_nonneg (fun z _ => hw0 t z) x
  have heps : 0 < Real.exp (-L) := Real.exp_pos _
  have hfinite : μ {x | Real.exp (-L) ≤ f x} ≠ ∞ :=
    (hint.measure_ge_lt_top heps).ne
  have hm := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hf0) hint
    (Real.exp (-L))
  have hreal : μ.real {x | Real.exp (-L) ≤ f x} ≤ S*Real.exp (-9*L) := by
    apply (mul_le_mul_iff_right₀ heps).mp
    have hexp : Real.exp (-L)*(S*Real.exp (-9*L)) = S*Real.exp (-10*L) := by
      rw [show Real.exp (-L)*(S*Real.exp (-9*L)) =
        S*(Real.exp (-9*L)*Real.exp (-L)) by ring,← Real.exp_add]
      congr 2
      ring
    rw [hexp]
    exact hm.trans hbound
  refine ⟨hbase.inter (measurableSet_le hf measurable_const),inter_subset_left,?_⟩
  apply (measure_mono (show base \ sourceGoodPathSet base tops weight bad L ⊆
      {x | Real.exp (-L) ≤ f x} from ?_)).trans
  · rw [← ENNReal.ofReal_toReal hfinite]
    exact ENNReal.ofReal_le_ofReal hreal
  · intro x hx
    have hn : ¬f x ≤ Real.exp (-L) := fun h => hx.2 ⟨hx.1,h⟩
    exact (lt_of_not_ge hn).le

end LipschitzHilbert

end

end OAI
