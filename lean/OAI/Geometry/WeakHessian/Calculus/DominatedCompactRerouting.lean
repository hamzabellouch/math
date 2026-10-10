import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.StrictSurplusCarrier

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessian
open MeasureTheory Set
open scoped ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma exists_dominated_of_compact_rerouting (ν : Measure X) [IsFiniteMeasure ν]
    {S : Set (ProbabilityMeasure X)} (hne : S.Nonempty) (hc : IsCompact S)
    (hr : ∀ μ ∈ S, ∀ P : Set X, StrictSurplusCarrier (μ:Measure X) ν P →
      0 < ((μ:Measure X)-ν) univ →
      ∃ (ρ β : Measure X) (η : ProbabilityMeasure X), IsFiniteMeasure β ∧
        ρ ≤ (μ:Measure X)-ν ∧ β univ = ρ univ ∧ η ∈ S ∧
        (η:Measure X) = (μ:Measure X)-ρ+β ∧
        ∀ B : Set X, MeasurableSet B → β Bᶜ = 0 →
          ν P + ((μ:Measure X)-ν) univ ≤ ν B) :
    ∃ μ ∈ S, (μ:Measure X) ≤ ν := by
  obtain ⟨μ₀,hμ₀,hmin⟩ := exists_cappedExcess_minimizer ν hne hc
  suffices hzero : cappedExcess ν μ₀ = 0 from ⟨μ₀,hμ₀,(cappedExcess_eq_zero_iff ν μ₀).mp hzero⟩
  by_contra hz
  let e := cappedExcess ν μ₀
  have he0 : 0 < e := bot_lt_iff_ne_bot.mpr hz
  have het : e ≠ ∞ := ne_top_of_le_ne_top (by simp) (cappedExcess_le_one ν μ₀)
  have he : 0 < e.toReal := ENNReal.toReal_pos he0.ne' het
  let T : Set ℝ := {a | ∃ μ ∈ S, cappedExcess ν μ = e ∧
    ∃ P : Set X, StrictSurplusCarrier (μ:Measure X) ν P ∧ a = (ν P).toReal}
  have hTne : T.Nonempty := by
    obtain ⟨P,hP⟩ := exists_strictSurplusCarrier (μ₀:Measure X) ν
    exact ⟨(ν P).toReal,μ₀,hμ₀,rfl,P,hP,rfl⟩
  have hTb : BddAbove T := by
    refine ⟨(ν univ).toReal,?_⟩
    rintro a ⟨μ,hμ,heq,P,hP,rfl⟩
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (subset_univ _))
  obtain ⟨a,ha,halt⟩ := exists_lt_of_lt_csSup hTne
    (show sSup T-e.toReal < sSup T by linarith)
  obtain ⟨μ,hμ,hμe,P,hP,rfl⟩ := ha
  have hμδ : ((μ:Measure X)-ν) univ = e := by
    rw [← cappedExcess_eq_positivePart]
    exact hμe
  obtain ⟨ρ,β,η,hβ,hρ,hmass,hη,hηeq,hspread⟩ := hr μ hμ P hP (by rw [hμδ]; exact he0)
  let := hβ
  let : IsFiniteMeasure ρ := isFiniteMeasure_of_le (μ:Measure X) (hρ.trans Measure.sub_le)
  have hmin' : ((μ:Measure X)-ν) univ ≤ (((μ:Measure X)-ρ+β)-ν) univ := by
    rw [← hηeq,← cappedExcess_eq_positivePart,← cappedExcess_eq_positivePart,hμe]
    exact hmin η hη
  obtain ⟨Q,hQ,hgrowth⟩ := excess_relocation_carrier_growth
    (μ:Measure X) ν ρ β hP hρ hmass hmin' hspread
  obtain ⟨hδ,_,_⟩ := excess_relocation_complementarity
    (μ:Measure X) ν ρ β hρ hmass hmin'
  have hηe : cappedExcess ν η = e := by
    rw [cappedExcess_eq_positivePart,hηeq,hδ,Measure.add_apply,
      Measure.sub_apply MeasurableSet.univ hρ,hmass,
      tsub_add_cancel_of_le (hρ univ),hμδ]
  have hQ' : StrictSurplusCarrier (η:Measure X) ν Q := hηeq.symm ▸ hQ
  have hQmem : (ν Q).toReal ∈ T := ⟨η,hη,hηe,Q,hQ',rfl⟩
  have hQsup : (ν Q).toReal ≤ sSup T := le_csSup hTb hQmem
  rw [hμδ] at hgrowth
  have hreal := ENNReal.toReal_mono (measure_ne_top ν Q) hgrowth
  rw [ENNReal.toReal_add (measure_ne_top ν P) het] at hreal
  linarith

end WeakHessian

end
end InlinedFile0

end OAI
