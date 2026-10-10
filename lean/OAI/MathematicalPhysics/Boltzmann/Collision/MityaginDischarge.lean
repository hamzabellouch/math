import OAI.MathematicalPhysics.Boltzmann.Collision.AnalyticRankAlmostEverywhere
import OAI.MathematicalPhysics.Boltzmann.Collision.MityaginPublished
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-! # Twenty-dimensional analytic zero-set nullity

One-dimensional isolated zeros, Fubini along lines through a nonzero point,
and the analytic identity principle give the required specialization of
Mityagin's Proposition 0.
-/
noncomputable section
open MeasureTheory MeasureTheory.Measure Set
namespace BoltzmannNonuniqueness.Published

def fiveGainParameterEquiv : FanPhase ≃L[ℝ] FiveGainMap.Parameters :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simp [FanPhase,FanRemainder,FiveGainMap.Parameters,FiveGainMap.V,
      Module.finrank_pi_fintype])

theorem mityagin2020FiveGainParameters : Mityagin2020FiveGainParameters := by
  classical
  intro U hU hconn f hf hne
  let e := fiveGainParameterEquiv
  have hpre : IsOpen (e ⁻¹' U) := hU.preimage e.continuous
  have hc : IsPreconnected (e ⁻¹' U) := e.toHomeomorph.isPreconnected_preimage.mpr hconn
  have ha : AnalyticOnNhd ℝ (f ∘ e) (e ⁻¹' U) := by
    intro x hx
    exact (hf _ hx).comp (e.toContinuousLinearMap.analyticAt x)
  have hn : ∃ a ∈ e ⁻¹' U, (f ∘ e) a ≠ 0 := by
    obtain ⟨a,ha,hfa⟩ := hne
    exact ⟨e.symm a,by simpa using ha,by simpa using hfa⟩
  have hnull := analytic_connected_zero_null hpre hc ha hn
  have : IsAddHaarMeasure (volume : Measure FanPhase) := by
    change IsAddHaarMeasure ((volume : Measure ℝ).prod (volume : Measure FanRemainder))
    infer_instance
  have : IsAddHaarMeasure (volume : Measure FiveGainMap.V) := by
    exact isAddHaarMeasure_volume_pi (Fin 3)
  have : IsAddHaarMeasure (volume : Measure (Fin 5 → ℝ)) :=
    isAddHaarMeasure_volume_pi (Fin 5)
  have : IsAddHaarMeasure (volume : Measure (Fin 5 → FiveGainMap.V)) := by
    infer_instance
  have : IsAddHaarMeasure (volume : Measure FiveGainMap.Parameters) := by
    change IsAddHaarMeasure ((volume : Measure (Fin 5 → ℝ)).prod
      (volume : Measure (Fin 5 → FiveGainMap.V)))
    infer_instance
  have hac : (volume : Measure FiveGainMap.Parameters) ≪
      Measure.map e (volume : Measure FanPhase) :=
    Measure.absolutelyContinuous_isAddHaarMeasure _ _
  have hm : MeasurableSet {x ∈ U | f x = 0} := by
    let g := U.piecewise f 0
    have hg : Measurable g := hf.continuousOn.measurable_piecewise
      continuous_zero.continuousOn hU.measurableSet
    have he : {x ∈ U | f x = 0} = U ∩ {x | g x = 0} := by
      ext x
      by_cases hx : x ∈ U <;> simp [g,hx]
    rw [he]
    exact hU.measurableSet.inter (measurableSet_eq_fun hg measurable_const)
  apply hac
  rw [Measure.map_apply e.continuous.measurable hm]
  exact hnull

end BoltzmannNonuniqueness.Published

end

end OAI
