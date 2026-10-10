import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatEntropyDissipation
import OAI.Geometry.WeakHessian.HeatFlow.HeatLipschitz
import OAI.Geometry.WeakHessian.HeatFlow.HeatDifferential

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile51
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] in
lemma entropyReal_eq_reducedDensity (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m,0 ≤ u x)
    (hi : Integrable u m) (hr : Integrable (fun x => reducedEntropy (u x)) m)
    (μ : ProbabilityMeasure X) (hμ : (μ:Measure X) = densityMeasure m u) :
    entropyReal m (μ:Measure X) = (∫ x,reducedEntropy (u x) ∂m)+1 := by
  have hmass : (∫ x,u x ∂m) = 1 := by
    have H := integral_densityMeasure m u hun (fun _ => (1:ℝ))
    rw [← hμ] at H
    simpa using H.symm
  have he := hμ.trans (densityMeasure_eq_square_sqrt u hun)
  let : IsFiniteMeasure (squareDensityMeasure m (fun x => Real.sqrt (u x))) := he ▸ inferInstance
  rw [he,squareDensity_entropy_eq (Lp.stronglyMeasurable u |>.measurable.sqrt),← hmass,← integral_add hr hi]
  apply integral_congr_ae
  filter_upwards [hun] with x hx
  simp only [Real.sq_sqrt hx,reducedEntropy,sub_add_cancel]

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_entropy_continuousOn {K N : ℝ}
    (hN : 1 < N) (hcd : CurvatureDimension m K N) (hfull : FullSupport m)
    (hfin : FiniteOnBoundedSets m) (o : X) (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    {b : ℝ} (hb : 0 ≤ b) : ContinuousOn (fun t => entropyReal m (μ t:Measure X)) (Icc 0 b) := by
  have hI := hcd.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  have hac := hI.2.1.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp)
  have hc : ContinuousOn (fun t => (∫ x,reducedEntropy (u x) ∂m)+1-
      ∫ r in 0..t,∫ x,fisherDensity (m := m) (cheegerHeat h r u) x ∂m) (Icc 0 b) := by
    apply ContinuousOn.sub continuousOn_const
    simpa only [uIcc_of_le hb] using hac.continuousOn
  apply hc.congr
  intro t ht
  dsimp only
  rw [hcd.cheegerHeat_entropy_dissipation hN hfull hfin o h hu hun hi hV hU hD hw ht.1,
    entropyReal_eq_reducedDensity _ (cheegerHeat_nonneg h ht.1 u hun)
      (cheegerHeat_integrable hfin o h u hi ht.1).1
      (integrable_reducedEntropy (Lp.memLp _) (cheegerHeat_nonneg h ht.1 u hun)
        (weighted_pairing (hcd.cheegerHeat_weighted hfin o h u hV hU ht.1).1 hD).1 hw) (μ t) (hμ t ht.1)]
  ring

lemma CurvatureDimension.cheegerHeat_cost_ac {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (hn : (ν:Measure X) ≪ m) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    AbsolutelyContinuousOnInterval (fun t => quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)) 0 b := by
  let C : ℝ≥0 := ⟨2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖,by positivity⟩
  have hl : LipschitzOnWith C (fun t => quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)) (Icc 0 b) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    convert! hcd.cheegerHeat_cost_lipschitz hfin o h hu hun hi hV hU hA μ hμ ν hn T hT hsν hW ht hs using 1
  apply LipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [uIcc_of_le hb] using hl

lemma RCD.cheegerHeat_comparison_ae {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hi : Integrable u m)
    {B : ℝ} (hB : 0 ≤ B) (huB : ∀ᵐ x ∂m,u x ≤ B)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hw : Integrable (fun x => Real.exp (-V x)) m)
    (μ : ℝ → ProbabilityMeasure X) (hμ : ∀ t, 0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (ν : ProbabilityMeasure X) (T : ℝ≥0) (hT : 0 < T)
    (hsν : (ν:Measure X) (Metric.closedBall o T)ᶜ = 0)
    {C : ℝ≥0∞} (hCt : C ≠ ∞) (hdν : (ν:Measure X) ≤ C • m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m)
    (hW1 : MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    {b : ℝ} (hb : 0 ≤ b) :
    ∀ᵐ t ∂volume.restrict (Icc 0 b),
      deriv (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)) t/2+
        K/2*quadraticWassersteinSq (μ t:Measure X) (ν:Measure X) ≤
          entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X) := by
  have hac := hrcd.1.cheegerHeat_cost_ac hfin o h hu hun hi hV hU hA μ hμ ν
    (Measure.absolutelyContinuous_of_le_smul hdν) T hT hsν hW hb
  have hI := hrcd.1.cheegerHeat_fisher_finite_action hN hfull hfin o h hu hun hi hV hU hD hw hb
  filter_upwards [ae_restrict_mem measurableSet_Icc,hI.1,
    ae_restrict_of_ae hac.ae_differentiableAt,ae_restrict_of_ae (show ∀ᵐ t ∂(volume:Measure ℝ), t ≠ 0 by simp [ae_iff])] with t ht hIt hdt ht0
  exact hrcd.cheegerHeat_comparison_deriv hN hfin o h hu hun hi hB huB hV hU hA hD hw μ hμ
    ν T hT hsν hCt hdν hW hW1 (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hIt
    (hdt (by simpa only [uIcc_of_le hb] using ht)).hasDerivAt
end WeakHessian

end
end InlinedFile51

end OAI
