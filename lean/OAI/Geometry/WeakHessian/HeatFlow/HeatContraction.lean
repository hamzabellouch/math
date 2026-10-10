import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatComparison
import OAI.Geometry.WeakHessian.HeatFlow.HeatCostTopology
import OAI.Geometry.WeakHessian.Transport.EVIContraction

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile73
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

lemma continuous_max_zero_of_continuousOn_Icc {f : ℝ → ℝ}
    (hf : ∀ b : ℝ, ContinuousOn f (Icc 0 b)) : Continuous (fun t => f (max t 0)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hc : Continuous (fun t : ℝ => max t 0) := by fun_prop
  have ht : Tendsto (fun t : ℝ => max t 0) (𝓝 x) (𝓝 (max x 0)) := hc.tendsto x
  apply (hf (max x 0+1) (max x 0) ⟨le_max_right _ _,by linarith⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨ht,?_⟩
  filter_upwards [ht.eventually_le_const (by linarith : max x 0 < max x 0+1)] with y hy
  exact ⟨le_max_right _ _,hy⟩

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_contraction_weighted {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    (hum : ∫ x,u x ∂m = 1) (hvm : ∫ x,v x ∂m = 1)
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (huB : ∀ᵐ x ∂m,|u x| ≤ B) (hvC : ∀ᵐ x ∂m,|v x| ≤ C)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hU' : MemLp (fun x => v x*Real.exp (V x)) 2 m)
    (hdecay : MemLp (fun x => Real.exp (-V x)) 2 m)
    (hD : MemLp (fun x => V x*Real.exp (-V x)) 2 m)
    (hdecayi : Integrable (fun x => Real.exp (-V x)) m)
    (hhalf : MemLp (fun x => Real.exp (-(V x/2))) 2 m)
    (hhalfi : Integrable (fun x => Real.exp (-(V x/2))) m)
    (hW : ∀ T : ℝ≥0, MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m ∧
      MemLp (fun x => (dist x o+T)*Real.exp (-V x)) 2 m)
    (μ ν : ℝ → ProbabilityMeasure X)
    (hμ : ∀ t,0 ≤ t → (μ t:Measure X) = densityMeasure m (cheegerHeat h t u))
    (hν : ∀ t,0 ≤ t → (ν t:Measure X) = densityMeasure m (cheegerHeat h t v))
    {b : ℝ} (hb : 0 ≤ b) :
    Real.exp (2*K*b)*quadraticWassersteinSq (μ b:Measure X) (ν b:Measure X) ≤
      quadraticWassersteinSq (μ 0:Measure X) (ν 0:Measure X) := by
  have hui := integrable_of_integral_eq_one hum
  have hvi := integrable_of_integral_eq_one hvm
  have hE := continuous_max_zero_of_continuousOn_Icc (fun b =>
    hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h u hun hui hV hU hD hdecayi hhalf hhalfi μ hμ (b := b))
  have hF := continuous_max_zero_of_continuousOn_Icc (fun b =>
    hrcd.1.cheegerHeat_entropy_continuousOn_weighted hN hfull hfin o h v hvn hvi hV hU' hD hdecayi hhalf hhalfi ν hν (b := b))
  have hM (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (μ t:Measure X) := by
    rw [hμ t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
      (cheegerHeat_nonneg h ht u hun) (hrcd.1.cheegerHeat_weighted hfin o h u hV hU ht).1 (hW 0).1
  have hM' (t : ℝ) (ht : 0 ≤ t) : Integrable (fun x => dist x o^2) (ν t:Measure X) := by
    rw [hν t ht]
    simpa only [NNReal.coe_zero,add_zero] using densityMeasure_quadratic_integrable o 0 _
      (cheegerHeat_nonneg h ht v hvn) (hrcd.1.cheegerHeat_weighted hfin o h v hV hU' ht).1 (hW 0).1
  have hDc : ContinuousOn (fun t => quadraticWassersteinSq (μ t:Measure X) (ν t:Measure X)) (Icc 0 b) := by
    rw [continuousOn_iff_continuous_domRestrict,continuous_iff_seqContinuous]
    intro ts t ht
    have hT : Tendsto (fun n => (ts n:ℝ)) atTop (𝓝 (t:ℝ)) := (continuous_subtype_val.tendsto t).comp ht
    exact quadraticWassersteinSq_tendsto_pair (μ t) (ν t) (fun n => μ (ts n)) (fun n => ν (ts n)) o
      (hM t t.property.1) (hM' t t.property.1) (fun n => hM (ts n) (ts n).property.1) (fun n => hM' (ts n) (ts n).property.1)
      (hrcd.1.cheegerHeat_cost_zero_tendsto hfin o h u hun hui hV hU (fun T => (hW T).1) μ hμ
        (fun n => (ts n).property.1) t.property.1 hT)
      (hrcd.1.cheegerHeat_cost_zero_tendsto hfin o h v hvn hvi hV hU' (fun T => (hW T).1) ν hν
        (fun n => (ts n).property.1) t.property.1 hT)
  apply evi_doubling_contraction (D := fun s t => quadraticWassersteinSq (μ s:Measure X) (ν t:Measure X)) (K := K) hE hF hb hDc
  · intro x s r hx hs hr
    have H := hrcd.cheegerHeat_comparison_shift hN hfull hfin o h u v hun hvn hum hvm hB hC huB hvC
      hV hU hU' hdecay hD hdecayi hhalf hhalfi hW μ ν hμ hν hx hs hr
    convert H using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht0 : 0 ≤ t := (uIcc_of_le hs ▸ ht).1
    rw [max_eq_left hr,max_eq_left (add_nonneg hx ht0)]
  · intro x s r hx hs hr
    have H := hrcd.cheegerHeat_comparison_shift hN hfull hfin o h v u hvn hun hvm hum hC hB hvC huB
      hV hU' hU hdecay hD hdecayi hhalf hhalfi hW ν μ hν hμ hx hs hr
    simp_rw [quadraticWassersteinSq_comm (ν _:Measure X) (μ _:Measure X)] at H
    convert H using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    have ht0 : 0 ≤ t := (uIcc_of_le hs ▸ ht).1
    rw [max_eq_left hr,max_eq_left (add_nonneg hx ht0)]
end WeakHessian

end
end InlinedFile73

end OAI
