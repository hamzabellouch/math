import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatAbs
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatFTC
import OAI.Geometry.WeakHessian.HeatFlow.HeatCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile50
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

lemma RCD.cheegerHeat_comparison_deriv {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfin : FiniteOnBoundedSets m) (o : X)
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
    {t d : ℝ} (ht : 0 < t)
    (hI : Integrable (fisherDensity (m := m) (cheegerHeat h t u)) m)
    (hd : HasDerivAt (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)) d t) :
    d/2+K/2*quadraticWassersteinSq (μ t:Measure X) (ν:Measure X) ≤
      entropyReal m (ν:Measure X)-entropyReal m (μ t:Measure X) := by
  have hn (s : ℝ) (hs : 0 ≤ s) := cheegerHeat_nonneg h hs u hun
  have hi' (s : ℝ) (hs : 0 ≤ s) := (cheegerHeat_integrable hfin o h u hi hs).1
  have hwU (s : ℝ) (hs : 0 ≤ s) := (hrcd.1.cheegerHeat_weighted hfin o h u hV hU hs).1
  have hwA := (hrcd.1.cheegerHeat_weighted hfin o h A hV hA ht.le).1
  have hB' (s : ℝ) (hs : 0 ≤ s) : ∀ᵐ x ∂m,cheegerHeat h s u x ≤ B :=
    (cheegerHeat_bounded h hs hB u ((hun.and huB).mono fun x hx => by rw [abs_of_nonneg hx.1]; exact hx.2)).mono
      fun x hx => (le_abs_self _).trans hx
  have hL := hrcd.1.global_isLaplacian_of_formGenerator hfin o h (cheegerHeat h t u)
    (cheegerHeat h t A) ((cheeger_closedQuadraticEnergy h).formGenerator_heat m hu t)
  have hEnt : FiniteEntropy m (μ t:Measure X) := by
    have he := hμ t ht.le
    let : IsFiniteMeasure (densityMeasure m (cheegerHeat h t u)) := he ▸ inferInstance
    rw [he]
    exact densityMeasure_finiteEntropy _ (hn t ht.le) (hi' t ht.le) (weighted_pairing (hwU t ht.le) hD).1 hw
  obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar,hent⟩ := hrcd.generator_entropy_subdifferential hN hfin o hL
    (hn t ht.le) (hi' t ht.le) hB (hB' t ht.le) hI (μ t) ν (hμ t ht.le) hEnt T hT hV
    (hwU t ht.le) hwA hW hW1 hsν hCt hdν
  have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
  have hp := hrcd.1.cheegerHeat_weighted_deriv hfin o h hu hV hU hA hφW
    (hφ.cut_memLp hfin o hT) ht
  have hmin : IsLocalMin (fun s => quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)-
      2*(∫ x,cheegerHeat h s u x*φ x ∂m)) t := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hnν : (ν:Measure X) ≪ m := Measure.absolutelyContinuous_of_le_smul hdν
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hrcd.1.density_cost_support o T (cheegerHeat h s u)
      (hn s hs.le) (hi' s hs.le) (μ s) ν (hμ s hs.le) hnν hsν (hwU s hs.le) hW
    have hSW : Integrable (fun x => (dist x o+T)^2) (μ s:Measure X) := by
      rw [hμ s hs.le]
      exact densityMeasure_quadratic_integrable o T _ (hn s hs.le) (hwU s hs.le) hW
    have H := hvar (μ s) hSW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,
      hμ t ht.le,hμ s hs.le,integral_densityMeasure m _ (hn t ht.le),integral_densityMeasure m _ (hn s hs.le)] at H
    rw [← hμ t ht.le,← hμ s hs.le] at H
    change quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)-2*(∫ x,cheegerHeat h t u x*φ x ∂m) ≤ _
    linarith
  have H := hmin.hasDerivAt_eq_zero (hd.sub (hp.const_mul 2))
  rw [← hqo.quadraticWassersteinSq_eq] at hent
  linarith
end WeakHessian

end
end InlinedFile50

end OAI
