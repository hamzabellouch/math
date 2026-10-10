import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.CheegerHeatAbs
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatFTC
import OAI.Geometry.WeakHessian.HeatFlow.HeatCost

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile49
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}

omit [CompleteSpace X] in
lemma CurvatureDimension.cheegerHeat_weighted_pairing_lipschitz {K N : ℝ}
    (hcd : CurvatureDimension m K N) (hfin : FiniteOnBoundedSets m) (o : X)
    (h : QuadraticCheegerEnergy m) {u A : Lp ℝ 2 m}
    (hu : (cheeger_closedQuadraticEnergy h).IsFormGenerator u A)
    {V : X → ℝ} {L : ℝ≥0} (hV : LipschitzWith L V)
    (hU : MemLp (fun x => u x*Real.exp (V x)) 2 m)
    (hA : MemLp (fun x => A x*Real.exp (V x)) 2 m)
    {φ : X → ℝ} (hφ : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hcut : ∀ n, MemLp (fun x => φ x*radialCutoff o n x) 2 m)
    {b s t : ℝ} (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    |(∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m)| ≤
      (‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hφ.toLp _‖)*|t-s| := by
  let g (s : ℝ) := ∫ x,cheegerHeat h (max s 0) A x*φ x ∂m
  have hc : Continuous g := hcd.cheegerHeat_weighted_pairing_continuous hfin o h A hV hA hφ hcut
  have he (r : ℝ) (hr : 0 ≤ r) : (∫ z in 0..r,g z) =
      (∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,u x*φ x ∂m) := by
    rw [← hcd.cheegerHeat_weighted_FTC hfin o h hu hV hU hA hφ hcut hr]
    apply intervalIntegral.integral_congr
    intro z hz
    rw [uIcc_of_le hr] at hz
    simp only [g,max_eq_left hz.1]
  have hst := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 s) (hc.intervalIntegrable (μ := volume) s t)
  rw [he s hs.1,he t ht.1] at hst
  have he' : (∫ x,cheegerHeat h t u x*φ x ∂m)-(∫ x,cheegerHeat h s u x*φ x ∂m) = ∫ z in s..t,g z := by linarith
  rw [he',← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro z hz
  have hz' : z ∈ Icc 0 b := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hz)
  simp only [g,max_eq_left hz'.1]
  exact (weighted_pairing (hcd.cheegerHeat_weighted hfin o h A hV hA hz'.1).1 hφ).2.trans
    (mul_le_mul_of_nonneg_right
      ((hcd.cheegerHeat_weighted_norm hfin o h A hV hA hz'.1).trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz'.2 (sq_nonneg _))) (norm_nonneg _)))
      (norm_nonneg _))

omit [BorelSpace X] [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma QuadraticLipschitzBound.weighted_norm_le (o : X) {T : ℝ} (hT : 0 ≤ T)
    {φ V : X → ℝ} (hφ : QuadraticLipschitzBound o T φ) (hzero : φ o = 0)
    (hφW : MemLp (fun x => φ x*Real.exp (-V x)) 2 m)
    (hW : MemLp (fun x => (dist x o+T)^2*Real.exp (-V x)) 2 m) :
    ‖hφW.toLp _‖ ≤ ‖hW.toLp _‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [hφW.coeFn_toLp,hW.coeFn_toLp] with x hx hy
  rw [hx,hy]
  simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg (dist x o+T)),abs_of_pos (Real.exp_pos (-V x))]
  exact mul_le_mul_of_nonneg_right (hφ.centered_bound hT hzero x) (Real.exp_pos _).le

variable [SigmaFinite m]

lemma CurvatureDimension.cheegerHeat_cost_lipschitz {K N : ℝ}
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
    {b s t : ℝ} (hs : s ∈ Icc 0 b) (ht : t ∈ Icc 0 b) :
    |quadraticWassersteinSq (μ t:Measure X) (ν:Measure X)-quadraticWassersteinSq (μ s:Measure X) (ν:Measure X)| ≤
      (2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|t-s| := by
  have hw (r : ℝ) (hr : 0 ≤ r) := (hcd.cheegerHeat_weighted hfin o h u hV hU hr).1
  have hnU (r : ℝ) (hr : 0 ≤ r) := cheegerHeat_nonneg h hr u hun
  have hiU (r : ℝ) (hr : 0 ≤ r) := (cheegerHeat_integrable hfin o h u hi hr).1
  have hex (r : ℝ) (hr : 0 ≤ r) := hcd.density_cost_support o T (cheegerHeat h r u)
    (hnU r hr) (hiU r hr) (μ r) ν (hμ r hr) hn hsν (hw r hr) hW
  have one (r v : ℝ) (hr : r ∈ Icc 0 b) (hv : v ∈ Icc 0 b) :
      quadraticWassersteinSq (μ r:Measure X) (ν:Measure X)-quadraticWassersteinSq (μ v:Measure X) (ν:Measure X) ≤
        (2*‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v| := by
    obtain ⟨q,φ,hqp,hqo,hqt,hφ,hφ0,hvar⟩ := hex r hr.1
    obtain ⟨q',ψ,hq'p,hq'o,hq't,_⟩ := hex v hv.1
    have hvW : Integrable (fun x => (dist x o+T)^2) (μ v:Measure X) := by
      rw [hμ v hv.1]
      exact densityMeasure_quadratic_integrable o T _ (hnU v hv.1) (hw v hv.1) hW
    have H := hvar (μ v) hvW q' hq'o.1 hq't
    rw [← hqo.quadraticWassersteinSq_eq,← hq'o.quadraticWassersteinSq_eq,
      hμ r hr.1,hμ v hv.1,integral_densityMeasure m _ (hnU r hr.1),integral_densityMeasure m _ (hnU v hv.1)] at H
    rw [← hμ r hr.1,← hμ v hv.1] at H
    have hφW := hφ.weighted_memLp o T.coe_nonneg hφ0 hV.continuous.measurable hW
    have H' := hcd.cheegerHeat_weighted_pairing_lipschitz hfin o h hu hV hU hA hφW
      (hφ.cut_memLp hfin o hT) hv hr
    have Hnorm := hφ.weighted_norm_le o T.coe_nonneg hφ0 hφW hW
    have H'' : |(∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,cheegerHeat h v u x*φ x ∂m)| ≤
        (‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v| :=
      H'.trans (by gcongr)
    calc
      _ ≤ 2*((∫ x,cheegerHeat h r u x*φ x ∂m)-(∫ x,cheegerHeat h v u x*φ x ∂m)) := H
      _ ≤ 2*((‖hA.toLp _‖*Real.exp ((L:ℝ)^2*b)*‖hW.toLp _‖)*|r-v|) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans H'') (by norm_num)
      _ = _ := by ring
  apply abs_le.mpr
  exact ⟨by have H := one s t hs ht; rw [abs_sub_comm s t] at H; linarith,one t s ht hs⟩
end WeakHessian

end
end InlinedFile49

end OAI
