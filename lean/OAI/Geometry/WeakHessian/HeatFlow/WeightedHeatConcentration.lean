import Mathlib
import OAI.Geometry.WeakHessian.Transport.SmoothedPlanSupport
import OAI.Geometry.WeakHessian.Entropy.EntropyDensityBounds
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatLaw
import OAI.Geometry.WeakHessian.Transport.CouplingConcentration

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_abs_bound_probability {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hf : AEStronglyMeasurable f μ) {B : ℝ} (hB : ∀ x,|f x| ≤ B) :
    |∫ x,f x ∂μ| ≤ B := by
  have hi := Integrable.of_bound hf B (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hB x)
  apply abs_integral_le_integral_abs.trans
  simpa only [integral_const,probReal_univ,one_smul] using
    integral_mono_ae hi.abs (integrable_const B) (ae_of_all _ hB)

lemma RCD.weighted_heat_concentration {K N : ℝ} (hN : 1 < N) (hrcd : RCD m K N)
    (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m) (o : X)
    {F : X → ℝ} (hF : Continuous F) {CF : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (u : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x)))
    (hun : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),0 ≤ u x)
    (hum : ∫ x,u x ∂exponentialMeasure m (fun x => a*F x) = 1)
    {Bu : ℝ} (hBu : 0 ≤ Bu) (hub : ∀ᵐ x ∂exponentialMeasure m (fun x => a*F x),|u x| ≤ Bu)
    {r : ℝ} (hr : 0 ≤ r)
    (hs : ∀ᵐ x ∂densityMeasure (exponentialMeasure m (fun x => a*F x)) u,dist x o ≤ r)
    {B : ℝ≥0} (hB : 0 < B)
    (hcap : densityMeasure (exponentialMeasure m (fun x => a*F x)) u ≤ (B:ℝ≥0∞) • m)
    {c : ℝ} (hc : 0 < c) (he : Integrable (fun x => Real.exp (-(c*dist x o))) m)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ μ : ProbabilityMeasure X,(μ:Measure X) = densityMeasure (exponentialMeasure m (fun x => a*F x)) (cheegerHeat h T u) ∧
      FiniteEntropy m (μ:Measure X) ∧ Integrable (fun x => dist x o) (μ:Measure X) ∧
      (∫ x,dist x o ∂(μ:Measure X))^2 ≤
        4*r^2+8*T*(|Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1)+
          16*(T*a)*CF+16*T^2*c^2 := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal)
    (exponentialMeasure_comparable (m := m) (V := fun x => a*F x)
      (fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a))).2
  let : SigmaFinite ν := sigmaFinite_of_finiteOnBoundedSets ν hnfin o
  have hVb : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hVm : Measurable (fun x => a*F x) := (continuous_const.mul hF).measurable
  have hsupport : ∀ᵐ x ∂ν,r+1 ≤ dist x o → u x = 0 := by
    filter_upwards [density_zero_of_ae_law hun hs] with x hx hd
    exact hx (by linarith)
  obtain ⟨μ,hμ,hEν,hEm,hμi,heμ⟩ := hrcd.weighted_heat_law_finiteEntropy hN hfull hfin o hVm hVb h u hun hum hsupport hT
  obtain ⟨μ₀,hμ₀,hEν₀,hEm₀,hμi₀,heμ₀⟩ := hrcd.weighted_heat_law_finiteEntropy hN hfull hfin o hVm hVb h u hun hum hsupport (T := 0) le_rfl
  rw [cheegerHeat_zero] at hμ₀
  change (μ₀ : Measure X) = densityMeasure ν u at hμ₀
  have hupper : entropyReal ν (μ₀:Measure X) ≤ Real.log B-a*(∫ x,F x ∂(μ₀:Measure X)) := by
    have H := entropyReal_exponential_upper hEm₀ hVm hVb hB (by rwa [hμ₀])
    rwa [integral_const_mul] at H
  have hlower : 1-c*(∫ x,dist x o ∂(μ:Measure X))-(∫ x,Real.exp (-(c*dist x o)) ∂m)-
      a*(∫ x,F x ∂(μ:Measure X)) ≤ entropyReal ν (μ:Measure X) := by
    rw [heμ,integral_const_mul]
    have H := entropyReal_lower_confinement hEm (hμi.const_mul c) he
    rw [integral_const_mul] at H
    linarith
  let D := |Real.log (B:ℝ)|+(∫ x,Real.exp (-(c*dist x o)) ∂m)+1
  let y := ∫ x,dist x o ∂(μ:Measure X)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hy : 0 ≤ y := integral_nonneg fun x => dist_nonneg
  have hCF : 0 ≤ CF := (abs_nonneg (F o)).trans (hFb o)
  have hdrop : entropyReal ν (μ₀:Measure X)-entropyReal ν (μ:Measure X) ≤ D+2*a*CF+c*y := by
    have hF0 := integral_abs_bound_probability hF.aestronglyMeasurable (μ := (μ₀:Measure X)) hFb
    have hF1 := integral_abs_bound_probability hF.aestronglyMeasurable (μ := (μ:Measure X)) hFb
    have H0 := (abs_le.mp hF0).1
    have H1 := (abs_le.mp hF1).2
    have hlog := le_abs_self (Real.log (B:ℝ))
    dsimp [D,y]
    nlinarith
  obtain ⟨p,hp,hp0,hp1,hcost⟩ := hrcd.weighted_heat_entropy_real_coupling hN hfull hfin o hVb h u hun hum hBu hub hsupport hT
  let := hp
  have hcost' : QuadraticTransportCost p ≤ ENNReal.ofReal (2*T*(D+2*a*CF+c*y)) := by
    apply hcost.trans
    apply ENNReal.ofReal_le_ofReal
    rw [← hμ₀,← hμ]
    exact mul_le_mul_of_nonneg_left hdrop (by positivity)
  have H := coupling_firstMoment_le (μ := (μ:Measure X))
    (ν := (μ₀:Measure X)) ⟨hp0.trans hμ.symm,hp1.trans hμ₀.symm⟩ o hμi
    (by positivity : 0 ≤ 2*T*(D+2*a*CF+c*y)) (by rwa [hμ₀]) hcost'
  refine ⟨μ,hμ,hEm,hμi,?_⟩
  exact firstMoment_entropy_absorption hy hr hT hD ha hCF hc.le H

end WeakHessian

end
end

end OAI
