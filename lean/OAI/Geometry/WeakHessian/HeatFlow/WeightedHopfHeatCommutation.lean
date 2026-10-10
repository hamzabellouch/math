import Mathlib
import OAI.Geometry.WeakHessian.Transport.DriftLipschitzContraction
import OAI.Geometry.WeakHessian.HeatFlow.WeightedHeatCostAction
import OAI.Geometry.WeakHessian.LocalBounds.BoundedLawDualPointwise

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile229
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma WeakHessianUpperBound.rcd_weighted_hopf_heat_commutation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (o : X) {F G : X → ℝ} (hHess : WeakHessianUpperBound m F G)
    {L : ℝ≥0} (hF : LipschitzWith L F) {CF CG : ℝ} (hFb : ∀ x,|F x| ≤ CF)
    (hGb : ∀ x,|G x| ≤ CG) (hGc : Continuous G) {a : ℝ} (ha : 0 ≤ a)
    (h : QuadraticCheegerEnergy (exponentialMeasure m (fun x => a*F x)))
    (φ : X →ᵇ ℝ) (hφ : HasCompactSupport (φ : X → ℝ)) {D : ℝ≥0} (hφL : LipschitzWith D φ)
    {T : ℝ} (hT : 0 ≤ T) :
    ∃ (u v : Lp ℝ 2 (exponentialMeasure m (fun x => a*F x))) (U V : X → ℝ),
      u =ᵐ[exponentialMeasure m (fun x => a*F x)] φ ∧
      v =ᵐ[exponentialMeasure m (fun x => a*F x)] boundedHopfMap φ 1 ∧
      GloballyLipschitz U ∧ GloballyLipschitz V ∧
      U =ᵐ[exponentialMeasure m (fun x => a*F x)] cheegerHeat h T u ∧
      V =ᵐ[exponentialMeasure m (fun x => a*F x)] cheegerHeat h T v ∧
      ∀ x,V x ≤ hopfLax U (Real.exp (2*(K-a*CG)*T)) x := by
  let ν := exponentialMeasure m (fun x => a*F x)
  have hVB : ∀ x,|a*F x| ≤ |a| *CF := fun x => by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hFb x) (abs_nonneg a)
  have hcomp := exponentialMeasure_comparable (m := m) hVB
  have hnfin := hfin.of_le_smul (C := (Real.exp (|a| *CF)).toNNReal) hcomp.2
  obtain ⟨u,v,hu,hv,hcost⟩ := hHess.rcd_weighted_heat_hopf_cost hN hrcd hfull hfin o
    hF hFb hGb hGc ha h φ hφ hφL hT
  have hφS := sobolev_of_lipschitz_compactSupport hnfin hφL hφ
  obtain ⟨DQ,hQL⟩ := boundedHopfMap_lipschitz φ (by norm_num : (0:ℝ)<1)
  have hQS := sobolev_of_lipschitz_compactSupport hnfin hQL
    (boundedHopfMap_compactSupport φ o hφ (by norm_num : (0:ℝ)<1))
  obtain ⟨U,hUL,hU⟩ := hHess.rcd_weighted_heat_lipschitz hN hrcd hfull hfin o
    hF hFb hGb hGc ha h hφL hφS hT
  obtain ⟨V,hVL,hV⟩ := hHess.rcd_weighted_heat_lipschitz hN hrcd hfull hfin o
    hF hFb hGb hGc ha h hQL hQS hT
  have hue : hφS.1.toLp (φ:X→ℝ) = u := Lp.ext (hφS.1.coeFn_toLp.trans hu.symm)
  have hve : hQS.1.toLp (boundedHopfMap φ 1:X→ℝ) = v := Lp.ext (hQS.1.coeFn_toLp.trans hv.symm)
  rw [hue] at hU
  rw [hve] at hV
  refine ⟨u,v,U,V,hu,hv,⟨_,hUL⟩,⟨_,hVL⟩,hU,hV,?_⟩
  have HD : ∀ x y,V x-U y ≤ (2*Real.exp (2*(K-a*CG)*T))⁻¹*dist x y^2 := by
    apply lipschitz_dual_of_bounded_laws hfull hfin o hVL hUL (by positivity)
    intro μ₀ μ₁ R hs₀ hs₁ C hC0 hCt hd₀ hd₁
    have hac₀ : (μ₀:Measure X) ≪ ν :=
      (Measure.absolutelyContinuous_of_le_smul hd₀).trans (Measure.absolutelyContinuous_of_le_smul hcomp.1)
    have hac₁ : (μ₁:Measure X) ≪ ν :=
      (Measure.absolutelyContinuous_of_le_smul hd₁).trans (Measure.absolutelyContinuous_of_le_smul hcomp.1)
    have H := hcost μ₀ μ₁ R hs₀ hs₁ C hC0 hCt hd₀ hd₁
    rw [← integral_congr_ae (hac₀.ae_le hU),← integral_congr_ae (hac₁.ae_le hV)] at H
    simpa only [div_eq_mul_inv,mul_comm] using H
  intro x
  apply le_csInf ⟨hopfObjective U (Real.exp (2*(K-a*CG)*T)) x x,mem_range_self x⟩
  rintro z ⟨y,rfl⟩
  have H := HD x y
  dsimp only [hopfObjective]
  linarith [show dist x y^2/(2*Real.exp (2*(K-a*CG)*T)) =
    (2*Real.exp (2*(K-a*CG)*T))⁻¹*dist x y^2 by ring]
end WeakHessian

end
end InlinedFile229

end OAI
