import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.HeatEntropyTransport

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_renormalizedEntropy_eq (u : Lp ℝ 2 m) (hu : Integrable u m)
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x,renormalizedEntropy ε (u x) ∂m) =
      (∫ x,regularizedEntropy ε (u x) ∂m)+Real.log ε*(∫ x,u x ∂m) := by
  simp only [renormalizedEntropy]
  rw [integral_add (regularizedEntropy_integrable hε u) (hu.const_mul _),integral_const_mul]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma tendsto_regularizedEntropy_difference (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    Tendsto (fun n => (∫ x,regularizedEntropy (fisherEpsilon n) (u x) ∂m)-
      (∫ x,regularizedEntropy (fisherEpsilon n) (v x) ∂m)) atTop
      (𝓝 ((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (v x) ∂m))) := by
  have H := (tendsto_integral_renormalizedEntropy (Lp.memLp u) hun huV hV).sub
    (tendsto_integral_renormalizedEntropy (Lp.memLp v) hvn hvV hV)
  simpa only [integral_renormalizedEntropy_eq u hu (fisherEpsilon_pos _),
    integral_renormalizedEntropy_eq v hv (fisherEpsilon_pos _),hm,add_sub_add_right_eq_sub] using H

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
    [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma entropy_dual_of_regularized (u v : Lp ℝ 2 m)
    (hu : Integrable u m) (hv : Integrable v m)
    (hm : (∫ x,u x ∂m) = ∫ x,v x ∂m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hvV : Integrable (fun x => v x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m)
    {A B T D : ℝ} (hd : ∀ ε : ℝ,0 < ε →
      A+T*((∫ x,regularizedEntropy ε (u x) ∂m)-
        (∫ x,regularizedEntropy ε (v x) ∂m)) ≤ B+ε*D) :
    A+T*((∫ x,reducedEntropy (u x) ∂m)-
      (∫ x,reducedEntropy (v x) ∂m)) ≤ B := by
  have H := le_of_tendsto_of_tendsto
    ((tendsto_regularizedEntropy_difference u v hu hv hm hun hvn huV hvV hV).const_mul T |>.const_add A)
    (fisherEpsilon_tendsto.mul_const D |>.const_add B)
    (Eventually.of_forall fun n => hd (fisherEpsilon n) (fisherEpsilon_pos n))
  simpa only [zero_mul,add_zero] using H

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_entropy_dual_reduced
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T q : ℝ} (hT : 0 ≤ T) (hq : 0 < q)
    (hui : Integrable u m) (hPi : Integrable (cheegerHeat h T u) m)
    (hm : (∫ x,cheegerHeat h T u x ∂m) = ∫ x,u x ∂m)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hPV : Integrable (fun x => cheegerHeat h T u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) :
    (∫ x,cheegerHeat h T u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x,u x*boundedHopfMap f q x ∂m)+
      T*((∫ x,reducedEntropy (cheegerHeat h T u x) ∂m)-
        (∫ x,reducedEntropy (u x) ∂m)) ≤ 0 := by
  apply entropy_dual_of_regularized (cheegerHeat h T u) u hPi hui hm
    (cheegerHeat_nonneg h hT u hun) hun hPV huV hV
    (D := compactHopfDualBound hfin o f hf hq/2)
  intro ε hε
  simpa only [zero_add,mul_div_assoc] using
    cheegerHeat_entropy_dual hfin o hID hpar h u hun hub hB hT hq f hf hε

end WeakHessian

end
end

end OAI
