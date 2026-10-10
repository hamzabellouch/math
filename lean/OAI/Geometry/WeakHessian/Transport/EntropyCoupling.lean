import Mathlib
import OAI.Geometry.WeakHessian.Calculus.CompactHopfDualLimit
import OAI.Geometry.WeakHessian.Entropy.ReducedEntropyDual

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

omit [TopologicalSpace.SeparableSpace X] in
lemma compact_hopf_dual_zero_time (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (f : X →ᵇ ℝ)
    (hf : GloballyLipschitz (f : X → ℝ)) {B : ℝ}
    (hd : ∀ q : ℝ,0 < q → (∫ x,boundedHopfMap f (q+1) x ∂μ)-
      (∫ x,boundedHopfMap f q x ∂ν) ≤ B) :
    (∫ x,boundedHopfMap f 1 x ∂μ)-(∫ x,f x ∂ν) ≤ B := by
  obtain ⟨L,hL⟩ := hf
  have h₁ := ((continuousOn_integral_boundedHopfMap (m := μ) f hL) 1 (by norm_num : (1:ℝ) ∈ Ici 0)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨by simpa using fisherEpsilon_tendsto.add_const 1,
      Eventually.of_forall fun n => by simpa only [mem_Ici] using add_nonneg (fisherEpsilon_pos n).le zero_le_one⟩)
  have h₀ := ((continuousOn_integral_boundedHopfMap (m := ν) f hL) 0 (by simp : (0:ℝ) ∈ Ici 0)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨fisherEpsilon_tendsto,
      Eventually.of_forall fun n => (fisherEpsilon_pos n).le⟩)
  simpa only [boundedHopfMap_zero] using le_of_tendsto (h₁.sub h₀)
    (Eventually.of_forall fun n => hd (fisherEpsilon n) (fisherEpsilon_pos n))

lemma coupling_of_entropy_dual (o : X) (u v : Lp ℝ 2 m)
    (hun : ∀ᵐ x ∂m,0 ≤ u x) (hvn : ∀ᵐ x ∂m,0 ≤ v x)
    [IsProbabilityMeasure (densityMeasure m u)] [IsProbabilityMeasure (densityMeasure m v)]
    {A T : ℝ}
    (hd : ∀ (f : X →ᵇ ℝ),HasCompactSupport (f : X → ℝ) →
      GloballyLipschitz (f : X → ℝ) → ∀ q : ℝ,0 < q →
      (∫ x,u x*boundedHopfMap f (q+1) x ∂m)-(∫ x,v x*boundedHopfMap f q x ∂m)+
        T*((∫ x,reducedEntropy (u x) ∂m)-(∫ x,reducedEntropy (v x) ∂m)) ≤ A) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure m u ∧ p.map Prod.snd = densityMeasure m v ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*(A-T*((∫ x,reducedEntropy (u x) ∂m)-
          (∫ x,reducedEntropy (v x) ∂m)))) := by
  apply exists_proper_coupling_cost_of_compact_hopf_bound _ _ o
  intro f hc hL
  apply compact_hopf_dual_zero_time _ _ f hL
  intro q hq
  rw [integral_densityMeasure m u hun,integral_densityMeasure m v hvn]
  have H := hd f hc hL q hq
  linarith

lemma cheegerHeat_entropy_coupling
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T : ℝ} (hT : 0 ≤ T) (hm : ∫ x,u x ∂m = 1)
    (hPm : ∫ x,cheegerHeat h T u x ∂m = 1)
    {V : X → ℝ} (huV : Integrable (fun x => u x*V x) m)
    (hPV : Integrable (fun x => cheegerHeat h T u x*V x) m)
    (hV : Integrable (fun x => Real.exp (-V x)) m) :
    ∃ p : Measure (X×X),IsProbabilityMeasure p ∧
      p.map Prod.fst = densityMeasure m (cheegerHeat h T u) ∧ p.map Prod.snd = densityMeasure m u ∧
      (∫⁻ z,(edist z.1 z.2)^2 ∂p) ≤
        ENNReal.ofReal (2*T*((∫ x,reducedEntropy (u x) ∂m)-
          (∫ x,reducedEntropy (cheegerHeat h T u x) ∂m))) := by
  let := densityMeasure_probability_of_integrable u hun (integrable_of_integral_eq_one hm) hm
  let := densityMeasure_probability_of_integrable (cheegerHeat h T u)
    (cheegerHeat_nonneg h hT u hun) (integrable_of_integral_eq_one hPm) hPm
  have H := coupling_of_entropy_dual o (cheegerHeat h T u) u
    (cheegerHeat_nonneg h hT u hun) hun (T := T) (A := 0) (by
      intro f hc _ q hq
      exact cheegerHeat_entropy_dual_reduced hfin o hID hpar h u hun hub hB hT hq
        (integrable_of_integral_eq_one hm) (integrable_of_integral_eq_one hPm)
        (hPm.trans hm.symm) huV hPV hV f hc)
  simpa only [zero_sub, ← mul_neg, neg_sub, mul_assoc] using H

end WeakHessian

end
end

end OAI
