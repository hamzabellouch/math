import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.PlanHeatEntropy
import OAI.Geometry.WeakHessian.HeatFlow.InitialHeatLimit

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

omit [BorelSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] in
lemma FormActionBound.zero {ρ : X → ℝ} (hρ : ∀ᵐ x ∂m, 0 ≤ ρ x) :
    FormActionBound m ρ (0 : Lp ℝ 2 m) 0 := by
  intro f _hf
  have H : 0 ≤ ∫ x, ρ x*(weakGradient m (f : X → ℝ) x)^2 ∂m :=
    integral_nonneg_of_ae (hρ.mono fun _ hx => mul_nonneg hx (sq_nonneg _))
  simpa only [inner_zero_left,mul_zero,sub_nonpos,zero_add] using H

lemma cheegerHeat_entropy_action
    (hfin : FiniteOnBoundedSets m)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {θ : ℝ → ℝ} {s τ ε : ℝ} (hθ : HasDerivAt θ τ s)
    (hpos : 0 < θ s) (hε : 0 < ε) :
    ∃ v : Lp ℝ 2 m, ∃ e : ℝ,
      HasDerivAt (fun z => cheegerHeat h (θ z) u) v s ∧
      HasDerivAt (fun z => ∫ x, regularizedEntropy ε (cheegerHeat h (θ z) u x) ∂m) e s ∧
      FormActionBound m (fun x => cheegerHeat h (θ s) u x+ε) v (-2*τ*e) := by
  obtain ⟨L,hL,hD,hE⟩ := cheegerHeat_diagonal_entropy_hasDerivAt hfin h hθ
    (hasDerivAt_const s u) hpos hε
  simp only [map_zero,zero_add] at hD hE
  refine ⟨_,_,hD,hE,?_⟩
  have hPb := cheegerHeat_bounded h hpos.le hB u hub
  have hPn := cheegerHeat_nonneg h hpos.le u hun
  have hA : FormActionBound m (fun x => cheegerHeat h (θ s) u x+ε) (0 : Lp ℝ 2 m) 0 :=
    FormActionBound.zero (hPn.mono fun _ hx => add_nonneg hx hε.le)
  have H := hA.logarithmic_shift hfin hpar
    (identified_isLaplacian_of_formGenerator hfin hID h _ _ hL) hPn hPb hε τ
  simpa only [zero_add,zero_sub,neg_mul] using H

lemma cheegerHeat_entropy_dual_positive
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {δ T q : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, cheegerHeat h (δ+T) u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x, cheegerHeat h δ u x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) u x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ u x) ∂m)) ≤
      ε*compactHopfDualBound hfin o f hf hq/2 := by
  let U' := fun s : ℝ => cheegerHeat h (δ+T*s) u
  have hU'c : ContinuousOn U' (Icc 0 1) := by
    apply (cheegerHeat_continuousOn hfin h u).comp (by fun_prop)
    intro s hs
    exact add_nonneg hδ.le (mul_nonneg hT hs.1)
  let E := fun ε s => ∫ x, regularizedEntropy ε (U' s x) ∂m
  have hEc (ε : ℝ) (hε : 0 < ε) : ContinuousOn (E ε) (Icc 0 1) := by
    intro s hs
    exact ((regularizedEntropy_hasFDeriv hε (U' s)).continuousAt).comp_continuousWithinAt (hU'c s hs)
  have H := compact_dual_of_entropy_actions hfin o hU'c hEc
    (P := fun _ => 0) (a := fun _ => 0) (τ := T) continuousOn_const
    (fun s _ => by simpa using hasDerivAt_const s (0:ℝ))
    (fun s hs => cheegerHeat_nonneg h (add_nonneg hδ.le (mul_nonneg hT hs)) u hun)
    (by
      intro ε hε s hs
      have Hd : HasDerivAt (fun z : ℝ => δ+T*z) T s := by
        simpa only [id_eq,mul_one] using ((hasDerivAt_id s).const_mul T).const_add δ
      simpa only [zero_sub,neg_mul,U',E] using cheegerHeat_entropy_action hfin hID hpar h u hun hub hB
        Hd (add_pos_of_pos_of_nonneg hδ (mul_nonneg hT hs.1)) hε) f hf hq ε hε
  simpa only [U',E,mul_one,mul_zero,add_zero,sub_self,zero_add] using H

lemma cheegerHeat_entropy_dual
    (hfin : FiniteOnBoundedSets m) (o : X)
    (hID : ∀ f : X → ℝ, Sobolev m f → cheegerEnergy m f =
      ENNReal.ofReal ((∫ x, (weakGradient m f x)^2 ∂m)/2))
    (hpar : LocalGradientParallelogram m) (h : QuadraticCheegerEnergy m)
    (u : Lp ℝ 2 m) (hun : ∀ᵐ x ∂m, 0 ≤ u x)
    {B : ℝ} (hub : ∀ᵐ x ∂m, |u x| ≤ B) (hB : 0 ≤ B)
    {T q : ℝ} (hT : 0 ≤ T) (hq : 0 < q)
    (f : X →ᵇ ℝ) (hf : HasCompactSupport (f : X → ℝ)) {ε : ℝ} (hε : 0 < ε) :
    (∫ x, cheegerHeat h T u x*boundedHopfMap f (q+1) x ∂m)-
      (∫ x, u x*boundedHopfMap f q x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h T u x) ∂m)-
        (∫ x, regularizedEntropy ε (u x) ∂m)) ≤
      ε*compactHopfDualBound hfin o f hf hq/2 := by
  have h₀ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n+T) u) atTop
      (𝓝 (cheegerHeat h T u)) := cheegerHeat_tendsto_nonneg hfin h u hT
    (by simpa only [zero_add] using fisherEpsilon_tendsto.add_const T)
    (Eventually.of_forall fun n => add_nonneg (fisherEpsilon_pos n).le hT)
  have h₁ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n) u) atTop (𝓝 u) := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using
      cheegerHeat_tendsto_nonneg hfin h u (le_refl 0) fisherEpsilon_tendsto
        (Eventually.of_forall fun n => (fisherEpsilon_pos n).le)
  have hE₀ := ((regularizedEntropy_hasFDeriv hε (cheegerHeat h T u)).continuousAt).tendsto.comp h₀
  have hE₁ := ((regularizedEntropy_hasFDeriv hε u).continuousAt).tendsto.comp h₁
  have hL := ((integral_mul_tendsto_L2 h₀
    (boundedHopfMap_memLp_compact hfin f o hf (by linarith : 0 < q+1))).sub
    (integral_mul_tendsto_L2 h₁ (boundedHopfMap_memLp_compact hfin f o hf hq))).add
    ((hE₀.sub hE₁).const_mul T)
  exact le_of_tendsto hL (Eventually.of_forall fun n =>
    cheegerHeat_entropy_dual_positive hfin o hID hpar h u hun hub hB
      (fisherEpsilon_pos n) hT hq f hf hε)

end WeakHessian

end
end

end OAI
