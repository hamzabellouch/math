import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.InitialHeatLimit

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X}

lemma compact_dual_heat_offset_limit_local
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (u₀ u₁ : Lp ℝ 2 m) {φ₀ φ₁ : X → ℝ} (hφ₀ : MemLp φ₀ 2 m) (hφ₁ : MemLp φ₁ 2 m)
    {T ε η : ℝ} (hT : 0 ≤ T) (hε : 0 < ε) (hη : 0 < η)
    {A : ℝ → ℝ} (hA : ContinuousAt A 0)
    (H : ∀ δ,δ ∈ Ioo 0 η →
      (∫ x,cheegerHeat h δ u₁ x*φ₁ x ∂m)-
        (∫ x,cheegerHeat h (δ+T) u₀ x*φ₀ x ∂m)+
      T*((∫ x,regularizedEntropy ε (cheegerHeat h (δ+T) u₀ x) ∂m)-
        (∫ x,regularizedEntropy ε (cheegerHeat h δ u₁ x) ∂m)) ≤ A δ) :
    (∫ x,u₁ x*φ₁ x ∂m)-(∫ x,cheegerHeat h T u₀ x*φ₀ x ∂m)+
      T*((∫ x,regularizedEntropy ε (cheegerHeat h T u₀ x) ∂m)-
        (∫ x,regularizedEntropy ε (u₁ x) ∂m)) ≤ A 0 := by
  have h₀ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n+T) u₀) atTop
      (𝓝 (cheegerHeat h T u₀)) := cheegerHeat_tendsto_nonneg hfin h u₀ hT
    (by simpa only [zero_add] using fisherEpsilon_tendsto.add_const T)
    (Eventually.of_forall fun n => add_nonneg (fisherEpsilon_pos n).le hT)
  have h₁ : Tendsto (fun n => cheegerHeat h (fisherEpsilon n) u₁) atTop (𝓝 u₁) := by
    simpa only [cheegerHeat_zero,one_apply_eq_self] using
      cheegerHeat_tendsto_nonneg hfin h u₁ (le_refl 0) fisherEpsilon_tendsto
        (Eventually.of_forall fun n => (fisherEpsilon_pos n).le)
  have hE₀ := ((regularizedEntropy_hasFDeriv hε (cheegerHeat h T u₀)).continuousAt).tendsto.comp h₀
  have hE₁ := ((regularizedEntropy_hasFDeriv hε u₁).continuousAt).tendsto.comp h₁
  have hL := ((integral_mul_tendsto_L2 h₁ hφ₁).sub (integral_mul_tendsto_L2 h₀ hφ₀)).add
    ((hE₀.sub hE₁).const_mul T)
  apply le_of_tendsto_of_tendsto hL (hA.tendsto.comp fisherEpsilon_tendsto)
  filter_upwards [fisherEpsilon_tendsto.eventually (gt_mem_nhds hη)] with n hn
  exact H _ ⟨fisherEpsilon_pos n,hn⟩

end WeakHessian

end
end

end OAI
