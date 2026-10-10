import Mathlib
import OAI.Geometry.WeakHessian.Entropy.FisherEpsilon

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [MetricSpace X] [BorelSpace X] [CompleteSpace X] [ProperSpace X]
  [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma integral_mul_tendsto_L2 {ι : Type*} {l : Filter ι}
    {u : ι → Lp ℝ 2 m} {v : Lp ℝ 2 m} (hu : Tendsto u l (𝓝 v))
    {f : X → ℝ} (hf : MemLp f 2 m) :
    Tendsto (fun n => ∫ x, u n x*f x ∂m) l (𝓝 (∫ x, v x*f x ∂m)) := by
  let F : Lp ℝ 2 m := hf.toLp f
  have hp (w : Lp ℝ 2 m) : (∫ x, w x*f x ∂m) = ⟪F,w⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with x hx
    simp only [F,hx,RCLike.inner_apply,RCLike.conj_to_real]
  simp_rw [hp]
  exact tendsto_const_nhds.inner hu

omit [CompleteSpace X] [SigmaFinite m] in
lemma cheegerHeat_tendsto_nonneg
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m) (u : Lp ℝ 2 m)
    {ι : Type*} {l : Filter ι} {θ : ι → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hθ : Tendsto θ l (𝓝 t)) (hn : ∀ᶠ i in l, 0 ≤ θ i) :
    Tendsto (fun i => cheegerHeat h (θ i) u) l (𝓝 (cheegerHeat h t u)) :=
  ((cheegerHeat_continuousOn hfin h u) t ht).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hθ,hn⟩)

lemma heat_action_integral_factor (k A δ T : ℝ) :
    (∫ s in (0:ℝ)..1, A/Real.exp (2*k*(δ+T*(1-s)))/2) =
      Real.exp (-(2*k*δ))*(∫ s in (0:ℝ)..1, A/Real.exp (2*k*T*(1-s))/2) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  dsimp only
  rw [show 2*k*(δ+T*(1-s)) = 2*k*δ+2*k*T*(1-s) by ring,
    Real.exp_add,Real.exp_neg]
  field_simp

omit [CompleteSpace X] [SigmaFinite m] in
lemma compact_dual_heat_offset_limit
    (hfin : FiniteOnBoundedSets m) (h : QuadraticCheegerEnergy m)
    (u₀ u₁ : Lp ℝ 2 m) {φ₀ φ₁ : X → ℝ} (hφ₀ : MemLp φ₀ 2 m) (hφ₁ : MemLp φ₁ 2 m)
    {T ε k A D : ℝ} (hT : 0 ≤ T) (hε : 0 < ε)
    (H : ∀ δ, 0 < δ →
      (∫ x, cheegerHeat h δ u₁ x*φ₁ x ∂m)-
        (∫ x, cheegerHeat h (δ+T) u₀ x*φ₀ x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h (δ+T) u₀ x) ∂m)-
        (∫ x, regularizedEntropy ε (cheegerHeat h δ u₁ x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, A/Real.exp (2*k*(δ+T*(1-s)))/2)+ε*D/2) :
      (∫ x, u₁ x*φ₁ x ∂m)-(∫ x, cheegerHeat h T u₀ x*φ₀ x ∂m)+
      T*((∫ x, regularizedEntropy ε (cheegerHeat h T u₀ x) ∂m)-
        (∫ x, regularizedEntropy ε (u₁ x) ∂m)) ≤
      (∫ s in (0:ℝ)..1, A/Real.exp (2*k*T*(1-s))/2)+ε*D/2 := by
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
  have hR : Tendsto (fun n =>
      (∫ s in (0:ℝ)..1, A/Real.exp (2*k*(fisherEpsilon n+T*(1-s)))/2)+ε*D/2) atTop
      (𝓝 ((∫ s in (0:ℝ)..1, A/Real.exp (2*k*T*(1-s))/2)+ε*D/2)) := by
    simp_rw [heat_action_integral_factor]
    have HH := (((Real.continuous_exp.tendsto _).comp (fisherEpsilon_tendsto.const_mul (2*k)).neg).mul_const
      (∫ s in (0:ℝ)..1, A/Real.exp (2*k*T*(1-s))/2)).add_const (ε*D/2)
    simpa only [Function.comp_def,mul_zero,neg_zero,Real.exp_zero,one_mul] using HH
  exact le_of_tendsto_of_tendsto' hL hR (fun n => H (fisherEpsilon n) (fisherEpsilon_pos n))

end WeakHessian

end
end

end OAI
