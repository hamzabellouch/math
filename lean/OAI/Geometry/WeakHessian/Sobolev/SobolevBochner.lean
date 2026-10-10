import Mathlib
import OAI.Geometry.WeakHessian.Sobolev.OriginalBochner
import OAI.Geometry.WeakHessian.HeatFlow.SobolevHeatPairing

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile109
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport WeakHessianFunctional
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X} [SigmaFinite m]

lemma RCD.original_bochner_sobolev_multiplier {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (o : X) {u A ξ : Lp ℝ 2 m}
    (hu : IsLaplacian m (u : X → ℝ) A)
    (hξ : Sobolev m (ξ : X → ℝ))
    (hξi : Integrable ξ m) {e : X → ℝ} {L : ℝ≥0} (hel : LipschitzWith L e)
    (heξ : e =ᵐ[m] ξ) (hen : ∀ᵐ x ∂m,0 ≤ e x) {C : ℝ} (hC : 0 ≤ C)
    (heC : ∀ᵐ x ∂m,|e x| ≤ C)
    (hqs : Sobolev m (fun x => (weakGradient m (u : X → ℝ) x)^2)) :
    K*(∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m) ≤
      -(1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)+
        (∫ x,A x*(e x*A x+gamma m e u x) ∂m) := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  have hpar := hrcd.1.global_localGradientParallelogram hfin o h
  have hq := hqs.1
  let q := hq.toLp (fun x => (weakGradient m (u : X → ℝ) x)^2)
  have hW : MemLp (fun x => e x*A x+gamma m e u x) 2 m := by
    apply MemLp.add _ (memLp_gamma_of_lipschitz hfin hpar hel hu.1)
    simpa only [mul_comm] using memLp_mul_bounded (Lp.memLp A) hel.continuous.aestronglyMeasurable heC
  let W := hW.toLp (fun x => e x*A x+gamma m e u x)
  let E := ∫ x,e x*(weakGradient m (u : X → ℝ) x)^2 ∂m
  have hE : E = ⟪q,ξ⟫_ℝ := by
    rw [← integral_Lp_function_eq_inner ξ hq]
    exact integral_congr_ae (heξ.fun_mul .rfl)
  have hWu : (∫ x,e x*gamma m (u : X → ℝ) u x ∂m) = -⟪W,u⟫_ℝ := by
    rw [hu.weighted_pairing hfin hpar hu.1 hel heC,integral_Lp_function_eq_inner u hW]
  have hzero : E = -⟪W,u⟫_ℝ := by
    rw [← hWu]
    exact integral_congr_ae (by filter_upwards [gamma_self (m := m) (u : X → ℝ)] with x hx; rw [hx])
  let D := hu.1.2.2.toLp (weakGradient m (u : X → ℝ))
  have hD : IsMinimalLocalWeakUpperGradient m (u : X → ℝ) D :=
    (weakGradient_isMinimal hu.1.2.1.2).congr_ae .rfl hu.1.2.2.coeFn_toLp.symm
  have hξn : ∀ᵐ x ∂m,0 ≤ ξ x := by filter_upwards [heξ,hen] with x hx hn; simpa only [← hx] using hn
  have hξC : ∀ᵐ x ∂m,ξ x ≤ C := by filter_upwards [heξ,heC] with x hx hn; rw [← hx]; exact (le_abs_self _).trans hn
  have H (t : ℝ) (ht : 0 ≤ t) :
      -2*⟪W,cheegerHeat h t u⟫_ℝ-E ≤ Real.exp (-2*K*t)*⟪q,cheegerHeat h t ξ⟫_ℝ := by
    have hS := hrcd.cheegerHeat_sobolev hfin h o hD ht
    have hlow := weighted_gradient_tangent hfin hpar hu.1 hS hel.continuous.aestronglyMeasurable hen heC
    rw [hu.weighted_pairing hfin hpar hS hel heC,
      integral_Lp_function_eq_inner (cheegerHeat h t u) hW] at hlow
    have hhi := hrcd.cheegerHeat_gradient_integral hN hfull hfin h o hD ht ξ hξi hξn hC hξC
    have helhs : (∫ x,ξ x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m) =
        ∫ x,e x*(weakGradient m (cheegerHeat h t u : X → ℝ) x)^2 ∂m :=
      integral_congr_ae (heξ.symm.fun_mul .rfl)
    have herhs : (∫ x,cheegerHeat h t ξ x*(D x)^2 ∂m) = ⟪q,cheegerHeat h t ξ⟫_ℝ := by
      rw [← integral_Lp_function_eq_inner (cheegerHeat h t ξ) hq]
      exact integral_congr_ae (by filter_upwards [hu.1.2.2.coeFn_toLp] with x hx; rw [hx])
    rw [helhs,herhs] at hhi
    calc
      _ = 2*(-⟪W,cheegerHeat h t u⟫_ℝ)-E := by ring
      _ ≤ _ := hlow.trans hhi
  have hud := (cheeger_closedQuadraticEnergy h).heat_deriv_form_zero m (cheeger_domain_dense h)
    (hrcd.1.global_formGenerator_of_isLaplacian hfin o h u A hu)
  have hξd := hrcd.1.cheegerHeat_pairing_deriv_zero hfin h o hξ ((sobolev_congr_ae hq.coeFn_toLp.symm).mp hqs)
  let d := -(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)
  have heq : (-(∫ x,gamma m (ξ : X → ℝ) q x ∂m)) = d := by
    congr 1
    exact integral_congr_ae (gamma_congr_ae heξ.symm hq.coeFn_toLp)
  rw [heq] at hξd
  change HasDerivWithinAt (fun t => cheegerHeat h t u) A (Ici 0) 0 at hud
  have h1 : HasDerivWithinAt (fun t => ⟪W,cheegerHeat h t u⟫_ℝ) ⟪W,A⟫_ℝ (Ici 0) 0 := by
    simpa only [inner_zero_left,add_zero] using (hasDerivWithinAt_const 0 (Ici 0) W).inner ℝ hud
  have h2 : HasDerivWithinAt (fun t => ⟪q,cheegerHeat h t ξ⟫_ℝ) d (Ici 0) 0 := hξd
  have hexd : HasDerivWithinAt (fun t : ℝ => Real.exp (-2*K*t)) (-2*K) (Ici 0) 0 := by
    simpa using (((hasDerivWithinAt_id 0 (Ici 0)).const_mul (-2*K)).exp)
  have hd : HasDerivWithinAt
      (fun t => Real.exp (-2*K*t)*⟪q,cheegerHeat h t ξ⟫_ℝ-(-2*⟪W,cheegerHeat h t u⟫_ℝ-E))
      ((-2*K)*⟪q,ξ⟫_ℝ+d+2*⟪W,A⟫_ℝ) (Ici 0) 0 := by
    have HH := (hexd.mul h2).sub ((h1.const_mul (-2)).sub_const E)
    simp only [mul_zero,Real.exp_zero,cheegerHeat_zero,one_apply_eq_self,one_mul] at HH
    convert! HH using 1
    ring
  have hnon := right_deriv_nonneg_of_nonneg hd (by simp [cheegerHeat_zero,← hE]; linarith [hzero])
    (fun t ht => sub_nonneg.mpr (H t ht))
  rw [integral_Lp_function_eq_inner A hW]
  change K*E ≤ -(1/2)*(∫ x,gamma m e (fun y => (weakGradient m (u : X → ℝ) y)^2) x ∂m)+⟪W,A⟫_ℝ
  change (-2*K)*⟪q,ξ⟫_ℝ+d+2*⟪W,A⟫_ℝ ≥ 0 at hnon
  rw [← hE] at hnon
  dsimp only [d] at hnon
  linarith
end WeakHessian

end
end InlinedFile109

end OAI
