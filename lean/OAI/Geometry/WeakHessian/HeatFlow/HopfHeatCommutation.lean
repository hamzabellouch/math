import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.SpatialHeat
import OAI.Geometry.WeakHessian.LocalBounds.SpatialDual
import OAI.Geometry.WeakHessian.Calculus.CompactHopf

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile83
noncomputable section
namespace WeakHessian
open Set Filter MeasureTheory WeakHessianTransport
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X] {m : Measure X}
variable [SigmaFinite m]

omit [CompleteSpace X] in
lemma RCD.exists_boundedLipschitz_heatVersion {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (f : X →ᵇ ℝ) (hf : GloballyLipschitz (f : X → ℝ))
    (hf2 : MemLp f 2 m) {t : ℝ} (ht : 0 ≤ t) :
    ∃ F : X →ᵇ ℝ,GloballyLipschitz (F : X → ℝ) ∧
      F =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧ ‖F‖ ≤ ‖f‖ := by
  obtain ⟨L,hL⟩ := hf
  obtain ⟨F,hF,hFe⟩ := hrcd.cheegerHeat_lipschitzVersion hN hfull hfin h hL hf2
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) ht
  have hfb : ∀ᵐ x ∂m,|hf2.toLp f x| ≤ ‖f‖ := by
    filter_upwards [hf2.coeFn_toLp] with x hx
    rw [hx]
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  have hFb := heat_continuousVersion_bounded hfull h _ (norm_nonneg f) hfb ht hF.continuous hFe
  let F' : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF.continuous ‖f‖
    (fun x => by simpa only [Real.norm_eq_abs] using hFb x)
  refine ⟨F',⟨_,hF⟩,hFe,?_⟩
  apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
  intro x
  change ‖F x‖ ≤ ‖f‖
  simpa only [Real.norm_eq_abs] using hFb x

lemma RCD.hopf_heat_commutation {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (f : X →ᵇ ℝ) (hf : GloballyLipschitz (f : X → ℝ))
    (hf2 : MemLp f 2 m) {s : ℝ} (hs : 0 < s) (hQ2 : MemLp (boundedHopfMap f s) 2 m)
    {t : ℝ} (ht : 0 ≤ t) :
    ∃ F Q : X →ᵇ ℝ, GloballyLipschitz (F : X → ℝ) ∧ GloballyLipschitz (Q : X → ℝ) ∧
      F =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧
      Q =ᵐ[m] cheegerHeat h t (hQ2.toLp (boundedHopfMap f s)) ∧
      ‖F‖ ≤ ‖f‖ ∧ ∀ x,Q x ≤ hopfLax F (s*Real.exp (2*K*t)) x := by
  obtain ⟨F,hF,hFe,hFb⟩ := hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h f hf hf2 ht
  obtain ⟨Q,hQ,hQe,hQb⟩ := hrcd.exists_boundedLipschitz_heatVersion hN hfull hfin h (boundedHopfMap f s)
    (boundedHopfMap_lipschitz f hs) hQ2 ht
  refine ⟨F,Q,hF,hQ,hFe,hQe,hFb,?_⟩
  have hdual : ∀ x y,boundedHopfMap f s x-f y ≤ (1/(2*s))*dist x y^2 := by
    intro x y
    rw [boundedHopfMap_apply_pos f hs]
    have H := hopfLax_le_objective (fun x => (boundedContinuous_bounds f x).1) hs x y
    dsimp only [hopfObjective] at H
    linarith [show dist x y^2/(2*s) = (1/(2*s))*dist x y^2 by ring]
  have HD := hrcd.cheegerHeat_dual_pointwise hN hfull hfin h (boundedHopfMap f s).continuous f.continuous
    hQ2 hf2 (fun x => by simpa only [Real.norm_eq_abs] using (boundedHopfMap f s).norm_coe_le_norm x)
    (fun x => by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x) (by positivity) hdual ht
    Q.continuous F.continuous hQe hFe
  have he : (1/(2*s))*Real.exp (-2*K*t) = 1/(2*(s*Real.exp (2*K*t))) := by
    have hn : -2*K*t = -(2*K*t) := by ring
    rw [hn,Real.exp_neg]
    field_simp
  intro x
  apply le_csInf ⟨hopfObjective F (s*Real.exp (2*K*t)) x x,mem_range_self x⟩
  rintro z ⟨y,rfl⟩
  have H := HD x y
  rw [he] at H
  dsimp only [hopfObjective]
  linarith [show dist x y^2/(2*(s*Real.exp (2*K*t))) = (1/(2*(s*Real.exp (2*K*t))))*dist x y^2 by ring]

lemma RCD.hopf_heat_commutation_compact {K N : ℝ}
    (hN : 1 < N) (hrcd : RCD m K N) (hfull : FullSupport m) (hfin : FiniteOnBoundedSets m)
    (h : QuadraticCheegerEnergy m) (f : X →ᵇ ℝ) (o : X)
    (hf : GloballyLipschitz (f : X → ℝ)) (hfc : HasCompactSupport (f : X → ℝ))
    {s : ℝ} (hs : 0 < s) {t : ℝ} (ht : 0 ≤ t) :
    ∃ (hf2 : MemLp f 2 m) (hQ2 : MemLp (boundedHopfMap f s) 2 m) (F Q : X →ᵇ ℝ),
      GloballyLipschitz (F : X → ℝ) ∧ GloballyLipschitz (Q : X → ℝ) ∧
      F =ᵐ[m] cheegerHeat h t (hf2.toLp f) ∧
      Q =ᵐ[m] cheegerHeat h t (hQ2.toLp (boundedHopfMap f s)) ∧
      ‖F‖ ≤ ‖f‖ ∧ ∀ x,Q x ≤ hopfLax F (s*Real.exp (2*K*t)) x := by
  have hf2 := (sobolev_of_lipschitz_compactSupport hfin hf.choose_spec hfc).1
  have hQ2 := boundedHopfMap_memLp_compact hfin f o hfc hs
  exact ⟨hf2,hQ2,hrcd.hopf_heat_commutation hN hfull hfin h f hf hf2 hs hQ2 ht⟩
end WeakHessian

end
end InlinedFile83

end OAI
