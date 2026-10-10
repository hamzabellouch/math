import OAI.Geometry.RCD.Heat.CompactHeatSecondDerivativeBound
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! # A common Lipschitz bound for the actual first time derivatives -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)

theorem first_derivative_uniform_lipschitz (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s)
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    ∃ L : ℝ≥0, ∀ k, LipschitzOnWith L (deriv (D.interpolationMean H k)) (Icc a b) := by
  intro H
  let δ := min a (1-b)
  have hδ : 0 < δ := lt_min ha (sub_pos.mpr hb)
  have hδa : δ ≤ a := min_le_left _ _
  have hδb : δ ≤ 1-b := min_le_right _ _
  obtain ⟨B,hB,hbound⟩ := D.second_derivative_uniform_bound hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν hR hδ hS hT f A hf hs
  let L : ℝ≥0 := ⟨B,hB⟩
  have htime (x : ℝ) (hx : x ∈ Icc a b) : x ∈ Ioo (0:ℝ) 1 :=
    ⟨ha.trans_le hx.1,hx.2.trans_lt hb⟩
  have hwindow (x : ℝ) (hx : x ∈ Icc a b) : δ ≤ x ∧ δ ≤ 1-x :=
    ⟨hδa.trans hx.1,by linarith [hx.2]⟩
  refine ⟨L,fun k => ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le _ _ (convex_Icc _ _)
  · intro x hx
    obtain ⟨u,v,uv,wu,wv,_,_,_,_,_,hd⟩ := D.interpolationMean_hessian
      ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν f A hf hs k ⟨x,htime x hx⟩
    exact hd.differentiableAt
  · intro x hx
    have hh := hbound k ⟨⟨x,htime x hx⟩,hwindow x hx⟩
    change ‖deriv (deriv (D.interpolationMean H k)) x‖ ≤ B
    simpa only [Real.norm_eq_abs] using hh

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
