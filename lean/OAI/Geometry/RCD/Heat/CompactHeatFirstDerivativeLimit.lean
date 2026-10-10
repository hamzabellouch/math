import OAI.Geometry.RCD.Heat.CompactHeatDerivativeLipschitz
import OAI.Geometry.RCD.Heat.CompactHeatMeanDifferentiable
import OAI.Geometry.RCD.Metric.DerivativeValueCompactness

namespace OAI

/-! # First-derivative convergence on the original heat-law subsequence -/

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal BoundedContinuousFunction
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

theorem first_derivative_limit (hK : K ≤ 0) (hε1 : ∀ k, ε k ≤ 1)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (i : ℕ → ℕ) (Q₀ : Ioo (0:ℝ) 1 → ProbabilityMeasure X)
    (hweak : ∀ t, Tendsto (fun k => D.interpolationLaw (i k) t) atTop (𝓝 (Q₀ t)))
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {s : ℝ} (hs : 0 < s)
    (t : Ioo (0:ℝ) 1) :
    let H := kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f
    ∃ v : ℝ, Tendsto (fun k => deriv (D.interpolationMean H (i k)) t) atTop (𝓝 v) := by
  intro H
  let a := (t:ℝ)/2
  let b := (1+(t:ℝ))/2
  have ha : 0 < a := by dsimp only [a]; linarith [t.property.1]
  have hb : b < 1 := by dsimp only [b]; linarith [t.property.2]
  have ht : (t:ℝ) ∈ Ioo a b := by
    dsimp only [a,b]
    constructor <;> linarith [t.property.1,t.property.2]
  obtain ⟨L,hL⟩ := D.first_derivative_uniform_lipschitz hK hε1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hμ hν hR hS hT f A hf hs ha hb
  obtain ⟨hLip,hBound⟩ := hX.kernelHeat_bounded_regularity hn p
    (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) f A hf s hs
  let Hb : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup H hLip.continuous A
    (fun x => by simpa only [Real.norm_eq_abs] using hBound x)
  apply exists_derivative_limit_of_values (fun k => D.interpolationMean H (i k)) L ht
  · intro k x hx
    exact D.interpolationMean_differentiable ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν Hb (i k)
      ⟨x,ha.trans_le hx.1,hx.2.trans_lt hb⟩
  · exact fun k => hL (i k)
  · intro x hx
    let u : Ioo (0:ℝ) 1 := ⟨x,ha.trans_le hx.1,hx.2.trans_lt hb⟩
    exact ⟨_,D.heat_interpolationMean_law_limit i u (Q₀ u) (hweak u) f A hf hs⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
