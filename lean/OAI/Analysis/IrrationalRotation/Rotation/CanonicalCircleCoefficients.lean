import OAI.Analysis.IrrationalRotation.Rotation.CircleCocycleWindow
import OAI.Analysis.IrrationalRotation.Rotation.ParameterCircleReindex

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem parameter_cocycle_eq_product (k : ℤ) (x : Circle) :
    p.floorCocycle θ k x = ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost k
      (fun n => p.q (n + 1) • x) := by
  rw [hp.parameter_cocycle_eq_flattened]
  simp only [CircleWeights.cocycle, CircleWeights.floorCost,
    ProductCocycle.cocycleVersion, CircleWeights.coordinate,
    CircleWeights.representative, CircleWeights.phase,
    CircleParameterData.flattenedFrequency, CircleParameterData.alpha,
    ProductCocycle.representative, Int.cast_natCast, natCast_zsmul]

theorem canonical_finite_window_coefficients (j : ℕ) (hj : 1 ≤ j) (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (p.floorCocycle θ v x : ℂ)‖ ≤ p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(p.floorCocycle θ (-v) y : ℂ) * conj (γ (-v))‖ ≤ p.coefficientBound j) := by
  simpa only [hp.parameter_cocycle_eq_product] using
    hp.finite_window_coefficients j hj x y hleft hright ξ γ hξ hγ

theorem canonical_raw_event_coefficients (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hcurrent : ∀ i ∈ p.block j,
      X i < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < Y i)
    (hfuture : ∀ s, j < s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (p.floorCocycle θ v (MixedRadix.circleValue d) : ℂ)‖ ≤
        p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(p.floorCocycle θ (-v) (MixedRadix.circleValue e) : ℂ) * conj (γ (-v))‖ ≤
        p.coefficientBound j) := by
  have hexcl := hp.source_good_event_exclusions j hj d e hd he X Y hX hY
    hdigit hedigit hcurrent hfuture
  exact hp.canonical_finite_window_coefficients j hj _ _
    (fun s hs i hi => (hexcl s hs i hi).1)
    (fun s hs i hi => (hexcl s hs i hi).2) ξ γ hξ hγ

end Invariant233.CircleParameterLaws

end

end OAI
