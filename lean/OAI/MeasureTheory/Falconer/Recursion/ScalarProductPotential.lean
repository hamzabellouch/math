import OAI.MeasureTheory.Falconer.Measures.ScalarProductFrostman
import OAI.MeasureTheory.Falconer.Recursion.FiniteCountingPotential

namespace OAI

/-! The inverse-distance potential of the separated scalar product,
obtained from its interpolated finite Frostman estimate. -/
namespace Falconer

theorem scalar_product_dyadic_potential (n : ℕ) {K κ : ℝ}
    (hK : 0 ≤ K) (hκ : 0 < κ) (hκ1 : κ ≤ 1/2)
    (X : Finset ℝ) (hX : X.Nonempty)
    (hsep : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → 1/(2:ℝ)^n ≤ |x-y|)
    (hball : ∀ u r : ℝ, 1/(2:ℝ)^n ≤ r → r ≤ 1 →
      ((X.filter fun x => |x-u| ≤ r).card : ℝ) ≤ K*r^κ*(X.card : ℝ))
    (z : Space 2) :
    let δ : ℝ := 1/(2:ℝ)^n
    let θ := productInterpolationWeight κ
    let C := max 1 (81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ)))
    (∑ q ∈ scalarProductPoints X X, 1/max (dist z q) δ) ≤
      C*planarPotentialConstant 1 (1+κ/2)*(X.card : ℝ)^2 := by
  dsimp only
  let δ : ℝ := 1/(2:ℝ)^n
  let θ := productInterpolationWeight κ
  let C₀ := 81^θ*K^(2*(1-θ))*(δ*(X.card : ℝ))^(-(2*θ))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hp := scalarProductPoints_frostman_above_one hδ hK hκ hκ1 X hX hsep hball
  have hball' : NormalizedFiniteBallBound δ (1+κ/2) (max 1 C₀) (scalarProductPoints X X) := by
    intro c r hdr hr1
    have hh := hp c r hdr hr1
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right 1 C₀) (Real.rpow_nonneg (hδ.le.trans hdr) _))
      (Nat.cast_nonneg _))
  have hh := finite_dyadic_truncated_potential_real (scalarProductPoints X X) z n
    (le_max_left 1 C₀) (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) < 1+κ/2) hball'
  simpa only [Real.rpow_one,scalarProductPoints_card,Nat.cast_mul,pow_two] using hh

end Falconer

end OAI
