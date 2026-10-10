import OAI.Analysis.IrrationalRotation.Rotation.CircleWeightDecay
import OAI.Analysis.IrrationalRotation.Rotation.WeightedShiftPowers

namespace OAI

noncomputable section
open Filter Finset MeasureTheory
open scoped Topology BigOperators ENNReal

namespace InvariantProjection.CircleFiberDecay

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev Circle := AddCircle (1 : ℝ)

lemma coordinate_product_eq (θ : ℝ) (f : Circle → ℝ)
    (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ))
    (x : Circle) (k : ℤ) (n : ℕ) :
    (∏ j ∈ range n, w x (k + j)) =
      ((∏ j ∈ range n, f ((x + k • (θ : Circle)) + j • (θ : Circle)) : ℝ) : ℂ) := by
  simp only [hw, add_zsmul, natCast_zsmul, ← add_assoc]
  norm_cast

theorem norm_fiber_power_le (θ : ℝ) (f : Circle → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ))
    (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ x, (∏ j ∈ range n, f (x + j • (θ : Circle))) ≤ B) (x : Circle) :
    ‖(Invariant233.WeightedShift.operator (w x)) ^ n‖ ≤ B := by
  apply Invariant233.WeightedShift.norm_operator_pow_le (w x) n hB
  intro k
  rw [coordinate_product_eq θ f w hw x k n, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg]
  · exact hprod (x + k • (θ : Circle))
  · exact prod_nonneg fun j _ => hf0 _

theorem all_rates_fiber_decay {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞)
    (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ)) :
    ∀ a : ℝ, 0 < a → ∀ᶠ (n : ℕ) in atTop, ∀ x,
      ‖(Invariant233.WeightedShift.operator (w x)) ^ n‖ ≤ Real.exp (-a * n) := by
  intro a ha
  filter_upwards [CircleWeightDecay.all_rates_decay hθ f hf0 hf1 hpos hlog a ha] with n hn
  exact norm_fiber_power_le θ f hf0 w hw n (Real.exp_nonneg _) hn

theorem fiber_norm_quasinilpotent {θ : ℝ} (hθ : Irrational θ) (f : C(Circle, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂AddCircle.haarAddCircle, 0 < f x)
    (hlog : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂AddCircle.haarAddCircle) = ∞)
    (w : Circle → Invariant233.WeightedShift.Weight)
    (hw : ∀ x k, w x k = (f (x + k • (θ : Circle)) : ℂ)) (x : Circle) :
    Tendsto (fun n : ℕ => ‖(Invariant233.WeightedShift.operator (w x)) ^ n‖ ^
      (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply Invariant233.norm_quasinilpotent_of_exponential_decay
  intro a ha
  filter_upwards [all_rates_fiber_decay hθ f hf0 hf1 hpos hlog w hw a ha] with n hn
  exact hn x

end InvariantProjection.CircleFiberDecay

end

end OAI
