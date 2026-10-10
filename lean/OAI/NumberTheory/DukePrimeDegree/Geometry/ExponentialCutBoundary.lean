import OAI.NumberTheory.DukePrimeDegree.Geometry.ExponentialLevelBudget
import OAI.NumberTheory.DukePrimeDegree.Geometry.VaryingCutBoundary

namespace OAI

/-! # Boundary avoidance for exponentially sized families of cuts -/

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace DukePrimeDegree

theorem ae_eventually_avoid_exponential_cut_levels
    {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) {T : Y → Y} (hT : MeasurePreserving T μ μ)
    (N : ℕ → ℕ) (f : ∀ m, Fin (N m) → Y → ℝ)
    (hf : ∀ m i, Measurable (f m i)) (c : ∀ m, Fin (N m) → ℝ)
    (D : ℕ → ℝ) (hD : ∀ m, 0 ≤ D m)
    (hbound : ∀ m i k, μ (realBoundaryStrip (f m i) (c m i) ((1/4:ℝ)^k)) ≤
      ENNReal.ofReal (D m*(1/2:ℝ)^k))
    (L : ℕ → ℕ) {C δ K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hsize : ∀ m, (N m:ℝ≥0∞)*ENNReal.ofReal (D m) ≤
      ENNReal.ofReal (K*Real.exp (C*(m:ℝ))))
    (hL : ∀ k, (L k:ℝ) ≤ δ*(k:ℝ)) (hdecay : C*δ < Real.log 2) :
    ∀ᵐ x ∂μ, ∀ᶠ k : ℕ in atTop, ∀ m ≤ L k, ∀ i,
      (1/4:ℝ)^k < |f m i (T^[k] x)-c m i| := by
  apply ae_eventually_avoid_varying_cut_levels μ hT N f hf c L
    (fun k => (1/4:ℝ)^k) (fun m k => ENNReal.ofReal (D m*(1/2:ℝ)^k)) hbound
  have hsum := (summable_exponential_level_budget L hC hK hL hdecay).tsum_ofReal_ne_top
  apply ne_top_of_le_ne_top hsum
  apply ENNReal.tsum_le_tsum
  intro k
  calc
    _ ≤ ∑ m ∈ Finset.range (L k+1),
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ))*(1/2:ℝ)^k) := by
      apply Finset.sum_le_sum
      intro m _
      rw [ENNReal.ofReal_mul (hD m),←mul_assoc,
        ENNReal.ofReal_mul (mul_nonneg hK (Real.exp_pos _).le)]
      exact mul_le_mul' (hsize m) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity),
        ←Finset.sum_mul]

end DukePrimeDegree

end

end OAI
