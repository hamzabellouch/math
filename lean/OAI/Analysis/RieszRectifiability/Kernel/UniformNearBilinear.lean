import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.NearBilinear

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set
open scoped NNReal

theorem near_fractionalBilinear_uniformly_small {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → Measure (Ambient d)) [∀ j, IsFiniteMeasure (μ j)]
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j))
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, Measurable (w j))
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j).prod (μ j)))
    (E M : ℝ)
    (hE : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalPairEnergy (p + 1) (w j) q.1 q.2 ∂(μ j).prod (μ j)) ≤ E)
    (hM : ∀ j, (μ j).real univ ≤ M)
    (ψ : Ambient d → ℝ) (L : ℝ≥0) (hψ : LipschitzWith L ψ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ j : ℕ, ∀ r : ℝ, 0 < r → r < δ →
      (∫ q in nearPairSet r, |fractionalBilinear (p + 1) (w j) ψ q.1 q.2|
        ∂(μ j).prod (μ j)) < ε := by
  have hC0 : 0 ≤ C := (hg 0).1
  have hE0 : 0 ≤ E :=
    (integral_nonneg (fun q => fractionalPairEnergy_nonneg (p + 1) (w 0) q.1 q.2)).trans (hE 0)
  have hM0 : 0 ≤ M := measureReal_nonneg.trans (hM 0)
  let D : ℝ := E * (L : ℝ) ^ 2 * M * (2 * C * 2 ^ (p + 1) * 2 ^ p)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  intro ε hε
  refine ⟨ε ^ 2 / (D + 1), by positivity, ?_⟩
  intro j r hr hsmall
  have hb : (∫ q in nearPairSet r, |fractionalBilinear (p + 1) (w j) ψ q.1 q.2|
      ∂(μ j).prod (μ j)) ^ 2 ≤ D * r := by
    calc
      _ ≤ (∫ q : Ambient d × Ambient d, fractionalPairEnergy (p + 1) (w j) q.1 q.2
          ∂(μ j).prod (μ j)) *
          ((L : ℝ) ^ 2 * ((μ j).real univ * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) :=
        (near_fractionalBilinear_integrable_and_bound p C (μ j) (hg j) (w j) ψ (hw j)
          L hψ (henergy j) r hr).2
      _ ≤ E * ((L : ℝ) ^ 2 * (M * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)))) := by
        apply mul_le_mul (hE j) _ (by positivity) hE0
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hM j) (by positivity)) (sq_nonneg _)
      _ = _ := by dsimp [D]; ring
  have hs : r * (D + 1) < ε ^ 2 := (lt_div_iff₀ (by positivity : 0 < D + 1)).mp hsmall
  nlinarith

end

end RieszRectifiability

end OAI
