import OAI.Analysis.LipschitzHilbert.Phase.SourceGridPrediction
import OAI.Analysis.LipschitzHilbert.Phase.SourcePredictionValues

namespace OAI

/-! A block with no continuing eligible-top child has prediction one.
It does not require selecting a fictitious child for the graph argument. -/

noncomputable section
open Set MeasureTheory
namespace LipschitzHilbert

 theorem source_empty_prediction {ι κ : Type} [Fintype ι] [IsEmpty ι] [Fintype κ]
    (p μ n : ℝ) (hp : 0 < p) (c : ι → ℝ) (A : ι → EuclideanSpace ℂ κ) (lam : ι → ℂ) :
    sourcePredictionValue p μ n c A lam = 1 := by
  simp only [sourcePredictionValue,Finset.univ_eq_empty,Finset.sum_empty,add_zero,
    energyRatio,norm_zero,Real.zero_rpow hp.ne',div_one]

/-- The same normalized local factor API covers an empty continuing
family, even when the distinguished path has ended. -/
theorem source_empty_grid_prediction {ι κ : Type} [Fintype ι] [IsEmpty ι] [Fintype κ]
    (grid : FiniteLineGrid) (level : ℕ) (p μ e : ℝ) (hp : 0 < p) (he : 0 ≤ e)
    (n : ℝ → ℝ) (c : ℝ → ι → ℝ) (A : ℝ → ι → EuclideanSpace ℂ κ)
    (lam : ℝ → ι → ℂ) :
    ∃ Γ : ℝ → ℝ, Measurable Γ ∧
      Integrable Γ (intervalProbability grid.origin (grid.origin+grid.width)) ∧
      (∀ b, 0 ≤ Γ b) ∧
      (∫ b, Γ b ∂intervalProbability grid.origin (grid.origin+grid.width)) ≤ 1 ∧
      (∀ b d, grid.index level b = grid.index level d → Γ b = Γ d) ∧
      ∀ b ∈ grid.root, sourcePredictionValue p μ (n b) (c b) (A b) (lam b) ≤ Real.exp e*Γ b := by
  let := intervalProbability_isProbability
    (show grid.origin < grid.origin+grid.width by linarith [grid.width_pos])
  refine ⟨fun _ => 1,measurable_const,integrable_const 1,fun _ => zero_le_one,?_,?_,?_⟩
  · simp
  · intro b d _
    rfl
  · intro b _
    rw [source_empty_prediction p μ (n b) hp,mul_one]
    exact Real.one_le_exp_iff.mpr he

end LipschitzHilbert

end

end OAI
