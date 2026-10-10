import OAI.Computability.PerfectCompleteness.Decoding.TwoResponseCollisionLemmas
import OAI.Computability.PerfectCompleteness.Reduction.FixedCallBudgetLemmas

namespace OAI

section

namespace PerfectCompleteness.FixedRankContradiction

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games

noncomputable section

theorem probability_split {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (event low : Ω → Bool) :
    μ.probability event = μ.probability (fun x => event x && low x) +
      μ.probability (fun x => event x && !(low x)) := by
  unfold FiniteDistribution.probability
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  cases he : event x <;> cases hl : low x <;> simp [he, hl]

variable {δ : ℚ} {hδ : 0 < δ} (p : FixedParameters.Parameters δ hδ)

def gamma (height : Nat) : ℝ :=
  UpperParameterScalars.gamma (InitialParameters.useful δ) p.plan.density
    (InitialParameters.inverse δ) p.plan.order (FixedRows.rows p.plan height)

theorem impossible {Ω : Type*} [Fintype Ω] (μ : FiniteDistribution Ω)
    (event low : Ω → Bool) (height : Nat) (hheight : height ≤ p.plan.depth)
    (hupper : gamma p height ≤ μ.probability event)
    (hhigh : μ.probability (fun x => event x && !(low x)) ^ 2 ≤
      gamma p height ^ 2 / 8 + 2 * p.accuracy)
    (hlow : μ.probability (fun x => event x && low x) < p.accuracy) : False := by
  have hgamma : 0 < gamma p height :=
    UpperParameterScalars.gamma_pos (InitialParameters.useful_pos hδ)
      p.plan.density_pos (InitialParameters.inverse_pos hδ)
      p.plan.order (FixedRows.rows p.plan height)
  have hsmall := p.accuracy_small height hheight
  simp only [CommonAccuracy.tolerance, lt_min_iff] at hsmall
  have hsquare : p.accuracy < gamma p height ^ 2 / 640 := hsmall.2.2.2.1
  have hlinear : p.accuracy < gamma p height / 40 := hsmall.2.2.2.2
  have hhalf : μ.probability (fun x => event x && !(low x)) < gamma p height / 2 := by
    by_contra hn
    have hge := le_of_not_gt hn
    have hnonneg := μ.probability_nonnegative (fun x => event x && !(low x))
    have hsq := (sq_le_sq₀ (by positivity : 0 ≤ gamma p height / 2) hnonneg).mpr hge
    nlinarith
  have hsplit := probability_split μ event low
  linarith

end
end PerfectCompleteness.FixedRankContradiction

end

end OAI
