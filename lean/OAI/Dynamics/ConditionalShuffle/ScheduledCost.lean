import OAI.Dynamics.ConditionalShuffle.OverlayRate

namespace OAI

noncomputable section
open scoped Classical
namespace Revealed.Scheduled
open Thorp Thorp.Conditional Thorp.Conditional.Hybrid Revealed.Split Revealed.Instrument Revealed.Disintegration
variable {ι α : Type} [Fintype ι] [Fintype α] [DecidableEq α]

lemma interval_cost_le (d t : ℕ) (σ : ℕ → Bool) (e : Outside ι α (Position d))
    (c : (Equiv.Perm α → ℝ) → ℝ) (C : ℝ)
    (h : let μ := fairMass (fun ω : History d t =>
      ((publicHistory (fun i : Fin t => σ i.val) ω, splitPath (sectionFrame e) t ω),
        assignment ((sectionFrame e).trans (run d t ω))))
      ∑ p, marginal μ p * c (conditional μ p) ≤ C)
    : ∀ F : Fintype (Fin t → Symbol ι α d),
    @Finset.sum (Fin t → Symbol ι α d) ℝ _ (@Finset.univ _ F)
      (fun p => probability (interval d t σ) e p * c (kernel (interval d t σ) e p)) ≤ C := by
  let B : Fintype (Fin t → Symbol ι α d) := inferInstance
  have hh := (interval_weighted_cost d t σ e c).le.trans h
  intro F
  have hF : F = B := Subsingleton.elim _ _
  rw [hF]
  exact hh

end Revealed.Scheduled

end

end OAI
