import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.NonflatSupportHole
import OAI.Analysis.RieszRectifiability.Flatness.RelativePlaneDimensionDrop

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Module
open scoped ENNReal

theorem not_global_nonflat_annular_measure {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (hne : μ ≠ 0) (C G B ε : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hB : GlobalSmoothAnnularBound n μ B) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ¬ GlobalBilateralLower n μ ε := by
  have hmain : ∀ k : ℕ, ∀ (P : Submodule ℝ (Ambient d)) (σ : Measure (Ambient d))
      (A H η : ℝ), Module.finrank ℝ P = k → σ ≠ 0 → 0 < A →
      GlobalUpperGrowth n H σ →
      (∀ x ∈ σ.support, ∀ R : ℝ, 0 < R → ENNReal.ofReal (R ^ n / A) ≤ σ (ball x R)) →
      GlobalSmoothAnnularBound n σ B → 0 < η → η ≤ 1 → GlobalBilateralLower n σ η →
      σ.support ⊆ (P : Set (Ambient d)) → False := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro P σ A H η hdim hσ hA hH hl hAnn hη hη1 hbad hP
      obtain ⟨c, hcP, hc⟩ := GlobalBilateralLower.exists_relative_hole σ A H η hA hH hl hη hbad P hP
      obtain ⟨Q, hQ, ν, _, hν, hgν, _, hlν, hνQ, hAnnν, hbadν⟩ :=
        exists_relative_plane_dimension_drop hn hnd σ hσ A H B η hA hH hl hAnn hη hη1 hbad P hP c hcP hc
      exact ih (Module.finrank ℝ Q) (hQ.trans_eq hdim) Q ν
        ((A * 4 ^ n) * 4 ^ n) ((H * 2 ^ n) * 2 ^ n) (η / 4096) rfl hν
        (by positivity) hgν hlν hAnnν (by positivity) (by linarith) hbadν hνQ
  intro hbad
  exact hmain (Module.finrank ℝ (⊤ : Submodule ℝ (Ambient d))) ⊤ μ C G ε rfl
    hne hC hg hlower hB hε hε1 hbad (fun _ _ => Submodule.mem_top)

theorem exists_flat_ball_of_global_annular_bound {n d : ℕ} (hn : 1 ≤ n) (hnd : n ≤ d)
    (μ : Measure (Ambient d)) (hne : μ ≠ 0) (C G B : ℝ) (hC : 0 < C)
    (hg : GlobalUpperGrowth n G μ)
    (hlower : ∀ x ∈ μ.support, ∀ R : ℝ, 0 < R →
      ENNReal.ofReal (R ^ n / C) ≤ μ (ball x R))
    (hB : GlobalSmoothAnnularBound n μ B) (ε : ℝ) (hε : 0 < ε) :
    ∃ a ∈ μ.support, ∃ r : ℝ, 0 < r ∧ bilateralBeta n μ a r < ε := by
  by_contra hnone
  apply not_global_nonflat_annular_measure hn hnd μ hne C G B (min ε 1) hC hg hlower hB
    (lt_min hε zero_lt_one) (min_le_right _ _)
  intro a ha r hr
  apply (min_le_left ε 1).trans
  exact le_of_not_gt (fun hb => hnone ⟨a, ha, r, hr, hb⟩)

end

end RieszRectifiability

end OAI
