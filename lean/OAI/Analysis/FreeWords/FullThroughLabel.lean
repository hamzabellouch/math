import Mathlib
import OAI.Analysis.FreeWords.FreeWords
import OAI.Analysis.FreeWords.ThroughLabel

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

universe u

theorem free_words_through_label :
    ∃ C : ℕ → ℝ, (∀ r, 0 < C r) ∧
      ∀ N : ℕ, 1 ≤ N → ∃ d₀ : ℕ, N ≤ d₀ ∧
        ∀ d : ℕ, d₀ ≤ d →
          (∀ r : ℕ, 1 ≤ r → r ≤ N →
            ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
              (τ : A →ₚ[ℂ] ℂ), FaithfulTracial τ →
              ∀ (P : FreePartitions τ r d) (W : Sym (Fin d) r),
                ‖wordSum P W‖ ≤ KKThroughLabel.beta C d r W) ∧
          (∀ r : ℕ, 1 ≤ r → r ≤ N → ∀ a : Fin d,
            KKThroughLabel.throughSum C d r a ≤ 64) := by
  have h : ∀ r : ℕ, ∃ C : ℝ, 0 < C ∧ ∃ D : ℕ, r ≤ D ∧
      ∀ d : ℕ, D ≤ d → 1 ≤ r →
        ∀ (A : Type u) [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
          (τ : A →ₚ[ℂ] ℂ), FaithfulTracial τ →
          ∀ (P : FreePartitions τ r d) (W : Sym (Fin d) r),
            ‖wordSum P W‖ ≤
              (if (W : Multiset (Fin d)).Nodup then 7*Real.sqrt ((r-1).factorial:ℝ)
                else C) * (d:ℝ)^(-((r-1:ℕ):ℝ)/2) := by
    intro r
    by_cases hr : 1 ≤ r
    · obtain ⟨C, hC, D, hD, hb⟩ := free_projection_words r hr
      exact ⟨C, hC, D, hD, fun d hd _ => hb d hd⟩
    · exact ⟨1, zero_lt_one, r, le_rfl, fun _ _ hr' => (hr hr').elim⟩
  choose C hC D hD hbound using h
  refine ⟨C, hC, ?_⟩
  intro N hN
  obtain ⟨d₀, hd₀, hthreshold, hsum⟩ := KKThroughLabel.through_label C D N hN
  refine ⟨d₀, (hD N).trans (hthreshold N hN le_rfl), ?_⟩
  intro d hd
  constructor
  · intro r hr hrN A instA instO instS τ hτ P W
    exact hbound r d ((hthreshold r hr hrN).trans hd) hr A τ hτ P W
  · exact hsum d hd

end

end KKFreeWords
end

end OAI
