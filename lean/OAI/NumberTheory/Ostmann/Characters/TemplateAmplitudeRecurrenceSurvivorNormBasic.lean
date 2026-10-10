import OAI.NumberTheory.Ostmann.Characters.TemplateActualPivotFactors

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem norm_survivingPrimeRow_le {S : Type*} [Fintype S] [DecidableEq S]
    (r : S → ℕ) [∀ i, Fact (r i).Prime]
    (i : S) (χ : MulChar (ZMod (r i)) ℂ) (a : ZMod (r i))
    (ν : ℂ) (hν : ‖ν‖ ≤ 1) (b : S → ℤ) (bP : ℤ) (P : ℕ) (v : ℤ) :
    ‖survivingPrimeRow r i χ a ν b bP P v‖ ≤ 1 := by
  simp only [survivingPrimeRow, translatedAdditivePhase, norm_mul,
    (ZMod.stdAddChar : AddChar (ZMod (r i)) ℂ).norm_apply, one_mul]
  apply le_trans (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hν).trans
      (norm_character_zpow_le_one χ _ bP)))
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro h hh; exact norm_nonneg _
  · intro h hh; exact norm_character_zpow_le_one χ _ (b h)

theorem norm_actualPivotSurviving_le (k j : ℕ) (hj : j < k) (width : Role → ℕ)
    (r : SurvivingPrimeIndex k j width → ℕ) [∀ i, Fact (r i).Prime]
    (χ : ∀ i, MulChar (ZMod (r i)) ℂ) (hχ : ∀ i, χ i ≠ 1)
    (a : ∀ i, ZMod (r i)) (P : ℕ) (s : ℤ) (t : HistoryReconstruction.Tree j)
    (ht : ∀ i, HistoryFrequencyUnits (r i) j s t) :
    ‖actualPivotSurviving k j hj width r χ a P s t‖ ≤ 1 := by
  rw [actualPivotSurviving, norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    exact norm_survivingPrimeRow_le r i (χ i) (a i) _
      (norm_actualHistoryUnary k width (χ i) (hχ i) j s t (ht i) _).le _ _ P s

end Ostmann.Characters.Template

end

end OAI
