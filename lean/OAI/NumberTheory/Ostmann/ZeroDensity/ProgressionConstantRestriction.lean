import OAI.NumberTheory.Ostmann.ZeroDensity.PublishedProgressionInputs

namespace OAI

/-! # Decreasing the common exceptional-zero constant -/

namespace Ostmann

/-- Completeness and Page uniqueness persist when the exceptional strip is
narrowed. The prime-progression estimate and its actual zero are unchanged. -/
noncomputable def PublishedProgressionInput.restrictKappa (P : PublishedProgressionInput)
    (κ : ℝ) (hκ : 0 < κ) (hκP : κ ≤ P.kappa) : PublishedProgressionInput where
  kappa := κ
  decay := P.decay
  errorConstant := P.errorConstant
  kappa_pos := hκ
  decay_pos := P.decay_pos
  errorConstant_nonneg := P.errorConstant_nonneg
  localZero := P.localZero
  divides := P.divides
  complete := by
    intro q hq e he hβ
    apply P.complete q hq e he
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hl : 0 < Real.log (4 * (q : ℝ)) := Real.log_pos (by linarith)
    have hh := div_le_div_of_nonneg_right hκP hl.le
    linarith
  unique := by
    intro Q hQ e f he hf hβ hγ
    apply P.unique Q hQ e f he hf
    all_goals
      have hQ' : (2 : ℝ) ≤ Q := by exact_mod_cast hQ
      have hl : 0 < Real.log (4 * (Q : ℝ)) := Real.log_pos (by linarith)
      have hh := div_le_div_of_nonneg_right hκP hl.le
      linarith
  theta := P.theta

end Ostmann

end OAI
