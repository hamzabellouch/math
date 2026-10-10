import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinNorm
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminalIndexedReindex

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Characters.Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def pairedTerminalUnary (k j : ℕ) (width : Role→ℕ)
    (χ : (schedule k j).Constituent width→(q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : (schedule k j).Constituent width→ℕ→ℂ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) : ℂ :=
  (ζ (σ i) q * historyUnaryAt k j width (χ i) s t (σ i) q) *
    conj (ζ (ρ i) q * historyUnaryAt k j width (χ i) s u (ρ i) q)

theorem norm_pairedTerminalUnary_le (k j : ℕ) (width : Role→ℕ)
    (χ : (schedule k j).Constituent width→(q:ℕ)→MulChar (ZMod q) ℂ)
    (ζ : (schedule k j).Constituent width→ℕ→ℂ)
    (σ ρ : Equiv.Perm ((schedule k j).Constituent width))
    (s : ℤ) (t u : HistoryReconstruction.Tree j)
    (i : (schedule k j).Constituent width) (q : ℕ) [Fact q.Prime]
    (hχ : χ i q≠1) (hζσ : ‖ζ (σ i) q‖≤1) (hζρ : ‖ζ (ρ i) q‖≤1)
    (ht : HistoryFrequencyUnits q j s t) (hu : HistoryFrequencyUnits q j s u) :
    ‖pairedTerminalUnary k j width χ ζ σ ρ s t u i q‖≤1 := by
  simp only [pairedTerminalUnary,historyUnaryAt_prime,norm_mul,Complex.norm_conj,
    norm_actualHistoryUnary k width (χ i q) hχ j s t ht,
    norm_actualHistoryUnary k width (χ i q) hχ j s u hu,mul_one]
  exact (mul_le_mul hζσ hζρ (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
