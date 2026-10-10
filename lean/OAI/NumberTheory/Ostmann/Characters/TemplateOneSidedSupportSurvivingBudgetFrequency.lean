import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateFrequencyScales
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateSupportRemovalPriorProperties
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedSupportSurvivingBudgetDivisors

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedSupportSurviving
open Template SymbolicHistory TemplateOneSidedBudget TemplateOneSidedSupportTelescoping
open HigherBiasSource HigherBiasSource.SourceTemplate DiagonalEstimate InitialCharacterScale
open HistoryFrequencyLabels HistoryFrequencyBudget Filter
attribute [local instance] Classical.propDecidable

theorem eventually_actualFamilies_divisorsBelow (k : ℕ) {BD α : ℝ}
    (hBD : 0 ≤ BD) (hα : 0 < α) :
    ∀ᶠ L : ℝ in atTop, ∀ (d : Decomposition) (E : Finset ℕ) (δ β ρ γ c₀ c : ℝ),
    (∀p∈E, α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
    ∀ (s : SelectedWordSource d E δ L k α β ρ γ c₀) (w : FixedConfigurationWitness s c BD)
      (j : ℕ), j ≤ k → ∀ (P : ℤ)
      (e : Equiv.Perm (ActualCopied w.configuration (wordSize k L) j))
      (h : SourceHistory (k:=k) (L:=L) (BD:=BD) j)
      (i : GroupedSourceIndex w j) (q : Expr (GroupedSourceIndex w j)),
      q∈actualFamilies k (survivingWidth k j (sourceWidth w.configuration (wordSize k L))) j
        (origins k j) h.val.1 (groupedExpressions k j (sourceWidth w.configuration (wordSize k L)) P e)
        h.val.2 i →
      ∀ (u : GroupedSourceIndex w j) (n : ℤ), n∈groupedSourceIntegerSupport w j u →
        q.DivisorsBelow n.toNat := by
  filter_upwards [actualFrequencyCutoff_eventually k hBD hα] with L hL
  intro d E δ β ρ γ c₀ c hband s w j hj P e h i q hq u n hn
  have hb := (groupedSourceIntegerSupport_bounds w j hband u hn).1
  rw [groupedSourceIntegerSupport_eq_nat_image] at hn
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
  have hp0 : (0:ℝ) < p := by exact_mod_cast (groupedSourceNaturalSupport_prime w j u hp).pos
  have hlog : Real.exp (α*L) ≤ Real.log p := by
    have hh := Real.log_le_log (Real.exp_pos (Real.exp (α*L))) (by simpa only [Int.cast_natCast] using hb)
    simpa only [Real.log_exp] using hh
  have hcut := hL.2 p hlog
  apply obstructionExpressions_divisorsBelow k j
    (ranges (BD+20*Real.log (depthScale k)) (wordSize k L:ℝ) j) p ?_ [] false
    h.val.1 _ h.val.2 (groupedExpressions_divisorsBelow k j _ P e p) h.property q
    (actualFamilies_obstructions _ _ _ _ _ _ _ false i q hq)
  intro path f hf
  have hh := ((hL.1 j hj path f hf).2).trans_lt hcut
  have hh' : (f.natAbs:ℤ) < (p:ℤ) := by exact_mod_cast hh
  simpa only [Int.natCast_natAbs] using hh'

end Ostmann.Characters.TemplateOneSidedSupportSurviving

end

end OAI
