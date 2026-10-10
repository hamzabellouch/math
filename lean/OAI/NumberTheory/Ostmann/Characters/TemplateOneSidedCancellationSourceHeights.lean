import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimatePivotHeight
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationSurvivingSlice
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputs
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhasePriorJoinSourceSelectedNormBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedCancellation
open Template TemplateSupportRemoval Preliminaries Template.OneSidedPhase TemplateOneSidedNumericInputs
open HigherBiasSource HigherBiasSource.SourceTemplate InitialCharacterScale DiagonalEstimate
open TemplateOneSidedSourceScales HistoryFrequencyBudget Filter
attribute [local instance] Classical.propDecidable

theorem source_X_ge_one {d : Decomposition} {E : Finset ℕ}
    {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD) :
    (1:ℝ) ≤ s.locations.X := by
  have hp : 0<s.locations.X := by exact_mod_cast fixedConfiguration_X_pos w
  exact_mod_cast hp

theorem sourceHeldCoordinates_height {d : Decomposition} {E : Finset ℕ}
    {δ L α β ρ γ c₀ c BD Cmod : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (j : ℕ) (hL : 0≤L) (hCmod : 0≤Cmod)
    (hband : ∀p∈E,α*L≤Real.log (Real.log p) ∧ Real.log (Real.log p)≤β*L)
    (p : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L))→PrimeUpTo s.locations.Q)
    (hmass : (sourceSurvivorPrior w j).mass p≠0)
    (i l : SurvivingPrimeIndex k j (sourceWidth w.configuration (wordSize k L)))
    (q r : PrimeUpTo s.locations.Q) (hq : q∈sourceSurvivorShells w j i)
    (hr : r∈sourceSurvivorShells w j l) :
    ∀v,|((insertCoordinate i (heldPrimeCoordinates p i l r) (q.val:ℤ) v:ℤ):ℝ)| ≤
      Real.exp (rowLogHeight Cmod (depthScale k) (β+1) L) := by
  have hb : Real.exp (β*L) ≤ Real.exp ((β+1)*L) := Real.exp_le_exp.mpr (by nlinarith)
  apply heldPrimeCoordinates_height p i l q r hCmod
  · intro v
    exact (sourceSurvivorShells_log_bounds w hband j v (p v)
      (sourceSurvivorPrior_mem_of_mass_ne_zero w j p hmass v)).2.trans hb
  · exact (sourceSurvivorShells_log_bounds w hband j i q hq).2.trans hb
  · exact (sourceSurvivorShells_log_bounds w hband j l r hr).2.trans hb

theorem source_compiler_heights_eventually (k j : ℕ) (BD c β : ℝ)
    (hBD : 0≤BD) (hβ : -1<β) :
    ∀ᶠ L : ℝ in atTop,∀Cmod : ℝ,0≤Cmod →
      linearEnvelope (BD+20*Real.log (depthScale k)) j*(wordSize k L:ℝ) ≤
        rowLogHeight Cmod (depthScale k) (β+1) L ∧
      ∀(d : Decomposition)(E : Finset ℕ)(δ α ρ γ c₀ : ℝ)
        (s : SelectedWordSource d E δ L k α β ρ γ c₀)(w : FixedConfigurationWitness s c BD),
        j<k → ∀P∈DiagonalEstimate.sourcePivotRanges w j,
          |(P:ℝ)| ≤ Real.exp (rowLogHeight Cmod (depthScale k) (β+1) L) := by
  have ha : 0≤BD+20*Real.log (depthScale k) :=
    add_nonneg hBD (mul_nonneg (by norm_num) (Real.log_nonneg (one_le_depthScale k)))
  filter_upwards [eventually_linear_frequency_height
    (linearEnvelope (BD+20*Real.log (depthScale k)) j) (depthScale k) (β+1)
    (linearEnvelope_pos ha j).le (depthScale_pos k).le (by linarith),
    sourcePivotRanges_height_eventually k c β hβ] with L hfreq hP
  intro Cmod hCmod
  refine ⟨by simpa only [wordSize] using hfreq Cmod hCmod,?_⟩
  intro d E δ α ρ γ c₀ s w hj P hmem
  apply (hP d E δ α ρ γ c₀ BD s w j hj P hmem).trans
  apply Real.exp_le_exp.mpr
  unfold rowLogHeight
  have hpoly : 0≤historyPolynomialCost Cmod (depthScale k) 3 L := by
    unfold historyPolynomialCost
    positivity
  linarith [Real.log_nonneg (by norm_num : (1:ℝ)≤4)]

end Ostmann.Characters.TemplateOneSidedCancellation

end

end OAI
