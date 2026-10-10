import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorSource
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMarginalScalesBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedNumericInputsAtoms

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate Preliminaries
open InitialCharacterScale Filter TemplateOneSidedNumericInputs TemplateOneSidedPrior
attribute [local instance] Classical.propDecidable

theorem eventually_sourceScheduled_marginal_bounds (k : ℕ)
    {α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ BD : ℝ),
      (∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j i,
        Real.exp (-(β+1)*L) ≤ primeShellMass (sourceScheduledShells w j i) ∧
        1/primeShellMass (sourceScheduledShells w j i) ≤ Real.exp ((β+1)*L) ∧
        ∀p,(primeShellPrior (sourceScheduledShells w j i) (sourceScheduledShells_pos w j i)).mass p ≤
          Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
  have hβ : 0 < β := hα.trans hαβ
  filter_upwards [eventually_sourceScheduled_mass_lower k hα hαβ hρ hγ hc₀ hc,
    eventually_primeShellPrior_mass_le (c:=β+1) hα (by linarith)] with L hmass hatom
  intro d E δ BD hE hband s w j i
  have hm := hmass d E δ BD hE s w j i
  refine ⟨hm,source_normalization_le _ hm,?_⟩
  exact hatom _ (sourceScheduledShells_pos w j i) hm
    (fun p hp=>(fixedConfiguration_scheduled_log_bounds w hband j i p hp).1)

theorem eventually_sourceSurvivor_marginal_bounds (k : ℕ)
    {α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ BD : ℝ),
      (∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀j i,
        Real.exp (-(β+1)*L) ≤ primeShellMass (sourceSurvivorShells w j i) ∧
        1/primeShellMass (sourceSurvivorShells w j i) ≤ Real.exp ((β+1)*L) ∧
        ∀n : ℤ,sourceSurvivorIntegerWeight w j i n ≤
          Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
  filter_upwards [eventually_sourceScheduled_marginal_bounds k hα hαβ hρ hγ hc₀ hc]
    with L hL
  intro d E δ BD hE hband s w j i
  have hh : Real.exp (-(β+1)*L) ≤ primeShellMass (sourceSurvivorShells w j i) ∧
      1/primeShellMass (sourceSurvivorShells w j i) ≤ Real.exp ((β+1)*L) ∧
      ∀p,(primeShellPrior (sourceSurvivorShells w j i) (sourceSurvivorShells_pos w j i)).mass p ≤
        Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
    cases i with
    | inl a =>
      exact hL d E δ BD hE hband s w j
        (copiedConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) a)
    | inr a =>
      exact hL d E δ BD hE hband s w j
        (outsideConstituentOld (schedule k j) j (sourceWidth w.configuration (wordSize k L)) a)
  refine ⟨hh.1,hh.2.1,?_⟩
  intro n
  by_cases hn : n∈integerPrimeSupport (sourceSurvivorShells w j i)
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
    exact (integerPrimeWeight_cast _ (sourceSurvivorShells_pos w j i) p).le.trans (hh.2.2 p)
  · change integerPrimeWeight _ n ≤ _
    rw [integerPrimeWeight,ite_eq_right hn]
    exact (Real.exp_pos _).le

end Ostmann.Characters.DiagonalEstimate

end

end OAI
