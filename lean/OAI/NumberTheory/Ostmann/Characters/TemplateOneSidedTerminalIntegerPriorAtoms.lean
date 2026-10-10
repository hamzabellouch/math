import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateMarginalScales
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalIntegerPriorProperties

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale DiagonalEstimate Filter
attribute [local instance] Classical.propDecidable

theorem eventually_terminalSource_marginal_bounds (k : ℕ)
    {α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ BD : ℝ),
      (∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀n (i : terminalSourceIndex w n),
        Real.exp (-(β+1)*L) ≤ primeShellMass (sourceScheduledShells w (n+1) i) ∧
        1/primeShellMass (sourceScheduledShells w (n+1) i) ≤ Real.exp ((β+1)*L) ∧
        ∀a : ℤ,terminalSourceIntegerWeight w n i a ≤
          Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
  filter_upwards [eventually_sourceScheduled_marginal_bounds k hα hαβ hρ hγ hc₀ hc]
    with L hL
  intro d E δ BD hE hband s w n i
  have hh := hL d E δ BD hE hband s w (n+1) i
  refine ⟨hh.1,hh.2.1,?_⟩
  intro a
  by_cases ha : a∈terminalSourceIntegerSupport w n i
  · obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact (terminalSourceIntegerWeight_cast w n i p).le.trans (hh.2.2 p)
  · rw [terminalSourceIntegerWeight_eq_zero_of_not_mem w n i a ha]
    exact (Real.exp_pos _).le

theorem eventually_terminalSourceIntegerWeight_le (k : ℕ)
    {α β ρ γ c₀ c : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hρ : 0 < ρ) (hγ : 0 < γ) (hc₀ : 0 < c₀) (hc : 0 < c) :
    ∀ᶠ L : ℝ in atTop,∀(d : Decomposition)(E : Finset ℕ)(δ BD : ℝ),
      (∀p∈E,p.Prime) →
      (∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      ∀s : SelectedWordSource d E δ L k α β ρ γ c₀,∀w : FixedConfigurationWitness s c BD,
      ∀n (i : terminalSourceIndex w n) (a : ℤ),terminalSourceIntegerWeight w n i a ≤
        Real.exp (-(1/2:ℝ)*Real.exp (α*L)) := by
  filter_upwards [eventually_terminalSource_marginal_bounds k hα hαβ hρ hγ hc₀ hc]
    with L hL
  intro d E δ BD hE hband s w n i
  exact (hL d E δ BD hE hband s w n i).2.2

end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
