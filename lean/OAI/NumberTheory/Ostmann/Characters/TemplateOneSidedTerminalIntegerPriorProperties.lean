import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateIntegerPriorProperties
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedTerminalIntegerPriorBasic

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval
open Construction Preliminaries Template HigherBiasSource HigherBiasSource.SourceTemplate
open InitialCharacterScale DiagonalEstimate TemplateOneSidedSourceScales
attribute [local instance] Classical.propDecidable

section
variable {d : Decomposition} {E : Finset ℕ} {δ L α β ρ γ c₀ c BD : ℝ} {k : ℕ}
    {s : SelectedWordSource d E δ L k α β ρ γ c₀} (w : FixedConfigurationWitness s c BD)
    (n : ℕ)

theorem terminalSourceIntegerSupport_eq_nat_image (i : terminalSourceIndex w n) :
    terminalSourceIntegerSupport w n i=
      (terminalSourceNaturalSupport w n i).image (fun p:ℕ=>(p:ℤ)) :=
  integerPrimeSupport_eq_nat_image _

theorem terminalSourceNaturalSupport_prime (i : terminalSourceIndex w n) {p : ℕ}
    (hp : p∈terminalSourceNaturalSupport w n i) : p.Prime := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  exact primeUpTo_prime q

theorem terminalSourceIntegerSupport_positive_prime (i : terminalSourceIndex w n) {a : ℤ}
    (ha : a∈terminalSourceIntegerSupport w n i) : 0 < a ∧ a.natAbs.Prime :=
  integerPrimeSupport_positive_prime ha

theorem terminalSourceIntegerWeight_nonneg (i : terminalSourceIndex w n) (a : ℤ) :
    0 ≤ terminalSourceIntegerWeight w n i a :=
  integerPrimeWeight_nonneg _ (sourceScheduledShells_pos w (n+1) i) a

theorem terminalSourceIntegerWeight_pos_iff (i : terminalSourceIndex w n) (a : ℤ) :
    0 < terminalSourceIntegerWeight w n i a ↔ a∈terminalSourceIntegerSupport w n i :=
  integerPrimeWeight_pos_iff _ (sourceScheduledShells_pos w (n+1) i) a

theorem terminalSourceIntegerWeight_eq_zero_of_not_mem (i : terminalSourceIndex w n) (a : ℤ)
    (ha : a∉terminalSourceIntegerSupport w n i) : terminalSourceIntegerWeight w n i a=0 :=
  ite_eq_right ha

theorem terminalSourceIntegerWeight_sum (i : terminalSourceIndex w n) :
    (∑a∈terminalSourceIntegerSupport w n i,terminalSourceIntegerWeight w n i a)=1 :=
  integerPrimeWeight_sum _ (sourceScheduledShells_pos w (n+1) i)

theorem terminalSourceIntegerSupport_bounds
    (hband : ∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)
    (i : terminalSourceIndex w n) {a : ℤ} (ha : a∈terminalSourceIntegerSupport w n i) :
    Real.exp (Real.exp (α*L)) ≤ (a:ℝ) ∧ (a:ℝ) ≤ Real.exp (Real.exp (β*L)) :=
  integerPrimeSupport_exp_bounds
    (fixedConfiguration_scheduled_log_bounds w hband (n+1) i) ha

theorem terminalSourceIntegerSupport_abs_le
    (hband : ∀p∈E,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L)
    (i : terminalSourceIndex w n) {a : ℤ} (ha : a∈terminalSourceIntegerSupport w n i) :
    |(a:ℝ)| ≤ Real.exp (Real.exp (β*L)) := by
  rw [abs_of_pos (by exact_mod_cast (terminalSourceIntegerSupport_positive_prime w n i ha).1)]
  exact (terminalSourceIntegerSupport_bounds w n hband i ha).2

end
end Ostmann.Characters.TemplateOneSidedTerminalSupportRemoval

end

end OAI
