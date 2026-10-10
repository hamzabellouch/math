import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCancellation
import OAI.NumberTheory.Ostmann.Characters.HigherBiasHarmonicAssembly
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationTerminalActual

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters
open Construction Filter HigherBiasContradiction
open scoped BigOperators

theorem eventually_no_higher_biased_mass (d : Decomposition) (α β mass δ : ℝ)
    (hα : 0 < α) (hαβ : α < β) (hmass : 0 < mass) (hδ : 0 < δ) (hδu : δ ≤ 1) :
    ∀ᶠ L : ℝ in atTop,∀E : Finset ℕ,
      (∀p∈E,p.Prime ∧ α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      mass*L ≤ harmonicPrimeMass E → (∀p∈E,δ ≤ higherPrimeBias d p) → False := by
  apply no_biased_mass_of_actual_cancellation d α β mass δ hα hαβ hmass hδ hδu
  · intro ρ γ c₀ c BD hρ hγ hc₀ hc hBD
    exact Filter.Eventually.of_forall (fun n=>actual_terminalCancellation d δ n
      hα hαβ hρ hγ hc₀ hc (zero_le_one.trans hBD))
  · intro ρ γ c₀ c BD hρ hγ hc₀ hc hBD
    exact Filter.Eventually.of_forall (fun k=>actual_diagonalCancellation d δ k
      hα hαβ hρ hγ hc₀ hc (zero_le_one.trans hBD))

theorem eventually_higher_harmonic_band_le (d : Decomposition)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,∀P : Finset ℕ,(∀p∈P,p.Prime) →
      (∀p∈P,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      (∑p∈P,higherPrimeBias d p/p) ≤ ε*L := by
  apply harmonic_band_le_of_actual_cancellation d hα hαβ ?_ ?_ ε hε
  · intro δ _hδ _hδu ρ γ c₀ c BD hρ hγ hc₀ hc hBD
    exact Filter.Eventually.of_forall (fun n=>actual_terminalCancellation d δ n
      hα hαβ hρ hγ hc₀ hc (zero_le_one.trans hBD))
  · intro δ _hδ _hδu ρ γ c₀ c BD hρ hγ hc₀ hc hBD
    exact Filter.Eventually.of_forall (fun k=>actual_diagonalCancellation d δ k
      hα hαβ hρ hγ hc₀ hc (zero_le_one.trans hBD))

theorem higherHarmonicBandMass_isLittleO (d : Decomposition)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    higherHarmonicBandMass d α β =o[atTop] (fun L : ℝ=>L) :=
  higherHarmonicBandMass_isLittleO_of_eventually d
    (eventually_higher_harmonic_band_le d hα hαβ)

end Ostmann.Characters

end

end OAI
