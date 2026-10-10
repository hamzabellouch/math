import OAI.NumberTheory.Ostmann.Characters.HigherBiasContradictionAssembly
import OAI.NumberTheory.Ostmann.Characters.HigherBiasHarmonicTransfer

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Characters.HigherBiasContradiction
open Construction Filter
open scoped BigOperators

theorem harmonic_band_le_of_actual_cancellation (d : Decomposition)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hterminal : ∀δ : ℝ,0 < δ → δ ≤ 1 →
      ∀ρ γ c₀ c BD : ℝ,0 < ρ → 0 < γ → 0 < c₀ → 0 < c → 1 ≤ BD →
      ∀ᶠn : ℕ in atTop,TerminalCancellation d δ α β ρ γ c₀ c BD n)
    (hdiagonal : ∀δ : ℝ,0 < δ → δ ≤ 1 →
      ∀ρ γ c₀ c BD : ℝ,0 < ρ → 0 < γ → 0 < c₀ → 0 < c → 1 ≤ BD →
      ∀ᶠk : ℕ in atTop,DiagonalCancellation d δ α β ρ γ c₀ c BD k)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ L : ℝ in atTop,∀ P : Finset ℕ,(∀p∈P,p.Prime) →
      (∀p∈P,α*L ≤ Real.log (Real.log p) ∧ Real.log (Real.log p) ≤ β*L) →
      (∑p∈P,higherPrimeBias d p/p) ≤ ε*L := by
  apply eventually_higher_harmonic_band_le_of_no_biased_mass d hα hαβ ?_ ε hε
  intro δ hδ hδu mass hmass
  exact no_biased_mass_of_actual_cancellation d α β mass δ hα hαβ hmass hδ hδu
    (hterminal δ hδ hδu) (hdiagonal δ hδ hδu)

theorem harmonic_isLittleO_of_actual_cancellation (d : Decomposition)
    {α β : ℝ} (hα : 0 < α) (hαβ : α < β)
    (hterminal : ∀δ : ℝ,0 < δ → δ ≤ 1 →
      ∀ρ γ c₀ c BD : ℝ,0 < ρ → 0 < γ → 0 < c₀ → 0 < c → 1 ≤ BD →
      ∀ᶠn : ℕ in atTop,TerminalCancellation d δ α β ρ γ c₀ c BD n)
    (hdiagonal : ∀δ : ℝ,0 < δ → δ ≤ 1 →
      ∀ρ γ c₀ c BD : ℝ,0 < ρ → 0 < γ → 0 < c₀ → 0 < c → 1 ≤ BD →
      ∀ᶠk : ℕ in atTop,DiagonalCancellation d δ α β ρ γ c₀ c BD k) :
    higherHarmonicBandMass d α β =o[atTop] (fun L : ℝ=>L) :=
  higherHarmonicBandMass_isLittleO_of_eventually d
    (harmonic_band_le_of_actual_cancellation d hα hαβ hterminal hdiagonal)

end Ostmann.Characters.HigherBiasContradiction

end

end OAI
