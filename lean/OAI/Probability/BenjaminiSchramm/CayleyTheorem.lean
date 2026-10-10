import OAI.Probability.BenjaminiSchramm.CayleyCritical
import OAI.Probability.BenjaminiSchramm.PhaseInput
import OAI.Probability.BenjaminiSchramm.ExponentialDecay

namespace OAI

open MeasureTheory

namespace Percolation.BenjaminiSchramm

universe u
variable {Λ : Type u} [Group Λ]

theorem cayley_main
    (S : Finset Λ) (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (_hone : 1 ∉ S)
    (hgen : Subgroup.closure (S : Set Λ) = ⊤) (hna : ¬ FolnerAmenable Λ) :
    OperatorBounded (cayleyBond S) (pc (cayleyBond S)) ∧
      MainConclusion (cayleyBond S) ∧
      ∀ p : unitInterval, pc (cayleyBond S) < p → p < pu (cayleyBond S) →
        ∀ᵐ ω ∂law p, (infiniteClusters (cayleyBond S) ω).Infinite := by
  let : Infinite Λ := infinite_of_not_folnerAmenable hna
  have hconn := cayleyBond_connected S hgen
  have hloc := cayleyBond_locallyFinite S hsym
  have hqt := cayleyBond_quasiTransitive S
  have hb := cayley_critical_bounded S hsym _hone hgen hna
  exact ⟨hb, mainConclusion_of_critical_bounded (cayleyBond S) hconn hloc hqt hb,
    publishedPhaseInput_proved (cayleyBond S) hconn hloc hqt⟩

end Percolation.BenjaminiSchramm

end OAI
