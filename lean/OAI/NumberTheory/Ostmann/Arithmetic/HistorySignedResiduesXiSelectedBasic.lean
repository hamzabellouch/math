import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesXi
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportReductionSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter HistorySignedXiTransport

theorem selected_changed_decoded_largePrimes_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0<k) :
    ∀ᶠ L : ℝ in atTop,∀(E : Finset ℕ)(C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L)≤C.blockBase → C.blockBase-2<(C.giantCenter:ℝ) →
      (C.giantCenter:ℝ)<C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)|≤favorableBlockWidth L/16 → |(C.spectatorBin:ℝ)|≤favorableBlockWidth L/16 →
      ∀l≤k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀(x : OuterSample C.sources (Template.current seed l) C.giant)
        (s Xp Xm : ℤ) (c : HistoryChoices C.sources seed V l),
      (outerPrior C.sources (Template.current seed l) C.giant).mass x≠0 →
      choicesMass C.sources seed V l c≠0 →
      HistorySupportReduction.LargePrimes V
        (decodeHistory C.sources seed V l
          (giantState (outerState C.sources (Template.current seed l) C.giant x s) Xp Xm) c) := by
  filter_upwards [initial_sources_above_frequencies_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x s Xp Xm c hx hc
  have hx' : C.giant.law.mass x.1*(C.giant.law.mass x.2.1*
      (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x.2.2)≠0 := hx
  have hmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  apply HistorySupportReduction.decoded_largePrimes C.sources _ _ l _ c
  · exact Template.assignedSlots_matches _ _ _
  · exact assignedSlots_source_mass_ne_zero _ _ _ hmass
  · exact hc
  · intro j hj
    exact (hL E C hG hcl hcu hb hd j (hj.trans hl)).2

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
