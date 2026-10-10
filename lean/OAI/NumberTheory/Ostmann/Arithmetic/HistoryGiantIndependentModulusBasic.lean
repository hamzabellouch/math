import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantReferenceMeanMetadata
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualSelected

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantIndependentModulus
open Construction Conclusion Filter HistorySignedResidues HistoryGiantReferenceMean HistorySignedXiTransport

theorem selected_fixedSmall_factorBound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (a : State) (c : HistoryChoices C.sources seed V l) (outside : List ℕ),
        Template.Matches (Template.current seed l) a.small →
        (∀ q ∈ a.small, sourceMass C.sources q ≠ 0) →
        choicesMass C.sources seed V l c ≠ 0 →
        (decodeHistory C.sources seed V l a c).Supported V outside →
        factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
          (decodeHistory C.sources seed V l a c) := by
  filter_upwards [selected_sources_factorCap_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hsource hm
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro a c outside ha hroot hc hs
  have hm' : 1 ≤ bulkSize k L := by exact_mod_cast hm
  have hfreqNat : a.frequency.natAbs ≤ frequencyBound Bs BD Bz k L l := by
    simpa only [decodeHistory_root] using History.supported_root_frequency_bound hs
  have hfreqReal : |(a.frequency : ℝ)| ≤ (frequencyBound Bs BD Bz k L l : ℝ) := by
    have hh : (a.frequency.natAbs : ℝ) ≤ (frequencyBound Bs BD Bz k L l : ℝ) :=
      by exact_mod_cast hfreqNat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  exact factorBound_decode C.sources _ _ k (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
    (fun j hj => actual_current_length_le k L hj)
    (fun j hj => actual_frequency_le_cap Bs BD Bz k L hm' hj)
    (hsource E C hG hcl hcu hb hd) l hl a c ha hroot hc
    (hfreqReal.trans (actual_frequency_le_cap Bs BD Bz k L hm' hl))

end Ostmann.Arithmetic.HistoryGiantIndependentModulus

end

end OAI
