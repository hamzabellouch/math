import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedDecodeSupported
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedXiTransportBasic

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedXiTransport
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistorySignedDecode

theorem actualScalar_changedGiants (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (Xp Xm : ℤ) (hp : 0≤Xp) (hm : 0≤Xm)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (hc' : (decodeHistory sources seed V l (giantState a Xp Xm) c).Supported V outside)
    (b s : ℕ) (X tb td G : ℝ) :
    actualRealHistoryScalar b s X tb td G outside (decodeHistory sources seed V l a c) hc
      (signedGiantSample (decodeHistory sources seed V l a c) Xp Xm)=
    actualRealHistoryScalar b s X tb td G outside
      (decodeHistory sources seed V l (giantState a Xp Xm) c) hc'
      (fun i => (integerSample (decodeHistory sources seed V l (giantState a Xp Xm) c) i:ℝ)) := by
  apply actualRealHistoryScalar_eq_of_coordinates seed _ _ hc hc'
    (decoded_tree_source_labels sources seed V l a c ha)
    (decoded_tree_source_labels sources seed V l (giantState a Xp Xm) c ha)
    (decoded_plan_eq sources seed V outside l a (giantState a Xp Xm) c c ha ha rfl rfl hc hc')
  exact signedGiantSample_coordinate_eq sources seed V l a c ha Xp Xm hp hm

theorem decoded_rebuild_nonnegative (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (Xp Xm : ℤ)
    (hc' : (decodeHistory sources seed V l (giantState a Xp Xm) c).Supported V outside) :
    (rebuild (decodeHistory sources seed V l a c) Xp Xm).Nonnegative := by
  rw [rebuild_decodeHistory]
  exact signedDecode_nonnegative_of_supported sources seed V l
    ⟨a.frequency,Xp,Xm,a.small⟩ c outside hc'

theorem decoded_rebuild_toHistory (sources : SourceFamily) (seed : List SourceSlot)
    (V : ℕ→ℕ) (outside : List ℕ) (l : ℕ) (a : State) (c : HistoryChoices sources seed V l)
    (Xp Xm : ℤ)
    (hc' : (decodeHistory sources seed V l (giantState a Xp Xm) c).Supported V outside) :
    (rebuild (decodeHistory sources seed V l a c) Xp Xm).toHistory=
      decodeHistory sources seed V l (giantState a Xp Xm) c := by
  rw [rebuild_decodeHistory]
  exact signedDecode_toHistory_of_supported sources seed V l
    ⟨a.frequency,Xp,Xm,a.small⟩ c outside hc'

end Ostmann.Arithmetic.HistorySignedXiTransport

end

end OAI
