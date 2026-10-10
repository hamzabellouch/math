import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedXiTransportScalar
import OAI.NumberTheory.Ostmann.Construction.ActualHistoryPairXi

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedXiTransport
open Construction CanonicalOccurrenceTransport HistoryOccurrenceVariables HistorySymbolicEncoding
open HistorySignedDecode HistoryPairPattern HistoryPairSmoothXi

theorem supportedHistoryPairXi_changedGiants (d : Decomposition)
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ) (outside : List ℕ)
    (l : ℕ) (a b : State) (c e : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (Xp Xm : ℤ) (hp : 0≤Xp) (hm : 0≤Xm)
    (hc : (decodeHistory sources seed V l a c).Supported V outside)
    (he : (decodeHistory sources seed V l b e).Supported V outside)
    (hc' : (decodeHistory sources seed V l (giantState a Xp Xm) c).Supported V outside)
    (he' : (decodeHistory sources seed V l (giantState b Xp Xm) e).Supported V outside)
    (bcount scount : ℕ) (X tb td G : ℝ) :
    supportedHistoryPairXi d V outside bcount scount X tb td G
      (decodeHistory sources seed V l (giantState a Xp Xm) c)
      (decodeHistory sources seed V l (giantState b Xp Xm) e)=
    (((decodeHistory sources seed V l a c).compensationProduct:ℂ)*
      ((decodeHistory sources seed V l b e).compensationProduct:ℂ))*
      actualRealXi bcount scount X tb td G outside
        (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e) hc he
        (signedGiantSample (decodeHistory sources seed V l a c) Xp Xm)
        (signedGiantSample (decodeHistory sources seed V l b e) Xp Xm)*
      HistorySignedSpectator.pairSpectator (residueTransform d) outside
        (rebuild (decodeHistory sources seed V l a c) Xp Xm)
        (rebuild (decodeHistory sources seed V l b e) Xp Xm) := by
  have hroot : RootGiantsAgree
      (decodeHistory sources seed V l (giantState a Xp Xm) c)
      (decodeHistory sources seed V l (giantState b Xp Xm) e) := by
    simp only [RootGiantsAgree,decodeHistory_root,giantState,and_self]
  have hXi := congrArg₂ (fun x y : ℂ => x*star y)
    (actualScalar_changedGiants sources seed V outside l a c ha Xp Xm hp hm hc hc'
      bcount scount X tb td G)
    (actualScalar_changedGiants sources seed V outside l b e hb Xp Xm hp hm he he'
      bcount scount X tb td G)
  change actualRealXi bcount scount X tb td G outside
      (decodeHistory sources seed V l a c) (decodeHistory sources seed V l b e) hc he
      (signedGiantSample (decodeHistory sources seed V l a c) Xp Xm)
      (signedGiantSample (decodeHistory sources seed V l b e) Xp Xm)=
    actualRealXi bcount scount X tb td G outside
      (decodeHistory sources seed V l (giantState a Xp Xm) c)
      (decodeHistory sources seed V l (giantState b Xp Xm) e) hc' he'
      (fun i => (integerSample _ i:ℝ)) (fun i => (integerSample _ i:ℝ)) at hXi
  have hspec := HistorySignedSpectator.pairSpectator_eq_projection (residueTransform d) outside
    (rebuild (decodeHistory sources seed V l a c) Xp Xm)
    (rebuild (decodeHistory sources seed V l b e) Xp Xm)
    (decoded_rebuild_nonnegative sources seed V outside l a c Xp Xm hc')
    (decoded_rebuild_nonnegative sources seed V outside l b e Xp Xm he')
  rw [decoded_rebuild_toHistory sources seed V outside l a c Xp Xm hc',
    decoded_rebuild_toHistory sources seed V outside l b e Xp Xm he'] at hspec
  simp only [supportedHistoryPairXi,dite_eq_left hc',dite_eq_left he',pairedRealXi,
    leftMap_sample,rightMap_sample _ _ hroot]
  rw [←hXi,←hspec,
    decoded_compensationProduct_eq sources seed V l (giantState a Xp Xm) a c,
    decoded_compensationProduct_eq sources seed V l (giantState b Xp Xm) b e]

end Ostmann.Arithmetic.HistorySignedXiTransport

end

end OAI
