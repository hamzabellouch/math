import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseOutside
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSpectator

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryOccurrenceVariables HistorySignedDecode HistorySignedSpectatorCRT
open HistorySignedSpectator HistorySignedResidueFactorization

theorem residueSpectator_nonzero_outsideUnits_decode_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a b : State) (c : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (hab : a.frequency=b.frequency) (hbprime : b.PrimeSmall)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (hV : ∀q∈outside,∀j≤l,V j<q)
    (Xp Xm : ℤ)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (hz : residueSpectator g outside outside.prod (decodeHistory sources seed V l b c) Xp Xm≠0) :
    OutsideUnits outside (rebuild (decodeHistory sources seed V l b c) Xp Xm) :=
  residueSpectator_nonzero_outsideUnits_static _
    (staticSkeleton_decode_redraw sources seed V l a b c ha hb hs hab hbprime)
    g outside hprime hg hV
    (internal_outside_product_coprime_decode_redraw sources seed V l a b c hs) Xp Xm hi hz

theorem residuePairSpectator_nonzero_outsideUnits_decode_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a a' b b' : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hb' : Template.Matches (Template.current seed l) b'.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ks : (decodeHistory sources seed V l a' d).Supported V outside)
    (hab : a.frequency=b.frequency) (hab' : a'.frequency=b'.frequency)
    (hbprime : b.PrimeSmall) (hbprime' : b'.PrimeSmall)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (hV : ∀q∈outside,∀j≤l,V j<q)
    (Xp Xm : ℤ)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (ki : (rebuild (decodeHistory sources seed V l b' d) Xp Xm).IntegralGuard)
    (hz : residuePairSpectator g outside outside.prod (decodeHistory sources seed V l b c)
      (decodeHistory sources seed V l b' d) (Xp,Xm)≠0) :
    OutsideUnits outside (rebuild (decodeHistory sources seed V l b c) Xp Xm) ∧
      OutsideUnits outside (rebuild (decodeHistory sources seed V l b' d) Xp Xm) :=
  residuePairSpectator_nonzero_outsideUnits_static _ _
    (staticSkeleton_decode_redraw sources seed V l a b c ha hb hs hab hbprime)
    (staticSkeleton_decode_redraw sources seed V l a' b' d ha' hb' ks hab' hbprime')
    g outside hprime hg hV
    (internal_outside_product_coprime_decode_redraw sources seed V l a b c hs)
    (internal_outside_product_coprime_decode_redraw sources seed V l a' b' d ks) Xp Xm hi ki hz

theorem residuePairSpectator_nonzero_pivotOutsideCoprime_decode_redraw
    (sources : SourceFamily) (seed : List SourceSlot) (V : ℕ→ℕ)
    (outside : List ℕ) (l : ℕ) (a a' b b' : State)
    (c d : HistoryChoices sources seed V l)
    (ha : Template.Matches (Template.current seed l) a.small)
    (ha' : Template.Matches (Template.current seed l) a'.small)
    (hb : Template.Matches (Template.current seed l) b.small)
    (hb' : Template.Matches (Template.current seed l) b'.small)
    (hs : (decodeHistory sources seed V l a c).Supported V outside)
    (ks : (decodeHistory sources seed V l a' d).Supported V outside)
    (hab : a.frequency=b.frequency) (hab' : a'.frequency=b'.frequency)
    (hbprime : b.PrimeSmall) (hbprime' : b'.PrimeSmall)
    (g : (q:ℕ)→ZMod q→ℂ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (hV : ∀q∈outside,∀j≤l,V j<q)
    (Xp Xm : ℤ)
    (hi : (rebuild (decodeHistory sources seed V l b c) Xp Xm).IntegralGuard)
    (ki : (rebuild (decodeHistory sources seed V l b' d) Xp Xm).IntegralGuard)
    (hz : residuePairSpectator g outside outside.prod (decodeHistory sources seed V l b c)
      (decodeHistory sources seed V l b' d) (Xp,Xm)≠0) :
    PivotOutsideCoprime outside (rebuild (decodeHistory sources seed V l b c) Xp Xm) ∧
      PivotOutsideCoprime outside (rebuild (decodeHistory sources seed V l b' d) Xp Xm) := by
  have hu := residuePairSpectator_nonzero_outsideUnits_decode_redraw sources seed V outside l
    a a' b b' c d ha ha' hb hb' hs ks hab hab' hbprime hbprime' g hprime hg hV Xp Xm hi ki hz
  exact ⟨hu.1.pivotOutsideCoprime,hu.2.pivotOutsideCoprime⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
