import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSourceUnits
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryBulkSupportConverseSpectatorDivisors
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorCRTResidue

namespace OAI

open Erdos970

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistoryBulkSupportConverse
open Construction HistoryOccurrenceVariables HistorySignedDecode HistorySignedResidues
open HistorySignedSpectatorCRT HistorySignedSpectator HistorySignedResidueFactorization

theorem static_frequencies_coprime_outside {l : ℕ} {V : ℕ→ℕ}
    (h : History l) (hs : StaticSkeleton V h) (outside : List ℕ)
    (hprime : ∀q∈outside,q.Prime) (hV : ∀q∈outside,∀j≤l,V j<q) :
    ∀s∈h.frequencies,Nat.Coprime s.natAbs outside.prod := by
  intro s hsm
  obtain ⟨hs0,j,hjl,hjb⟩ := hs.frequency_bounds s hsm
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  exact (History.prime_coprime_small_frequency (hprime q hq) hs0
    (hjb.trans_lt (hV q hq j hjl))).symm

theorem residueSpectator_intCast_static {l : ℕ} {V : ℕ→ℕ}
    (h : History l) (hs : StaticSkeleton V h) (g : (q:ℕ)→ZMod q→ℂ)
    (outside : List ℕ) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i : InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard) :
    residueSpectator g outside outside.prod h Xp Xm=
      spectatorProduct g outside (rebuild h Xp Xm) :=
  residueSpectator_intCast h g outside (divisorProduct h) outside.prod
    (fun _q hq => List.dvd_prod hq) (divisorData_of_static h hs)
    (divisorProduct_coprime_of_frequencies_internal h outside.prod
      (static_frequencies_coprime_outside h hs outside hprime hV) hu) Xp Xm hi

theorem residueSpectator_nonzero_outsideUnits_static {l : ℕ} {V : ℕ→ℕ}
    (h : History l) (hs : StaticSkeleton V h) (g : (q:ℕ)→ZMod q→ℂ)
    (outside : List ℕ) (hprime : ∀q∈outside,q.Prime) (hg : ∀q∈outside,g q 0=0)
    (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i : InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard)
    (hz : residueSpectator g outside outside.prod h Xp Xm≠0) :
    OutsideUnits outside (rebuild h Xp Xm) := by
  rw [residueSpectator_intCast_static h hs g outside hprime hV hu Xp Xm hi] at hz
  exact spectatorProduct_nonzero_rebuild_outsideUnits g outside hprime hg h Xp Xm hz

theorem residuePairSpectator_intCast_static {l : ℕ} {V : ℕ→ℕ}
    (h k : History l) (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (hprime : ∀q∈outside,q.Prime)
    (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i : InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (ku : ∀i : InternalKey k,Nat.Coprime (internalSlot k i).value outside.prod)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard)
    (ki : (rebuild k Xp Xm).IntegralGuard) :
    residuePairSpectator g outside outside.prod h k (Xp,Xm)=
      pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm) := by
  rw [residuePairSpectator,pairSpectator,
    residueSpectator_intCast_static h hs g outside hprime hV hu Xp Xm hi,
    residueSpectator_intCast_static k ks g outside hprime hV ku Xp Xm ki]

theorem residuePairSpectator_nonzero_outsideUnits_static {l : ℕ} {V : ℕ→ℕ}
    (h k : History l) (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i : InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (ku : ∀i : InternalKey k,Nat.Coprime (internalSlot k i).value outside.prod)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard)
    (ki : (rebuild k Xp Xm).IntegralGuard)
    (hz : residuePairSpectator g outside outside.prod h k (Xp,Xm)≠0) :
    OutsideUnits outside (rebuild h Xp Xm) ∧ OutsideUnits outside (rebuild k Xp Xm) := by
  rw [residuePairSpectator_intCast_static h k hs ks g outside hprime hV hu ku Xp Xm hi ki] at hz
  exact pairSpectator_nonzero_rebuild_outsideUnits g outside hprime hg h k Xp Xm Xp Xm hz

theorem residuePairSpectator_nonzero_pivotOutsideCoprime_static {l : ℕ} {V : ℕ→ℕ}
    (h k : History l) (hs : StaticSkeleton V h) (ks : StaticSkeleton V k)
    (g : (q:ℕ)→ZMod q→ℂ) (outside : List ℕ) (hprime : ∀q∈outside,q.Prime)
    (hg : ∀q∈outside,g q 0=0) (hV : ∀q∈outside,∀j≤l,V j<q)
    (hu : ∀i : InternalKey h,Nat.Coprime (internalSlot h i).value outside.prod)
    (ku : ∀i : InternalKey k,Nat.Coprime (internalSlot k i).value outside.prod)
    (Xp Xm : ℤ) (hi : (rebuild h Xp Xm).IntegralGuard)
    (ki : (rebuild k Xp Xm).IntegralGuard)
    (hz : residuePairSpectator g outside outside.prod h k (Xp,Xm)≠0) :
    PivotOutsideCoprime outside (rebuild h Xp Xm) ∧
      PivotOutsideCoprime outside (rebuild k Xp Xm) := by
  have ho := residuePairSpectator_nonzero_outsideUnits_static h k hs ks g outside hprime hg
    hV hu ku Xp Xm hi ki hz
  exact ⟨ho.1.pivotOutsideCoprime,ho.2.pivotOutsideCoprime⟩

end Ostmann.Arithmetic.HistoryBulkSupportConverse

end

end OAI
