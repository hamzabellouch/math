import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPairRepresentatives
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedNumeratorsPair

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistorySignedDecode HistorySignedNumerators HistoryOccurrenceVariables
open HistoryPairPattern HistoryPairRows MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

def PairNumeratorSquares (h k : History l) (Xp Xm : ℤ) : Prop :=
  ∀i : Occurrences h k, ¬((slot h k i).value:ℤ)^2 ∣ pairActual h k Xp Xm i

def OwnPrimeSquareLines (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (Xp Xm : ℤ) : Prop :=
  ∀i : Occurrences h k, ¬((slot h k i).value:ℤ)^2 ∣
    eval (pairSample h k) (leftFlag h k hs ks i)*Xp+
      eval (pairSample h k) (rightFlag h k hs ks i)*Xm

theorem pairNumeratorSquares_iff (h k : History l) (Xp Xm : ℤ) :
    PairNumeratorSquares h k Xp Xm ↔
      (∀i : InternalKey h, ¬((internalSlot h i).value:ℤ)^2 ∣ actual h Xp Xm i) ∧
      (∀i : InternalKey k, ¬((internalSlot k i).value:ℤ)^2 ∣ actual k Xp Xm i) := by
  constructor
  · intro ha
    exact ⟨fun i => ha (.inl i),fun i => ha (.inr i)⟩
  · rintro ⟨ha,hb⟩ (i|i)
    · exact ha i
    · exact hb i

theorem pairNumeratorSquares_iff_ownPrimeSquareLines (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hroot : RootGiantsAgree h k) (Xp Xm : ℤ)
    (hi : (rebuild h Xp Xm).IntegralGuard) (ki : (rebuild k Xp Xm).IntegralGuard)
    (hx : ∀i : Occurrences h k, AncestorUnits h k
      (fun j => (pairSample h k j:ZMod (slot h k i).value)) i)
    (hV : ∀i : Occurrences h k,∀j≤l,V j<(slot h k i).value) :
    PairNumeratorSquares h k Xp Xm ↔ OwnPrimeSquareLines h k hs ks Xp Xm := by
  apply forall_congr'
  intro i
  let : Fact (slot h k i).value.Prime := ⟨HistoryPairRepresentatives.slot_prime h k hs ks i⟩
  exact not_congr (pairActual_power_dvd_iff h k hs ks hroot Xp Xm hi ki
    i (slot h k i).value 2 (hx i) (hV i))

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
