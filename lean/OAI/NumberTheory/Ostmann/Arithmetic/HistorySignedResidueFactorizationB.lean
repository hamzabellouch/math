import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCRTIntegrationModuli
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedFrequencyCanonical
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationSquares

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryPairPattern HistoryPairRows HistoryPairRepresentatives
open HistoryCRTIntegration HistoryFrequencyResidues MvPolynomial
variable {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}

theorem ownPrimeSquare_dvd_representativeModulus (h k : History l) (i : Occurrences h k) :
    (slot h k i).value^2 ∣ representativeModulus h k := by
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem
    (fun r : Representative h k => (prime h k r)^2) (Finset.mem_univ (label h k i))
  refine ⟨c, ?_⟩
  simpa only [representativeModulus, prime_label] using hc

theorem ownPrime_dvd_representativeModulus (h k : History l) (i : Occurrences h k) :
    (slot h k i).value ∣ representativeModulus h k :=
  (dvd_pow_self _ (by decide : 2 ≠ 0)).trans (ownPrimeSquare_dvd_representativeModulus h k i)

def ownPrimeProjectionB (h k : History l) (i : Occurrences h k) :
    ZMod (representativeModulus h k) →+* ZMod (slot h k i).value :=
  ZMod.castHom (ownPrime_dvd_representativeModulus h k i) _

def ownPrimeSquareProjectionB (h k : History l) (i : Occurrences h k) :
    ZMod (representativeModulus h k) →+* ZMod ((slot h k i).value^2) :=
  ZMod.castHom (ownPrimeSquare_dvd_representativeModulus h k i) _

def ownPrimeLineB (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ZMod (slot h k i).value :=
  (eval (pairSample h k) (leftFlag h k hs ks i) : ℤ)*ownPrimeProjectionB h k i z.1+
    (eval (pairSample h k) (rightFlag h k hs ks i) : ℤ)*ownPrimeProjectionB h k i z.2

def ownPrimeSquareLineB (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k) (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ZMod ((slot h k i).value^2) :=
  (eval (pairSample h k) (leftFlag h k hs ks i) : ℤ)*ownPrimeSquareProjectionB h k i z.1+
    (eval (pairSample h k) (rightFlag h k hs ks i) : ℤ)*ownPrimeSquareProjectionB h k i z.2

def finiteOwnPrimeLinesB (h k : History l) (hs : h.Supported V outside) (ks : k.Supported V outside)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) : Prop :=
  ∀ i : Occurrences h k, ownPrimeLineB h k hs ks i z = 0 ∧
    ownPrimeSquareLineB h k hs ks i z ≠ 0

@[simp] theorem ownPrimeLineB_intCast (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i : Occurrences h k) (Xp Xm : ℤ) :
    ownPrimeLineB h k hs ks i (Xp, Xm) =
      ((eval (pairSample h k) (leftFlag h k hs ks i)*Xp+
        eval (pairSample h k) (rightFlag h k hs ks i)*Xm : ℤ) : ZMod (slot h k i).value) := by
  simp only [ownPrimeLineB, ownPrimeProjectionB, map_intCast, Int.cast_add, Int.cast_mul]

@[simp] theorem ownPrimeSquareLineB_intCast (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (i : Occurrences h k) (Xp Xm : ℤ) :
    ownPrimeSquareLineB h k hs ks i (Xp, Xm) =
      ((eval (pairSample h k) (leftFlag h k hs ks i)*Xp+
        eval (pairSample h k) (rightFlag h k hs ks i)*Xm : ℤ) : ZMod ((slot h k i).value^2)) := by
  simp only [ownPrimeSquareLineB, ownPrimeSquareProjectionB, map_intCast, Int.cast_add, Int.cast_mul]

theorem ownPrimeLines_and_squareLines_iff_finiteB (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (Xp Xm : ℤ) :
    (OwnPrimeLines h k hs ks Xp Xm ∧ OwnPrimeSquareLines h k hs ks Xp Xm) ↔
      finiteOwnPrimeLinesB h k hs ks (Xp, Xm) := by
  simp only [OwnPrimeLines, OwnPrimeSquareLines, finiteOwnPrimeLinesB,
    ownPrimeLineB_intCast, ownPrimeSquareLineB_intCast,
    ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]
  exact forall_and.symm

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
