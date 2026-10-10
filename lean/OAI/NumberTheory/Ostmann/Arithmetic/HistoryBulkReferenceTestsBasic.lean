import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResidueFactorizationBlocks

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryBulkReferenceTests
open Construction HistoryPairPattern HistoryPairRows HistoryCRTIntegration
open HistorySignedResidueFactorization MvPolynomial
variable {l : ℕ} {V : ℕ→ℕ} {outside : List ℕ}

def ownPrimeLineAt (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (v : PairKey h k→ℤ) (i : Occurrences h k)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ZMod (slot h k i).value :=
  (eval v (leftFlag h k hs ks i):ℤ)*ownPrimeProjectionB h k i z.1+
    (eval v (rightFlag h k hs ks i):ℤ)*ownPrimeProjectionB h k i z.2

def ownPrimeSquareLineAt (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (v : PairKey h k→ℤ) (i : Occurrences h k)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ZMod ((slot h k i).value^2) :=
  (eval v (leftFlag h k hs ks i):ℤ)*ownPrimeSquareProjectionB h k i z.1+
    (eval v (rightFlag h k hs ks i):ℤ)*ownPrimeSquareProjectionB h k i z.2

def finiteOwnPrimeLinesAt (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) : Prop :=
  ∀i:Occurrences h k,ownPrimeLineAt h k hs ks v i z=0 ∧
    ownPrimeSquareLineAt h k hs ks v i z≠0

def primeResidueIndicatorAt (h k : History l) (hs : h.Supported V outside)
    (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) : ℂ :=
  guardIndicator (finiteOwnPrimeLinesAt h k hs ks v z)

@[simp] theorem ownPrimeLineAt_intCast (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (i : Occurrences h k) (Xp Xm : ℤ) :
    ownPrimeLineAt h k hs ks v i (Xp,Xm)=
      ((eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm:ℤ):
        ZMod (slot h k i).value) := by
  simp only [ownPrimeLineAt,ownPrimeProjectionB,map_intCast,Int.cast_add,Int.cast_mul]

@[simp] theorem ownPrimeSquareLineAt_intCast (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (i : Occurrences h k) (Xp Xm : ℤ) :
    ownPrimeSquareLineAt h k hs ks v i (Xp,Xm)=
      ((eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm:ℤ):
        ZMod ((slot h k i).value^2)) := by
  simp only [ownPrimeSquareLineAt,ownPrimeSquareProjectionB,map_intCast,Int.cast_add,Int.cast_mul]

theorem finiteOwnPrimeLinesAt_intCast_iff (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (Xp Xm : ℤ) :
    finiteOwnPrimeLinesAt h k hs ks v (Xp,Xm) ↔
      ∀i:Occurrences h k,
        ((slot h k i).value:ℤ) ∣
          eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm ∧
        ¬((slot h k i).value:ℤ)^2 ∣
          eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm := by
  simp only [finiteOwnPrimeLinesAt,ownPrimeLineAt_intCast,ownPrimeSquareLineAt_intCast,
    ne_eq,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_pow]

@[simp] theorem primeResidueIndicatorAt_ne_zero_iff (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    primeResidueIndicatorAt h k hs ks v z≠0 ↔ finiteOwnPrimeLinesAt h k hs ks v z := by
  classical
  simp [primeResidueIndicatorAt,guardIndicator]

theorem tests_of_primeResidueIndicatorAt_ne_zero (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside) (v : PairKey h k→ℤ)
    (Xp Xm : ℤ) (hz : primeResidueIndicatorAt h k hs ks v (Xp,Xm)≠0) :
    ∀i:Occurrences h k,
      ((slot h k i).value:ℤ) ∣
        eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm ∧
      ¬((slot h k i).value:ℤ)^2 ∣
        eval v (leftFlag h k hs ks i)*Xp+eval v (rightFlag h k hs ks i)*Xm :=
  (finiteOwnPrimeLinesAt_intCast_iff h k hs ks v Xp Xm).mp
    ((primeResidueIndicatorAt_ne_zero_iff h k hs ks v (Xp,Xm)).mp hz)

@[simp] theorem ownPrimeLineAt_pairSample (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ownPrimeLineAt h k hs ks (pairSample h k) i z=ownPrimeLineB h k hs ks i z := rfl

@[simp] theorem ownPrimeSquareLineAt_pairSample (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (i : Occurrences h k)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    ownPrimeSquareLineAt h k hs ks (pairSample h k) i z=ownPrimeSquareLineB h k hs ks i z := rfl

@[simp] theorem primeResidueIndicatorAt_pairSample (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (z : ZMod (representativeModulus h k) × ZMod (representativeModulus h k)) :
    primeResidueIndicatorAt h k hs ks (pairSample h k) z=primeResidueIndicatorB h k hs ks z := rfl

end Ostmann.Arithmetic.HistoryBulkReferenceTests

end

end OAI
