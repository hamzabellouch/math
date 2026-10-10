import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SupportedContraction

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I1PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 3 2 3)) (shape 3 2 3) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) a
def CB3_2_3I1PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) a
lemma CB3_2_3I1PairRaw_sound (a : PairSlot) :
    (CB3_2_3I1PairRaw a).Encloses (CB3_2_3I1PairValue a) := by
  exact pairLawBall_sound_on (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) (fun u _ a => B3_2_3Little_sound (complement (shape 3 2 3) u) ((stageBPriority (shape 3 2 3)) 1) a) a
def CB3_2_3I1PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(7877790787272644406002286888011 / 12500000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(29096219242250260539924793114627 / 100000000000000000000000000000000), (6672748363 / 25000000000000000000000000000000)⟩ ⟨(-23084056834545939993716178416747 / 50000000000000000000000000000000), (21175823713 / 50000000000000000000000000000000)⟩ ⟨-1, 7877790787272644406002286888011, 6250000000000000000000000000000⟩,
   .log ⟨(8810343598851601529271500513163 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(30591214521027938277171173564403 / 100000000000000000000000000000000), (2985060543 / 20000000000000000000000000000000)⟩ ⟨(-86804828261792762424949258480639 / 50000000000000000000000000000000), (84703294947 / 100000000000000000000000000000000)⟩ ⟨-3, 8810343598851601529271500513163, 6250000000000000000000000000000⟩,
   .log ⟨(86814965320621931744785142163 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(4120725593087330713512283586423 / 100000000000000000000000000000000), (1470702737 / 100000000000000000000000000000000)⟩ ⟨(-474656135364313515533899147094047 / 100000000000000000000000000000000), (169406589809 / 100000000000000000000000000000000)⟩ ⟨-7, 86814965320621931744785142163, 78125000000000000000000000000⟩]
lemma CB3_2_3I1PairCertificates_valid :
    CB3_2_3I1PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 1 => 1
  | 2, 0 => 2
  | 3, 0 => 3
  | 0, 2 => 2
  | 0, 3 => 3
  | _, _ => 0
def CB3_2_3I1PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1PairCertificates (CB3_2_3I1PairCertificateIndex a)).input
lemma CB3_2_3I1PairP_check : ∀ a : PairSlot, contains (CB3_2_3I1PairRaw a) (CB3_2_3I1PairP a) = true := by
  decide +kernel
lemma CB3_2_3I1PairP_sound (a : PairSlot) :
    (CB3_2_3I1PairP a).Encloses (CB3_2_3I1PairValue a) :=
  contains_sound (CB3_2_3I1PairRaw_sound a) (CB3_2_3I1PairP_check a)
def CB3_2_3I1PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1PairCertificates (CB3_2_3I1PairCertificateIndex a)).output
lemma CB3_2_3I1PairTerms_sound (a : PairSlot) :
    (CB3_2_3I1PairTerms a).Encloses (Foundation.entropyTerm (CB3_2_3I1PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1PairCertificates_valid
    (CB3_2_3I1PairCertificateIndex a) (CB3_2_3I1PairP_sound a)
def CB3_2_3I1PairEntropy : Ball := ⟨(98520099470480798521291707416279 / 100000000000000000000000000000000), (14870751089 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I1PairEntropy_sound : CB3_2_3I1PairEntropy.Encloses (Foundation.finiteEntropy CB3_2_3I1PairValue) := by
  exact contains_sound (entropyPair_enclosed CB3_2_3I1PairValue CB3_2_3I1PairTerms CB3_2_3I1PairTerms_sound) (by decide +kernel)
def CB3_2_3I1PairMass : Ball := ⟨1, (3 / 2500000000000000000000000000000)⟩
lemma CB3_2_3I1PairMass_sound : CB3_2_3I1PairMass.Encloses (∑ a, CB3_2_3I1PairValue a) := by
  exact contains_sound (pairSumBall_sound CB3_2_3I1PairP CB3_2_3I1PairValue CB3_2_3I1PairP_sound) (by decide +kernel)
def CB3_2_3I1PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_2_3I1PairMassTermLog : Ball := ⟨0, (10587911901 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I1PairMassTermLog_sound : CB3_2_3I1PairMassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I1PairMass_sound) (w := CB3_2_3I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1PairMassTerm : Ball := ⟨0, (21175823803 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1PairMassTerm_sound : CB3_2_3I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1PairMass_sound) CB3_2_3I1PairMassTermLog_sound) (by decide +kernel)
def CB3_2_3I1PairH : Ball := ⟨(98520099470480798521291707416279 / 100000000000000000000000000000000), (80658828159 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1PairH_sound : CB3_2_3I1PairH.Encloses (homogeneousEntropy CB3_2_3I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1PairValue CB3_2_3I1PairMassTerm_sound CB3_2_3I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I1R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 0 a
def CB3_2_3I1R0Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 0 a
lemma CB3_2_3I1R0Raw_sound (a : Fin 6) :
    (CB3_2_3I1R0Raw a).Encloses (CB3_2_3I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 0 a
def CB3_2_3I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4622209212727355593997713111989 / 25000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩ ⟨(31209212985956947397911481005053 / 100000000000000000000000000000000), (3915163519 / 25000000000000000000000000000000)⟩ ⟨(-84400152474767063710553601532469 / 50000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩ ⟨-3, 4622209212727355593997713111989, 3125000000000000000000000000000⟩]
lemma CB3_2_3I1R0Certificates_valid :
    CB3_2_3I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_2_3I1R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R0Certificates (CB3_2_3I1R0CertificateIndex a)).input
lemma CB3_2_3I1R0P_check : ∀ a : Fin 6, contains (CB3_2_3I1R0Raw a) (CB3_2_3I1R0P a) = true := by
  decide +kernel
lemma CB3_2_3I1R0P_sound (a : Fin 6) :
    (CB3_2_3I1R0P a).Encloses (CB3_2_3I1R0Value a) :=
  contains_sound (CB3_2_3I1R0Raw_sound a) (CB3_2_3I1R0P_check a)
def CB3_2_3I1R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R0Certificates (CB3_2_3I1R0CertificateIndex a)).output
lemma CB3_2_3I1R0Terms_sound (a : Fin 6) :
    (CB3_2_3I1R0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R0Certificates_valid
    (CB3_2_3I1R0CertificateIndex a) (CB3_2_3I1R0P_sound a)
def CB3_2_3I1R0Entropy : Ball := ⟨(31209212985956947397911481005053 / 100000000000000000000000000000000), (3915163519 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I1R0Entropy_sound : CB3_2_3I1R0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R0Value CB3_2_3I1R0Terms CB3_2_3I1R0Terms_sound) (by decide +kernel)
def CB3_2_3I1R0Mass : Ball := ⟨(4622209212727355593997713111989 / 25000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1R0Mass_sound : CB3_2_3I1R0Mass.Encloses (∑ a, CB3_2_3I1R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R0P CB3_2_3I1R0Value CB3_2_3I1R0P_sound) (by decide +kernel)
def CB3_2_3I1R0MassTermLogWitness : LogWitness := ⟨-3, 4622209212727355593997713111989, 3125000000000000000000000000000⟩
def CB3_2_3I1R0MassTermLog : Ball := ⟨(-84400152474767063710553601532469 / 50000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I1R0MassTermLog_sound : CB3_2_3I1R0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I1R0Mass_sound) (w := CB3_2_3I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1R0MassTerm : Ball := ⟨(31209212985956947397911481005053 / 100000000000000000000000000000000), (3915163519 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I1R0MassTerm_sound : CB3_2_3I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1R0Mass_sound) CB3_2_3I1R0MassTermLog_sound) (by decide +kernel)
def CB3_2_3I1R0H : Ball := ⟨0, (3915163519 / 12500000000000000000000000000000)⟩
lemma CB3_2_3I1R0H_sound : CB3_2_3I1R0H.Encloses (homogeneousEntropy CB3_2_3I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R0Value CB3_2_3I1R0MassTerm_sound CB3_2_3I1R0Entropy_sound) (by decide +kernel)
def CB3_2_3I1R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 1 a
def CB3_2_3I1R1Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 1 a
lemma CB3_2_3I1R1Raw_sound (a : Fin 6) :
    (CB3_2_3I1R1Raw a).Encloses (CB3_2_3I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 1 a
def CB3_2_3I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(62861587115248395273289176036939 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(14591271509207952834805282866537 / 50000000000000000000000000000000), (13311458879 / 50000000000000000000000000000000)⟩ ⟨(-46423490652429086244419251190089 / 100000000000000000000000000000000), (661744491 / 1562500000000000000000000000000)⟩ ⟨-1, 62861587115248395273289176036939, 50000000000000000000000000000000⟩]
lemma CB3_2_3I1R1Certificates_valid :
    CB3_2_3I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_2_3I1R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R1Certificates (CB3_2_3I1R1CertificateIndex a)).input
lemma CB3_2_3I1R1P_check : ∀ a : Fin 6, contains (CB3_2_3I1R1Raw a) (CB3_2_3I1R1P a) = true := by
  decide +kernel
lemma CB3_2_3I1R1P_sound (a : Fin 6) :
    (CB3_2_3I1R1P a).Encloses (CB3_2_3I1R1Value a) :=
  contains_sound (CB3_2_3I1R1Raw_sound a) (CB3_2_3I1R1P_check a)
def CB3_2_3I1R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R1Certificates (CB3_2_3I1R1CertificateIndex a)).output
lemma CB3_2_3I1R1Terms_sound (a : Fin 6) :
    (CB3_2_3I1R1Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R1Certificates_valid
    (CB3_2_3I1R1CertificateIndex a) (CB3_2_3I1R1P_sound a)
def CB3_2_3I1R1Entropy : Ball := ⟨(14591271509207952834805282866537 / 50000000000000000000000000000000), (13311458879 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I1R1Entropy_sound : CB3_2_3I1R1Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R1Value CB3_2_3I1R1Terms CB3_2_3I1R1Terms_sound) (by decide +kernel)
def CB3_2_3I1R1Mass : Ball := ⟨(62861587115248395273289176036939 / 100000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1R1Mass_sound : CB3_2_3I1R1Mass.Encloses (∑ a, CB3_2_3I1R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R1P CB3_2_3I1R1Value CB3_2_3I1R1P_sound) (by decide +kernel)
def CB3_2_3I1R1MassTermLogWitness : LogWitness := ⟨-1, 62861587115248395273289176036939, 50000000000000000000000000000000⟩
def CB3_2_3I1R1MassTermLog : Ball := ⟨(-46423490652429086244419251190089 / 100000000000000000000000000000000), (661744491 / 1562500000000000000000000000000)⟩
lemma CB3_2_3I1R1MassTermLog_sound : CB3_2_3I1R1MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I1R1Mass_sound) (w := CB3_2_3I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1R1MassTerm : Ball := ⟨(14591271509207952834805282866537 / 50000000000000000000000000000000), (13311458879 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I1R1MassTerm_sound : CB3_2_3I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1R1Mass_sound) CB3_2_3I1R1MassTermLog_sound) (by decide +kernel)
def CB3_2_3I1R1H : Ball := ⟨0, (13311458879 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I1R1H_sound : CB3_2_3I1R1H.Encloses (homogeneousEntropy CB3_2_3I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R1Value CB3_2_3I1R1MassTerm_sound CB3_2_3I1R1Entropy_sound) (by decide +kernel)
def CB3_2_3I1R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 2 a
def CB3_2_3I1R2Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 2 a
lemma CB3_2_3I1R2Raw_sound (a : Fin 6) :
    (CB3_2_3I1R2Raw a).Encloses (CB3_2_3I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 2 a
def CB3_2_3I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8292001037702510443718443883251 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩ ⟨(7449250501188492770577657387111 / 25000000000000000000000000000000), (14047196249 / 100000000000000000000000000000000)⟩ ⟨(-89836584285480008963634165386603 / 50000000000000000000000000000000), (8470329493 / 10000000000000000000000000000000)⟩ ⟨-3, 8292001037702510443718443883251, 6250000000000000000000000000000⟩,
   .log ⟨(749918571577850432764580593809 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(3669322200592286143146381383681 / 100000000000000000000000000000000), (1429212923 / 100000000000000000000000000000000)⟩ ⟨(-489296083556368762978102141460269 / 100000000000000000000000000000000), (95291206707 / 50000000000000000000000000000000)⟩ ⟨-8, 749918571577850432764580593809, 390625000000000000000000000000⟩]
lemma CB3_2_3I1R2Certificates_valid :
    CB3_2_3I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_2_3I1R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R2Certificates (CB3_2_3I1R2CertificateIndex a)).input
lemma CB3_2_3I1R2P_check : ∀ a : Fin 6, contains (CB3_2_3I1R2Raw a) (CB3_2_3I1R2P a) = true := by
  decide +kernel
lemma CB3_2_3I1R2P_sound (a : Fin 6) :
    (CB3_2_3I1R2P a).Encloses (CB3_2_3I1R2Value a) :=
  contains_sound (CB3_2_3I1R2Raw_sound a) (CB3_2_3I1R2P_check a)
def CB3_2_3I1R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R2Certificates (CB3_2_3I1R2CertificateIndex a)).output
lemma CB3_2_3I1R2Terms_sound (a : Fin 6) :
    (CB3_2_3I1R2Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R2Certificates_valid
    (CB3_2_3I1R2CertificateIndex a) (CB3_2_3I1R2P_sound a)
def CB3_2_3I1R2Entropy : Ball := ⟨(267730593642770057803656087457 / 800000000000000000000000000000), (3869102293 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I1R2Entropy_sound : CB3_2_3I1R2Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R2Value CB3_2_3I1R2Terms CB3_2_3I1R2Terms_sound) (by decide +kernel)
def CB3_2_3I1R2Mass : Ball := ⟨(17333920646982871320201468360311 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
lemma CB3_2_3I1R2Mass_sound : CB3_2_3I1R2Mass.Encloses (∑ a, CB3_2_3I1R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R2P CB3_2_3I1R2Value CB3_2_3I1R2P_sound) (by decide +kernel)
def CB3_2_3I1R2MassTermLogWitness : LogWitness := ⟨-3, 17333920646982871320201468360311, 12500000000000000000000000000000⟩
def CB3_2_3I1R2MassTermLog : Ball := ⟨(-175250487316902480110780974093599 / 100000000000000000000000000000000), (84703294933 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1R2MassTermLog_sound : CB3_2_3I1R2MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I1R2Mass_sound) (w := CB3_2_3I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1R2MassTerm : Ball := ⟨(15188890202481328612979926606431 / 50000000000000000000000000000000), (14682401991 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1R2MassTerm_sound : CB3_2_3I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1R2Mass_sound) CB3_2_3I1R2MassTermLog_sound) (by decide +kernel)
def CB3_2_3I1R2H : Ball := ⟨(3088543800383599999497157719263 / 100000000000000000000000000000000), (30158811163 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1R2H_sound : CB3_2_3I1R2H.Encloses (homogeneousEntropy CB3_2_3I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R2Value CB3_2_3I1R2MassTerm_sound CB3_2_3I1R2Entropy_sound) (by decide +kernel)
def CB3_2_3I1R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 3 a
def CB3_2_3I1R3Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 3 a
lemma CB3_2_3I1R3Raw_sound (a : Fin 6) :
    (CB3_2_3I1R3Raw a).Encloses (CB3_2_3I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 3 a
def CB3_2_3I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R3Certificates_valid :
    CB3_2_3I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R3Certificates (CB3_2_3I1R3CertificateIndex a)).input
lemma CB3_2_3I1R3P_check : ∀ a : Fin 6, contains (CB3_2_3I1R3Raw a) (CB3_2_3I1R3P a) = true := by
  decide +kernel
lemma CB3_2_3I1R3P_sound (a : Fin 6) :
    (CB3_2_3I1R3P a).Encloses (CB3_2_3I1R3Value a) :=
  contains_sound (CB3_2_3I1R3Raw_sound a) (CB3_2_3I1R3P_check a)
def CB3_2_3I1R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R3Certificates (CB3_2_3I1R3CertificateIndex a)).output
lemma CB3_2_3I1R3Terms_sound (a : Fin 6) :
    (CB3_2_3I1R3Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R3Certificates_valid
    (CB3_2_3I1R3CertificateIndex a) (CB3_2_3I1R3P_sound a)
def CB3_2_3I1R3Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R3Entropy_sound : CB3_2_3I1R3Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R3Value CB3_2_3I1R3Terms CB3_2_3I1R3Terms_sound) (by decide +kernel)
def CB3_2_3I1R3Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R3Mass_sound : CB3_2_3I1R3Mass.Encloses (∑ a, CB3_2_3I1R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R3P CB3_2_3I1R3Value CB3_2_3I1R3P_sound) (by decide +kernel)
def CB3_2_3I1R3MassTerm : Ball := .exact 0
lemma CB3_2_3I1R3MassTerm_sound : CB3_2_3I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R3Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R3Mass_sound)
def CB3_2_3I1R3H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R3H_sound : CB3_2_3I1R3H.Encloses (homogeneousEntropy CB3_2_3I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R3Value CB3_2_3I1R3MassTerm_sound CB3_2_3I1R3Entropy_sound) (by decide +kernel)
def CB3_2_3I1R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 4 a
def CB3_2_3I1R4Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 4 a
lemma CB3_2_3I1R4Raw_sound (a : Fin 6) :
    (CB3_2_3I1R4Raw a).Encloses (CB3_2_3I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 4 a
def CB3_2_3I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R4Certificates_valid :
    CB3_2_3I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R4Certificates (CB3_2_3I1R4CertificateIndex a)).input
lemma CB3_2_3I1R4P_check : ∀ a : Fin 6, contains (CB3_2_3I1R4Raw a) (CB3_2_3I1R4P a) = true := by
  decide +kernel
lemma CB3_2_3I1R4P_sound (a : Fin 6) :
    (CB3_2_3I1R4P a).Encloses (CB3_2_3I1R4Value a) :=
  contains_sound (CB3_2_3I1R4Raw_sound a) (CB3_2_3I1R4P_check a)
def CB3_2_3I1R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R4Certificates (CB3_2_3I1R4CertificateIndex a)).output
lemma CB3_2_3I1R4Terms_sound (a : Fin 6) :
    (CB3_2_3I1R4Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R4Certificates_valid
    (CB3_2_3I1R4CertificateIndex a) (CB3_2_3I1R4P_sound a)
def CB3_2_3I1R4Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R4Entropy_sound : CB3_2_3I1R4Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R4Value CB3_2_3I1R4Terms CB3_2_3I1R4Terms_sound) (by decide +kernel)
def CB3_2_3I1R4Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R4Mass_sound : CB3_2_3I1R4Mass.Encloses (∑ a, CB3_2_3I1R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R4P CB3_2_3I1R4Value CB3_2_3I1R4P_sound) (by decide +kernel)
def CB3_2_3I1R4MassTerm : Ball := .exact 0
lemma CB3_2_3I1R4MassTerm_sound : CB3_2_3I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R4Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R4Mass_sound)
def CB3_2_3I1R4H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R4H_sound : CB3_2_3I1R4H.Encloses (homogeneousEntropy CB3_2_3I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R4Value CB3_2_3I1R4MassTerm_sound CB3_2_3I1R4Entropy_sound) (by decide +kernel)
def CB3_2_3I1R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 5 a
def CB3_2_3I1R5Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 5 a
lemma CB3_2_3I1R5Raw_sound (a : Fin 6) :
    (CB3_2_3I1R5Raw a).Encloses (CB3_2_3I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 5 a
def CB3_2_3I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R5Certificates_valid :
    CB3_2_3I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R5Certificates (CB3_2_3I1R5CertificateIndex a)).input
lemma CB3_2_3I1R5P_check : ∀ a : Fin 6, contains (CB3_2_3I1R5Raw a) (CB3_2_3I1R5P a) = true := by
  decide +kernel
lemma CB3_2_3I1R5P_sound (a : Fin 6) :
    (CB3_2_3I1R5P a).Encloses (CB3_2_3I1R5Value a) :=
  contains_sound (CB3_2_3I1R5Raw_sound a) (CB3_2_3I1R5P_check a)
def CB3_2_3I1R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R5Certificates (CB3_2_3I1R5CertificateIndex a)).output
lemma CB3_2_3I1R5Terms_sound (a : Fin 6) :
    (CB3_2_3I1R5Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R5Certificates_valid
    (CB3_2_3I1R5CertificateIndex a) (CB3_2_3I1R5P_sound a)
def CB3_2_3I1R5Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R5Entropy_sound : CB3_2_3I1R5Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R5Value CB3_2_3I1R5Terms CB3_2_3I1R5Terms_sound) (by decide +kernel)
def CB3_2_3I1R5Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R5Mass_sound : CB3_2_3I1R5Mass.Encloses (∑ a, CB3_2_3I1R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R5P CB3_2_3I1R5Value CB3_2_3I1R5P_sound) (by decide +kernel)
def CB3_2_3I1R5MassTerm : Ball := .exact 0
lemma CB3_2_3I1R5MassTerm_sound : CB3_2_3I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R5Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R5Mass_sound)
def CB3_2_3I1R5H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R5H_sound : CB3_2_3I1R5H.Encloses (homogeneousEntropy CB3_2_3I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R5Value CB3_2_3I1R5MassTerm_sound CB3_2_3I1R5Entropy_sound) (by decide +kernel)
def CB3_2_3I1R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 6 a
def CB3_2_3I1R6Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 6 a
lemma CB3_2_3I1R6Raw_sound (a : Fin 6) :
    (CB3_2_3I1R6Raw a).Encloses (CB3_2_3I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 6 a
def CB3_2_3I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R6Certificates_valid :
    CB3_2_3I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R6Certificates (CB3_2_3I1R6CertificateIndex a)).input
lemma CB3_2_3I1R6P_check : ∀ a : Fin 6, contains (CB3_2_3I1R6Raw a) (CB3_2_3I1R6P a) = true := by
  decide +kernel
lemma CB3_2_3I1R6P_sound (a : Fin 6) :
    (CB3_2_3I1R6P a).Encloses (CB3_2_3I1R6Value a) :=
  contains_sound (CB3_2_3I1R6Raw_sound a) (CB3_2_3I1R6P_check a)
def CB3_2_3I1R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R6Certificates (CB3_2_3I1R6CertificateIndex a)).output
lemma CB3_2_3I1R6Terms_sound (a : Fin 6) :
    (CB3_2_3I1R6Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R6Certificates_valid
    (CB3_2_3I1R6CertificateIndex a) (CB3_2_3I1R6P_sound a)
def CB3_2_3I1R6Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R6Entropy_sound : CB3_2_3I1R6Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R6Value CB3_2_3I1R6Terms CB3_2_3I1R6Terms_sound) (by decide +kernel)
def CB3_2_3I1R6Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R6Mass_sound : CB3_2_3I1R6Mass.Encloses (∑ a, CB3_2_3I1R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R6P CB3_2_3I1R6Value CB3_2_3I1R6P_sound) (by decide +kernel)
def CB3_2_3I1R6MassTerm : Ball := .exact 0
lemma CB3_2_3I1R6MassTerm_sound : CB3_2_3I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R6Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R6Mass_sound)
def CB3_2_3I1R6H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R6H_sound : CB3_2_3I1R6H.Encloses (homogeneousEntropy CB3_2_3I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R6Value CB3_2_3I1R6MassTerm_sound CB3_2_3I1R6Entropy_sound) (by decide +kernel)
def CB3_2_3I1R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 7 a
def CB3_2_3I1R7Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 7 a
lemma CB3_2_3I1R7Raw_sound (a : Fin 6) :
    (CB3_2_3I1R7Raw a).Encloses (CB3_2_3I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 7 a
def CB3_2_3I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R7Certificates_valid :
    CB3_2_3I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R7Certificates (CB3_2_3I1R7CertificateIndex a)).input
lemma CB3_2_3I1R7P_check : ∀ a : Fin 6, contains (CB3_2_3I1R7Raw a) (CB3_2_3I1R7P a) = true := by
  decide +kernel
lemma CB3_2_3I1R7P_sound (a : Fin 6) :
    (CB3_2_3I1R7P a).Encloses (CB3_2_3I1R7Value a) :=
  contains_sound (CB3_2_3I1R7Raw_sound a) (CB3_2_3I1R7P_check a)
def CB3_2_3I1R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R7Certificates (CB3_2_3I1R7CertificateIndex a)).output
lemma CB3_2_3I1R7Terms_sound (a : Fin 6) :
    (CB3_2_3I1R7Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R7Certificates_valid
    (CB3_2_3I1R7CertificateIndex a) (CB3_2_3I1R7P_sound a)
def CB3_2_3I1R7Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R7Entropy_sound : CB3_2_3I1R7Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R7Value CB3_2_3I1R7Terms CB3_2_3I1R7Terms_sound) (by decide +kernel)
def CB3_2_3I1R7Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R7Mass_sound : CB3_2_3I1R7Mass.Encloses (∑ a, CB3_2_3I1R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R7P CB3_2_3I1R7Value CB3_2_3I1R7P_sound) (by decide +kernel)
def CB3_2_3I1R7MassTerm : Ball := .exact 0
lemma CB3_2_3I1R7MassTerm_sound : CB3_2_3I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R7Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R7Mass_sound)
def CB3_2_3I1R7H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R7H_sound : CB3_2_3I1R7H.Encloses (homogeneousEntropy CB3_2_3I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R7Value CB3_2_3I1R7MassTerm_sound CB3_2_3I1R7Entropy_sound) (by decide +kernel)
def CB3_2_3I1R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 8 a
def CB3_2_3I1R8Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 8 a
lemma CB3_2_3I1R8Raw_sound (a : Fin 6) :
    (CB3_2_3I1R8Raw a).Encloses (CB3_2_3I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 8 a
def CB3_2_3I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R8Certificates_valid :
    CB3_2_3I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R8Certificates (CB3_2_3I1R8CertificateIndex a)).input
lemma CB3_2_3I1R8P_check : ∀ a : Fin 6, contains (CB3_2_3I1R8Raw a) (CB3_2_3I1R8P a) = true := by
  decide +kernel
lemma CB3_2_3I1R8P_sound (a : Fin 6) :
    (CB3_2_3I1R8P a).Encloses (CB3_2_3I1R8Value a) :=
  contains_sound (CB3_2_3I1R8Raw_sound a) (CB3_2_3I1R8P_check a)
def CB3_2_3I1R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R8Certificates (CB3_2_3I1R8CertificateIndex a)).output
lemma CB3_2_3I1R8Terms_sound (a : Fin 6) :
    (CB3_2_3I1R8Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R8Certificates_valid
    (CB3_2_3I1R8CertificateIndex a) (CB3_2_3I1R8P_sound a)
def CB3_2_3I1R8Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R8Entropy_sound : CB3_2_3I1R8Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R8Value CB3_2_3I1R8Terms CB3_2_3I1R8Terms_sound) (by decide +kernel)
def CB3_2_3I1R8Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R8Mass_sound : CB3_2_3I1R8Mass.Encloses (∑ a, CB3_2_3I1R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R8P CB3_2_3I1R8Value CB3_2_3I1R8P_sound) (by decide +kernel)
def CB3_2_3I1R8MassTerm : Ball := .exact 0
lemma CB3_2_3I1R8MassTerm_sound : CB3_2_3I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R8Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R8Mass_sound)
def CB3_2_3I1R8H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R8H_sound : CB3_2_3I1R8H.Encloses (homogeneousEntropy CB3_2_3I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R8Value CB3_2_3I1R8MassTerm_sound CB3_2_3I1R8Entropy_sound) (by decide +kernel)
def CB3_2_3I1R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 9 a
def CB3_2_3I1R9Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 9 a
lemma CB3_2_3I1R9Raw_sound (a : Fin 6) :
    (CB3_2_3I1R9Raw a).Encloses (CB3_2_3I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 9 a
def CB3_2_3I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R9Certificates_valid :
    CB3_2_3I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R9Certificates (CB3_2_3I1R9CertificateIndex a)).input
lemma CB3_2_3I1R9P_check : ∀ a : Fin 6, contains (CB3_2_3I1R9Raw a) (CB3_2_3I1R9P a) = true := by
  decide +kernel
lemma CB3_2_3I1R9P_sound (a : Fin 6) :
    (CB3_2_3I1R9P a).Encloses (CB3_2_3I1R9Value a) :=
  contains_sound (CB3_2_3I1R9Raw_sound a) (CB3_2_3I1R9P_check a)
def CB3_2_3I1R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R9Certificates (CB3_2_3I1R9CertificateIndex a)).output
lemma CB3_2_3I1R9Terms_sound (a : Fin 6) :
    (CB3_2_3I1R9Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R9Certificates_valid
    (CB3_2_3I1R9CertificateIndex a) (CB3_2_3I1R9P_sound a)
def CB3_2_3I1R9Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R9Entropy_sound : CB3_2_3I1R9Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R9Value CB3_2_3I1R9Terms CB3_2_3I1R9Terms_sound) (by decide +kernel)
def CB3_2_3I1R9Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R9Mass_sound : CB3_2_3I1R9Mass.Encloses (∑ a, CB3_2_3I1R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R9P CB3_2_3I1R9Value CB3_2_3I1R9P_sound) (by decide +kernel)
def CB3_2_3I1R9MassTerm : Ball := .exact 0
lemma CB3_2_3I1R9MassTerm_sound : CB3_2_3I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R9Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R9Mass_sound)
def CB3_2_3I1R9H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R9H_sound : CB3_2_3I1R9H.Encloses (homogeneousEntropy CB3_2_3I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R9Value CB3_2_3I1R9MassTerm_sound CB3_2_3I1R9Entropy_sound) (by decide +kernel)
def CB3_2_3I1R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 10 a
def CB3_2_3I1R10Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 10 a
lemma CB3_2_3I1R10Raw_sound (a : Fin 6) :
    (CB3_2_3I1R10Raw a).Encloses (CB3_2_3I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 10 a
def CB3_2_3I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R10Certificates_valid :
    CB3_2_3I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R10Certificates (CB3_2_3I1R10CertificateIndex a)).input
lemma CB3_2_3I1R10P_check : ∀ a : Fin 6, contains (CB3_2_3I1R10Raw a) (CB3_2_3I1R10P a) = true := by
  decide +kernel
lemma CB3_2_3I1R10P_sound (a : Fin 6) :
    (CB3_2_3I1R10P a).Encloses (CB3_2_3I1R10Value a) :=
  contains_sound (CB3_2_3I1R10Raw_sound a) (CB3_2_3I1R10P_check a)
def CB3_2_3I1R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R10Certificates (CB3_2_3I1R10CertificateIndex a)).output
lemma CB3_2_3I1R10Terms_sound (a : Fin 6) :
    (CB3_2_3I1R10Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R10Certificates_valid
    (CB3_2_3I1R10CertificateIndex a) (CB3_2_3I1R10P_sound a)
def CB3_2_3I1R10Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R10Entropy_sound : CB3_2_3I1R10Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R10Value CB3_2_3I1R10Terms CB3_2_3I1R10Terms_sound) (by decide +kernel)
def CB3_2_3I1R10Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R10Mass_sound : CB3_2_3I1R10Mass.Encloses (∑ a, CB3_2_3I1R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R10P CB3_2_3I1R10Value CB3_2_3I1R10P_sound) (by decide +kernel)
def CB3_2_3I1R10MassTerm : Ball := .exact 0
lemma CB3_2_3I1R10MassTerm_sound : CB3_2_3I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R10Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R10Mass_sound)
def CB3_2_3I1R10H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R10H_sound : CB3_2_3I1R10H.Encloses (homogeneousEntropy CB3_2_3I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R10Value CB3_2_3I1R10MassTerm_sound CB3_2_3I1R10Entropy_sound) (by decide +kernel)
def CB3_2_3I1R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 11 a
def CB3_2_3I1R11Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 11 a
lemma CB3_2_3I1R11Raw_sound (a : Fin 6) :
    (CB3_2_3I1R11Raw a).Encloses (CB3_2_3I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 11 a
def CB3_2_3I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R11Certificates_valid :
    CB3_2_3I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R11Certificates (CB3_2_3I1R11CertificateIndex a)).input
lemma CB3_2_3I1R11P_check : ∀ a : Fin 6, contains (CB3_2_3I1R11Raw a) (CB3_2_3I1R11P a) = true := by
  decide +kernel
lemma CB3_2_3I1R11P_sound (a : Fin 6) :
    (CB3_2_3I1R11P a).Encloses (CB3_2_3I1R11Value a) :=
  contains_sound (CB3_2_3I1R11Raw_sound a) (CB3_2_3I1R11P_check a)
def CB3_2_3I1R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R11Certificates (CB3_2_3I1R11CertificateIndex a)).output
lemma CB3_2_3I1R11Terms_sound (a : Fin 6) :
    (CB3_2_3I1R11Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R11Certificates_valid
    (CB3_2_3I1R11CertificateIndex a) (CB3_2_3I1R11P_sound a)
def CB3_2_3I1R11Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R11Entropy_sound : CB3_2_3I1R11Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R11Value CB3_2_3I1R11Terms CB3_2_3I1R11Terms_sound) (by decide +kernel)
def CB3_2_3I1R11Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R11Mass_sound : CB3_2_3I1R11Mass.Encloses (∑ a, CB3_2_3I1R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R11P CB3_2_3I1R11Value CB3_2_3I1R11P_sound) (by decide +kernel)
def CB3_2_3I1R11MassTerm : Ball := .exact 0
lemma CB3_2_3I1R11MassTerm_sound : CB3_2_3I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R11Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R11Mass_sound)
def CB3_2_3I1R11H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R11H_sound : CB3_2_3I1R11H.Encloses (homogeneousEntropy CB3_2_3I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R11Value CB3_2_3I1R11MassTerm_sound CB3_2_3I1R11Entropy_sound) (by decide +kernel)
def CB3_2_3I1R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 12 a
def CB3_2_3I1R12Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 12 a
lemma CB3_2_3I1R12Raw_sound (a : Fin 6) :
    (CB3_2_3I1R12Raw a).Encloses (CB3_2_3I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 12 a
def CB3_2_3I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R12Certificates_valid :
    CB3_2_3I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R12Certificates (CB3_2_3I1R12CertificateIndex a)).input
lemma CB3_2_3I1R12P_check : ∀ a : Fin 6, contains (CB3_2_3I1R12Raw a) (CB3_2_3I1R12P a) = true := by
  decide +kernel
lemma CB3_2_3I1R12P_sound (a : Fin 6) :
    (CB3_2_3I1R12P a).Encloses (CB3_2_3I1R12Value a) :=
  contains_sound (CB3_2_3I1R12Raw_sound a) (CB3_2_3I1R12P_check a)
def CB3_2_3I1R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R12Certificates (CB3_2_3I1R12CertificateIndex a)).output
lemma CB3_2_3I1R12Terms_sound (a : Fin 6) :
    (CB3_2_3I1R12Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R12Certificates_valid
    (CB3_2_3I1R12CertificateIndex a) (CB3_2_3I1R12P_sound a)
def CB3_2_3I1R12Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R12Entropy_sound : CB3_2_3I1R12Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R12Value CB3_2_3I1R12Terms CB3_2_3I1R12Terms_sound) (by decide +kernel)
def CB3_2_3I1R12Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R12Mass_sound : CB3_2_3I1R12Mass.Encloses (∑ a, CB3_2_3I1R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R12P CB3_2_3I1R12Value CB3_2_3I1R12P_sound) (by decide +kernel)
def CB3_2_3I1R12MassTerm : Ball := .exact 0
lemma CB3_2_3I1R12MassTerm_sound : CB3_2_3I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R12Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R12Mass_sound)
def CB3_2_3I1R12H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R12H_sound : CB3_2_3I1R12H.Encloses (homogeneousEntropy CB3_2_3I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R12Value CB3_2_3I1R12MassTerm_sound CB3_2_3I1R12Entropy_sound) (by decide +kernel)
def CB3_2_3I1R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 13 a
def CB3_2_3I1R13Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 13 a
lemma CB3_2_3I1R13Raw_sound (a : Fin 6) :
    (CB3_2_3I1R13Raw a).Encloses (CB3_2_3I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 13 a
def CB3_2_3I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R13Certificates_valid :
    CB3_2_3I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R13Certificates (CB3_2_3I1R13CertificateIndex a)).input
lemma CB3_2_3I1R13P_check : ∀ a : Fin 6, contains (CB3_2_3I1R13Raw a) (CB3_2_3I1R13P a) = true := by
  decide +kernel
lemma CB3_2_3I1R13P_sound (a : Fin 6) :
    (CB3_2_3I1R13P a).Encloses (CB3_2_3I1R13Value a) :=
  contains_sound (CB3_2_3I1R13Raw_sound a) (CB3_2_3I1R13P_check a)
def CB3_2_3I1R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R13Certificates (CB3_2_3I1R13CertificateIndex a)).output
lemma CB3_2_3I1R13Terms_sound (a : Fin 6) :
    (CB3_2_3I1R13Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R13Certificates_valid
    (CB3_2_3I1R13CertificateIndex a) (CB3_2_3I1R13P_sound a)
def CB3_2_3I1R13Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R13Entropy_sound : CB3_2_3I1R13Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R13Value CB3_2_3I1R13Terms CB3_2_3I1R13Terms_sound) (by decide +kernel)
def CB3_2_3I1R13Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R13Mass_sound : CB3_2_3I1R13Mass.Encloses (∑ a, CB3_2_3I1R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R13P CB3_2_3I1R13Value CB3_2_3I1R13P_sound) (by decide +kernel)
def CB3_2_3I1R13MassTerm : Ball := .exact 0
lemma CB3_2_3I1R13MassTerm_sound : CB3_2_3I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R13Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R13Mass_sound)
def CB3_2_3I1R13H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R13H_sound : CB3_2_3I1R13H.Encloses (homogeneousEntropy CB3_2_3I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R13Value CB3_2_3I1R13MassTerm_sound CB3_2_3I1R13Entropy_sound) (by decide +kernel)
def CB3_2_3I1R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 14 a
def CB3_2_3I1R14Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 14 a
lemma CB3_2_3I1R14Raw_sound (a : Fin 6) :
    (CB3_2_3I1R14Raw a).Encloses (CB3_2_3I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 14 a
def CB3_2_3I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R14Certificates_valid :
    CB3_2_3I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R14Certificates (CB3_2_3I1R14CertificateIndex a)).input
lemma CB3_2_3I1R14P_check : ∀ a : Fin 6, contains (CB3_2_3I1R14Raw a) (CB3_2_3I1R14P a) = true := by
  decide +kernel
lemma CB3_2_3I1R14P_sound (a : Fin 6) :
    (CB3_2_3I1R14P a).Encloses (CB3_2_3I1R14Value a) :=
  contains_sound (CB3_2_3I1R14Raw_sound a) (CB3_2_3I1R14P_check a)
def CB3_2_3I1R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R14Certificates (CB3_2_3I1R14CertificateIndex a)).output
lemma CB3_2_3I1R14Terms_sound (a : Fin 6) :
    (CB3_2_3I1R14Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R14Certificates_valid
    (CB3_2_3I1R14CertificateIndex a) (CB3_2_3I1R14P_sound a)
def CB3_2_3I1R14Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R14Entropy_sound : CB3_2_3I1R14Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R14Value CB3_2_3I1R14Terms CB3_2_3I1R14Terms_sound) (by decide +kernel)
def CB3_2_3I1R14Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R14Mass_sound : CB3_2_3I1R14Mass.Encloses (∑ a, CB3_2_3I1R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R14P CB3_2_3I1R14Value CB3_2_3I1R14P_sound) (by decide +kernel)
def CB3_2_3I1R14MassTerm : Ball := .exact 0
lemma CB3_2_3I1R14MassTerm_sound : CB3_2_3I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R14Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R14Mass_sound)
def CB3_2_3I1R14H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R14H_sound : CB3_2_3I1R14H.Encloses (homogeneousEntropy CB3_2_3I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R14Value CB3_2_3I1R14MassTerm_sound CB3_2_3I1R14Entropy_sound) (by decide +kernel)
def CB3_2_3I1R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 15 a
def CB3_2_3I1R15Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 15 a
lemma CB3_2_3I1R15Raw_sound (a : Fin 6) :
    (CB3_2_3I1R15Raw a).Encloses (CB3_2_3I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 15 a
def CB3_2_3I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R15Certificates_valid :
    CB3_2_3I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R15Certificates (CB3_2_3I1R15CertificateIndex a)).input
lemma CB3_2_3I1R15P_check : ∀ a : Fin 6, contains (CB3_2_3I1R15Raw a) (CB3_2_3I1R15P a) = true := by
  decide +kernel
lemma CB3_2_3I1R15P_sound (a : Fin 6) :
    (CB3_2_3I1R15P a).Encloses (CB3_2_3I1R15Value a) :=
  contains_sound (CB3_2_3I1R15Raw_sound a) (CB3_2_3I1R15P_check a)
def CB3_2_3I1R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R15Certificates (CB3_2_3I1R15CertificateIndex a)).output
lemma CB3_2_3I1R15Terms_sound (a : Fin 6) :
    (CB3_2_3I1R15Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R15Certificates_valid
    (CB3_2_3I1R15CertificateIndex a) (CB3_2_3I1R15P_sound a)
def CB3_2_3I1R15Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R15Entropy_sound : CB3_2_3I1R15Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R15Value CB3_2_3I1R15Terms CB3_2_3I1R15Terms_sound) (by decide +kernel)
def CB3_2_3I1R15Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R15Mass_sound : CB3_2_3I1R15Mass.Encloses (∑ a, CB3_2_3I1R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R15P CB3_2_3I1R15Value CB3_2_3I1R15P_sound) (by decide +kernel)
def CB3_2_3I1R15MassTerm : Ball := .exact 0
lemma CB3_2_3I1R15MassTerm_sound : CB3_2_3I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R15Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R15Mass_sound)
def CB3_2_3I1R15H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R15H_sound : CB3_2_3I1R15H.Encloses (homogeneousEntropy CB3_2_3I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R15Value CB3_2_3I1R15MassTerm_sound CB3_2_3I1R15Entropy_sound) (by decide +kernel)
def CB3_2_3I1R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) 16 a
def CB3_2_3I1R16Raw (a : Fin 6) : Ball := residualBall (below (shape 3 2 3)) B3_2_3Law (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) 16 a
lemma CB3_2_3I1R16Raw_sound (a : Fin 6) :
    (CB3_2_3I1R16Raw a).Encloses (CB3_2_3I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u => B3_2_3Little u ((stageBPriority (shape 3 2 3)) 1)) (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) (fun u _ a => B3_2_3Little_sound u ((stageBPriority (shape 3 2 3)) 1) a) 16 a
def CB3_2_3I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_2_3I1R16Certificates_valid :
    CB3_2_3I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I1R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_2_3I1R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R16Certificates (CB3_2_3I1R16CertificateIndex a)).input
lemma CB3_2_3I1R16P_check : ∀ a : Fin 6, contains (CB3_2_3I1R16Raw a) (CB3_2_3I1R16P a) = true := by
  decide +kernel
lemma CB3_2_3I1R16P_sound (a : Fin 6) :
    (CB3_2_3I1R16P a).Encloses (CB3_2_3I1R16Value a) :=
  contains_sound (CB3_2_3I1R16Raw_sound a) (CB3_2_3I1R16P_check a)
def CB3_2_3I1R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I1R16Certificates (CB3_2_3I1R16CertificateIndex a)).output
lemma CB3_2_3I1R16Terms_sound (a : Fin 6) :
    (CB3_2_3I1R16Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I1R16Certificates_valid
    (CB3_2_3I1R16CertificateIndex a) (CB3_2_3I1R16P_sound a)
def CB3_2_3I1R16Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R16Entropy_sound : CB3_2_3I1R16Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1R16Value CB3_2_3I1R16Terms CB3_2_3I1R16Terms_sound) (by decide +kernel)
def CB3_2_3I1R16Mass : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R16Mass_sound : CB3_2_3I1R16Mass.Encloses (∑ a, CB3_2_3I1R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_2_3I1R16P CB3_2_3I1R16Value CB3_2_3I1R16P_sound) (by decide +kernel)
def CB3_2_3I1R16MassTerm : Ball := .exact 0
lemma CB3_2_3I1R16MassTerm_sound : CB3_2_3I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1R16Value a))) :=
  entropyTerm_zero_ball (CB3_2_3I1R16Mass_sound)
def CB3_2_3I1R16H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1R16H_sound : CB3_2_3I1R16H.Encloses (homogeneousEntropy CB3_2_3I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1R16Value CB3_2_3I1R16MassTerm_sound CB3_2_3I1R16Entropy_sound) (by decide +kernel)
def CB3_2_3I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_2_3I1R0H
  | 1 => CB3_2_3I1R1H
  | 2 => CB3_2_3I1R2H
  | 3 => CB3_2_3I1R3H
  | 4 => CB3_2_3I1R4H
  | 5 => CB3_2_3I1R5H
  | 6 => CB3_2_3I1R6H
  | 7 => CB3_2_3I1R7H
  | 8 => CB3_2_3I1R8H
  | 9 => CB3_2_3I1R9H
  | 10 => CB3_2_3I1R10H
  | 11 => CB3_2_3I1R11H
  | 12 => CB3_2_3I1R12H
  | 13 => CB3_2_3I1R13H
  | 14 => CB3_2_3I1R14H
  | 15 => CB3_2_3I1R15H
  | 16 => CB3_2_3I1R16H
  | _ => (.exact 0)
lemma CB3_2_3I1ResidualEntropies_sound (k : Fin 17) :
    (CB3_2_3I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_2_3I1R0H_sound
  · exact CB3_2_3I1R1H_sound
  · exact CB3_2_3I1R2H_sound
  · exact CB3_2_3I1R3H_sound
  · exact CB3_2_3I1R4H_sound
  · exact CB3_2_3I1R5H_sound
  · exact CB3_2_3I1R6H_sound
  · exact CB3_2_3I1R7H_sound
  · exact CB3_2_3I1R8H_sound
  · exact CB3_2_3I1R9H_sound
  · exact CB3_2_3I1R10H_sound
  · exact CB3_2_3I1R11H_sound
  · exact CB3_2_3I1R12H_sound
  · exact CB3_2_3I1R13H_sound
  · exact CB3_2_3I1R14H_sound
  · exact CB3_2_3I1R15H_sound
  · exact CB3_2_3I1R16H_sound
def CB3_2_3I1S2_2_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1) a : ℝ)
def CB3_2_3I1S2_2_0E_2LogWitness : LogWitness := ⟨-1, 224407, 125000⟩
def CB3_2_3I1S2_2_0E_2Log : Ball := ⟨(-5399977520216846740471713413351 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0E_2Log_sound : CB3_2_3I1S2_2_0E_2Log.Encloses (Real.log (CB3_2_3I1S2_2_0Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (2 : Fin 6)) (w := CB3_2_3I1S2_2_0E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1S2_2_0E_2 : Ball := ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0E_2_sound : CB3_2_3I1S2_2_0E_2.Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (2 : Fin 6)) CB3_2_3I1S2_2_0E_2Log_sound) (by decide +kernel)
def CB3_2_3I1S2_2_0E_3LogWitness : LogWitness := ⟨-4, 25593, 15625⟩
def CB3_2_3I1S2_2_0E_3Log : Ball := ⟨(-113957102063378952030784463086693 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0E_3Log_sound : CB3_2_3I1S2_2_0E_3Log.Encloses (Real.log (CB3_2_3I1S2_2_0Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (3 : Fin 6)) (w := CB3_2_3I1S2_2_0E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I1S2_2_0E_3 : Ball := ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0E_3_sound : CB3_2_3I1S2_2_0E_3.Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (3 : Fin 6)) CB3_2_3I1S2_2_0E_3Log_sound) (by decide +kernel)
def CB3_2_3I1S2_2_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9694342043034415411912286335599 / 100000000000000000000000000000000), (19008012261 / 50000000000000000000000000000000)⟩
  | 3 => ⟨(11666016452432230077295467055111 / 50000000000000000000000000000000), (10839057111 / 100000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB3_2_3I1S2_2_0Terms_sound (a : Fin 6) :
    (CB3_2_3I1S2_2_0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1S2_2_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (1 : Fin 6)))
  · exact CB3_2_3I1S2_2_0E_2_sound
  · exact CB3_2_3I1S2_2_0E_3_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) (5 : Fin 6)))
def CB3_2_3I1S2_2_0Entropy : Ball := ⟨(33026374947898875566503220445821 / 100000000000000000000000000000000), (48855081633 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0Entropy_sound : CB3_2_3I1S2_2_0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1S2_2_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1S2_2_0Value CB3_2_3I1S2_2_0Terms CB3_2_3I1S2_2_0Terms_sound) (by decide +kernel)
def CB3_2_3I1S2_2_0Mass : Ball := ⟨1, 0⟩
lemma CB3_2_3I1S2_2_0Mass_sound : CB3_2_3I1S2_2_0Mass.Encloses (∑ a, CB3_2_3I1S2_2_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1)) CB3_2_3I1S2_2_0Value (B3_2_3Little_sound (shape 2 2 0) ((stageBPriority (shape 3 2 3)) 1))) (by decide +kernel)
def CB3_2_3I1S2_2_0MassTermLog : Ball := .exact 0
lemma CB3_2_3I1S2_2_0MassTermLog_sound : CB3_2_3I1S2_2_0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1S2_2_0Value a))) := by
  exact log_exact_one_ball (CB3_2_3I1S2_2_0Mass_sound)
def CB3_2_3I1S2_2_0MassTerm : Ball := ⟨0, 0⟩
lemma CB3_2_3I1S2_2_0MassTerm_sound : CB3_2_3I1S2_2_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1S2_2_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1S2_2_0Mass_sound) CB3_2_3I1S2_2_0MassTermLog_sound) (by decide +kernel)
def CB3_2_3I1S2_2_0H : Ball := ⟨(33026374947898875566503220445821 / 100000000000000000000000000000000), (48855081633 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1S2_2_0H_sound : CB3_2_3I1S2_2_0H.Encloses (homogeneousEntropy CB3_2_3I1S2_2_0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1S2_2_0Value CB3_2_3I1S2_2_0MassTerm_sound CB3_2_3I1S2_2_0Entropy_sound) (by decide +kernel)
def CB3_2_3I1S3_1_0Value (a : Fin 6) : ℝ := (littleLaw (shape 3 2 3) (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1) a : ℝ)
def CB3_2_3I1S3_1_0E_1Log : Ball := .exact 0
lemma CB3_2_3I1S3_1_0E_1Log_sound : CB3_2_3I1S3_1_0E_1Log.Encloses (Real.log (CB3_2_3I1S3_1_0Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (1 : Fin 6))
def CB3_2_3I1S3_1_0E_1 : Ball := ⟨0, 0⟩
lemma CB3_2_3I1S3_1_0E_1_sound : CB3_2_3I1S3_1_0E_1.Encloses (Foundation.entropyTerm (CB3_2_3I1S3_1_0Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (1 : Fin 6)) CB3_2_3I1S3_1_0E_1Log_sound) (by decide +kernel)
def CB3_2_3I1S3_1_0Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_2_3I1S3_1_0Terms_sound (a : Fin 6) :
    (CB3_2_3I1S3_1_0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I1S3_1_0Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (0 : Fin 6)))
  · exact CB3_2_3I1S3_1_0E_1_sound
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) (5 : Fin 6)))
def CB3_2_3I1S3_1_0Entropy : Ball := ⟨0, 0⟩
lemma CB3_2_3I1S3_1_0Entropy_sound : CB3_2_3I1S3_1_0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I1S3_1_0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_2_3I1S3_1_0Value CB3_2_3I1S3_1_0Terms CB3_2_3I1S3_1_0Terms_sound) (by decide +kernel)
def CB3_2_3I1S3_1_0Mass : Ball := ⟨1, 0⟩
lemma CB3_2_3I1S3_1_0Mass_sound : CB3_2_3I1S3_1_0Mass.Encloses (∑ a, CB3_2_3I1S3_1_0Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_2_3Little (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1)) CB3_2_3I1S3_1_0Value (B3_2_3Little_sound (shape 3 1 0) ((stageBPriority (shape 3 2 3)) 1))) (by decide +kernel)
def CB3_2_3I1S3_1_0MassTermLog : Ball := .exact 0
lemma CB3_2_3I1S3_1_0MassTermLog_sound : CB3_2_3I1S3_1_0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I1S3_1_0Value a))) := by
  exact log_exact_one_ball (CB3_2_3I1S3_1_0Mass_sound)
def CB3_2_3I1S3_1_0MassTerm : Ball := ⟨0, 0⟩
lemma CB3_2_3I1S3_1_0MassTerm_sound : CB3_2_3I1S3_1_0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I1S3_1_0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I1S3_1_0Mass_sound) CB3_2_3I1S3_1_0MassTermLog_sound) (by decide +kernel)
def CB3_2_3I1S3_1_0H : Ball := ⟨0, 0⟩
lemma CB3_2_3I1S3_1_0H_sound : CB3_2_3I1S3_1_0H.Encloses (homogeneousEntropy CB3_2_3I1S3_1_0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I1S3_1_0Value CB3_2_3I1S3_1_0MassTerm_sound CB3_2_3I1S3_1_0Entropy_sound) (by decide +kernel)
def CB3_2_3I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 2, 0 => CB3_2_3I1S2_2_0H
  | 3, 1, 0 => CB3_2_3I1S3_1_0H
  | _, _, _ => (.exact 0)
lemma CB3_2_3I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 2 3))
    (hd : designated (stageBPriority (shape 3 2 3)) 1 u) :
    (CB3_2_3I1Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) u)) := by
  rw [B3_2_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 0 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 0 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 0 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 1 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 2 0 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB3_2_3I1S2_2_0H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 2 3)) 1 (shape 3 0 1) by decide +kernel) hd |>.elim
  · exact CB3_2_3I1S3_1_0H_sound
def CB3_2_3I1Singleton : Ball := ⟨(76285391168564629548214282781 / 20000000000000000000000000000000), (564235257 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I1Singleton_sound : CB3_2_3I1Singleton.Encloses
    (singletonEntropy (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1
    CB3_2_3I1Singles (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ)) (fun u _ => B3_2_3Law_sound u) CB3_2_3I1Singles_sound) (by decide +kernel)
def CB3_2_3I1Group : Ball := ⟨(216873172264151446702389320823 / 6250000000000000000000000000000), (14411273761 / 12500000000000000000000000000000)⟩
lemma CB3_2_3I1Group_sound : CB3_2_3I1Group.Encloses
    (groupedEntropy (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (stageBPriority (shape 3 2 3)) 1 (fun u a => (littleLaw (shape 3 2 3) u ((stageBPriority (shape 3 2 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_2_3I1Singleton_sound
    (finSumBall_sound 17 CB3_2_3I1ResidualEntropies _ CB3_2_3I1ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_2_3I1H : Ball := ⟨(91580157958027952226815249149943 / 100000000000000000000000000000000), (62247841667 / 20000000000000000000000000000000)⟩
lemma CB3_2_3I1_sound : CB3_2_3I1H.Encloses (stageBCapacity (shape 3 2 3) 1) := by
  have hb := contains_sound (Ball.add_sound CB3_2_3I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_2_3I1Group_sound)))
    (show contains (.add CB3_2_3I1PairH (.neg (.mul (.exact 2) CB3_2_3I1Group))) CB3_2_3I1H = true by decide +kernel)
  unfold CB3_2_3I1PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
