import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_2_5I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 1 2 5)) (shape 1 2 5) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) a
def CB1_2_5I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) a
lemma CB1_2_5I2PairRaw_sound (a : PairSlot) :
    (CB1_2_5I2PairRaw a).Encloses (CB1_2_5I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) (fun u _ a => B1_2_5Little_sound (complement (shape 1 2 5) u) ((stageBPriority (shape 1 2 5)) 2) a) a
def CB1_2_5I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩ ⟨(-180734080505688700582649404519601 / 25000000000000000000000000000000), (10164395423 / 4000000000000000000000000000000)⟩ ⟨-11, 36249118515191988245121850051, 24414062500000000000000000000⟩,
   .log ⟨(9630112437092073853782692487793 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩ ⟨(7038046066567514544201224208257 / 20000000000000000000000000000000), (15294417267 / 50000000000000000000000000000000)⟩ ⟨(-36541868605081082766507538514009 / 50000000000000000000000000000000), (31763735573 / 50000000000000000000000000000000)⟩ ⟨-2, 9630112437092073853782692487793, 5000000000000000000000000000000⟩,
   .log ⟨(1776939577509246754596293860933 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(7161559846725884578897458412633 / 100000000000000000000000000000000), (658492791 / 25000000000000000000000000000000)⟩ ⟨(-403027763992083044849969306255681 / 100000000000000000000000000000000), (29646153201 / 20000000000000000000000000000000)⟩ ⟨-6, 1776939577509246754596293860933, 1562500000000000000000000000000⟩]
lemma CB1_2_5I2PairCertificates_valid :
    CB1_2_5I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CB1_2_5I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2PairCertificates (CB1_2_5I2PairCertificateIndex a)).input
lemma CB1_2_5I2PairP_check : ∀ a : PairSlot, contains (CB1_2_5I2PairRaw a) (CB1_2_5I2PairP a) = true := by
  decide +kernel
lemma CB1_2_5I2PairP_sound (a : PairSlot) :
    (CB1_2_5I2PairP a).Encloses (CB1_2_5I2PairValue a) :=
  contains_sound (CB1_2_5I2PairRaw_sound a) (CB1_2_5I2PairP_check a)
def CB1_2_5I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2PairCertificates (CB1_2_5I2PairCertificateIndex a)).output
lemma CB1_2_5I2PairTerms_sound (a : PairSlot) :
    (CB1_2_5I2PairTerms a).Encloses (Foundation.entropyTerm (CB1_2_5I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2PairCertificates_valid
    (CB1_2_5I2PairCertificateIndex a) (CB1_2_5I2PairP_sound a)
def CB1_2_5I2PairEntropy : Ball := ⟨(42875906267882254072548923946733 / 50000000000000000000000000000000), (33407030893 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I2PairEntropy_sound : CB1_2_5I2PairEntropy.Encloses (Foundation.finiteEntropy CB1_2_5I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB1_2_5I2PairValue CB1_2_5I2PairTerms CB1_2_5I2PairTerms_sound) (by decide +kernel)
def CB1_2_5I2PairMass : Ball := ⟨1, (13 / 12500000000000000000000000000000)⟩
lemma CB1_2_5I2PairMass_sound : CB1_2_5I2PairMass.Encloses (∑ a, CB1_2_5I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB1_2_5I2PairP CB1_2_5I2PairValue CB1_2_5I2PairP_sound) (by decide +kernel)
def CB1_2_5I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_2_5I2PairMassTermLog : Ball := ⟨0, (10587911893 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I2PairMassTermLog_sound : CB1_2_5I2PairMassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_2_5I2PairMass_sound) (w := CB1_2_5I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I2PairMassTerm : Ball := ⟨0, (21175823787 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2PairMassTerm_sound : CB1_2_5I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2PairMass_sound) CB1_2_5I2PairMassTermLog_sound) (by decide +kernel)
def CB1_2_5I2PairH : Ball := ⟨(42875906267882254072548923946733 / 50000000000000000000000000000000), (87989885573 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2PairH_sound : CB1_2_5I2PairH.Encloses (homogeneousEntropy CB1_2_5I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2PairValue CB1_2_5I2PairMassTerm_sound CB1_2_5I2PairEntropy_sound) (by decide +kernel)

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
def CB1_2_5I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 0 a
def CB1_2_5I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 0 a
lemma CB1_2_5I2R0Raw_sound (a : Fin 6) :
    (CB1_2_5I2R0Raw a).Encloses (CB1_2_5I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 0 a
def CB1_2_5I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R0Certificates_valid :
    CB1_2_5I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R0Certificates (CB1_2_5I2R0CertificateIndex a)).input
lemma CB1_2_5I2R0P_check : ∀ a : Fin 6, contains (CB1_2_5I2R0Raw a) (CB1_2_5I2R0P a) = true := by
  decide +kernel
lemma CB1_2_5I2R0P_sound (a : Fin 6) :
    (CB1_2_5I2R0P a).Encloses (CB1_2_5I2R0Value a) :=
  contains_sound (CB1_2_5I2R0Raw_sound a) (CB1_2_5I2R0P_check a)
def CB1_2_5I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R0Certificates (CB1_2_5I2R0CertificateIndex a)).output
lemma CB1_2_5I2R0Terms_sound (a : Fin 6) :
    (CB1_2_5I2R0Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R0Certificates_valid
    (CB1_2_5I2R0CertificateIndex a) (CB1_2_5I2R0P_sound a)
def CB1_2_5I2R0Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R0Entropy_sound : CB1_2_5I2R0Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R0Value CB1_2_5I2R0Terms CB1_2_5I2R0Terms_sound) (by decide +kernel)
def CB1_2_5I2R0Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R0Mass_sound : CB1_2_5I2R0Mass.Encloses (∑ a, CB1_2_5I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R0P CB1_2_5I2R0Value CB1_2_5I2R0P_sound) (by decide +kernel)
def CB1_2_5I2R0MassTerm : Ball := .exact 0
lemma CB1_2_5I2R0MassTerm_sound : CB1_2_5I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R0Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R0Mass_sound)
def CB1_2_5I2R0H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R0H_sound : CB1_2_5I2R0H.Encloses (homogeneousEntropy CB1_2_5I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R0Value CB1_2_5I2R0MassTerm_sound CB1_2_5I2R0Entropy_sound) (by decide +kernel)
def CB1_2_5I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 1 a
def CB1_2_5I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 1 a
lemma CB1_2_5I2R1Raw_sound (a : Fin 6) :
    (CB1_2_5I2R1Raw a).Encloses (CB1_2_5I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 1 a
def CB1_2_5I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩ ⟨(-180734080505688700582649404519601 / 25000000000000000000000000000000), (10164395423 / 4000000000000000000000000000000)⟩ ⟨-11, 36249118515191988245121850051, 24414062500000000000000000000⟩]
lemma CB1_2_5I2R1Certificates_valid :
    CB1_2_5I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB1_2_5I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R1Certificates (CB1_2_5I2R1CertificateIndex a)).input
lemma CB1_2_5I2R1P_check : ∀ a : Fin 6, contains (CB1_2_5I2R1Raw a) (CB1_2_5I2R1P a) = true := by
  decide +kernel
lemma CB1_2_5I2R1P_sound (a : Fin 6) :
    (CB1_2_5I2R1P a).Encloses (CB1_2_5I2R1Value a) :=
  contains_sound (CB1_2_5I2R1Raw_sound a) (CB1_2_5I2R1P_check a)
def CB1_2_5I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R1Certificates (CB1_2_5I2R1CertificateIndex a)).output
lemma CB1_2_5I2R1Terms_sound (a : Fin 6) :
    (CB1_2_5I2R1Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R1Certificates_valid
    (CB1_2_5I2R1CertificateIndex a) (CB1_2_5I2R1P_sound a)
def CB1_2_5I2R1Entropy : Ball := ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩
lemma CB1_2_5I2R1Entropy_sound : CB1_2_5I2R1Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R1Value CB1_2_5I2R1Terms CB1_2_5I2R1Terms_sound) (by decide +kernel)
def CB1_2_5I2R1Mass : Ball := ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2R1Mass_sound : CB1_2_5I2R1Mass.Encloses (∑ a, CB1_2_5I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R1P CB1_2_5I2R1Value CB1_2_5I2R1P_sound) (by decide +kernel)
def CB1_2_5I2R1MassTermLogWitness : LogWitness := ⟨-11, 36249118515191988245121850051, 24414062500000000000000000000⟩
def CB1_2_5I2R1MassTermLog : Ball := ⟨(-180734080505688700582649404519601 / 25000000000000000000000000000000), (10164395423 / 4000000000000000000000000000000)⟩
lemma CB1_2_5I2R1MassTermLog_sound : CB1_2_5I2R1MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_2_5I2R1Mass_sound) (w := CB1_2_5I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I2R1MassTerm : Ball := ⟨(104823217663759354529068898563 / 20000000000000000000000000000000), (36845039 / 20000000000000000000000000000000)⟩
lemma CB1_2_5I2R1MassTerm_sound : CB1_2_5I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2R1Mass_sound) CB1_2_5I2R1MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2R1H : Ball := ⟨0, (36845039 / 10000000000000000000000000000000)⟩
lemma CB1_2_5I2R1H_sound : CB1_2_5I2R1H.Encloses (homogeneousEntropy CB1_2_5I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R1Value CB1_2_5I2R1MassTerm_sound CB1_2_5I2R1Entropy_sound) (by decide +kernel)
def CB1_2_5I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 2 a
def CB1_2_5I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 2 a
lemma CB1_2_5I2R2Raw_sound (a : Fin 6) :
    (CB1_2_5I2R2Raw a).Encloses (CB1_2_5I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 2 a
def CB1_2_5I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(7284663137258594485497802035789 / 20000000000000000000000000000000), (10079080399 / 50000000000000000000000000000000)⟩ ⟨(-114786322022754802330597789937667 / 100000000000000000000000000000000), (63527471099 / 100000000000000000000000000000000)⟩ ⟨-2, 396642594740867223667445521291, 312500000000000000000000000000⟩]
lemma CB1_2_5I2R2Certificates_valid :
    CB1_2_5I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | _ => 0
def CB1_2_5I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R2Certificates (CB1_2_5I2R2CertificateIndex a)).input
lemma CB1_2_5I2R2P_check : ∀ a : Fin 6, contains (CB1_2_5I2R2Raw a) (CB1_2_5I2R2P a) = true := by
  decide +kernel
lemma CB1_2_5I2R2P_sound (a : Fin 6) :
    (CB1_2_5I2R2P a).Encloses (CB1_2_5I2R2Value a) :=
  contains_sound (CB1_2_5I2R2Raw_sound a) (CB1_2_5I2R2P_check a)
def CB1_2_5I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R2Certificates (CB1_2_5I2R2CertificateIndex a)).output
lemma CB1_2_5I2R2Terms_sound (a : Fin 6) :
    (CB1_2_5I2R2Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R2Certificates_valid
    (CB1_2_5I2R2CertificateIndex a) (CB1_2_5I2R2P_sound a)
def CB1_2_5I2R2Entropy : Ball := ⟨(7284663137258594485497802035789 / 20000000000000000000000000000000), (10079080399 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I2R2Entropy_sound : CB1_2_5I2R2Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R2Value CB1_2_5I2R2Terms CB1_2_5I2R2Terms_sound) (by decide +kernel)
def CB1_2_5I2R2Mass : Ball := ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
lemma CB1_2_5I2R2Mass_sound : CB1_2_5I2R2Mass.Encloses (∑ a, CB1_2_5I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R2P CB1_2_5I2R2Value CB1_2_5I2R2P_sound) (by decide +kernel)
def CB1_2_5I2R2MassTermLogWitness : LogWitness := ⟨-2, 396642594740867223667445521291, 312500000000000000000000000000⟩
def CB1_2_5I2R2MassTermLog : Ball := ⟨(-114786322022754802330597789937667 / 100000000000000000000000000000000), (63527471099 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2R2MassTermLog_sound : CB1_2_5I2R2MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_2_5I2R2Mass_sound) (w := CB1_2_5I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I2R2MassTerm : Ball := ⟨(7284663137258594485497802035789 / 20000000000000000000000000000000), (10079080399 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I2R2MassTerm_sound : CB1_2_5I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2R2Mass_sound) CB1_2_5I2R2MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2R2H : Ball := ⟨0, (10079080399 / 25000000000000000000000000000000)⟩
lemma CB1_2_5I2R2H_sound : CB1_2_5I2R2H.Encloses (homogeneousEntropy CB1_2_5I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R2Value CB1_2_5I2R2MassTerm_sound CB1_2_5I2R2Entropy_sound) (by decide +kernel)
def CB1_2_5I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 3 a
def CB1_2_5I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 3 a
lemma CB1_2_5I2R3Raw_sound (a : Fin 6) :
    (CB1_2_5I2R3Raw a).Encloses (CB1_2_5I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 3 a
def CB1_2_5I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R3Certificates_valid :
    CB1_2_5I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R3Certificates (CB1_2_5I2R3CertificateIndex a)).input
lemma CB1_2_5I2R3P_check : ∀ a : Fin 6, contains (CB1_2_5I2R3Raw a) (CB1_2_5I2R3P a) = true := by
  decide +kernel
lemma CB1_2_5I2R3P_sound (a : Fin 6) :
    (CB1_2_5I2R3P a).Encloses (CB1_2_5I2R3Value a) :=
  contains_sound (CB1_2_5I2R3Raw_sound a) (CB1_2_5I2R3P_check a)
def CB1_2_5I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R3Certificates (CB1_2_5I2R3CertificateIndex a)).output
lemma CB1_2_5I2R3Terms_sound (a : Fin 6) :
    (CB1_2_5I2R3Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R3Certificates_valid
    (CB1_2_5I2R3CertificateIndex a) (CB1_2_5I2R3P_sound a)
def CB1_2_5I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R3Entropy_sound : CB1_2_5I2R3Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R3Value CB1_2_5I2R3Terms CB1_2_5I2R3Terms_sound) (by decide +kernel)
def CB1_2_5I2R3Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R3Mass_sound : CB1_2_5I2R3Mass.Encloses (∑ a, CB1_2_5I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R3P CB1_2_5I2R3Value CB1_2_5I2R3P_sound) (by decide +kernel)
def CB1_2_5I2R3MassTerm : Ball := .exact 0
lemma CB1_2_5I2R3MassTerm_sound : CB1_2_5I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R3Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R3Mass_sound)
def CB1_2_5I2R3H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R3H_sound : CB1_2_5I2R3H.Encloses (homogeneousEntropy CB1_2_5I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R3Value CB1_2_5I2R3MassTerm_sound CB1_2_5I2R3Entropy_sound) (by decide +kernel)
def CB1_2_5I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 4 a
def CB1_2_5I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 4 a
lemma CB1_2_5I2R4Raw_sound (a : Fin 6) :
    (CB1_2_5I2R4Raw a).Encloses (CB1_2_5I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 4 a
def CB1_2_5I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R4Certificates_valid :
    CB1_2_5I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R4Certificates (CB1_2_5I2R4CertificateIndex a)).input
lemma CB1_2_5I2R4P_check : ∀ a : Fin 6, contains (CB1_2_5I2R4Raw a) (CB1_2_5I2R4P a) = true := by
  decide +kernel
lemma CB1_2_5I2R4P_sound (a : Fin 6) :
    (CB1_2_5I2R4P a).Encloses (CB1_2_5I2R4Value a) :=
  contains_sound (CB1_2_5I2R4Raw_sound a) (CB1_2_5I2R4P_check a)
def CB1_2_5I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R4Certificates (CB1_2_5I2R4CertificateIndex a)).output
lemma CB1_2_5I2R4Terms_sound (a : Fin 6) :
    (CB1_2_5I2R4Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R4Certificates_valid
    (CB1_2_5I2R4CertificateIndex a) (CB1_2_5I2R4P_sound a)
def CB1_2_5I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R4Entropy_sound : CB1_2_5I2R4Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R4Value CB1_2_5I2R4Terms CB1_2_5I2R4Terms_sound) (by decide +kernel)
def CB1_2_5I2R4Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R4Mass_sound : CB1_2_5I2R4Mass.Encloses (∑ a, CB1_2_5I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R4P CB1_2_5I2R4Value CB1_2_5I2R4P_sound) (by decide +kernel)
def CB1_2_5I2R4MassTerm : Ball := .exact 0
lemma CB1_2_5I2R4MassTerm_sound : CB1_2_5I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R4Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R4Mass_sound)
def CB1_2_5I2R4H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R4H_sound : CB1_2_5I2R4H.Encloses (homogeneousEntropy CB1_2_5I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R4Value CB1_2_5I2R4MassTerm_sound CB1_2_5I2R4Entropy_sound) (by decide +kernel)
def CB1_2_5I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 5 a
def CB1_2_5I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 5 a
lemma CB1_2_5I2R5Raw_sound (a : Fin 6) :
    (CB1_2_5I2R5Raw a).Encloses (CB1_2_5I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 5 a
def CB1_2_5I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R5Certificates_valid :
    CB1_2_5I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R5Certificates (CB1_2_5I2R5CertificateIndex a)).input
lemma CB1_2_5I2R5P_check : ∀ a : Fin 6, contains (CB1_2_5I2R5Raw a) (CB1_2_5I2R5P a) = true := by
  decide +kernel
lemma CB1_2_5I2R5P_sound (a : Fin 6) :
    (CB1_2_5I2R5P a).Encloses (CB1_2_5I2R5Value a) :=
  contains_sound (CB1_2_5I2R5Raw_sound a) (CB1_2_5I2R5P_check a)
def CB1_2_5I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R5Certificates (CB1_2_5I2R5CertificateIndex a)).output
lemma CB1_2_5I2R5Terms_sound (a : Fin 6) :
    (CB1_2_5I2R5Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R5Certificates_valid
    (CB1_2_5I2R5CertificateIndex a) (CB1_2_5I2R5P_sound a)
def CB1_2_5I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R5Entropy_sound : CB1_2_5I2R5Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R5Value CB1_2_5I2R5Terms CB1_2_5I2R5Terms_sound) (by decide +kernel)
def CB1_2_5I2R5Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R5Mass_sound : CB1_2_5I2R5Mass.Encloses (∑ a, CB1_2_5I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R5P CB1_2_5I2R5Value CB1_2_5I2R5P_sound) (by decide +kernel)
def CB1_2_5I2R5MassTerm : Ball := .exact 0
lemma CB1_2_5I2R5MassTerm_sound : CB1_2_5I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R5Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R5Mass_sound)
def CB1_2_5I2R5H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R5H_sound : CB1_2_5I2R5H.Encloses (homogeneousEntropy CB1_2_5I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R5Value CB1_2_5I2R5MassTerm_sound CB1_2_5I2R5Entropy_sound) (by decide +kernel)
def CB1_2_5I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 6 a
def CB1_2_5I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 6 a
lemma CB1_2_5I2R6Raw_sound (a : Fin 6) :
    (CB1_2_5I2R6Raw a).Encloses (CB1_2_5I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 6 a
def CB1_2_5I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R6Certificates_valid :
    CB1_2_5I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R6Certificates (CB1_2_5I2R6CertificateIndex a)).input
lemma CB1_2_5I2R6P_check : ∀ a : Fin 6, contains (CB1_2_5I2R6Raw a) (CB1_2_5I2R6P a) = true := by
  decide +kernel
lemma CB1_2_5I2R6P_sound (a : Fin 6) :
    (CB1_2_5I2R6P a).Encloses (CB1_2_5I2R6Value a) :=
  contains_sound (CB1_2_5I2R6Raw_sound a) (CB1_2_5I2R6P_check a)
def CB1_2_5I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R6Certificates (CB1_2_5I2R6CertificateIndex a)).output
lemma CB1_2_5I2R6Terms_sound (a : Fin 6) :
    (CB1_2_5I2R6Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R6Certificates_valid
    (CB1_2_5I2R6CertificateIndex a) (CB1_2_5I2R6P_sound a)
def CB1_2_5I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R6Entropy_sound : CB1_2_5I2R6Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R6Value CB1_2_5I2R6Terms CB1_2_5I2R6Terms_sound) (by decide +kernel)
def CB1_2_5I2R6Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R6Mass_sound : CB1_2_5I2R6Mass.Encloses (∑ a, CB1_2_5I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R6P CB1_2_5I2R6Value CB1_2_5I2R6P_sound) (by decide +kernel)
def CB1_2_5I2R6MassTerm : Ball := .exact 0
lemma CB1_2_5I2R6MassTerm_sound : CB1_2_5I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R6Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R6Mass_sound)
def CB1_2_5I2R6H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R6H_sound : CB1_2_5I2R6H.Encloses (homogeneousEntropy CB1_2_5I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R6Value CB1_2_5I2R6MassTerm_sound CB1_2_5I2R6Entropy_sound) (by decide +kernel)
def CB1_2_5I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 7 a
def CB1_2_5I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 7 a
lemma CB1_2_5I2R7Raw_sound (a : Fin 6) :
    (CB1_2_5I2R7Raw a).Encloses (CB1_2_5I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 7 a
def CB1_2_5I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R7Certificates_valid :
    CB1_2_5I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R7Certificates (CB1_2_5I2R7CertificateIndex a)).input
lemma CB1_2_5I2R7P_check : ∀ a : Fin 6, contains (CB1_2_5I2R7Raw a) (CB1_2_5I2R7P a) = true := by
  decide +kernel
lemma CB1_2_5I2R7P_sound (a : Fin 6) :
    (CB1_2_5I2R7P a).Encloses (CB1_2_5I2R7Value a) :=
  contains_sound (CB1_2_5I2R7Raw_sound a) (CB1_2_5I2R7P_check a)
def CB1_2_5I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R7Certificates (CB1_2_5I2R7CertificateIndex a)).output
lemma CB1_2_5I2R7Terms_sound (a : Fin 6) :
    (CB1_2_5I2R7Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R7Certificates_valid
    (CB1_2_5I2R7CertificateIndex a) (CB1_2_5I2R7P_sound a)
def CB1_2_5I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R7Entropy_sound : CB1_2_5I2R7Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R7Value CB1_2_5I2R7Terms CB1_2_5I2R7Terms_sound) (by decide +kernel)
def CB1_2_5I2R7Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R7Mass_sound : CB1_2_5I2R7Mass.Encloses (∑ a, CB1_2_5I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R7P CB1_2_5I2R7Value CB1_2_5I2R7P_sound) (by decide +kernel)
def CB1_2_5I2R7MassTerm : Ball := .exact 0
lemma CB1_2_5I2R7MassTerm_sound : CB1_2_5I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R7Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R7Mass_sound)
def CB1_2_5I2R7H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R7H_sound : CB1_2_5I2R7H.Encloses (homogeneousEntropy CB1_2_5I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R7Value CB1_2_5I2R7MassTerm_sound CB1_2_5I2R7Entropy_sound) (by decide +kernel)
def CB1_2_5I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 8 a
def CB1_2_5I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 8 a
lemma CB1_2_5I2R8Raw_sound (a : Fin 6) :
    (CB1_2_5I2R8Raw a).Encloses (CB1_2_5I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 8 a
def CB1_2_5I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R8Certificates_valid :
    CB1_2_5I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R8Certificates (CB1_2_5I2R8CertificateIndex a)).input
lemma CB1_2_5I2R8P_check : ∀ a : Fin 6, contains (CB1_2_5I2R8Raw a) (CB1_2_5I2R8P a) = true := by
  decide +kernel
lemma CB1_2_5I2R8P_sound (a : Fin 6) :
    (CB1_2_5I2R8P a).Encloses (CB1_2_5I2R8Value a) :=
  contains_sound (CB1_2_5I2R8Raw_sound a) (CB1_2_5I2R8P_check a)
def CB1_2_5I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R8Certificates (CB1_2_5I2R8CertificateIndex a)).output
lemma CB1_2_5I2R8Terms_sound (a : Fin 6) :
    (CB1_2_5I2R8Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R8Certificates_valid
    (CB1_2_5I2R8CertificateIndex a) (CB1_2_5I2R8P_sound a)
def CB1_2_5I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R8Entropy_sound : CB1_2_5I2R8Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R8Value CB1_2_5I2R8Terms CB1_2_5I2R8Terms_sound) (by decide +kernel)
def CB1_2_5I2R8Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R8Mass_sound : CB1_2_5I2R8Mass.Encloses (∑ a, CB1_2_5I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R8P CB1_2_5I2R8Value CB1_2_5I2R8P_sound) (by decide +kernel)
def CB1_2_5I2R8MassTerm : Ball := .exact 0
lemma CB1_2_5I2R8MassTerm_sound : CB1_2_5I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R8Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R8Mass_sound)
def CB1_2_5I2R8H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R8H_sound : CB1_2_5I2R8H.Encloses (homogeneousEntropy CB1_2_5I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R8Value CB1_2_5I2R8MassTerm_sound CB1_2_5I2R8Entropy_sound) (by decide +kernel)
def CB1_2_5I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 9 a
def CB1_2_5I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 9 a
lemma CB1_2_5I2R9Raw_sound (a : Fin 6) :
    (CB1_2_5I2R9Raw a).Encloses (CB1_2_5I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 9 a
def CB1_2_5I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R9Certificates_valid :
    CB1_2_5I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R9Certificates (CB1_2_5I2R9CertificateIndex a)).input
lemma CB1_2_5I2R9P_check : ∀ a : Fin 6, contains (CB1_2_5I2R9Raw a) (CB1_2_5I2R9P a) = true := by
  decide +kernel
lemma CB1_2_5I2R9P_sound (a : Fin 6) :
    (CB1_2_5I2R9P a).Encloses (CB1_2_5I2R9Value a) :=
  contains_sound (CB1_2_5I2R9Raw_sound a) (CB1_2_5I2R9P_check a)
def CB1_2_5I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R9Certificates (CB1_2_5I2R9CertificateIndex a)).output
lemma CB1_2_5I2R9Terms_sound (a : Fin 6) :
    (CB1_2_5I2R9Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R9Certificates_valid
    (CB1_2_5I2R9CertificateIndex a) (CB1_2_5I2R9P_sound a)
def CB1_2_5I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R9Entropy_sound : CB1_2_5I2R9Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R9Value CB1_2_5I2R9Terms CB1_2_5I2R9Terms_sound) (by decide +kernel)
def CB1_2_5I2R9Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R9Mass_sound : CB1_2_5I2R9Mass.Encloses (∑ a, CB1_2_5I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R9P CB1_2_5I2R9Value CB1_2_5I2R9P_sound) (by decide +kernel)
def CB1_2_5I2R9MassTerm : Ball := .exact 0
lemma CB1_2_5I2R9MassTerm_sound : CB1_2_5I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R9Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R9Mass_sound)
def CB1_2_5I2R9H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R9H_sound : CB1_2_5I2R9H.Encloses (homogeneousEntropy CB1_2_5I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R9Value CB1_2_5I2R9MassTerm_sound CB1_2_5I2R9Entropy_sound) (by decide +kernel)
def CB1_2_5I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 10 a
def CB1_2_5I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 10 a
lemma CB1_2_5I2R10Raw_sound (a : Fin 6) :
    (CB1_2_5I2R10Raw a).Encloses (CB1_2_5I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 10 a
def CB1_2_5I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R10Certificates_valid :
    CB1_2_5I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R10Certificates (CB1_2_5I2R10CertificateIndex a)).input
lemma CB1_2_5I2R10P_check : ∀ a : Fin 6, contains (CB1_2_5I2R10Raw a) (CB1_2_5I2R10P a) = true := by
  decide +kernel
lemma CB1_2_5I2R10P_sound (a : Fin 6) :
    (CB1_2_5I2R10P a).Encloses (CB1_2_5I2R10Value a) :=
  contains_sound (CB1_2_5I2R10Raw_sound a) (CB1_2_5I2R10P_check a)
def CB1_2_5I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R10Certificates (CB1_2_5I2R10CertificateIndex a)).output
lemma CB1_2_5I2R10Terms_sound (a : Fin 6) :
    (CB1_2_5I2R10Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R10Certificates_valid
    (CB1_2_5I2R10CertificateIndex a) (CB1_2_5I2R10P_sound a)
def CB1_2_5I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R10Entropy_sound : CB1_2_5I2R10Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R10Value CB1_2_5I2R10Terms CB1_2_5I2R10Terms_sound) (by decide +kernel)
def CB1_2_5I2R10Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R10Mass_sound : CB1_2_5I2R10Mass.Encloses (∑ a, CB1_2_5I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R10P CB1_2_5I2R10Value CB1_2_5I2R10P_sound) (by decide +kernel)
def CB1_2_5I2R10MassTerm : Ball := .exact 0
lemma CB1_2_5I2R10MassTerm_sound : CB1_2_5I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R10Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R10Mass_sound)
def CB1_2_5I2R10H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R10H_sound : CB1_2_5I2R10H.Encloses (homogeneousEntropy CB1_2_5I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R10Value CB1_2_5I2R10MassTerm_sound CB1_2_5I2R10Entropy_sound) (by decide +kernel)
def CB1_2_5I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 11 a
def CB1_2_5I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 11 a
lemma CB1_2_5I2R11Raw_sound (a : Fin 6) :
    (CB1_2_5I2R11Raw a).Encloses (CB1_2_5I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 11 a
def CB1_2_5I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R11Certificates_valid :
    CB1_2_5I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R11Certificates (CB1_2_5I2R11CertificateIndex a)).input
lemma CB1_2_5I2R11P_check : ∀ a : Fin 6, contains (CB1_2_5I2R11Raw a) (CB1_2_5I2R11P a) = true := by
  decide +kernel
lemma CB1_2_5I2R11P_sound (a : Fin 6) :
    (CB1_2_5I2R11P a).Encloses (CB1_2_5I2R11Value a) :=
  contains_sound (CB1_2_5I2R11Raw_sound a) (CB1_2_5I2R11P_check a)
def CB1_2_5I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R11Certificates (CB1_2_5I2R11CertificateIndex a)).output
lemma CB1_2_5I2R11Terms_sound (a : Fin 6) :
    (CB1_2_5I2R11Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R11Certificates_valid
    (CB1_2_5I2R11CertificateIndex a) (CB1_2_5I2R11P_sound a)
def CB1_2_5I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R11Entropy_sound : CB1_2_5I2R11Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R11Value CB1_2_5I2R11Terms CB1_2_5I2R11Terms_sound) (by decide +kernel)
def CB1_2_5I2R11Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R11Mass_sound : CB1_2_5I2R11Mass.Encloses (∑ a, CB1_2_5I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R11P CB1_2_5I2R11Value CB1_2_5I2R11P_sound) (by decide +kernel)
def CB1_2_5I2R11MassTerm : Ball := .exact 0
lemma CB1_2_5I2R11MassTerm_sound : CB1_2_5I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R11Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R11Mass_sound)
def CB1_2_5I2R11H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R11H_sound : CB1_2_5I2R11H.Encloses (homogeneousEntropy CB1_2_5I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R11Value CB1_2_5I2R11MassTerm_sound CB1_2_5I2R11Entropy_sound) (by decide +kernel)
def CB1_2_5I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 12 a
def CB1_2_5I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 12 a
lemma CB1_2_5I2R12Raw_sound (a : Fin 6) :
    (CB1_2_5I2R12Raw a).Encloses (CB1_2_5I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 12 a
def CB1_2_5I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R12Certificates_valid :
    CB1_2_5I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R12Certificates (CB1_2_5I2R12CertificateIndex a)).input
lemma CB1_2_5I2R12P_check : ∀ a : Fin 6, contains (CB1_2_5I2R12Raw a) (CB1_2_5I2R12P a) = true := by
  decide +kernel
lemma CB1_2_5I2R12P_sound (a : Fin 6) :
    (CB1_2_5I2R12P a).Encloses (CB1_2_5I2R12Value a) :=
  contains_sound (CB1_2_5I2R12Raw_sound a) (CB1_2_5I2R12P_check a)
def CB1_2_5I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R12Certificates (CB1_2_5I2R12CertificateIndex a)).output
lemma CB1_2_5I2R12Terms_sound (a : Fin 6) :
    (CB1_2_5I2R12Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R12Certificates_valid
    (CB1_2_5I2R12CertificateIndex a) (CB1_2_5I2R12P_sound a)
def CB1_2_5I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R12Entropy_sound : CB1_2_5I2R12Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R12Value CB1_2_5I2R12Terms CB1_2_5I2R12Terms_sound) (by decide +kernel)
def CB1_2_5I2R12Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R12Mass_sound : CB1_2_5I2R12Mass.Encloses (∑ a, CB1_2_5I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R12P CB1_2_5I2R12Value CB1_2_5I2R12P_sound) (by decide +kernel)
def CB1_2_5I2R12MassTerm : Ball := .exact 0
lemma CB1_2_5I2R12MassTerm_sound : CB1_2_5I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R12Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R12Mass_sound)
def CB1_2_5I2R12H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R12H_sound : CB1_2_5I2R12H.Encloses (homogeneousEntropy CB1_2_5I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R12Value CB1_2_5I2R12MassTerm_sound CB1_2_5I2R12Entropy_sound) (by decide +kernel)
def CB1_2_5I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 13 a
def CB1_2_5I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 13 a
lemma CB1_2_5I2R13Raw_sound (a : Fin 6) :
    (CB1_2_5I2R13Raw a).Encloses (CB1_2_5I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 13 a
def CB1_2_5I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R13Certificates_valid :
    CB1_2_5I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R13Certificates (CB1_2_5I2R13CertificateIndex a)).input
lemma CB1_2_5I2R13P_check : ∀ a : Fin 6, contains (CB1_2_5I2R13Raw a) (CB1_2_5I2R13P a) = true := by
  decide +kernel
lemma CB1_2_5I2R13P_sound (a : Fin 6) :
    (CB1_2_5I2R13P a).Encloses (CB1_2_5I2R13Value a) :=
  contains_sound (CB1_2_5I2R13Raw_sound a) (CB1_2_5I2R13P_check a)
def CB1_2_5I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R13Certificates (CB1_2_5I2R13CertificateIndex a)).output
lemma CB1_2_5I2R13Terms_sound (a : Fin 6) :
    (CB1_2_5I2R13Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R13Certificates_valid
    (CB1_2_5I2R13CertificateIndex a) (CB1_2_5I2R13P_sound a)
def CB1_2_5I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R13Entropy_sound : CB1_2_5I2R13Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R13Value CB1_2_5I2R13Terms CB1_2_5I2R13Terms_sound) (by decide +kernel)
def CB1_2_5I2R13Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R13Mass_sound : CB1_2_5I2R13Mass.Encloses (∑ a, CB1_2_5I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R13P CB1_2_5I2R13Value CB1_2_5I2R13P_sound) (by decide +kernel)
def CB1_2_5I2R13MassTerm : Ball := .exact 0
lemma CB1_2_5I2R13MassTerm_sound : CB1_2_5I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R13Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R13Mass_sound)
def CB1_2_5I2R13H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R13H_sound : CB1_2_5I2R13H.Encloses (homogeneousEntropy CB1_2_5I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R13Value CB1_2_5I2R13MassTerm_sound CB1_2_5I2R13Entropy_sound) (by decide +kernel)
def CB1_2_5I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 14 a
def CB1_2_5I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 14 a
lemma CB1_2_5I2R14Raw_sound (a : Fin 6) :
    (CB1_2_5I2R14Raw a).Encloses (CB1_2_5I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 14 a
def CB1_2_5I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R14Certificates_valid :
    CB1_2_5I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R14Certificates (CB1_2_5I2R14CertificateIndex a)).input
lemma CB1_2_5I2R14P_check : ∀ a : Fin 6, contains (CB1_2_5I2R14Raw a) (CB1_2_5I2R14P a) = true := by
  decide +kernel
lemma CB1_2_5I2R14P_sound (a : Fin 6) :
    (CB1_2_5I2R14P a).Encloses (CB1_2_5I2R14Value a) :=
  contains_sound (CB1_2_5I2R14Raw_sound a) (CB1_2_5I2R14P_check a)
def CB1_2_5I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R14Certificates (CB1_2_5I2R14CertificateIndex a)).output
lemma CB1_2_5I2R14Terms_sound (a : Fin 6) :
    (CB1_2_5I2R14Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R14Certificates_valid
    (CB1_2_5I2R14CertificateIndex a) (CB1_2_5I2R14P_sound a)
def CB1_2_5I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R14Entropy_sound : CB1_2_5I2R14Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R14Value CB1_2_5I2R14Terms CB1_2_5I2R14Terms_sound) (by decide +kernel)
def CB1_2_5I2R14Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R14Mass_sound : CB1_2_5I2R14Mass.Encloses (∑ a, CB1_2_5I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R14P CB1_2_5I2R14Value CB1_2_5I2R14P_sound) (by decide +kernel)
def CB1_2_5I2R14MassTerm : Ball := .exact 0
lemma CB1_2_5I2R14MassTerm_sound : CB1_2_5I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R14Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R14Mass_sound)
def CB1_2_5I2R14H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R14H_sound : CB1_2_5I2R14H.Encloses (homogeneousEntropy CB1_2_5I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R14Value CB1_2_5I2R14MassTerm_sound CB1_2_5I2R14Entropy_sound) (by decide +kernel)
def CB1_2_5I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 15 a
def CB1_2_5I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 15 a
lemma CB1_2_5I2R15Raw_sound (a : Fin 6) :
    (CB1_2_5I2R15Raw a).Encloses (CB1_2_5I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 15 a
def CB1_2_5I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R15Certificates_valid :
    CB1_2_5I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R15Certificates (CB1_2_5I2R15CertificateIndex a)).input
lemma CB1_2_5I2R15P_check : ∀ a : Fin 6, contains (CB1_2_5I2R15Raw a) (CB1_2_5I2R15P a) = true := by
  decide +kernel
lemma CB1_2_5I2R15P_sound (a : Fin 6) :
    (CB1_2_5I2R15P a).Encloses (CB1_2_5I2R15Value a) :=
  contains_sound (CB1_2_5I2R15Raw_sound a) (CB1_2_5I2R15P_check a)
def CB1_2_5I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R15Certificates (CB1_2_5I2R15CertificateIndex a)).output
lemma CB1_2_5I2R15Terms_sound (a : Fin 6) :
    (CB1_2_5I2R15Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R15Certificates_valid
    (CB1_2_5I2R15CertificateIndex a) (CB1_2_5I2R15P_sound a)
def CB1_2_5I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R15Entropy_sound : CB1_2_5I2R15Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R15Value CB1_2_5I2R15Terms CB1_2_5I2R15Terms_sound) (by decide +kernel)
def CB1_2_5I2R15Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R15Mass_sound : CB1_2_5I2R15Mass.Encloses (∑ a, CB1_2_5I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R15P CB1_2_5I2R15Value CB1_2_5I2R15P_sound) (by decide +kernel)
def CB1_2_5I2R15MassTerm : Ball := .exact 0
lemma CB1_2_5I2R15MassTerm_sound : CB1_2_5I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R15Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R15Mass_sound)
def CB1_2_5I2R15H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R15H_sound : CB1_2_5I2R15H.Encloses (homogeneousEntropy CB1_2_5I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R15Value CB1_2_5I2R15MassTerm_sound CB1_2_5I2R15Entropy_sound) (by decide +kernel)
def CB1_2_5I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) 16 a
def CB1_2_5I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 1 2 5)) B1_2_5Law (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) 16 a
lemma CB1_2_5I2R16Raw_sound (a : Fin 6) :
    (CB1_2_5I2R16Raw a).Encloses (CB1_2_5I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u => B1_2_5Little u ((stageBPriority (shape 1 2 5)) 2)) (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) (fun u _ a => B1_2_5Little_sound u ((stageBPriority (shape 1 2 5)) 2) a) 16 a
def CB1_2_5I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB1_2_5I2R16Certificates_valid :
    CB1_2_5I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB1_2_5I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R16Certificates (CB1_2_5I2R16CertificateIndex a)).input
lemma CB1_2_5I2R16P_check : ∀ a : Fin 6, contains (CB1_2_5I2R16Raw a) (CB1_2_5I2R16P a) = true := by
  decide +kernel
lemma CB1_2_5I2R16P_sound (a : Fin 6) :
    (CB1_2_5I2R16P a).Encloses (CB1_2_5I2R16Value a) :=
  contains_sound (CB1_2_5I2R16Raw_sound a) (CB1_2_5I2R16P_check a)
def CB1_2_5I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I2R16Certificates (CB1_2_5I2R16CertificateIndex a)).output
lemma CB1_2_5I2R16Terms_sound (a : Fin 6) :
    (CB1_2_5I2R16Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R16Certificates_valid
    (CB1_2_5I2R16CertificateIndex a) (CB1_2_5I2R16P_sound a)
def CB1_2_5I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R16Entropy_sound : CB1_2_5I2R16Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R16Value CB1_2_5I2R16Terms CB1_2_5I2R16Terms_sound) (by decide +kernel)
def CB1_2_5I2R16Mass : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R16Mass_sound : CB1_2_5I2R16Mass.Encloses (∑ a, CB1_2_5I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB1_2_5I2R16P CB1_2_5I2R16Value CB1_2_5I2R16P_sound) (by decide +kernel)
def CB1_2_5I2R16MassTerm : Ball := .exact 0
lemma CB1_2_5I2R16MassTerm_sound : CB1_2_5I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2R16Value a))) :=
  entropyTerm_zero_ball (CB1_2_5I2R16Mass_sound)
def CB1_2_5I2R16H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2R16H_sound : CB1_2_5I2R16H.Encloses (homogeneousEntropy CB1_2_5I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2R16Value CB1_2_5I2R16MassTerm_sound CB1_2_5I2R16Entropy_sound) (by decide +kernel)
def CB1_2_5I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB1_2_5I2R0H
  | 1 => CB1_2_5I2R1H
  | 2 => CB1_2_5I2R2H
  | 3 => CB1_2_5I2R3H
  | 4 => CB1_2_5I2R4H
  | 5 => CB1_2_5I2R5H
  | 6 => CB1_2_5I2R6H
  | 7 => CB1_2_5I2R7H
  | 8 => CB1_2_5I2R8H
  | 9 => CB1_2_5I2R9H
  | 10 => CB1_2_5I2R10H
  | 11 => CB1_2_5I2R11H
  | 12 => CB1_2_5I2R12H
  | 13 => CB1_2_5I2R13H
  | 14 => CB1_2_5I2R14H
  | 15 => CB1_2_5I2R15H
  | 16 => CB1_2_5I2R16H
  | _ => (.exact 0)
lemma CB1_2_5I2ResidualEntropies_sound (k : Fin 17) :
    (CB1_2_5I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB1_2_5I2R0H_sound
  · exact CB1_2_5I2R1H_sound
  · exact CB1_2_5I2R2H_sound
  · exact CB1_2_5I2R3H_sound
  · exact CB1_2_5I2R4H_sound
  · exact CB1_2_5I2R5H_sound
  · exact CB1_2_5I2R6H_sound
  · exact CB1_2_5I2R7H_sound
  · exact CB1_2_5I2R8H_sound
  · exact CB1_2_5I2R9H_sound
  · exact CB1_2_5I2R10H_sound
  · exact CB1_2_5I2R11H_sound
  · exact CB1_2_5I2R12H_sound
  · exact CB1_2_5I2R13H_sound
  · exact CB1_2_5I2R14H_sound
  · exact CB1_2_5I2R15H_sound
  · exact CB1_2_5I2R16H_sound
def CB1_2_5I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_0_4E_5Log : Ball := .exact 0
lemma CB1_2_5I2S0_0_4E_5Log_sound : CB1_2_5I2S0_0_4E_5Log.Encloses (Real.log (CB1_2_5I2S0_0_4Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (5 : Fin 6))
def CB1_2_5I2S0_0_4E_5 : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_0_4E_5_sound : CB1_2_5I2S0_0_4E_5.Encloses (Foundation.entropyTerm (CB1_2_5I2S0_0_4Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (5 : Fin 6)) CB1_2_5I2S0_0_4E_5Log_sound) (by decide +kernel)
def CB1_2_5I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_2_5I2S0_0_4Terms_sound (a : Fin 6) :
    (CB1_2_5I2S0_0_4Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2S0_0_4Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6)))
  · exact CB1_2_5I2S0_0_4E_5_sound
def CB1_2_5I2S0_0_4Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_0_4Entropy_sound : CB1_2_5I2S0_0_4Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2S0_0_4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2S0_0_4Value CB1_2_5I2S0_0_4Terms CB1_2_5I2S0_0_4Terms_sound) (by decide +kernel)
def CB1_2_5I2S0_0_4Mass : Ball := ⟨1, 0⟩
lemma CB1_2_5I2S0_0_4Mass_sound : CB1_2_5I2S0_0_4Mass.Encloses (∑ a, CB1_2_5I2S0_0_4Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_2_5Little (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2)) CB1_2_5I2S0_0_4Value (B1_2_5Little_sound (shape 0 0 4) ((stageBPriority (shape 1 2 5)) 2))) (by decide +kernel)
def CB1_2_5I2S0_0_4MassTermLog : Ball := .exact 0
lemma CB1_2_5I2S0_0_4MassTermLog_sound : CB1_2_5I2S0_0_4MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2S0_0_4Value a))) := by
  exact log_exact_one_ball (CB1_2_5I2S0_0_4Mass_sound)
def CB1_2_5I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_0_4MassTerm_sound : CB1_2_5I2S0_0_4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2S0_0_4Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2S0_0_4Mass_sound) CB1_2_5I2S0_0_4MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2S0_0_4H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_0_4H_sound : CB1_2_5I2S0_0_4H.Encloses (homogeneousEntropy CB1_2_5I2S0_0_4Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2S0_0_4Value CB1_2_5I2S0_0_4MassTerm_sound CB1_2_5I2S0_0_4Entropy_sound) (by decide +kernel)
def CB1_2_5I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_1_3E_4Log : Ball := .exact 0
lemma CB1_2_5I2S0_1_3E_4Log_sound : CB1_2_5I2S0_1_3E_4Log.Encloses (Real.log (CB1_2_5I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6))
def CB1_2_5I2S0_1_3E_4 : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_1_3E_4_sound : CB1_2_5I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB1_2_5I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6)) CB1_2_5I2S0_1_3E_4Log_sound) (by decide +kernel)
def CB1_2_5I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_2_5I2S0_1_3Terms_sound (a : Fin 6) :
    (CB1_2_5I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (3 : Fin 6)))
  · exact CB1_2_5I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) (5 : Fin 6)))
def CB1_2_5I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_1_3Entropy_sound : CB1_2_5I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2S0_1_3Value CB1_2_5I2S0_1_3Terms CB1_2_5I2S0_1_3Terms_sound) (by decide +kernel)
def CB1_2_5I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB1_2_5I2S0_1_3Mass_sound : CB1_2_5I2S0_1_3Mass.Encloses (∑ a, CB1_2_5I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_2_5Little (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2)) CB1_2_5I2S0_1_3Value (B1_2_5Little_sound (shape 0 1 3) ((stageBPriority (shape 1 2 5)) 2))) (by decide +kernel)
def CB1_2_5I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB1_2_5I2S0_1_3MassTermLog_sound : CB1_2_5I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB1_2_5I2S0_1_3Mass_sound)
def CB1_2_5I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_1_3MassTerm_sound : CB1_2_5I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2S0_1_3Mass_sound) CB1_2_5I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_1_3H_sound : CB1_2_5I2S0_1_3H.Encloses (homogeneousEntropy CB1_2_5I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2S0_1_3Value CB1_2_5I2S0_1_3MassTerm_sound CB1_2_5I2S0_1_3Entropy_sound) (by decide +kernel)
def CB1_2_5I2S0_2_2Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S0_2_2E_2LogWitness : LogWitness := ⟨-1, 180469, 100000⟩
def CB1_2_5I2S0_2_2E_2Log : Ball := ⟨(-2568958716933578869052947578733 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2E_2Log_sound : CB1_2_5I2S0_2_2E_2Log.Encloses (Real.log (CB1_2_5I2S0_2_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (2 : Fin 6)) (w := CB1_2_5I2S0_2_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I2S0_2_2E_2 : Ball := ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2E_2_sound : CB1_2_5I2S0_2_2E_2.Encloses (Foundation.entropyTerm (CB1_2_5I2S0_2_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (2 : Fin 6)) CB1_2_5I2S0_2_2E_2Log_sound) (by decide +kernel)
def CB1_2_5I2S0_2_2E_3LogWitness : LogWitness := ⟨-4, 19531, 12500⟩
def CB1_2_5I2S0_2_2E_3Log : Ball := ⟨(-232631441969328242519371516318041 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2E_3Log_sound : CB1_2_5I2S0_2_2E_3Log.Encloses (Real.log (CB1_2_5I2S0_2_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (3 : Fin 6)) (w := CB1_2_5I2S0_2_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I2S0_2_2E_3 : Ball := ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2E_3_sound : CB1_2_5I2S0_2_2E_3.Encloses (Foundation.entropyTerm (CB1_2_5I2S0_2_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (3 : Fin 6)) CB1_2_5I2S0_2_2E_3Log_sound) (by decide +kernel)
def CB1_2_5I2S0_2_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(9272348213725720898382327931727 / 100000000000000000000000000000000), (38215797243 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(11358811732757374761614612713019 / 50000000000000000000000000000000), (1033962531 / 10000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB1_2_5I2S0_2_2Terms_sound (a : Fin 6) :
    (CB1_2_5I2S0_2_2Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2S0_2_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (1 : Fin 6)))
  · exact CB1_2_5I2S0_2_2E_2_sound
  · exact CB1_2_5I2S0_2_2E_3_sound
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) (5 : Fin 6)))
def CB1_2_5I2S0_2_2Entropy : Ball := ⟨(6397994335848094084322310671553 / 20000000000000000000000000000000), (48555422553 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2Entropy_sound : CB1_2_5I2S0_2_2Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2S0_2_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2S0_2_2Value CB1_2_5I2S0_2_2Terms CB1_2_5I2S0_2_2Terms_sound) (by decide +kernel)
def CB1_2_5I2S0_2_2Mass : Ball := ⟨1, 0⟩
lemma CB1_2_5I2S0_2_2Mass_sound : CB1_2_5I2S0_2_2Mass.Encloses (∑ a, CB1_2_5I2S0_2_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_2_5Little (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2)) CB1_2_5I2S0_2_2Value (B1_2_5Little_sound (shape 0 2 2) ((stageBPriority (shape 1 2 5)) 2))) (by decide +kernel)
def CB1_2_5I2S0_2_2MassTermLog : Ball := .exact 0
lemma CB1_2_5I2S0_2_2MassTermLog_sound : CB1_2_5I2S0_2_2MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2S0_2_2Value a))) := by
  exact log_exact_one_ball (CB1_2_5I2S0_2_2Mass_sound)
def CB1_2_5I2S0_2_2MassTerm : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S0_2_2MassTerm_sound : CB1_2_5I2S0_2_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2S0_2_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2S0_2_2Mass_sound) CB1_2_5I2S0_2_2MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2S0_2_2H : Ball := ⟨(6397994335848094084322310671553 / 20000000000000000000000000000000), (48555422553 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I2S0_2_2H_sound : CB1_2_5I2S0_2_2H.Encloses (homogeneousEntropy CB1_2_5I2S0_2_2Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2S0_2_2Value CB1_2_5I2S0_2_2MassTerm_sound CB1_2_5I2S0_2_2Entropy_sound) (by decide +kernel)
def CB1_2_5I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 1 2 5) (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2) a : ℝ)
def CB1_2_5I2S1_0_3E_4Log : Ball := .exact 0
lemma CB1_2_5I2S1_0_3E_4Log_sound : CB1_2_5I2S1_0_3E_4Log.Encloses (Real.log (CB1_2_5I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6))
def CB1_2_5I2S1_0_3E_4 : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S1_0_3E_4_sound : CB1_2_5I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB1_2_5I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (4 : Fin 6)) CB1_2_5I2S1_0_3E_4Log_sound) (by decide +kernel)
def CB1_2_5I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB1_2_5I2S1_0_3Terms_sound (a : Fin 6) :
    (CB1_2_5I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (3 : Fin 6)))
  · exact CB1_2_5I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) (5 : Fin 6)))
def CB1_2_5I2S1_0_3Entropy : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S1_0_3Entropy_sound : CB1_2_5I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2S1_0_3Value CB1_2_5I2S1_0_3Terms CB1_2_5I2S1_0_3Terms_sound) (by decide +kernel)
def CB1_2_5I2S1_0_3Mass : Ball := ⟨1, 0⟩
lemma CB1_2_5I2S1_0_3Mass_sound : CB1_2_5I2S1_0_3Mass.Encloses (∑ a, CB1_2_5I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B1_2_5Little (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2)) CB1_2_5I2S1_0_3Value (B1_2_5Little_sound (shape 1 0 3) ((stageBPriority (shape 1 2 5)) 2))) (by decide +kernel)
def CB1_2_5I2S1_0_3MassTermLog : Ball := .exact 0
lemma CB1_2_5I2S1_0_3MassTermLog_sound : CB1_2_5I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB1_2_5I2S1_0_3Mass_sound)
def CB1_2_5I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S1_0_3MassTerm_sound : CB1_2_5I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I2S1_0_3Mass_sound) CB1_2_5I2S1_0_3MassTermLog_sound) (by decide +kernel)
def CB1_2_5I2S1_0_3H : Ball := ⟨0, 0⟩
lemma CB1_2_5I2S1_0_3H_sound : CB1_2_5I2S1_0_3H.Encloses (homogeneousEntropy CB1_2_5I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I2S1_0_3Value CB1_2_5I2S1_0_3MassTerm_sound CB1_2_5I2S1_0_3Entropy_sound) (by decide +kernel)
def CB1_2_5I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB1_2_5I2S0_0_4H
  | 0, 1, 3 => CB1_2_5I2S0_1_3H
  | 0, 2, 2 => CB1_2_5I2S0_2_2H
  | 1, 0, 3 => CB1_2_5I2S1_0_3H
  | _, _, _ => (.exact 0)
lemma CB1_2_5I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 2 5))
    (hd : designated (stageBPriority (shape 1 2 5)) 2 u) :
    (CB1_2_5I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) u)) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB1_2_5I2S0_0_4H_sound
  · exact CB1_2_5I2S0_1_3H_sound
  · exact CB1_2_5I2S0_2_2H_sound
  · exact CB1_2_5I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 1 2 5)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (stageBPriority (shape 1 2 5)) 2 (shape 1 2 1) by decide +kernel) hd |>.elim
def CB1_2_5I2Singleton : Ball := ⟨(1455231344023407159119860932703 / 25000000000000000000000000000000), (883519043 / 10000000000000000000000000000000)⟩
lemma CB1_2_5I2Singleton_sound : CB1_2_5I2Singleton.Encloses
    (singletonEntropy (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2
    CB1_2_5I2Singles (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ)) (fun u _ => B1_2_5Law_sound u) CB1_2_5I2Singles_sound) (by decide +kernel)
def CB1_2_5I2Group : Ball := ⟨(1455231344023407159119860932703 / 25000000000000000000000000000000), (3094997651 / 6250000000000000000000000000000)⟩
lemma CB1_2_5I2Group_sound : CB1_2_5I2Group.Encloses
    (groupedEntropy (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (stageBPriority (shape 1 2 5)) 2 (fun u a => (littleLaw (shape 1 2 5) u ((stageBPriority (shape 1 2 5)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB1_2_5I2Singleton_sound
    (finSumBall_sound 17 CB1_2_5I2ResidualEntropies _ CB1_2_5I2ResidualEntropies_sound)) (by decide +kernel)

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
def CB1_2_5I2H : Ball := ⟨(37054980891788625436069480215921 / 50000000000000000000000000000000), (37405962081 / 20000000000000000000000000000000)⟩
lemma CB1_2_5I2_sound : CB1_2_5I2H.Encloses (stageBCapacity (shape 1 2 5) 2) := by
  have hb := contains_sound (Ball.add_sound CB1_2_5I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB1_2_5I2Group_sound)))
    (show contains (.add CB1_2_5I2PairH (.neg (.mul (.exact 2) CB1_2_5I2Group))) CB1_2_5I2H = true by decide +kernel)
  unfold CB1_2_5I2PairValue at hb
  simpa only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
