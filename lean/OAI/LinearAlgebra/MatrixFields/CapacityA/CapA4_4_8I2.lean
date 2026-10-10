import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA4_4_8I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_4_8I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA4_4_8I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA4_4_8I2R0Raw_sound (a : PairSlot) :
    (CA4_4_8I2R0Raw a).Encloses (CA4_4_8I2R0Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA4_4_8I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(100885900988501493060513433 / 100000000000000000000000000000000), (32159 / 100000000000000000000000000000000)⟩ ⟨(-415428107682506870021708107576163 / 25000000000000000000000000000000), (6617650791 / 1250000000000000000000000000000)⟩ ⟨-24, 3035600478242196747209827, 2980232238769531250000000⟩]
lemma CA4_4_8I2R0Certificates_valid :
    CA4_4_8I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_4_8I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R0Certificates (CA4_4_8I2R0CertificateIndex a)).input
lemma CA4_4_8I2R0P_check : ∀ a : PairSlot, contains (CA4_4_8I2R0Raw a) (CA4_4_8I2R0P a) = true := by
  decide +kernel
lemma CA4_4_8I2R0P_sound (a : PairSlot) :
    (CA4_4_8I2R0P a).Encloses (CA4_4_8I2R0Value a) :=
  contains_sound (CA4_4_8I2R0Raw_sound a) (CA4_4_8I2R0P_check a)
def CA4_4_8I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R0Certificates (CA4_4_8I2R0CertificateIndex a)).output
lemma CA4_4_8I2R0Terms_sound (a : PairSlot) :
    (CA4_4_8I2R0Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R0Certificates_valid
    (CA4_4_8I2R0CertificateIndex a) (CA4_4_8I2R0P_sound a)
def CA4_4_8I2R0Entropy : Ball := ⟨(100885900988501493060513433 / 100000000000000000000000000000000), (32159 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R0Entropy_sound : CA4_4_8I2R0Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R0Value CA4_4_8I2R0Terms CA4_4_8I2R0Terms_sound) (by decide +kernel)
def CA4_4_8I2R0Mass : Ball := ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R0Mass_sound : CA4_4_8I2R0Mass.Encloses (∑ a, CA4_4_8I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R0P CA4_4_8I2R0Value CA4_4_8I2R0P_sound) (by decide +kernel)
def CA4_4_8I2R0MassTermLogWitness : LogWitness := ⟨-24, 3035600478242196747209827, 2980232238769531250000000⟩
def CA4_4_8I2R0MassTermLog : Ball := ⟨(-415428107682506870021708107576163 / 25000000000000000000000000000000), (6617650791 / 1250000000000000000000000000000)⟩
lemma CA4_4_8I2R0MassTermLog_sound : CA4_4_8I2R0MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R0Mass_sound) (w := CA4_4_8I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R0MassTerm : Ball := ⟨(100885900988501493060513433 / 100000000000000000000000000000000), (32159 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R0MassTerm_sound : CA4_4_8I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R0Mass_sound) CA4_4_8I2R0MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R0H : Ball := ⟨0, (32159 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R0H_sound : CA4_4_8I2R0H.Encloses (homogeneousEntropy CA4_4_8I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R0Value CA4_4_8I2R0MassTerm_sound CA4_4_8I2R0Entropy_sound) (by decide +kernel)
def CA4_4_8I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA4_4_8I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA4_4_8I2R1Raw_sound (a : PairSlot) :
    (CA4_4_8I2R1Raw a).Encloses (CA4_4_8I2R1Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA4_4_8I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(809072654081018314756371891 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(8364595743039152683402561227 / 25000000000000000000000000000000), (10965003 / 100000000000000000000000000000000)⟩ ⟨(-1033849766253692344627325607201383 / 100000000000000000000000000000000), (169406620363 / 50000000000000000000000000000000)⟩ ⟨-15, 809072654081018314756371891, 762939453125000000000000000⟩]
lemma CA4_4_8I2R1Certificates_valid :
    CA4_4_8I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA4_4_8I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R1Certificates (CA4_4_8I2R1CertificateIndex a)).input
lemma CA4_4_8I2R1P_check : ∀ a : PairSlot, contains (CA4_4_8I2R1Raw a) (CA4_4_8I2R1P a) = true := by
  decide +kernel
lemma CA4_4_8I2R1P_sound (a : PairSlot) :
    (CA4_4_8I2R1P a).Encloses (CA4_4_8I2R1Value a) :=
  contains_sound (CA4_4_8I2R1Raw_sound a) (CA4_4_8I2R1P_check a)
def CA4_4_8I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R1Certificates (CA4_4_8I2R1CertificateIndex a)).output
lemma CA4_4_8I2R1Terms_sound (a : PairSlot) :
    (CA4_4_8I2R1Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R1Certificates_valid
    (CA4_4_8I2R1CertificateIndex a) (CA4_4_8I2R1P_sound a)
def CA4_4_8I2R1Entropy : Ball := ⟨(8364595743039152683402561227 / 12500000000000000000000000000000), (10965003 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R1Entropy_sound : CA4_4_8I2R1Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R1Value CA4_4_8I2R1Terms CA4_4_8I2R1Terms_sound) (by decide +kernel)
def CA4_4_8I2R1Mass : Ball := ⟨(809072654081018314756371891 / 12500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I2R1Mass_sound : CA4_4_8I2R1Mass.Encloses (∑ a, CA4_4_8I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R1P CA4_4_8I2R1Value CA4_4_8I2R1P_sound) (by decide +kernel)
def CA4_4_8I2R1MassTermLogWitness : LogWitness := ⟨-14, 809072654081018314756371891, 762939453125000000000000000⟩
def CA4_4_8I2R1MassTermLog : Ball := ⟨(-964535048197697813685602414151053 / 100000000000000000000000000000000), (317637417043 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R1MassTermLog_sound : CA4_4_8I2R1MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R1Mass_sound) (w := CA4_4_8I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R1MassTerm : Ball := ⟨(12486062902391588654992660491 / 20000000000000000000000000000000), (20559379 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R1MassTerm_sound : CA4_4_8I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R1Mass_sound) CA4_4_8I2R1MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R1H : Ball := ⟨(4486451432355278192257187361 / 100000000000000000000000000000000), (8497877 / 20000000000000000000000000000000)⟩
lemma CA4_4_8I2R1H_sound : CA4_4_8I2R1H.Encloses (homogeneousEntropy CA4_4_8I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R1Value CA4_4_8I2R1MassTerm_sound CA4_4_8I2R1Entropy_sound) (by decide +kernel)
def CA4_4_8I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA4_4_8I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA4_4_8I2R2Raw_sound (a : PairSlot) :
    (CA4_4_8I2R2Raw a).Encloses (CA4_4_8I2R2Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA4_4_8I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(144056175636722908392748111579 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(235629882179052930029979856781 / 25000000000000000000000000000000), (67111183 / 20000000000000000000000000000000)⟩ ⟨(-327136106643922294503498786915473 / 50000000000000000000000000000000), (232934061901 / 100000000000000000000000000000000)⟩ ⟨-10, 144056175636722908392748111579, 97656250000000000000000000000⟩,
   .log ⟨(325539556588240870788601551 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4776035556690193219567774997 / 5000000000000000000000000000000), (33089139 / 100000000000000000000000000000000)⟩ ⟨(-916946086127093913138421118852279 / 100000000000000000000000000000000), (79409341211 / 25000000000000000000000000000000)⟩ ⟨-14, 325539556588240870788601551, 190734863281250000000000000⟩,
   .log ⟨(527409107345197692454915661913 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(110649353178165597293078182089 / 4000000000000000000000000000000), (502574521 / 50000000000000000000000000000000)⟩ ⟨(-524494892281713229333103824387583 / 100000000000000000000000000000000), (47645603571 / 25000000000000000000000000000000)⟩ ⟨-8, 527409107345197692454915661913, 390625000000000000000000000000⟩]
lemma CA4_4_8I2R2Certificates_valid :
    CA4_4_8I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_4_8I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R2Certificates (CA4_4_8I2R2CertificateIndex a)).input
lemma CA4_4_8I2R2P_check : ∀ a : PairSlot, contains (CA4_4_8I2R2Raw a) (CA4_4_8I2R2P a) = true := by
  decide +kernel
lemma CA4_4_8I2R2P_sound (a : PairSlot) :
    (CA4_4_8I2R2P a).Encloses (CA4_4_8I2R2Value a) :=
  contains_sound (CA4_4_8I2R2Raw_sound a) (CA4_4_8I2R2P_check a)
def CA4_4_8I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R2Certificates (CA4_4_8I2R2CertificateIndex a)).output
lemma CA4_4_8I2R2Terms_sound (a : PairSlot) :
    (CA4_4_8I2R2Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R2Certificates_valid
    (CA4_4_8I2R2CertificateIndex a) (CA4_4_8I2R2P_sound a)
def CA4_4_8I2R2Entropy : Ball := ⟨(4842314309154171101349504406353 / 100000000000000000000000000000000), (34848783 / 2000000000000000000000000000000)⟩
lemma CA4_4_8I2R2Entropy_sound : CA4_4_8I2R2Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R2Value CA4_4_8I2R2Terms CA4_4_8I2R2Terms_sound) (by decide +kernel)
def CA4_4_8I2R2Mass : Ball := ⟨(167271198048058184994176476867 / 20000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I2R2Mass_sound : CA4_4_8I2R2Mass.Encloses (∑ a, CA4_4_8I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R2P CA4_4_8I2R2Value CA4_4_8I2R2P_sound) (by decide +kernel)
def CA4_4_8I2R2MassTermLogWitness : LogWitness := ⟨-7, 167271198048058184994176476867, 156250000000000000000000000000⟩
def CA4_4_8I2R2MassTermLog : Ball := ⟨(-1913548446750902621982351257567 / 400000000000000000000000000000), (84703295449 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R2MassTermLog_sound : CA4_4_8I2R2MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R2Mass_sound) (w := CA4_4_8I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R2MassTerm : Ball := ⟨(250063704071112776882502314991 / 6250000000000000000000000000000), (1416842229 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R2MassTerm_sound : CA4_4_8I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R2Mass_sound) CA4_4_8I2R2MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R2H : Ball := ⟨(841295044016366671229467366497 / 100000000000000000000000000000000), (3159281379 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R2H_sound : CA4_4_8I2R2H.Encloses (homogeneousEntropy CA4_4_8I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R2Value CA4_4_8I2R2MassTerm_sound CA4_4_8I2R2Entropy_sound) (by decide +kernel)
def CA4_4_8I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA4_4_8I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA4_4_8I2R3Raw_sound (a : PairSlot) :
    (CA4_4_8I2R3Raw a).Encloses (CA4_4_8I2R3Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA4_4_8I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(231085541255582019869870639891 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1402721013040971449198777249589 / 100000000000000000000000000000000), (489342689 / 100000000000000000000000000000000)⟩ ⟨(-151753437863249246125196915349431 / 25000000000000000000000000000000), (211758238127 / 100000000000000000000000000000000)⟩ ⟨-9, 231085541255582019869870639891, 195312500000000000000000000000⟩,
   .log ⟨(8143462990423164618805902263813 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩ ⟨(20423436017617139668532376373777 / 100000000000000000000000000000000), (4311113487 / 50000000000000000000000000000000)⟩ ⟨(-250795466764390145372495411941297 / 100000000000000000000000000000000), (105879118943 / 100000000000000000000000000000000)⟩ ⟨-4, 8143462990423164618805902263813, 6250000000000000000000000000000⟩,
   .log ⟨(105117771726331581854672918031 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(2300628469079708160672363099159 / 100000000000000000000000000000000), (200335991 / 25000000000000000000000000000000)⟩ ⟨(-109430994935341172217633508801731 / 20000000000000000000000000000000), (9529120693 / 5000000000000000000000000000000)⟩ ⟨-8, 105117771726331581854672918031, 97656250000000000000000000000⟩]
lemma CA4_4_8I2R3Certificates_valid :
    CA4_4_8I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_4_8I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R3Certificates (CA4_4_8I2R3CertificateIndex a)).input
lemma CA4_4_8I2R3P_check : ∀ a : PairSlot, contains (CA4_4_8I2R3Raw a) (CA4_4_8I2R3P a) = true := by
  decide +kernel
lemma CA4_4_8I2R3P_sound (a : PairSlot) :
    (CA4_4_8I2R3P a).Encloses (CA4_4_8I2R3Value a) :=
  contains_sound (CA4_4_8I2R3Raw_sound a) (CA4_4_8I2R3P_check a)
def CA4_4_8I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R3Certificates (CA4_4_8I2R3CertificateIndex a)).output
lemma CA4_4_8I2R3Terms_sound (a : PairSlot) :
    (CA4_4_8I2R3Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R3Certificates_valid
    (CA4_4_8I2R3CertificateIndex a) (CA4_4_8I2R3P_sound a)
def CA4_4_8I2R3Entropy : Ball := ⟨(965071419989512771136140668901 / 2000000000000000000000000000000), (9912913627 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R3Entropy_sound : CA4_4_8I2R3Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R3Value CA4_4_8I2R3Terms CA4_4_8I2R3Terms_sound) (by decide +kernel)
def CA4_4_8I2R3Mass : Ball := ⟨(2198754904646018241523616143957 / 12500000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R3Mass_sound : CA4_4_8I2R3Mass.Encloses (∑ a, CA4_4_8I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R3P CA4_4_8I2R3Value CA4_4_8I2R3P_sound) (by decide +kernel)
def CA4_4_8I2R3MassTermLogWitness : LogWitness := ⟨-3, 2198754904646018241523616143957, 1562500000000000000000000000000⟩
def CA4_4_8I2R3MassTermLog : Ball := ⟨(-173783739658914282888710670776333 / 100000000000000000000000000000000), (10587911911 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I2R3MassTermLog_sound : CA4_4_8I2R3MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R3Mass_sound) (w := CA4_4_8I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R3MassTerm : Ball := ⟨(30568627993821162617363647220061 / 100000000000000000000000000000000), (14899343047 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R3MassTerm_sound : CA4_4_8I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R3Mass_sound) CA4_4_8I2R3MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R3H : Ball := ⟨(17684943005654475939443386224989 / 100000000000000000000000000000000), (34725170301 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R3H_sound : CA4_4_8I2R3H.Encloses (homogeneousEntropy CA4_4_8I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R3Value CA4_4_8I2R3MassTerm_sound CA4_4_8I2R3Entropy_sound) (by decide +kernel)
def CA4_4_8I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA4_4_8I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA4_4_8I2R4Raw_sound (a : PairSlot) :
    (CA4_4_8I2R4Raw a).Encloses (CA4_4_8I2R4Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA4_4_8I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(13403335035357123995044009011 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(956185547634562661408467281 / 800000000000000000000000000000), (39735743 / 100000000000000000000000000000000)⟩ ⟨(-44587109528720255309049705569641 / 5000000000000000000000000000000), (148230769511 / 50000000000000000000000000000000)⟩ ⟨-13, 13403335035357123995044009011, 12207031250000000000000000000⟩,
   .log ⟨(913523187809309878302768426799 / 20000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(14096479448211469622923358799501 / 100000000000000000000000000000000), (2901690947 / 50000000000000000000000000000000)⟩ ⟨(-154308939677993030556111997454381 / 50000000000000000000000000000000), (127054942667 / 100000000000000000000000000000000)⟩ ⟨-5, 913523187809309878302768426799, 625000000000000000000000000000⟩,
   .log ⟨(47338644618955604669010009940067 / 100000000000000000000000000000000), (187 / 100000000000000000000000000000000)⟩ ⟨(1770094204759252533873753877557 / 5000000000000000000000000000000), (30073044083 / 100000000000000000000000000000000)⟩ ⟨(-18696080327260378709560136191337 / 25000000000000000000000000000000), (15881867861 / 25000000000000000000000000000000)⟩ ⟨-2, 47338644618955604669010009940067, 25000000000000000000000000000000⟩,
   .log ⟨(2194750548526808701414581112929 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(4190987875598734809524401416881 / 50000000000000000000000000000000), (3253295599 / 100000000000000000000000000000000)⟩ ⟨(-190955089561857887364725130187723 / 50000000000000000000000000000000), (74115383141 / 50000000000000000000000000000000)⟩ ⟨-6, 2194750548526808701414581112929, 1562500000000000000000000000000⟩,
   .log ⟨(5482600270839383620453587239 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(74734571046284442454206984143 / 10000000000000000000000000000000), (51083377 / 20000000000000000000000000000000)⟩ ⟨(-340780685050939403276333226608717 / 50000000000000000000000000000000), (909898681 / 390625000000000000000000000000)⟩ ⟨-10, 5482600270839383620453587239, 4882812500000000000000000000⟩]
lemma CA4_4_8I2R4Certificates_valid :
    CA4_4_8I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CA4_4_8I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R4Certificates (CA4_4_8I2R4CertificateIndex a)).input
lemma CA4_4_8I2R4P_check : ∀ a : PairSlot, contains (CA4_4_8I2R4Raw a) (CA4_4_8I2R4P a) = true := by
  decide +kernel
lemma CA4_4_8I2R4P_sound (a : PairSlot) :
    (CA4_4_8I2R4P a).Encloses (CA4_4_8I2R4Value a) :=
  contains_sound (CA4_4_8I2R4Raw_sound a) (CA4_4_8I2R4P_check a)
def CA4_4_8I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R4Certificates (CA4_4_8I2R4CertificateIndex a)).output
lemma CA4_4_8I2R4Terms_sound (a : PairSlot) :
    (CA4_4_8I2R4Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R4Certificates_valid
    (CA4_4_8I2R4CertificateIndex a) (CA4_4_8I2R4P_sound a)
def CA4_4_8I2R4Entropy : Ball := ⟨(40672593295687207125656793739673 / 50000000000000000000000000000000), (606516093 / 1250000000000000000000000000000)⟩
lemma CA4_4_8I2R4Entropy_sound : CA4_4_8I2R4Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R4Value CA4_4_8I2R4Terms CA4_4_8I2R4Terms_sound) (by decide +kernel)
def CA4_4_8I2R4Mass : Ball := ⟨(60999836269589822775266016196717 / 100000000000000000000000000000000), (53 / 20000000000000000000000000000000)⟩
lemma CA4_4_8I2R4Mass_sound : CA4_4_8I2R4Mass.Encloses (∑ a, CA4_4_8I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R4P CA4_4_8I2R4Value CA4_4_8I2R4P_sound) (by decide +kernel)
def CA4_4_8I2R4MassTermLogWitness : LogWitness := ⟨-1, 60999836269589822775266016196717, 50000000000000000000000000000000⟩
def CA4_4_8I2R4MassTermLog : Ball := ⟨(-24714950296173360416017773017097 / 50000000000000000000000000000000), (211758239 / 500000000000000000000000000000)⟩
lemma CA4_4_8I2R4MassTermLog_sound : CA4_4_8I2R4MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R4Mass_sound) (w := CA4_4_8I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R4MassTerm : Ball := ⟨(942254950923515926994287812149 / 3125000000000000000000000000000), (25834435947 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R4MassTerm_sound : CA4_4_8I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R4Mass_sound) CA4_4_8I2R4MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R4H : Ball := ⟨(25596514080910952293748188745289 / 50000000000000000000000000000000), (74355723387 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R4H_sound : CA4_4_8I2R4H.Encloses (homogeneousEntropy CA4_4_8I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R4Value CA4_4_8I2R4MassTerm_sound CA4_4_8I2R4Entropy_sound) (by decide +kernel)
def CA4_4_8I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA4_4_8I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA4_4_8I2R5Raw_sound (a : PairSlot) :
    (CA4_4_8I2R5Raw a).Encloses (CA4_4_8I2R5Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA4_4_8I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6093665150867149565350245629 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27459665581402125750187161693 / 25000000000000000000000000000000), (9677881 / 25000000000000000000000000000000)⟩ ⟨(-450626427635173236284494854820431 / 50000000000000000000000000000000), (6352747269 / 2000000000000000000000000000000)⟩ ⟨-14, 6093665150867149565350245629, 3051757812500000000000000000⟩,
   .log ⟨(897023998498120010140493588531 / 12500000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(3780993911075951227238194369531 / 20000000000000000000000000000000), (1899522237 / 25000000000000000000000000000000)⟩ ⟨(-16465008171318605507518053250799 / 6250000000000000000000000000000), (10587911893 / 10000000000000000000000000000000)⟩ ⟨-4, 897023998498120010140493588531, 781250000000000000000000000000⟩,
   .log ⟨(134656865576371148188256119323 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(15935424030593622966483144189 / 1000000000000000000000000000000), (570294023 / 100000000000000000000000000000000)⟩ ⟨(-591704847813934419974362172129767 / 100000000000000000000000000000000), (52939559393 / 25000000000000000000000000000000)⟩ ⟨-9, 134656865576371148188256119323, 97656250000000000000000000000⟩]
lemma CA4_4_8I2R5Certificates_valid :
    CA4_4_8I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA4_4_8I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R5Certificates (CA4_4_8I2R5CertificateIndex a)).input
lemma CA4_4_8I2R5P_check : ∀ a : PairSlot, contains (CA4_4_8I2R5Raw a) (CA4_4_8I2R5P a) = true := by
  decide +kernel
lemma CA4_4_8I2R5P_sound (a : PairSlot) :
    (CA4_4_8I2R5P a).Encloses (CA4_4_8I2R5Value a) :=
  contains_sound (CA4_4_8I2R5Raw_sound a) (CA4_4_8I2R5P_check a)
def CA4_4_8I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R5Certificates (CA4_4_8I2R5CertificateIndex a)).output
lemma CA4_4_8I2R5Terms_sound (a : PairSlot) :
    (CA4_4_8I2R5Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R5Certificates_valid
    (CA4_4_8I2R5CertificateIndex a) (CA4_4_8I2R5P_sound a)
def CA4_4_8I2R5Entropy : Ball := ⟨(20608350620764726935840034913327 / 50000000000000000000000000000000), (1641418899 / 10000000000000000000000000000000)⟩
lemma CA4_4_8I2R5Entropy_sound : CA4_4_8I2R5Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R5Value CA4_4_8I2R5Terms CA4_4_8I2R5Terms_sound) (by decide +kernel)
def CA4_4_8I2R5Mass : Ball := ⟨(932211631179929584578895179769 / 6250000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
lemma CA4_4_8I2R5Mass_sound : CA4_4_8I2R5Mass.Encloses (∑ a, CA4_4_8I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R5P CA4_4_8I2R5Value CA4_4_8I2R5P_sound) (by decide +kernel)
def CA4_4_8I2R5MassTermLogWitness : LogWitness := ⟨-3, 932211631179929584578895179769, 781250000000000000000000000000⟩
def CA4_4_8I2R5MassTermLog : Ball := ⟨(-2973088877719296093409086138257 / 1562500000000000000000000000000), (21175823817 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I2R5MassTermLog_sound : CA4_4_8I2R5MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R5Mass_sound) (w := CA4_4_8I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R5MassTerm : Ball := ⟨(28380651851178098873272106745451 / 100000000000000000000000000000000), (12633823681 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R5MassTerm_sound : CA4_4_8I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R5Mass_sound) CA4_4_8I2R5MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R5H : Ball := ⟨(12836049390351354998407963081203 / 100000000000000000000000000000000), (29048012671 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R5H_sound : CA4_4_8I2R5H.Encloses (homogeneousEntropy CA4_4_8I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R5Value CA4_4_8I2R5MassTerm_sound CA4_4_8I2R5Entropy_sound) (by decide +kernel)
def CA4_4_8I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA4_4_8I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA4_4_8I2R6Raw_sound (a : PairSlot) :
    (CA4_4_8I2R6Raw a).Encloses (CA4_4_8I2R6Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA4_4_8I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1054220569280610738843304011 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(5310019086066608398805522157 / 12500000000000000000000000000000), (2857473 / 20000000000000000000000000000000)⟩ ⟨(-201476588137152768544991639014469 / 20000000000000000000000000000000), (169406601321 / 50000000000000000000000000000000)⟩ ⟨-15, 1054220569280610738843304011, 762939453125000000000000000⟩,
   .log ⟨(265680321318957000479543 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1049232282837749481896411 / 20000000000000000000000000000000), (171 / 10000000000000000000000000000000)⟩ ⟨(-394922844728915929810464907407031 / 20000000000000000000000000000000), (635651102687 / 100000000000000000000000000000000)⟩ ⟨-29, 265680321318957000479543, 186264514923095703125000⟩,
   .log ⟨(442175225215818692390443759141 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1198564415727487612447426992829 / 50000000000000000000000000000000), (842708241 / 100000000000000000000000000000000)⟩ ⟨(-542121922431310976489391241826871 / 100000000000000000000000000000000), (190582414051 / 100000000000000000000000000000000)⟩ ⟨-8, 442175225215818692390443759141, 390625000000000000000000000000⟩]
lemma CA4_4_8I2R6Certificates_valid :
    CA4_4_8I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA4_4_8I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R6Certificates (CA4_4_8I2R6CertificateIndex a)).input
lemma CA4_4_8I2R6P_check : ∀ a : PairSlot, contains (CA4_4_8I2R6Raw a) (CA4_4_8I2R6P a) = true := by
  decide +kernel
lemma CA4_4_8I2R6P_sound (a : PairSlot) :
    (CA4_4_8I2R6P a).Encloses (CA4_4_8I2R6Value a) :=
  contains_sound (CA4_4_8I2R6Raw_sound a) (CA4_4_8I2R6P_check a)
def CA4_4_8I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R6Certificates (CA4_4_8I2R6CertificateIndex a)).output
lemma CA4_4_8I2R6Terms_sound (a : PairSlot) :
    (CA4_4_8I2R6Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R6Certificates_valid
    (CA4_4_8I2R6CertificateIndex a) (CA4_4_8I2R6P_sound a)
def CA4_4_8I2R6Entropy : Ball := ⟨(62052490728871733419264032607 / 2500000000000000000000000000000), (871286391 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R6Entropy_sound : CA4_4_8I2R6Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R6Value CA4_4_8I2R6Terms CA4_4_8I2R6Terms_sound) (by decide +kernel)
def CA4_4_8I2R6Mass : Ball := ⟨(90121904226141243243038230063 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
lemma CA4_4_8I2R6Mass_sound : CA4_4_8I2R6Mass.Encloses (∑ a, CA4_4_8I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R6P CA4_4_8I2R6Value CA4_4_8I2R6P_sound) (by decide +kernel)
def CA4_4_8I2R6MassTermLogWitness : LogWitness := ⟨-8, 90121904226141243243038230063, 78125000000000000000000000000⟩
def CA4_4_8I2R6MassTermLog : Ball := ⟨(-270116215365013740043416369183291 / 50000000000000000000000000000000), (95291207461 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R6MassTermLog_sound : CA4_4_8I2R6MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I2R6Mass_sound) (w := CA4_4_8I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I2R6MassTerm : Ball := ⟨(2434338769105351000162219863469 / 100000000000000000000000000000000), (858782551 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2R6MassTerm_sound : CA4_4_8I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I2R6Mass_sound) CA4_4_8I2R6MassTermLog_sound) (by decide +kernel)
def CA4_4_8I2R6H : Ball := ⟨(47760860049518336608341440811 / 100000000000000000000000000000000), (865034471 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2R6H_sound : CA4_4_8I2R6H.Encloses (homogeneousEntropy CA4_4_8I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R6Value CA4_4_8I2R6MassTerm_sound CA4_4_8I2R6Entropy_sound) (by decide +kernel)
def CA4_4_8I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA4_4_8I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA4_4_8I2R7Raw_sound (a : PairSlot) :
    (CA4_4_8I2R7Raw a).Encloses (CA4_4_8I2R7Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA4_4_8I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R7Certificates_valid :
    CA4_4_8I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R7Certificates (CA4_4_8I2R7CertificateIndex a)).input
lemma CA4_4_8I2R7P_check : ∀ a : PairSlot, contains (CA4_4_8I2R7Raw a) (CA4_4_8I2R7P a) = true := by
  decide +kernel
lemma CA4_4_8I2R7P_sound (a : PairSlot) :
    (CA4_4_8I2R7P a).Encloses (CA4_4_8I2R7Value a) :=
  contains_sound (CA4_4_8I2R7Raw_sound a) (CA4_4_8I2R7P_check a)
def CA4_4_8I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R7Certificates (CA4_4_8I2R7CertificateIndex a)).output
lemma CA4_4_8I2R7Terms_sound (a : PairSlot) :
    (CA4_4_8I2R7Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R7Certificates_valid
    (CA4_4_8I2R7CertificateIndex a) (CA4_4_8I2R7P_sound a)
def CA4_4_8I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R7Entropy_sound : CA4_4_8I2R7Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R7Value CA4_4_8I2R7Terms CA4_4_8I2R7Terms_sound) (by decide +kernel)
def CA4_4_8I2R7Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R7Mass_sound : CA4_4_8I2R7Mass.Encloses (∑ a, CA4_4_8I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R7P CA4_4_8I2R7Value CA4_4_8I2R7P_sound) (by decide +kernel)
def CA4_4_8I2R7MassTerm : Ball := .exact 0
lemma CA4_4_8I2R7MassTerm_sound : CA4_4_8I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R7Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R7Mass_sound)
def CA4_4_8I2R7H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R7H_sound : CA4_4_8I2R7H.Encloses (homogeneousEntropy CA4_4_8I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R7Value CA4_4_8I2R7MassTerm_sound CA4_4_8I2R7Entropy_sound) (by decide +kernel)
def CA4_4_8I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA4_4_8I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA4_4_8I2R8Raw_sound (a : PairSlot) :
    (CA4_4_8I2R8Raw a).Encloses (CA4_4_8I2R8Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA4_4_8I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R8Certificates_valid :
    CA4_4_8I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R8Certificates (CA4_4_8I2R8CertificateIndex a)).input
lemma CA4_4_8I2R8P_check : ∀ a : PairSlot, contains (CA4_4_8I2R8Raw a) (CA4_4_8I2R8P a) = true := by
  decide +kernel
lemma CA4_4_8I2R8P_sound (a : PairSlot) :
    (CA4_4_8I2R8P a).Encloses (CA4_4_8I2R8Value a) :=
  contains_sound (CA4_4_8I2R8Raw_sound a) (CA4_4_8I2R8P_check a)
def CA4_4_8I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R8Certificates (CA4_4_8I2R8CertificateIndex a)).output
lemma CA4_4_8I2R8Terms_sound (a : PairSlot) :
    (CA4_4_8I2R8Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R8Certificates_valid
    (CA4_4_8I2R8CertificateIndex a) (CA4_4_8I2R8P_sound a)
def CA4_4_8I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R8Entropy_sound : CA4_4_8I2R8Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R8Value CA4_4_8I2R8Terms CA4_4_8I2R8Terms_sound) (by decide +kernel)
def CA4_4_8I2R8Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R8Mass_sound : CA4_4_8I2R8Mass.Encloses (∑ a, CA4_4_8I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R8P CA4_4_8I2R8Value CA4_4_8I2R8P_sound) (by decide +kernel)
def CA4_4_8I2R8MassTerm : Ball := .exact 0
lemma CA4_4_8I2R8MassTerm_sound : CA4_4_8I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R8Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R8Mass_sound)
def CA4_4_8I2R8H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R8H_sound : CA4_4_8I2R8H.Encloses (homogeneousEntropy CA4_4_8I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R8Value CA4_4_8I2R8MassTerm_sound CA4_4_8I2R8Entropy_sound) (by decide +kernel)
def CA4_4_8I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA4_4_8I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA4_4_8I2R9Raw_sound (a : PairSlot) :
    (CA4_4_8I2R9Raw a).Encloses (CA4_4_8I2R9Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA4_4_8I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R9Certificates_valid :
    CA4_4_8I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R9Certificates (CA4_4_8I2R9CertificateIndex a)).input
lemma CA4_4_8I2R9P_check : ∀ a : PairSlot, contains (CA4_4_8I2R9Raw a) (CA4_4_8I2R9P a) = true := by
  decide +kernel
lemma CA4_4_8I2R9P_sound (a : PairSlot) :
    (CA4_4_8I2R9P a).Encloses (CA4_4_8I2R9Value a) :=
  contains_sound (CA4_4_8I2R9Raw_sound a) (CA4_4_8I2R9P_check a)
def CA4_4_8I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R9Certificates (CA4_4_8I2R9CertificateIndex a)).output
lemma CA4_4_8I2R9Terms_sound (a : PairSlot) :
    (CA4_4_8I2R9Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R9Certificates_valid
    (CA4_4_8I2R9CertificateIndex a) (CA4_4_8I2R9P_sound a)
def CA4_4_8I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R9Entropy_sound : CA4_4_8I2R9Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R9Value CA4_4_8I2R9Terms CA4_4_8I2R9Terms_sound) (by decide +kernel)
def CA4_4_8I2R9Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R9Mass_sound : CA4_4_8I2R9Mass.Encloses (∑ a, CA4_4_8I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R9P CA4_4_8I2R9Value CA4_4_8I2R9P_sound) (by decide +kernel)
def CA4_4_8I2R9MassTerm : Ball := .exact 0
lemma CA4_4_8I2R9MassTerm_sound : CA4_4_8I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R9Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R9Mass_sound)
def CA4_4_8I2R9H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R9H_sound : CA4_4_8I2R9H.Encloses (homogeneousEntropy CA4_4_8I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R9Value CA4_4_8I2R9MassTerm_sound CA4_4_8I2R9Entropy_sound) (by decide +kernel)
def CA4_4_8I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA4_4_8I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA4_4_8I2R10Raw_sound (a : PairSlot) :
    (CA4_4_8I2R10Raw a).Encloses (CA4_4_8I2R10Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA4_4_8I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R10Certificates_valid :
    CA4_4_8I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R10Certificates (CA4_4_8I2R10CertificateIndex a)).input
lemma CA4_4_8I2R10P_check : ∀ a : PairSlot, contains (CA4_4_8I2R10Raw a) (CA4_4_8I2R10P a) = true := by
  decide +kernel
lemma CA4_4_8I2R10P_sound (a : PairSlot) :
    (CA4_4_8I2R10P a).Encloses (CA4_4_8I2R10Value a) :=
  contains_sound (CA4_4_8I2R10Raw_sound a) (CA4_4_8I2R10P_check a)
def CA4_4_8I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R10Certificates (CA4_4_8I2R10CertificateIndex a)).output
lemma CA4_4_8I2R10Terms_sound (a : PairSlot) :
    (CA4_4_8I2R10Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R10Certificates_valid
    (CA4_4_8I2R10CertificateIndex a) (CA4_4_8I2R10P_sound a)
def CA4_4_8I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R10Entropy_sound : CA4_4_8I2R10Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R10Value CA4_4_8I2R10Terms CA4_4_8I2R10Terms_sound) (by decide +kernel)
def CA4_4_8I2R10Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R10Mass_sound : CA4_4_8I2R10Mass.Encloses (∑ a, CA4_4_8I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R10P CA4_4_8I2R10Value CA4_4_8I2R10P_sound) (by decide +kernel)
def CA4_4_8I2R10MassTerm : Ball := .exact 0
lemma CA4_4_8I2R10MassTerm_sound : CA4_4_8I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R10Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R10Mass_sound)
def CA4_4_8I2R10H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R10H_sound : CA4_4_8I2R10H.Encloses (homogeneousEntropy CA4_4_8I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R10Value CA4_4_8I2R10MassTerm_sound CA4_4_8I2R10Entropy_sound) (by decide +kernel)
def CA4_4_8I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA4_4_8I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA4_4_8I2R11Raw_sound (a : PairSlot) :
    (CA4_4_8I2R11Raw a).Encloses (CA4_4_8I2R11Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA4_4_8I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R11Certificates_valid :
    CA4_4_8I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R11Certificates (CA4_4_8I2R11CertificateIndex a)).input
lemma CA4_4_8I2R11P_check : ∀ a : PairSlot, contains (CA4_4_8I2R11Raw a) (CA4_4_8I2R11P a) = true := by
  decide +kernel
lemma CA4_4_8I2R11P_sound (a : PairSlot) :
    (CA4_4_8I2R11P a).Encloses (CA4_4_8I2R11Value a) :=
  contains_sound (CA4_4_8I2R11Raw_sound a) (CA4_4_8I2R11P_check a)
def CA4_4_8I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R11Certificates (CA4_4_8I2R11CertificateIndex a)).output
lemma CA4_4_8I2R11Terms_sound (a : PairSlot) :
    (CA4_4_8I2R11Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R11Certificates_valid
    (CA4_4_8I2R11CertificateIndex a) (CA4_4_8I2R11P_sound a)
def CA4_4_8I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R11Entropy_sound : CA4_4_8I2R11Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R11Value CA4_4_8I2R11Terms CA4_4_8I2R11Terms_sound) (by decide +kernel)
def CA4_4_8I2R11Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R11Mass_sound : CA4_4_8I2R11Mass.Encloses (∑ a, CA4_4_8I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R11P CA4_4_8I2R11Value CA4_4_8I2R11P_sound) (by decide +kernel)
def CA4_4_8I2R11MassTerm : Ball := .exact 0
lemma CA4_4_8I2R11MassTerm_sound : CA4_4_8I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R11Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R11Mass_sound)
def CA4_4_8I2R11H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R11H_sound : CA4_4_8I2R11H.Encloses (homogeneousEntropy CA4_4_8I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R11Value CA4_4_8I2R11MassTerm_sound CA4_4_8I2R11Entropy_sound) (by decide +kernel)
def CA4_4_8I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA4_4_8I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA4_4_8I2R12Raw_sound (a : PairSlot) :
    (CA4_4_8I2R12Raw a).Encloses (CA4_4_8I2R12Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA4_4_8I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R12Certificates_valid :
    CA4_4_8I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R12Certificates (CA4_4_8I2R12CertificateIndex a)).input
lemma CA4_4_8I2R12P_check : ∀ a : PairSlot, contains (CA4_4_8I2R12Raw a) (CA4_4_8I2R12P a) = true := by
  decide +kernel
lemma CA4_4_8I2R12P_sound (a : PairSlot) :
    (CA4_4_8I2R12P a).Encloses (CA4_4_8I2R12Value a) :=
  contains_sound (CA4_4_8I2R12Raw_sound a) (CA4_4_8I2R12P_check a)
def CA4_4_8I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R12Certificates (CA4_4_8I2R12CertificateIndex a)).output
lemma CA4_4_8I2R12Terms_sound (a : PairSlot) :
    (CA4_4_8I2R12Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R12Certificates_valid
    (CA4_4_8I2R12CertificateIndex a) (CA4_4_8I2R12P_sound a)
def CA4_4_8I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R12Entropy_sound : CA4_4_8I2R12Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R12Value CA4_4_8I2R12Terms CA4_4_8I2R12Terms_sound) (by decide +kernel)
def CA4_4_8I2R12Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R12Mass_sound : CA4_4_8I2R12Mass.Encloses (∑ a, CA4_4_8I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R12P CA4_4_8I2R12Value CA4_4_8I2R12P_sound) (by decide +kernel)
def CA4_4_8I2R12MassTerm : Ball := .exact 0
lemma CA4_4_8I2R12MassTerm_sound : CA4_4_8I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R12Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R12Mass_sound)
def CA4_4_8I2R12H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R12H_sound : CA4_4_8I2R12H.Encloses (homogeneousEntropy CA4_4_8I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R12Value CA4_4_8I2R12MassTerm_sound CA4_4_8I2R12Entropy_sound) (by decide +kernel)
def CA4_4_8I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA4_4_8I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA4_4_8I2R13Raw_sound (a : PairSlot) :
    (CA4_4_8I2R13Raw a).Encloses (CA4_4_8I2R13Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA4_4_8I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R13Certificates_valid :
    CA4_4_8I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R13Certificates (CA4_4_8I2R13CertificateIndex a)).input
lemma CA4_4_8I2R13P_check : ∀ a : PairSlot, contains (CA4_4_8I2R13Raw a) (CA4_4_8I2R13P a) = true := by
  decide +kernel
lemma CA4_4_8I2R13P_sound (a : PairSlot) :
    (CA4_4_8I2R13P a).Encloses (CA4_4_8I2R13Value a) :=
  contains_sound (CA4_4_8I2R13Raw_sound a) (CA4_4_8I2R13P_check a)
def CA4_4_8I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R13Certificates (CA4_4_8I2R13CertificateIndex a)).output
lemma CA4_4_8I2R13Terms_sound (a : PairSlot) :
    (CA4_4_8I2R13Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R13Certificates_valid
    (CA4_4_8I2R13CertificateIndex a) (CA4_4_8I2R13P_sound a)
def CA4_4_8I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R13Entropy_sound : CA4_4_8I2R13Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R13Value CA4_4_8I2R13Terms CA4_4_8I2R13Terms_sound) (by decide +kernel)
def CA4_4_8I2R13Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R13Mass_sound : CA4_4_8I2R13Mass.Encloses (∑ a, CA4_4_8I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R13P CA4_4_8I2R13Value CA4_4_8I2R13P_sound) (by decide +kernel)
def CA4_4_8I2R13MassTerm : Ball := .exact 0
lemma CA4_4_8I2R13MassTerm_sound : CA4_4_8I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R13Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R13Mass_sound)
def CA4_4_8I2R13H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R13H_sound : CA4_4_8I2R13H.Encloses (homogeneousEntropy CA4_4_8I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R13Value CA4_4_8I2R13MassTerm_sound CA4_4_8I2R13Entropy_sound) (by decide +kernel)
def CA4_4_8I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA4_4_8I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA4_4_8I2R14Raw_sound (a : PairSlot) :
    (CA4_4_8I2R14Raw a).Encloses (CA4_4_8I2R14Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA4_4_8I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R14Certificates_valid :
    CA4_4_8I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R14Certificates (CA4_4_8I2R14CertificateIndex a)).input
lemma CA4_4_8I2R14P_check : ∀ a : PairSlot, contains (CA4_4_8I2R14Raw a) (CA4_4_8I2R14P a) = true := by
  decide +kernel
lemma CA4_4_8I2R14P_sound (a : PairSlot) :
    (CA4_4_8I2R14P a).Encloses (CA4_4_8I2R14Value a) :=
  contains_sound (CA4_4_8I2R14Raw_sound a) (CA4_4_8I2R14P_check a)
def CA4_4_8I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R14Certificates (CA4_4_8I2R14CertificateIndex a)).output
lemma CA4_4_8I2R14Terms_sound (a : PairSlot) :
    (CA4_4_8I2R14Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R14Certificates_valid
    (CA4_4_8I2R14CertificateIndex a) (CA4_4_8I2R14P_sound a)
def CA4_4_8I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R14Entropy_sound : CA4_4_8I2R14Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R14Value CA4_4_8I2R14Terms CA4_4_8I2R14Terms_sound) (by decide +kernel)
def CA4_4_8I2R14Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R14Mass_sound : CA4_4_8I2R14Mass.Encloses (∑ a, CA4_4_8I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R14P CA4_4_8I2R14Value CA4_4_8I2R14P_sound) (by decide +kernel)
def CA4_4_8I2R14MassTerm : Ball := .exact 0
lemma CA4_4_8I2R14MassTerm_sound : CA4_4_8I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R14Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R14Mass_sound)
def CA4_4_8I2R14H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R14H_sound : CA4_4_8I2R14H.Encloses (homogeneousEntropy CA4_4_8I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R14Value CA4_4_8I2R14MassTerm_sound CA4_4_8I2R14Entropy_sound) (by decide +kernel)
def CA4_4_8I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA4_4_8I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA4_4_8I2R15Raw_sound (a : PairSlot) :
    (CA4_4_8I2R15Raw a).Encloses (CA4_4_8I2R15Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA4_4_8I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R15Certificates_valid :
    CA4_4_8I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R15Certificates (CA4_4_8I2R15CertificateIndex a)).input
lemma CA4_4_8I2R15P_check : ∀ a : PairSlot, contains (CA4_4_8I2R15Raw a) (CA4_4_8I2R15P a) = true := by
  decide +kernel
lemma CA4_4_8I2R15P_sound (a : PairSlot) :
    (CA4_4_8I2R15P a).Encloses (CA4_4_8I2R15Value a) :=
  contains_sound (CA4_4_8I2R15Raw_sound a) (CA4_4_8I2R15P_check a)
def CA4_4_8I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R15Certificates (CA4_4_8I2R15CertificateIndex a)).output
lemma CA4_4_8I2R15Terms_sound (a : PairSlot) :
    (CA4_4_8I2R15Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R15Certificates_valid
    (CA4_4_8I2R15CertificateIndex a) (CA4_4_8I2R15P_sound a)
def CA4_4_8I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R15Entropy_sound : CA4_4_8I2R15Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R15Value CA4_4_8I2R15Terms CA4_4_8I2R15Terms_sound) (by decide +kernel)
def CA4_4_8I2R15Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R15Mass_sound : CA4_4_8I2R15Mass.Encloses (∑ a, CA4_4_8I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R15P CA4_4_8I2R15Value CA4_4_8I2R15P_sound) (by decide +kernel)
def CA4_4_8I2R15MassTerm : Ball := .exact 0
lemma CA4_4_8I2R15MassTerm_sound : CA4_4_8I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R15Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R15Mass_sound)
def CA4_4_8I2R15H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R15H_sound : CA4_4_8I2R15H.Encloses (homogeneousEntropy CA4_4_8I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R15Value CA4_4_8I2R15MassTerm_sound CA4_4_8I2R15Entropy_sound) (by decide +kernel)
def CA4_4_8I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA4_4_8I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 4 8)) A4_4_8Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA4_4_8I2R16Raw_sound (a : PairSlot) :
    (CA4_4_8I2R16Raw a).Encloses (CA4_4_8I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 4 8) (show (shape 4 4 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA4_4_8I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_4_8I2R16Certificates_valid :
    CA4_4_8I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_4_8I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R16Certificates (CA4_4_8I2R16CertificateIndex a)).input
lemma CA4_4_8I2R16P_check : ∀ a : PairSlot, contains (CA4_4_8I2R16Raw a) (CA4_4_8I2R16P a) = true := by
  decide +kernel
lemma CA4_4_8I2R16P_sound (a : PairSlot) :
    (CA4_4_8I2R16P a).Encloses (CA4_4_8I2R16Value a) :=
  contains_sound (CA4_4_8I2R16Raw_sound a) (CA4_4_8I2R16P_check a)
def CA4_4_8I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I2R16Certificates (CA4_4_8I2R16CertificateIndex a)).output
lemma CA4_4_8I2R16Terms_sound (a : PairSlot) :
    (CA4_4_8I2R16Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I2R16Certificates_valid
    (CA4_4_8I2R16CertificateIndex a) (CA4_4_8I2R16P_sound a)
def CA4_4_8I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R16Entropy_sound : CA4_4_8I2R16Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_4_8I2R16Value CA4_4_8I2R16Terms CA4_4_8I2R16Terms_sound) (by decide +kernel)
def CA4_4_8I2R16Mass : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R16Mass_sound : CA4_4_8I2R16Mass.Encloses (∑ a, CA4_4_8I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_4_8I2R16P CA4_4_8I2R16Value CA4_4_8I2R16P_sound) (by decide +kernel)
def CA4_4_8I2R16MassTerm : Ball := .exact 0
lemma CA4_4_8I2R16MassTerm_sound : CA4_4_8I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I2R16Value a))) :=
  entropyTerm_zero_ball (CA4_4_8I2R16Mass_sound)
def CA4_4_8I2R16H : Ball := ⟨0, 0⟩
lemma CA4_4_8I2R16H_sound : CA4_4_8I2R16H.Encloses (homogeneousEntropy CA4_4_8I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I2R16Value CA4_4_8I2R16MassTerm_sound CA4_4_8I2R16Entropy_sound) (by decide +kernel)
def CA4_4_8I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_4_8I2R0H
  | 1 => CA4_4_8I2R1H
  | 2 => CA4_4_8I2R2H
  | 3 => CA4_4_8I2R3H
  | 4 => CA4_4_8I2R4H
  | 5 => CA4_4_8I2R5H
  | 6 => CA4_4_8I2R6H
  | 7 => CA4_4_8I2R7H
  | 8 => CA4_4_8I2R8H
  | 9 => CA4_4_8I2R9H
  | 10 => CA4_4_8I2R10H
  | 11 => CA4_4_8I2R11H
  | 12 => CA4_4_8I2R12H
  | 13 => CA4_4_8I2R13H
  | 14 => CA4_4_8I2R14H
  | 15 => CA4_4_8I2R15H
  | 16 => CA4_4_8I2R16H
  | _ => (.exact 0)
lemma CA4_4_8I2ResidualEntropies_sound (k : Fin 17) :
    (CA4_4_8I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_4_8I2R0H_sound
  · exact CA4_4_8I2R1H_sound
  · exact CA4_4_8I2R2H_sound
  · exact CA4_4_8I2R3H_sound
  · exact CA4_4_8I2R4H_sound
  · exact CA4_4_8I2R5H_sound
  · exact CA4_4_8I2R6H_sound
  · exact CA4_4_8I2R7H_sound
  · exact CA4_4_8I2R8H_sound
  · exact CA4_4_8I2R9H_sound
  · exact CA4_4_8I2R10H_sound
  · exact CA4_4_8I2R11H_sound
  · exact CA4_4_8I2R12H_sound
  · exact CA4_4_8I2R13H_sound
  · exact CA4_4_8I2R14H_sound
  · exact CA4_4_8I2R15H_sound
  · exact CA4_4_8I2R16H_sound
def CA4_4_8I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | 4, 0, 4 => Z4_0_4H2H
  | _, _, _ => (.exact 0)
lemma CA4_4_8I2Singles_sound (u : Shape) (hu : u ∈ below (shape 4 4 8))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA4_4_8I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact Z4_0_4H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 4 0) by decide +kernel) hd |>.elim
def CA4_4_8I2Singleton : Ball := ⟨(6400259021839332148975225827439 / 100000000000000000000000000000000), (2472876643 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I2Singleton_sound : CA4_4_8I2Singleton.Encloses
    (singletonEntropy (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA4_4_8I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_4_8Law_sound u) CA4_4_8I2Singles_sound) (by decide +kernel)
def CA4_4_8I2Group : Ball := ⟨(44503910967582653980176509309439 / 50000000000000000000000000000000), (148006563669 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2Group_sound : CA4_4_8I2Group.Encloses
    (groupedEntropy (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_4_8I2Singleton_sound
    (finSumBall_sound 17 CA4_4_8I2ResidualEntropies _ CA4_4_8I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_4_8I2H : Ball := ⟨(99575014003799578575617859383359 / 100000000000000000000000000000000), (453154407911 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I2_sound : CA4_4_8I2H.Encloses (stageACapacity (shape 4 4 8) 2) := by
  have hb := contains_sound (Ball.add_sound CA4_4_8I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_4_8I2Group_sound)))
    (show contains (.add CA4_4_8I2PairH (.neg (.mul (.exact 2) CA4_4_8I2Group))) CA4_4_8I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
