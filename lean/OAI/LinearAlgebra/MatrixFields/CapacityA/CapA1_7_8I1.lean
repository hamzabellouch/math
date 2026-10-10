import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA1_7_8I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_7_8I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_7_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA1_7_8I1R0Raw_sound (a : PairSlot) :
    (CA1_7_8I1R0Raw a).Encloses (CA1_7_8I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA1_7_8I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(584532371534609447407610401 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩ ⟨(-1204986858128109531200624689824771 / 100000000000000000000000000000000), (40234099213 / 10000000000000000000000000000000)⟩ ⟨-18, 584532371534609447407610401, 381469726562500000000000000⟩]
lemma CA1_7_8I1R0Certificates_valid :
    CA1_7_8I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_7_8I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R0Certificates (CA1_7_8I1R0CertificateIndex a)).input
lemma CA1_7_8I1R0P_check : ∀ a : PairSlot, contains (CA1_7_8I1R0Raw a) (CA1_7_8I1R0P a) = true := by
  decide +kernel
lemma CA1_7_8I1R0P_sound (a : PairSlot) :
    (CA1_7_8I1R0P a).Encloses (CA1_7_8I1R0Value a) :=
  contains_sound (CA1_7_8I1R0Raw_sound a) (CA1_7_8I1R0P_check a)
def CA1_7_8I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R0Certificates (CA1_7_8I1R0CertificateIndex a)).output
lemma CA1_7_8I1R0Terms_sound (a : PairSlot) :
    (CA1_7_8I1R0Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R0Certificates_valid
    (CA1_7_8I1R0CertificateIndex a) (CA1_7_8I1R0P_sound a)
def CA1_7_8I1R0Entropy : Ball := ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R0Entropy_sound : CA1_7_8I1R0Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R0Value CA1_7_8I1R0Terms CA1_7_8I1R0Terms_sound) (by decide +kernel)
def CA1_7_8I1R0Mass : Ball := ⟨(584532371534609447407610401 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R0Mass_sound : CA1_7_8I1R0Mass.Encloses (∑ a, CA1_7_8I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R0P CA1_7_8I1R0Value CA1_7_8I1R0P_sound) (by decide +kernel)
def CA1_7_8I1R0MassTermLogWitness : LogWitness := ⟨-18, 584532371534609447407610401, 381469726562500000000000000⟩
def CA1_7_8I1R0MassTermLog : Ball := ⟨(-1204986858128109531200624689824771 / 100000000000000000000000000000000), (40234099213 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I1R0MassTermLog_sound : CA1_7_8I1R0MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R0Mass_sound) (w := CA1_7_8I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R0MassTerm : Ball := ⟨(7043538258496618443777008947 / 100000000000000000000000000000000), (1175919 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R0MassTerm_sound : CA1_7_8I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R0Mass_sound) CA1_7_8I1R0MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R0H : Ball := ⟨0, (1175919 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1R0H_sound : CA1_7_8I1R0H.Encloses (homogeneousEntropy CA1_7_8I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R0Value CA1_7_8I1R0MassTerm_sound CA1_7_8I1R0Entropy_sound) (by decide +kernel)
def CA1_7_8I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_7_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA1_7_8I1R1Raw_sound (a : PairSlot) :
    (CA1_7_8I1R1Raw a).Encloses (CA1_7_8I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA1_7_8I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(37035762938464593102856286141 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(533899727137404610567259234731 / 100000000000000000000000000000000), (94111543 / 50000000000000000000000000000000)⟩ ⟨(-28831577090742589774638387234999 / 4000000000000000000000000000000), (15881867931 / 6250000000000000000000000000000)⟩ ⟨-11, 37035762938464593102856286141, 24414062500000000000000000000⟩]
lemma CA1_7_8I1R1Certificates_valid :
    CA1_7_8I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_7_8I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R1Certificates (CA1_7_8I1R1CertificateIndex a)).input
lemma CA1_7_8I1R1P_check : ∀ a : PairSlot, contains (CA1_7_8I1R1Raw a) (CA1_7_8I1R1P a) = true := by
  decide +kernel
lemma CA1_7_8I1R1P_sound (a : PairSlot) :
    (CA1_7_8I1R1P a).Encloses (CA1_7_8I1R1Value a) :=
  contains_sound (CA1_7_8I1R1Raw_sound a) (CA1_7_8I1R1P_check a)
def CA1_7_8I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R1Certificates (CA1_7_8I1R1CertificateIndex a)).output
lemma CA1_7_8I1R1Terms_sound (a : PairSlot) :
    (CA1_7_8I1R1Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R1Certificates_valid
    (CA1_7_8I1R1CertificateIndex a) (CA1_7_8I1R1P_sound a)
def CA1_7_8I1R1Entropy : Ball := ⟨(533899727137404610567259234731 / 50000000000000000000000000000000), (94111543 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1R1Entropy_sound : CA1_7_8I1R1Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R1Value CA1_7_8I1R1Terms CA1_7_8I1R1Terms_sound) (by decide +kernel)
def CA1_7_8I1R1Mass : Ball := ⟨(37035762938464593102856286141 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1R1Mass_sound : CA1_7_8I1R1Mass.Encloses (∑ a, CA1_7_8I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R1P CA1_7_8I1R1Value CA1_7_8I1R1P_sound) (by decide +kernel)
def CA1_7_8I1R1MassTermLogWitness : LogWitness := ⟨-10, 37035762938464593102856286141, 24414062500000000000000000000⟩
def CA1_7_8I1R1MassTermLog : Ball := ⟨(-130294941842514042684847297564929 / 20000000000000000000000000000000), (232934063213 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R1MassTermLog_sound : CA1_7_8I1R1MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R1Mass_sound) (w := CA1_7_8I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R1MassTerm : Ball := ⟨(965114515632076229225822100971 / 100000000000000000000000000000000), (345075657 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R1MassTerm_sound : CA1_7_8I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R1Mass_sound) CA1_7_8I1R1MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R1H : Ball := ⟨(102684938642732991908696368491 / 100000000000000000000000000000000), (721521829 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R1H_sound : CA1_7_8I1R1H.Encloses (homogeneousEntropy CA1_7_8I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R1Value CA1_7_8I1R1MassTerm_sound CA1_7_8I1R1Entropy_sound) (by decide +kernel)
def CA1_7_8I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_7_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA1_7_8I1R2Raw_sound (a : PairSlot) :
    (CA1_7_8I1R2Raw a).Encloses (CA1_7_8I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA1_7_8I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(191222039936786006968920366603 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(889192484118741395146123232667 / 20000000000000000000000000000000), (404928429 / 25000000000000000000000000000000)⟩ ⟨(-116251307173154539090529363913951 / 25000000000000000000000000000000), (169406590091 / 100000000000000000000000000000000)⟩ ⟨-7, 191222039936786006968920366603, 156250000000000000000000000000⟩,
   .log ⟨(99733771788650035743636910389 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(344601181037491046007893380543 / 50000000000000000000000000000000), (232313933 / 100000000000000000000000000000000)⟩ ⟨(-691042111127110831503848470013037 / 100000000000000000000000000000000), (46586812303 / 20000000000000000000000000000000)⟩ ⟨-10, 99733771788650035743636910389, 97656250000000000000000000000⟩,
   .log ⟨(893074147967023893622413206403 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(11902754689191070752310359424387 / 100000000000000000000000000000000), (567347429 / 12500000000000000000000000000000)⟩ ⟨(-333196149398296411637838059992123 / 100000000000000000000000000000000), (127054942517 / 100000000000000000000000000000000)⟩ ⟨-5, 893074147967023893622413206403, 781250000000000000000000000000⟩]
lemma CA1_7_8I1R2Certificates_valid :
    CA1_7_8I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_7_8I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R2Certificates (CA1_7_8I1R2CertificateIndex a)).input
lemma CA1_7_8I1R2P_check : ∀ a : PairSlot, contains (CA1_7_8I1R2Raw a) (CA1_7_8I1R2P a) = true := by
  decide +kernel
lemma CA1_7_8I1R2P_sound (a : PairSlot) :
    (CA1_7_8I1R2P a).Encloses (CA1_7_8I1R2Value a) :=
  contains_sound (CA1_7_8I1R2Raw_sound a) (CA1_7_8I1R2P_check a)
def CA1_7_8I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R2Certificates (CA1_7_8I1R2CertificateIndex a)).output
lemma CA1_7_8I1R2Terms_sound (a : PairSlot) :
    (CA1_7_8I1R2Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R2Certificates_valid
    (CA1_7_8I1R2CertificateIndex a) (CA1_7_8I1R2P_sound a)
def CA1_7_8I1R2Entropy : Ball := ⟨(22173084254528448887803165273229 / 100000000000000000000000000000000), (824283473 / 10000000000000000000000000000000)⟩
lemma CA1_7_8I1R2Entropy_sound : CA1_7_8I1R2Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R2Value CA1_7_8I1R2Terms CA1_7_8I1R2Terms_sound) (by decide +kernel)
def CA1_7_8I1R2Mass : Ball := ⟨(284199226740662785783306515621 / 5000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R2Mass_sound : CA1_7_8I1R2Mass.Encloses (∑ a, CA1_7_8I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R2P CA1_7_8I1R2Value CA1_7_8I1R2P_sound) (by decide +kernel)
def CA1_7_8I1R2MassTermLogWitness : LogWitness := ⟨-5, 284199226740662785783306515621, 156250000000000000000000000000⟩
def CA1_7_8I1R2MassTermLog : Ball := ⟨(-286751769658500763880690399379981 / 100000000000000000000000000000000), (7940933913 / 6250000000000000000000000000000)⟩
lemma CA1_7_8I1R2MassTermLog_sound : CA1_7_8I1R2MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R2Mass_sound) (w := CA1_7_8I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R2MassTerm : Ball := ⟨(3259785248138502638354366883571 / 20000000000000000000000000000000), (7221783373 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R2MassTerm_sound : CA1_7_8I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R2Mass_sound) CA1_7_8I1R2MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R2H : Ball := ⟨(2937079006917967848015665427687 / 50000000000000000000000000000000), (15464618103 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R2H_sound : CA1_7_8I1R2H.Encloses (homogeneousEntropy CA1_7_8I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R2Value CA1_7_8I1R2MassTerm_sound CA1_7_8I1R2Entropy_sound) (by decide +kernel)
def CA1_7_8I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_7_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA1_7_8I1R3Raw_sound (a : PairSlot) :
    (CA1_7_8I1R3Raw a).Encloses (CA1_7_8I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA1_7_8I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(23755725364738632673182145927 / 3125000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(92730302782309864385551828973 / 2500000000000000000000000000000), (72438777 / 5000000000000000000000000000000)⟩ ⟨(-487936599275307531018982220159061 / 100000000000000000000000000000000), (38116482761 / 20000000000000000000000000000000)⟩ ⟨-8, 23755725364738632673182145927, 12207031250000000000000000000⟩,
   .log ⟨(19452192305358146935978508749949 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(31847331688048502861394488834571 / 100000000000000000000000000000000), (16476647881 / 100000000000000000000000000000000)⟩ ⟨(-40930260183676172240128151715623 / 25000000000000000000000000000000), (84703294927 / 100000000000000000000000000000000)⟩ ⟨-3, 19452192305358146935978508749949, 12500000000000000000000000000000⟩,
   .log ⟨(935634211750446234858590523347 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(7444941879560739999523215666747 / 100000000000000000000000000000000), (554759107 / 20000000000000000000000000000000)⟩ ⟨(-79571073674531966587660539103193 / 20000000000000000000000000000000), (74115382997 / 50000000000000000000000000000000)⟩ ⟨-6, 935634211750446234858590523347, 781250000000000000000000000000⟩]
lemma CA1_7_8I1R3Certificates_valid :
    CA1_7_8I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_7_8I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R3Certificates (CA1_7_8I1R3CertificateIndex a)).input
lemma CA1_7_8I1R3P_check : ∀ a : PairSlot, contains (CA1_7_8I1R3Raw a) (CA1_7_8I1R3P a) = true := by
  decide +kernel
lemma CA1_7_8I1R3P_sound (a : PairSlot) :
    (CA1_7_8I1R3P a).Encloses (CA1_7_8I1R3Value a) :=
  contains_sound (CA1_7_8I1R3Raw_sound a) (CA1_7_8I1R3P_check a)
def CA1_7_8I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R3Certificates (CA1_7_8I1R3CertificateIndex a)).output
lemma CA1_7_8I1R3Terms_sound (a : PairSlot) :
    (CA1_7_8I1R3Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R3Certificates_valid
    (CA1_7_8I1R3CertificateIndex a) (CA1_7_8I1R3P_sound a)
def CA1_7_8I1R3Entropy : Ball := ⟨(21500742839450818718169888830119 / 25000000000000000000000000000000), (5174804739 / 12500000000000000000000000000000)⟩
lemma CA1_7_8I1R3Entropy_sound : CA1_7_8I1R3Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R3Value CA1_7_8I1R3Terms CA1_7_8I1R3Terms_sound) (by decide +kernel)
def CA1_7_8I1R3Mass : Ball := ⟨(22083643940530675651237518466307 / 50000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R3Mass_sound : CA1_7_8I1R3Mass.Encloses (∑ a, CA1_7_8I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R3P CA1_7_8I1R3Value CA1_7_8I1R3P_sound) (by decide +kernel)
def CA1_7_8I1R3MassTermLogWitness : LogWitness := ⟨-2, 22083643940530675651237518466307, 12500000000000000000000000000000⟩
def CA1_7_8I1R3MassTermLog : Ball := ⟨(-81718576409726083693032108385419 / 100000000000000000000000000000000), (31763735631 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R3MassTermLog_sound : CA1_7_8I1R3MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R3Mass_sound) (w := CA1_7_8I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R3MassTerm : Ball := ⟨(9023219723797202219809978218521 / 25000000000000000000000000000000), (28058361193 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R3MassTerm_sound : CA1_7_8I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R3Mass_sound) CA1_7_8I1R3MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R3H : Ball := ⟨(6238761557826808249179955305799 / 12500000000000000000000000000000), (13891359821 / 20000000000000000000000000000000)⟩
lemma CA1_7_8I1R3H_sound : CA1_7_8I1R3H.Encloses (homogeneousEntropy CA1_7_8I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R3Value CA1_7_8I1R3MassTerm_sound CA1_7_8I1R3Entropy_sound) (by decide +kernel)
def CA1_7_8I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_7_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA1_7_8I1R4Raw_sound (a : PairSlot) :
    (CA1_7_8I1R4Raw a).Encloses (CA1_7_8I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA1_7_8I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15627028006695398584059032451 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(230580833894447540330567428909 / 50000000000000000000000000000000), (1588393 / 1000000000000000000000000000000)⟩ ⟨(-737762912422167558497093805111299 / 100000000000000000000000000000000), (50821977159 / 20000000000000000000000000000000)⟩ ⟨-11, 15627028006695398584059032451, 12207031250000000000000000000⟩,
   .log ⟨(2473098266048731246033486140617 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(7435496762584514584666307602159 / 50000000000000000000000000000000), (6284387201 / 100000000000000000000000000000000)⟩ ⟨(-300655128211472434651138191805343 / 100000000000000000000000000000000), (127054942401 / 100000000000000000000000000000000)⟩ ⟨-5, 2473098266048731246033486140617, 1562500000000000000000000000000⟩,
   .log ⟨(28955837401340539615145743394389 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(17943908765390744531566152093057 / 50000000000000000000000000000000), (18394911377 / 100000000000000000000000000000000)⟩ ⟨(-123939836494316087214867202179321 / 100000000000000000000000000000000), (31763735643 / 50000000000000000000000000000000)⟩ ⟨-2, 28955837401340539615145743394389, 25000000000000000000000000000000⟩,
   .log ⟨(311323194051302437148547523701 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(459843328596575980405811384097 / 5000000000000000000000000000000), (147672563 / 4000000000000000000000000000000)⟩ ⟨(-369265234154702230875504734955431 / 100000000000000000000000000000000), (74115383051 / 50000000000000000000000000000000)⟩ ⟨-6, 311323194051302437148547523701, 195312500000000000000000000000⟩,
   .log ⟨(42574017330296904029223267387 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1309628587183769853925035297047 / 100000000000000000000000000000000), (9015399 / 2000000000000000000000000000000)⟩ ⟨(-76903042589535015149302725245349 / 12500000000000000000000000000000), (211758237299 / 100000000000000000000000000000000)⟩ ⟨-9, 42574017330296904029223267387, 39062500000000000000000000000⟩]
lemma CA1_7_8I1R4Certificates_valid :
    CA1_7_8I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R4CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 5 => 1
  | 1, 4 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 4, 1 => 2
  | 5, 0 => 1
  | _, _ => 0
def CA1_7_8I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R4Certificates (CA1_7_8I1R4CertificateIndex a)).input
lemma CA1_7_8I1R4P_check : ∀ a : PairSlot, contains (CA1_7_8I1R4Raw a) (CA1_7_8I1R4P a) = true := by
  decide +kernel
lemma CA1_7_8I1R4P_sound (a : PairSlot) :
    (CA1_7_8I1R4P a).Encloses (CA1_7_8I1R4Value a) :=
  contains_sound (CA1_7_8I1R4Raw_sound a) (CA1_7_8I1R4P_check a)
def CA1_7_8I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R4Certificates (CA1_7_8I1R4CertificateIndex a)).output
lemma CA1_7_8I1R4Terms_sound (a : PairSlot) :
    (CA1_7_8I1R4Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R4Certificates_valid
    (CA1_7_8I1R4CertificateIndex a) (CA1_7_8I1R4P_sound a)
def CA1_7_8I1R4Entropy : Ball := ⟨(86255489647744146633277294971313 / 100000000000000000000000000000000), (39115762479 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R4Entropy_sound : CA1_7_8I1R4Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R4Value CA1_7_8I1R4Terms CA1_7_8I1R4Terms_sound) (by decide +kernel)
def CA1_7_8I1R4Mass : Ball := ⟨(5520910985132668912809379616577 / 12500000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R4Mass_sound : CA1_7_8I1R4Mass.Encloses (∑ a, CA1_7_8I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R4P CA1_7_8I1R4Value CA1_7_8I1R4P_sound) (by decide +kernel)
def CA1_7_8I1R4MassTermLogWitness : LogWitness := ⟨-2, 5520910985132668912809379616577, 3125000000000000000000000000000⟩
def CA1_7_8I1R4MassTermLog : Ball := ⟨(-16343715281945216738606421677083 / 20000000000000000000000000000000), (15881867829 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1R4MassTermLog_sound : CA1_7_8I1R4MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R4Mass_sound) (w := CA1_7_8I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R4MassTerm : Ball := ⟨(9023219723797202219809978218521 / 25000000000000000000000000000000), (28058361237 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R4MassTerm_sound : CA1_7_8I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R4Mass_sound) CA1_7_8I1R4MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R4H : Ball := ⟨(50162610752555337754037382097229 / 100000000000000000000000000000000), (16793530929 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1R4H_sound : CA1_7_8I1R4H.Encloses (homogeneousEntropy CA1_7_8I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R4Value CA1_7_8I1R4MassTerm_sound CA1_7_8I1R4Entropy_sound) (by decide +kernel)
def CA1_7_8I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_7_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA1_7_8I1R5Raw_sound (a : PairSlot) :
    (CA1_7_8I1R5Raw a).Encloses (CA1_7_8I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA1_7_8I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(56490034731352553689181797071 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(383325221697784832231938850641 / 50000000000000000000000000000000), (16448067 / 6250000000000000000000000000000)⟩ ⟨(-67857140382502786554008324328631 / 10000000000000000000000000000000), (232934061397 / 100000000000000000000000000000000)⟩ ⟨-10, 56490034731352553689181797071, 48828125000000000000000000000⟩,
   .log ⟨(1256825878128021407454329983707 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩ ⟨(92588693557674396110477875221 / 1000000000000000000000000000000), (1863002657 / 50000000000000000000000000000000)⟩ ⟨(-92085840179767555893425843607037 / 25000000000000000000000000000000), (74115383169 / 50000000000000000000000000000000)⟩ ⟨-6, 1256825878128021407454329983707, 781250000000000000000000000000⟩,
   .log ⟨(107680220843939967773020797327 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(66122249585888860257413042173 / 5000000000000000000000000000000), (456043489 / 100000000000000000000000000000000)⟩ ⟨(-122812247351756970586692448402091 / 20000000000000000000000000000000), (105879118879 / 50000000000000000000000000000000)⟩ ⟨-9, 107680220843939967773020797327, 97656250000000000000000000000⟩]
lemma CA1_7_8I1R5Certificates_valid :
    CA1_7_8I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_7_8I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R5Certificates (CA1_7_8I1R5CertificateIndex a)).input
lemma CA1_7_8I1R5P_check : ∀ a : PairSlot, contains (CA1_7_8I1R5Raw a) (CA1_7_8I1R5P a) = true := by
  decide +kernel
lemma CA1_7_8I1R5P_sound (a : PairSlot) :
    (CA1_7_8I1R5P a).Encloses (CA1_7_8I1R5Value a) :=
  contains_sound (CA1_7_8I1R5Raw_sound a) (CA1_7_8I1R5P_check a)
def CA1_7_8I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R5Certificates (CA1_7_8I1R5CertificateIndex a)).output
lemma CA1_7_8I1R5Terms_sound (a : PairSlot) :
    (CA1_7_8I1R5Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R5Certificates_valid
    (CA1_7_8I1R5CertificateIndex a) (CA1_7_8I1R5P_sound a)
def CA1_7_8I1R5Entropy : Ball := ⟨(5673982395440393240329963033421 / 25000000000000000000000000000000), (35561743 / 400000000000000000000000000000)⟩
lemma CA1_7_8I1R5Entropy_sound : CA1_7_8I1R5Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R5Value CA1_7_8I1R5Terms CA1_7_8I1R5Terms_sound) (by decide +kernel)
def CA1_7_8I1R5Mass : Ball := ⟨(284199226740662785783306515621 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R5Mass_sound : CA1_7_8I1R5Mass.Encloses (∑ a, CA1_7_8I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R5P CA1_7_8I1R5Value CA1_7_8I1R5P_sound) (by decide +kernel)
def CA1_7_8I1R5MassTermLogWitness : LogWitness := ⟨-5, 284199226740662785783306515621, 156250000000000000000000000000⟩
def CA1_7_8I1R5MassTermLog : Ball := ⟨(-286751769658500763880690399379981 / 100000000000000000000000000000000), (15881867837 / 12500000000000000000000000000000)⟩
lemma CA1_7_8I1R5MassTermLog_sound : CA1_7_8I1R5MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R5Mass_sound) (w := CA1_7_8I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R5MassTerm : Ball := ⟨(3259785248138502638354366883571 / 20000000000000000000000000000000), (225680731 / 3125000000000000000000000000000)⟩
lemma CA1_7_8I1R5MassTerm_sound : CA1_7_8I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R5Mass_sound) CA1_7_8I1R5MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R5H : Ball := ⟨(6397003341069059769548017715829 / 100000000000000000000000000000000), (8056109571 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R5H_sound : CA1_7_8I1R5H.Encloses (homogeneousEntropy CA1_7_8I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R5Value CA1_7_8I1R5MassTerm_sound CA1_7_8I1R5Entropy_sound) (by decide +kernel)
def CA1_7_8I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_7_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA1_7_8I1R6Raw_sound (a : PairSlot) :
    (CA1_7_8I1R6Raw a).Encloses (CA1_7_8I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA1_7_8I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(23170151427983124544007071961 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(96967785677755872974651188937 / 50000000000000000000000000000000), (17172649 / 25000000000000000000000000000000)⟩ ⟨(-167401211820559185461068287890547 / 20000000000000000000000000000000), (148230767939 / 50000000000000000000000000000000)⟩ ⟨-13, 23170151427983124544007071961, 12207031250000000000000000000⟩,
   .log ⟨(329375579851911397821806799 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9069392947503710307608253179 / 50000000000000000000000000000000), (370537 / 6250000000000000000000000000000)⟩ ⟨(-13767555189703721075067192798127 / 1250000000000000000000000000000), (359989063331 / 100000000000000000000000000000000)⟩ ⟨-16, 329375579851911397821806799, 305175781250000000000000000⟩,
   .log ⟨(98508993099373009345192932651 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(681955852842247518025916899597 / 100000000000000000000000000000000), (114730511 / 50000000000000000000000000000000)⟩ ⟨(-138455552409171469827814519028301 / 20000000000000000000000000000000), (232934063557 / 100000000000000000000000000000000)⟩ ⟨-10, 98508993099373009345192932651, 97656250000000000000000000000⟩]
lemma CA1_7_8I1R6Certificates_valid :
    CA1_7_8I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA1_7_8I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R6Certificates (CA1_7_8I1R6CertificateIndex a)).input
lemma CA1_7_8I1R6P_check : ∀ a : PairSlot, contains (CA1_7_8I1R6Raw a) (CA1_7_8I1R6P a) = true := by
  decide +kernel
lemma CA1_7_8I1R6P_sound (a : PairSlot) :
    (CA1_7_8I1R6P a).Encloses (CA1_7_8I1R6Value a) :=
  contains_sound (CA1_7_8I1R6Raw_sound a) (CA1_7_8I1R6P_check a)
def CA1_7_8I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R6Certificates (CA1_7_8I1R6CertificateIndex a)).output
lemma CA1_7_8I1R6Terms_sound (a : PairSlot) :
    (CA1_7_8I1R6Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R6Certificates_valid
    (CA1_7_8I1R6CertificateIndex a) (CA1_7_8I1R6P_sound a)
def CA1_7_8I1R6Entropy : Ball := ⟨(1106104567343285851154954668061 / 100000000000000000000000000000000), (189349699 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R6Entropy_sound : CA1_7_8I1R6Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R6Value CA1_7_8I1R6Terms CA1_7_8I1R6Terms_sound) (by decide +kernel)
def CA1_7_8I1R6Mass : Ball := ⟨(148143051753858372411425144563 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R6Mass_sound : CA1_7_8I1R6Mass.Encloses (∑ a, CA1_7_8I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R6P CA1_7_8I1R6Value CA1_7_8I1R6P_sound) (by decide +kernel)
def CA1_7_8I1R6MassTermLogWitness : LogWitness := ⟨-10, 148143051753858372411425144563, 97656250000000000000000000000⟩
def CA1_7_8I1R6MassTermLog : Ball := ⟨(-16286867730314255335605912195633 / 2500000000000000000000000000000), (116467032619 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R6MassTermLog_sound : CA1_7_8I1R6MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R6Mass_sound) (w := CA1_7_8I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R6MassTerm : Ball := ⟨(482557257816038114612911050483 / 50000000000000000000000000000000), (345075679 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R6MassTerm_sound : CA1_7_8I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R6Mass_sound) CA1_7_8I1R6MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R6H : Ball := ⟨(28198010342241924385826513419 / 20000000000000000000000000000000), (723775077 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R6H_sound : CA1_7_8I1R6H.Encloses (homogeneousEntropy CA1_7_8I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R6Value CA1_7_8I1R6MassTerm_sound CA1_7_8I1R6Entropy_sound) (by decide +kernel)
def CA1_7_8I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_7_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA1_7_8I1R7Raw_sound (a : PairSlot) :
    (CA1_7_8I1R7Raw a).Encloses (CA1_7_8I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA1_7_8I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(35279809335985405792837309 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(72128460287202064852396239 / 2000000000000000000000000000000), (1195341 / 100000000000000000000000000000000)⟩ ⟨(-1277792837545734601079131937105397 / 100000000000000000000000000000000), (42351682797 / 10000000000000000000000000000000)⟩ ⟨-19, 35279809335985405792837309, 23841857910156250000000000⟩]
lemma CA1_7_8I1R7Certificates_valid :
    CA1_7_8I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 5 => 1
  | 5, 4 => 1
  | _, _ => 0
def CA1_7_8I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R7Certificates (CA1_7_8I1R7CertificateIndex a)).input
lemma CA1_7_8I1R7P_check : ∀ a : PairSlot, contains (CA1_7_8I1R7Raw a) (CA1_7_8I1R7P a) = true := by
  decide +kernel
lemma CA1_7_8I1R7P_sound (a : PairSlot) :
    (CA1_7_8I1R7P a).Encloses (CA1_7_8I1R7Value a) :=
  contains_sound (CA1_7_8I1R7Raw_sound a) (CA1_7_8I1R7P_check a)
def CA1_7_8I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R7Certificates (CA1_7_8I1R7CertificateIndex a)).output
lemma CA1_7_8I1R7Terms_sound (a : PairSlot) :
    (CA1_7_8I1R7Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R7Certificates_valid
    (CA1_7_8I1R7CertificateIndex a) (CA1_7_8I1R7P_sound a)
def CA1_7_8I1R7Entropy : Ball := ⟨(72128460287202064852396239 / 1000000000000000000000000000000), (1195341 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R7Entropy_sound : CA1_7_8I1R7Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R7Value CA1_7_8I1R7Terms CA1_7_8I1R7Terms_sound) (by decide +kernel)
def CA1_7_8I1R7Mass : Ball := ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I1R7Mass_sound : CA1_7_8I1R7Mass.Encloses (∑ a, CA1_7_8I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R7P CA1_7_8I1R7Value CA1_7_8I1R7P_sound) (by decide +kernel)
def CA1_7_8I1R7MassTermLogWitness : LogWitness := ⟨-18, 35279809335985405792837309, 23841857910156250000000000⟩
def CA1_7_8I1R7MassTermLog : Ball := ⟨(-1208478119489740070137408744055067 / 100000000000000000000000000000000), (402341004287 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R7MassTermLog_sound : CA1_7_8I1R7MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I1R7Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I1R7Mass_sound) (w := CA1_7_8I1R7MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I1R7MassTerm : Ball := ⟨(6821580422769314960419141647 / 100000000000000000000000000000000), (2271147 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R7MassTerm_sound : CA1_7_8I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R7Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I1R7Mass_sound) CA1_7_8I1R7MassTermLog_sound) (by decide +kernel)
def CA1_7_8I1R7H : Ball := ⟨(391265605950891524820482253 / 100000000000000000000000000000000), (4661829 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I1R7H_sound : CA1_7_8I1R7H.Encloses (homogeneousEntropy CA1_7_8I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R7Value CA1_7_8I1R7MassTerm_sound CA1_7_8I1R7Entropy_sound) (by decide +kernel)
def CA1_7_8I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_7_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA1_7_8I1R8Raw_sound (a : PairSlot) :
    (CA1_7_8I1R8Raw a).Encloses (CA1_7_8I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA1_7_8I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R8Certificates_valid :
    CA1_7_8I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R8Certificates (CA1_7_8I1R8CertificateIndex a)).input
lemma CA1_7_8I1R8P_check : ∀ a : PairSlot, contains (CA1_7_8I1R8Raw a) (CA1_7_8I1R8P a) = true := by
  decide +kernel
lemma CA1_7_8I1R8P_sound (a : PairSlot) :
    (CA1_7_8I1R8P a).Encloses (CA1_7_8I1R8Value a) :=
  contains_sound (CA1_7_8I1R8Raw_sound a) (CA1_7_8I1R8P_check a)
def CA1_7_8I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R8Certificates (CA1_7_8I1R8CertificateIndex a)).output
lemma CA1_7_8I1R8Terms_sound (a : PairSlot) :
    (CA1_7_8I1R8Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R8Certificates_valid
    (CA1_7_8I1R8CertificateIndex a) (CA1_7_8I1R8P_sound a)
def CA1_7_8I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R8Entropy_sound : CA1_7_8I1R8Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R8Value CA1_7_8I1R8Terms CA1_7_8I1R8Terms_sound) (by decide +kernel)
def CA1_7_8I1R8Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R8Mass_sound : CA1_7_8I1R8Mass.Encloses (∑ a, CA1_7_8I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R8P CA1_7_8I1R8Value CA1_7_8I1R8P_sound) (by decide +kernel)
def CA1_7_8I1R8MassTerm : Ball := .exact 0
lemma CA1_7_8I1R8MassTerm_sound : CA1_7_8I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R8Mass_sound)
def CA1_7_8I1R8H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R8H_sound : CA1_7_8I1R8H.Encloses (homogeneousEntropy CA1_7_8I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R8Value CA1_7_8I1R8MassTerm_sound CA1_7_8I1R8Entropy_sound) (by decide +kernel)
def CA1_7_8I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_7_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA1_7_8I1R9Raw_sound (a : PairSlot) :
    (CA1_7_8I1R9Raw a).Encloses (CA1_7_8I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA1_7_8I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R9Certificates_valid :
    CA1_7_8I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R9Certificates (CA1_7_8I1R9CertificateIndex a)).input
lemma CA1_7_8I1R9P_check : ∀ a : PairSlot, contains (CA1_7_8I1R9Raw a) (CA1_7_8I1R9P a) = true := by
  decide +kernel
lemma CA1_7_8I1R9P_sound (a : PairSlot) :
    (CA1_7_8I1R9P a).Encloses (CA1_7_8I1R9Value a) :=
  contains_sound (CA1_7_8I1R9Raw_sound a) (CA1_7_8I1R9P_check a)
def CA1_7_8I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R9Certificates (CA1_7_8I1R9CertificateIndex a)).output
lemma CA1_7_8I1R9Terms_sound (a : PairSlot) :
    (CA1_7_8I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R9Certificates_valid
    (CA1_7_8I1R9CertificateIndex a) (CA1_7_8I1R9P_sound a)
def CA1_7_8I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R9Entropy_sound : CA1_7_8I1R9Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R9Value CA1_7_8I1R9Terms CA1_7_8I1R9Terms_sound) (by decide +kernel)
def CA1_7_8I1R9Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R9Mass_sound : CA1_7_8I1R9Mass.Encloses (∑ a, CA1_7_8I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R9P CA1_7_8I1R9Value CA1_7_8I1R9P_sound) (by decide +kernel)
def CA1_7_8I1R9MassTerm : Ball := .exact 0
lemma CA1_7_8I1R9MassTerm_sound : CA1_7_8I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R9Mass_sound)
def CA1_7_8I1R9H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R9H_sound : CA1_7_8I1R9H.Encloses (homogeneousEntropy CA1_7_8I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R9Value CA1_7_8I1R9MassTerm_sound CA1_7_8I1R9Entropy_sound) (by decide +kernel)
def CA1_7_8I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_7_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA1_7_8I1R10Raw_sound (a : PairSlot) :
    (CA1_7_8I1R10Raw a).Encloses (CA1_7_8I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA1_7_8I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R10Certificates_valid :
    CA1_7_8I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R10Certificates (CA1_7_8I1R10CertificateIndex a)).input
lemma CA1_7_8I1R10P_check : ∀ a : PairSlot, contains (CA1_7_8I1R10Raw a) (CA1_7_8I1R10P a) = true := by
  decide +kernel
lemma CA1_7_8I1R10P_sound (a : PairSlot) :
    (CA1_7_8I1R10P a).Encloses (CA1_7_8I1R10Value a) :=
  contains_sound (CA1_7_8I1R10Raw_sound a) (CA1_7_8I1R10P_check a)
def CA1_7_8I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R10Certificates (CA1_7_8I1R10CertificateIndex a)).output
lemma CA1_7_8I1R10Terms_sound (a : PairSlot) :
    (CA1_7_8I1R10Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R10Certificates_valid
    (CA1_7_8I1R10CertificateIndex a) (CA1_7_8I1R10P_sound a)
def CA1_7_8I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R10Entropy_sound : CA1_7_8I1R10Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R10Value CA1_7_8I1R10Terms CA1_7_8I1R10Terms_sound) (by decide +kernel)
def CA1_7_8I1R10Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R10Mass_sound : CA1_7_8I1R10Mass.Encloses (∑ a, CA1_7_8I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R10P CA1_7_8I1R10Value CA1_7_8I1R10P_sound) (by decide +kernel)
def CA1_7_8I1R10MassTerm : Ball := .exact 0
lemma CA1_7_8I1R10MassTerm_sound : CA1_7_8I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R10Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R10Mass_sound)
def CA1_7_8I1R10H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R10H_sound : CA1_7_8I1R10H.Encloses (homogeneousEntropy CA1_7_8I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R10Value CA1_7_8I1R10MassTerm_sound CA1_7_8I1R10Entropy_sound) (by decide +kernel)
def CA1_7_8I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_7_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA1_7_8I1R11Raw_sound (a : PairSlot) :
    (CA1_7_8I1R11Raw a).Encloses (CA1_7_8I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA1_7_8I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R11Certificates_valid :
    CA1_7_8I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R11Certificates (CA1_7_8I1R11CertificateIndex a)).input
lemma CA1_7_8I1R11P_check : ∀ a : PairSlot, contains (CA1_7_8I1R11Raw a) (CA1_7_8I1R11P a) = true := by
  decide +kernel
lemma CA1_7_8I1R11P_sound (a : PairSlot) :
    (CA1_7_8I1R11P a).Encloses (CA1_7_8I1R11Value a) :=
  contains_sound (CA1_7_8I1R11Raw_sound a) (CA1_7_8I1R11P_check a)
def CA1_7_8I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R11Certificates (CA1_7_8I1R11CertificateIndex a)).output
lemma CA1_7_8I1R11Terms_sound (a : PairSlot) :
    (CA1_7_8I1R11Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R11Certificates_valid
    (CA1_7_8I1R11CertificateIndex a) (CA1_7_8I1R11P_sound a)
def CA1_7_8I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R11Entropy_sound : CA1_7_8I1R11Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R11Value CA1_7_8I1R11Terms CA1_7_8I1R11Terms_sound) (by decide +kernel)
def CA1_7_8I1R11Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R11Mass_sound : CA1_7_8I1R11Mass.Encloses (∑ a, CA1_7_8I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R11P CA1_7_8I1R11Value CA1_7_8I1R11P_sound) (by decide +kernel)
def CA1_7_8I1R11MassTerm : Ball := .exact 0
lemma CA1_7_8I1R11MassTerm_sound : CA1_7_8I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R11Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R11Mass_sound)
def CA1_7_8I1R11H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R11H_sound : CA1_7_8I1R11H.Encloses (homogeneousEntropy CA1_7_8I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R11Value CA1_7_8I1R11MassTerm_sound CA1_7_8I1R11Entropy_sound) (by decide +kernel)
def CA1_7_8I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_7_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA1_7_8I1R12Raw_sound (a : PairSlot) :
    (CA1_7_8I1R12Raw a).Encloses (CA1_7_8I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA1_7_8I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R12Certificates_valid :
    CA1_7_8I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R12Certificates (CA1_7_8I1R12CertificateIndex a)).input
lemma CA1_7_8I1R12P_check : ∀ a : PairSlot, contains (CA1_7_8I1R12Raw a) (CA1_7_8I1R12P a) = true := by
  decide +kernel
lemma CA1_7_8I1R12P_sound (a : PairSlot) :
    (CA1_7_8I1R12P a).Encloses (CA1_7_8I1R12Value a) :=
  contains_sound (CA1_7_8I1R12Raw_sound a) (CA1_7_8I1R12P_check a)
def CA1_7_8I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R12Certificates (CA1_7_8I1R12CertificateIndex a)).output
lemma CA1_7_8I1R12Terms_sound (a : PairSlot) :
    (CA1_7_8I1R12Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R12Certificates_valid
    (CA1_7_8I1R12CertificateIndex a) (CA1_7_8I1R12P_sound a)
def CA1_7_8I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R12Entropy_sound : CA1_7_8I1R12Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R12Value CA1_7_8I1R12Terms CA1_7_8I1R12Terms_sound) (by decide +kernel)
def CA1_7_8I1R12Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R12Mass_sound : CA1_7_8I1R12Mass.Encloses (∑ a, CA1_7_8I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R12P CA1_7_8I1R12Value CA1_7_8I1R12P_sound) (by decide +kernel)
def CA1_7_8I1R12MassTerm : Ball := .exact 0
lemma CA1_7_8I1R12MassTerm_sound : CA1_7_8I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R12Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R12Mass_sound)
def CA1_7_8I1R12H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R12H_sound : CA1_7_8I1R12H.Encloses (homogeneousEntropy CA1_7_8I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R12Value CA1_7_8I1R12MassTerm_sound CA1_7_8I1R12Entropy_sound) (by decide +kernel)
def CA1_7_8I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_7_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA1_7_8I1R13Raw_sound (a : PairSlot) :
    (CA1_7_8I1R13Raw a).Encloses (CA1_7_8I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA1_7_8I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R13Certificates_valid :
    CA1_7_8I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R13Certificates (CA1_7_8I1R13CertificateIndex a)).input
lemma CA1_7_8I1R13P_check : ∀ a : PairSlot, contains (CA1_7_8I1R13Raw a) (CA1_7_8I1R13P a) = true := by
  decide +kernel
lemma CA1_7_8I1R13P_sound (a : PairSlot) :
    (CA1_7_8I1R13P a).Encloses (CA1_7_8I1R13Value a) :=
  contains_sound (CA1_7_8I1R13Raw_sound a) (CA1_7_8I1R13P_check a)
def CA1_7_8I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R13Certificates (CA1_7_8I1R13CertificateIndex a)).output
lemma CA1_7_8I1R13Terms_sound (a : PairSlot) :
    (CA1_7_8I1R13Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R13Certificates_valid
    (CA1_7_8I1R13CertificateIndex a) (CA1_7_8I1R13P_sound a)
def CA1_7_8I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R13Entropy_sound : CA1_7_8I1R13Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R13Value CA1_7_8I1R13Terms CA1_7_8I1R13Terms_sound) (by decide +kernel)
def CA1_7_8I1R13Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R13Mass_sound : CA1_7_8I1R13Mass.Encloses (∑ a, CA1_7_8I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R13P CA1_7_8I1R13Value CA1_7_8I1R13P_sound) (by decide +kernel)
def CA1_7_8I1R13MassTerm : Ball := .exact 0
lemma CA1_7_8I1R13MassTerm_sound : CA1_7_8I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R13Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R13Mass_sound)
def CA1_7_8I1R13H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R13H_sound : CA1_7_8I1R13H.Encloses (homogeneousEntropy CA1_7_8I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R13Value CA1_7_8I1R13MassTerm_sound CA1_7_8I1R13Entropy_sound) (by decide +kernel)
def CA1_7_8I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_7_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA1_7_8I1R14Raw_sound (a : PairSlot) :
    (CA1_7_8I1R14Raw a).Encloses (CA1_7_8I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA1_7_8I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R14Certificates_valid :
    CA1_7_8I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R14Certificates (CA1_7_8I1R14CertificateIndex a)).input
lemma CA1_7_8I1R14P_check : ∀ a : PairSlot, contains (CA1_7_8I1R14Raw a) (CA1_7_8I1R14P a) = true := by
  decide +kernel
lemma CA1_7_8I1R14P_sound (a : PairSlot) :
    (CA1_7_8I1R14P a).Encloses (CA1_7_8I1R14Value a) :=
  contains_sound (CA1_7_8I1R14Raw_sound a) (CA1_7_8I1R14P_check a)
def CA1_7_8I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R14Certificates (CA1_7_8I1R14CertificateIndex a)).output
lemma CA1_7_8I1R14Terms_sound (a : PairSlot) :
    (CA1_7_8I1R14Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R14Certificates_valid
    (CA1_7_8I1R14CertificateIndex a) (CA1_7_8I1R14P_sound a)
def CA1_7_8I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R14Entropy_sound : CA1_7_8I1R14Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R14Value CA1_7_8I1R14Terms CA1_7_8I1R14Terms_sound) (by decide +kernel)
def CA1_7_8I1R14Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R14Mass_sound : CA1_7_8I1R14Mass.Encloses (∑ a, CA1_7_8I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R14P CA1_7_8I1R14Value CA1_7_8I1R14P_sound) (by decide +kernel)
def CA1_7_8I1R14MassTerm : Ball := .exact 0
lemma CA1_7_8I1R14MassTerm_sound : CA1_7_8I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R14Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R14Mass_sound)
def CA1_7_8I1R14H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R14H_sound : CA1_7_8I1R14H.Encloses (homogeneousEntropy CA1_7_8I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R14Value CA1_7_8I1R14MassTerm_sound CA1_7_8I1R14Entropy_sound) (by decide +kernel)
def CA1_7_8I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_7_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA1_7_8I1R15Raw_sound (a : PairSlot) :
    (CA1_7_8I1R15Raw a).Encloses (CA1_7_8I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA1_7_8I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R15Certificates_valid :
    CA1_7_8I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R15Certificates (CA1_7_8I1R15CertificateIndex a)).input
lemma CA1_7_8I1R15P_check : ∀ a : PairSlot, contains (CA1_7_8I1R15Raw a) (CA1_7_8I1R15P a) = true := by
  decide +kernel
lemma CA1_7_8I1R15P_sound (a : PairSlot) :
    (CA1_7_8I1R15P a).Encloses (CA1_7_8I1R15Value a) :=
  contains_sound (CA1_7_8I1R15Raw_sound a) (CA1_7_8I1R15P_check a)
def CA1_7_8I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R15Certificates (CA1_7_8I1R15CertificateIndex a)).output
lemma CA1_7_8I1R15Terms_sound (a : PairSlot) :
    (CA1_7_8I1R15Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R15Certificates_valid
    (CA1_7_8I1R15CertificateIndex a) (CA1_7_8I1R15P_sound a)
def CA1_7_8I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R15Entropy_sound : CA1_7_8I1R15Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R15Value CA1_7_8I1R15Terms CA1_7_8I1R15Terms_sound) (by decide +kernel)
def CA1_7_8I1R15Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R15Mass_sound : CA1_7_8I1R15Mass.Encloses (∑ a, CA1_7_8I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R15P CA1_7_8I1R15Value CA1_7_8I1R15P_sound) (by decide +kernel)
def CA1_7_8I1R15MassTerm : Ball := .exact 0
lemma CA1_7_8I1R15MassTerm_sound : CA1_7_8I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R15Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R15Mass_sound)
def CA1_7_8I1R15H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R15H_sound : CA1_7_8I1R15H.Encloses (homogeneousEntropy CA1_7_8I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R15Value CA1_7_8I1R15MassTerm_sound CA1_7_8I1R15Entropy_sound) (by decide +kernel)
def CA1_7_8I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_7_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 7 8)) A1_7_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA1_7_8I1R16Raw_sound (a : PairSlot) :
    (CA1_7_8I1R16Raw a).Encloses (CA1_7_8I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 7 8) (show (shape 1 7 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA1_7_8I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_7_8I1R16Certificates_valid :
    CA1_7_8I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_7_8I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R16Certificates (CA1_7_8I1R16CertificateIndex a)).input
lemma CA1_7_8I1R16P_check : ∀ a : PairSlot, contains (CA1_7_8I1R16Raw a) (CA1_7_8I1R16P a) = true := by
  decide +kernel
lemma CA1_7_8I1R16P_sound (a : PairSlot) :
    (CA1_7_8I1R16P a).Encloses (CA1_7_8I1R16Value a) :=
  contains_sound (CA1_7_8I1R16Raw_sound a) (CA1_7_8I1R16P_check a)
def CA1_7_8I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I1R16Certificates (CA1_7_8I1R16CertificateIndex a)).output
lemma CA1_7_8I1R16Terms_sound (a : PairSlot) :
    (CA1_7_8I1R16Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I1R16Certificates_valid
    (CA1_7_8I1R16CertificateIndex a) (CA1_7_8I1R16P_sound a)
def CA1_7_8I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R16Entropy_sound : CA1_7_8I1R16Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_7_8I1R16Value CA1_7_8I1R16Terms CA1_7_8I1R16Terms_sound) (by decide +kernel)
def CA1_7_8I1R16Mass : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R16Mass_sound : CA1_7_8I1R16Mass.Encloses (∑ a, CA1_7_8I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_7_8I1R16P CA1_7_8I1R16Value CA1_7_8I1R16P_sound) (by decide +kernel)
def CA1_7_8I1R16MassTerm : Ball := .exact 0
lemma CA1_7_8I1R16MassTerm_sound : CA1_7_8I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I1R16Value a))) :=
  entropyTerm_zero_ball (CA1_7_8I1R16Mass_sound)
def CA1_7_8I1R16H : Ball := ⟨0, 0⟩
lemma CA1_7_8I1R16H_sound : CA1_7_8I1R16H.Encloses (homogeneousEntropy CA1_7_8I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I1R16Value CA1_7_8I1R16MassTerm_sound CA1_7_8I1R16Entropy_sound) (by decide +kernel)
def CA1_7_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_7_8I1R0H
  | 1 => CA1_7_8I1R1H
  | 2 => CA1_7_8I1R2H
  | 3 => CA1_7_8I1R3H
  | 4 => CA1_7_8I1R4H
  | 5 => CA1_7_8I1R5H
  | 6 => CA1_7_8I1R6H
  | 7 => CA1_7_8I1R7H
  | 8 => CA1_7_8I1R8H
  | 9 => CA1_7_8I1R9H
  | 10 => CA1_7_8I1R10H
  | 11 => CA1_7_8I1R11H
  | 12 => CA1_7_8I1R12H
  | 13 => CA1_7_8I1R13H
  | 14 => CA1_7_8I1R14H
  | 15 => CA1_7_8I1R15H
  | 16 => CA1_7_8I1R16H
  | _ => (.exact 0)
lemma CA1_7_8I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_7_8I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_7_8I1R0H_sound
  · exact CA1_7_8I1R1H_sound
  · exact CA1_7_8I1R2H_sound
  · exact CA1_7_8I1R3H_sound
  · exact CA1_7_8I1R4H_sound
  · exact CA1_7_8I1R5H_sound
  · exact CA1_7_8I1R6H_sound
  · exact CA1_7_8I1R7H_sound
  · exact CA1_7_8I1R8H_sound
  · exact CA1_7_8I1R9H_sound
  · exact CA1_7_8I1R10H_sound
  · exact CA1_7_8I1R11H_sound
  · exact CA1_7_8I1R12H_sound
  · exact CA1_7_8I1R13H_sound
  · exact CA1_7_8I1R14H_sound
  · exact CA1_7_8I1R15H_sound
  · exact CA1_7_8I1R16H_sound
def CA1_7_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 7, 0 => Z1_7_0H1H
  | _, _, _ => (.exact 0)
lemma CA1_7_8I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 7 8))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_7_8I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 6 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 7 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact Z1_7_0H1H_sound
def CA1_7_8I1Singleton : Ball := ⟨(13901359324341445694796469 / 100000000000000000000000000000000), (1699 / 20000000000000000000000000000000)⟩
lemma CA1_7_8I1Singleton_sound : CA1_7_8I1Singleton.Encloses
    (singletonEntropy (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_7_8I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_7_8Law_sound u) CA1_7_8I1Singles_sound) (by decide +kernel)
def CA1_7_8I1Group : Ball := ⟨(28146986181848504264966179332283 / 25000000000000000000000000000000), (42415607743 / 25000000000000000000000000000000)⟩
lemma CA1_7_8I1Group_sound : CA1_7_8I1Group.Encloses
    (groupedEntropy (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_7_8I1Singleton_sound
    (finSumBall_sound 17 CA1_7_8I1ResidualEntropies _ CA1_7_8I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_7_8I1H : Ball := ⟨(21344728096657900435901341739 / 20000000000000000000000000000), (97509509711 / 20000000000000000000000000000000)⟩
lemma CA1_7_8I1_sound : CA1_7_8I1H.Encloses (stageACapacity (shape 1 7 8) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_7_8I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_7_8I1Group_sound)))
    (show contains (.add CA1_7_8I1PairH (.neg (.mul (.exact 2) CA1_7_8I1Group))) CA1_7_8I1H = true by decide +kernel)
  unfold CA1_7_8I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
