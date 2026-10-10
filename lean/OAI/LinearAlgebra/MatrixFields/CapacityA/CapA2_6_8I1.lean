import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_6_8I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_6_8I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA2_6_8I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA2_6_8I1R0Raw_sound (a : PairSlot) :
    (CA2_6_8I1R0Raw a).Encloses (CA2_6_8I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA2_6_8I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(482614198838945946544192483 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(135529298691786926273657801109 / 100000000000000000000000000000000), (11446131 / 25000000000000000000000000000000)⟩ ⟨(-87757272668467590908988813682361 / 10000000000000000000000000000000), (296461550987 / 100000000000000000000000000000000)⟩ ⟨-13, 482614198838945946544192483, 381469726562500000000000000⟩]
lemma CA2_6_8I1R0Certificates_valid :
    CA2_6_8I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_6_8I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R0Certificates (CA2_6_8I1R0CertificateIndex a)).input
lemma CA2_6_8I1R0P_check : ∀ a : PairSlot, contains (CA2_6_8I1R0Raw a) (CA2_6_8I1R0P a) = true := by
  decide +kernel
lemma CA2_6_8I1R0P_sound (a : PairSlot) :
    (CA2_6_8I1R0P a).Encloses (CA2_6_8I1R0Value a) :=
  contains_sound (CA2_6_8I1R0Raw_sound a) (CA2_6_8I1R0P_check a)
def CA2_6_8I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R0Certificates (CA2_6_8I1R0CertificateIndex a)).output
lemma CA2_6_8I1R0Terms_sound (a : PairSlot) :
    (CA2_6_8I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R0Certificates_valid
    (CA2_6_8I1R0CertificateIndex a) (CA2_6_8I1R0P_sound a)
def CA2_6_8I1R0Entropy : Ball := ⟨(135529298691786926273657801109 / 100000000000000000000000000000000), (11446131 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R0Entropy_sound : CA2_6_8I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R0Value CA2_6_8I1R0Terms CA2_6_8I1R0Terms_sound) (by decide +kernel)
def CA2_6_8I1R0Mass : Ball := ⟨(482614198838945946544192483 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R0Mass_sound : CA2_6_8I1R0Mass.Encloses (∑ a, CA2_6_8I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R0P CA2_6_8I1R0Value CA2_6_8I1R0P_sound) (by decide +kernel)
def CA2_6_8I1R0MassTermLogWitness : LogWitness := ⟨-13, 482614198838945946544192483, 381469726562500000000000000⟩
def CA2_6_8I1R0MassTermLog : Ball := ⟨(-87757272668467590908988813682361 / 10000000000000000000000000000000), (296461550987 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R0MassTermLog_sound : CA2_6_8I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R0Mass_sound) (w := CA2_6_8I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R0MassTerm : Ball := ⟨(135529298691786926273657801109 / 100000000000000000000000000000000), (11446131 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R0MassTerm_sound : CA2_6_8I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R0Mass_sound) CA2_6_8I1R0MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R0H : Ball := ⟨0, (11446131 / 12500000000000000000000000000000)⟩
lemma CA2_6_8I1R0H_sound : CA2_6_8I1R0H.Encloses (homogeneousEntropy CA2_6_8I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R0Value CA2_6_8I1R0MassTerm_sound CA2_6_8I1R0Entropy_sound) (by decide +kernel)
def CA2_6_8I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA2_6_8I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA2_6_8I1R1Raw_sound (a : PairSlot) :
    (CA2_6_8I1R1Raw a).Encloses (CA2_6_8I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA2_6_8I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(139327975552563848910158761633 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1729985614752913054347013600901 / 50000000000000000000000000000000), (1327673133 / 100000000000000000000000000000000)⟩ ⟨(-496665686239084569800190523237413 / 100000000000000000000000000000000), (190582414151 / 100000000000000000000000000000000)⟩ ⟨-8, 139327975552563848910158761633, 78125000000000000000000000000⟩]
lemma CA2_6_8I1R1Certificates_valid :
    CA2_6_8I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_6_8I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R1Certificates (CA2_6_8I1R1CertificateIndex a)).input
lemma CA2_6_8I1R1P_check : ∀ a : PairSlot, contains (CA2_6_8I1R1Raw a) (CA2_6_8I1R1P a) = true := by
  decide +kernel
lemma CA2_6_8I1R1P_sound (a : PairSlot) :
    (CA2_6_8I1R1P a).Encloses (CA2_6_8I1R1Value a) :=
  contains_sound (CA2_6_8I1R1Raw_sound a) (CA2_6_8I1R1P_check a)
def CA2_6_8I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R1Certificates (CA2_6_8I1R1CertificateIndex a)).output
lemma CA2_6_8I1R1Terms_sound (a : PairSlot) :
    (CA2_6_8I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R1Certificates_valid
    (CA2_6_8I1R1CertificateIndex a) (CA2_6_8I1R1P_sound a)
def CA2_6_8I1R1Entropy : Ball := ⟨(1729985614752913054347013600901 / 25000000000000000000000000000000), (1327673133 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R1Entropy_sound : CA2_6_8I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R1Value CA2_6_8I1R1Terms CA2_6_8I1R1Terms_sound) (by decide +kernel)
def CA2_6_8I1R1Mass : Ball := ⟨(139327975552563848910158761633 / 10000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R1Mass_sound : CA2_6_8I1R1Mass.Encloses (∑ a, CA2_6_8I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R1P CA2_6_8I1R1Value CA2_6_8I1R1P_sound) (by decide +kernel)
def CA2_6_8I1R1MassTermLogWitness : LogWitness := ⟨-7, 139327975552563848910158761633, 78125000000000000000000000000⟩
def CA2_6_8I1R1MassTermLog : Ball := ⟨(-427350968183090038858467330187083 / 100000000000000000000000000000000), (42351647617 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R1MassTermLog_sound : CA2_6_8I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R1Mass_sound) (w := CA2_6_8I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R1MassTerm : Ball := ⟨(5954194524737806017155259310491 / 100000000000000000000000000000000), (236030779 / 10000000000000000000000000000000)⟩
lemma CA2_6_8I1R1MassTerm_sound : CA2_6_8I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R1Mass_sound) CA2_6_8I1R1MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R1H : Ball := ⟨(965747934273846200232795093113 / 100000000000000000000000000000000), (626956757 / 12500000000000000000000000000000)⟩
lemma CA2_6_8I1R1H_sound : CA2_6_8I1R1H.Encloses (homogeneousEntropy CA2_6_8I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R1Value CA2_6_8I1R1MassTerm_sound CA2_6_8I1R1Entropy_sound) (by decide +kernel)
def CA2_6_8I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA2_6_8I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA2_6_8I1R2Raw_sound (a : PairSlot) :
    (CA2_6_8I1R2Raw a).Encloses (CA2_6_8I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA2_6_8I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3783651321028126610853790513179 / 100000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩ ⟨(12389493168156305713771513717961 / 100000000000000000000000000000000), (120182903 / 2500000000000000000000000000000)⟩ ⟨(-65489613692996028953092399509311 / 20000000000000000000000000000000), (7940933929 / 6250000000000000000000000000000)⟩ ⟨-5, 3783651321028126610853790513179, 3125000000000000000000000000000⟩,
   .log ⟨(96587081401284219179413856493 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(107331159910835579347332177653 / 5000000000000000000000000000000), (818124429 / 100000000000000000000000000000000)⟩ ⟨(-555618610448086834909677471211931 / 100000000000000000000000000000000), (42351647573 / 20000000000000000000000000000000)⟩ ⟨-9, 96587081401284219179413856493, 48828125000000000000000000000⟩,
   .log ⟨(3566440220939032184575400192723 / 25000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩ ⟨(13889914174162227826278016912847 / 50000000000000000000000000000000), (12083569723 / 100000000000000000000000000000000)⟩ ⟨(-194730786354033691219360199838101 / 100000000000000000000000000000000), (21175823823 / 25000000000000000000000000000000)⟩ ⟨-3, 3566440220939032184575400192723, 3125000000000000000000000000000⟩]
lemma CA2_6_8I1R2Certificates_valid :
    CA2_6_8I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_6_8I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R2Certificates (CA2_6_8I1R2CertificateIndex a)).input
lemma CA2_6_8I1R2P_check : ∀ a : PairSlot, contains (CA2_6_8I1R2Raw a) (CA2_6_8I1R2P a) = true := by
  decide +kernel
lemma CA2_6_8I1R2P_sound (a : PairSlot) :
    (CA2_6_8I1R2P a).Encloses (CA2_6_8I1R2Value a) :=
  contains_sound (CA2_6_8I1R2Raw_sound a) (CA2_6_8I1R2P_check a)
def CA2_6_8I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R2Certificates (CA2_6_8I1R2CertificateIndex a)).output
lemma CA2_6_8I1R2Terms_sound (a : PairSlot) :
    (CA2_6_8I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R2Certificates_valid
    (CA2_6_8I1R2CertificateIndex a) (CA2_6_8I1R2P_sound a)
def CA2_6_8I1R2Entropy : Ball := ⟨(7106507635133811281749043545967 / 12500000000000000000000000000000), (23334450821 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R2Entropy_sound : CA2_6_8I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R2Value CA2_6_8I1R2Terms CA2_6_8I1R2Terms_sound) (by decide +kernel)
def CA2_6_8I1R2Mass : Ball := ⟨(11302880088511327856722246324597 / 50000000000000000000000000000000), (73 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R2Mass_sound : CA2_6_8I1R2Mass.Encloses (∑ a, CA2_6_8I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R2P CA2_6_8I1R2Value CA2_6_8I1R2P_sound) (by decide +kernel)
def CA2_6_8I1R2MassTermLogWitness : LogWitness := ⟨-3, 11302880088511327856722246324597, 6250000000000000000000000000000⟩
def CA2_6_8I1R2MassTermLog : Ball := ⟨(-290422936932713047863097462883 / 195312500000000000000000000000), (42351647689 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R2MassTermLog_sound : CA2_6_8I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R2Mass_sound) (w := CA2_6_8I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R2MassTerm : Ball := ⟨(33613984062502332850118446500137 / 100000000000000000000000000000000), (19147824033 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R2MassTerm_sound : CA2_6_8I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R2Mass_sound) CA2_6_8I1R2MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R2H : Ball := ⟨(23238077018568157403873901867599 / 100000000000000000000000000000000), (21241137427 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R2H_sound : CA2_6_8I1R2H.Encloses (homogeneousEntropy CA2_6_8I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R2Value CA2_6_8I1R2MassTerm_sound CA2_6_8I1R2Entropy_sound) (by decide +kernel)
def CA2_6_8I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA2_6_8I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA2_6_8I1R3Raw_sound (a : PairSlot) :
    (CA2_6_8I1R3Raw a).Encloses (CA2_6_8I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA2_6_8I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50539334642013499758943026079 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1947820245347008096111170450639 / 50000000000000000000000000000000), (684935723 / 50000000000000000000000000000000)⟩ ⟨(-60219810072937825623662557649961 / 12500000000000000000000000000000), (33881318041 / 20000000000000000000000000000000)⟩ ⟨-7, 50539334642013499758943026079, 48828125000000000000000000000⟩,
   .log ⟨(5767145425469417847973279851969 / 25000000000000000000000000000000), (41 / 50000000000000000000000000000000)⟩ ⟨(16917328170640872016017922106491 / 50000000000000000000000000000000), (2442481119 / 12500000000000000000000000000000)⟩ ⟨(-146669859372099005298085022603483 / 100000000000000000000000000000000), (84703295087 / 100000000000000000000000000000000)⟩ ⟨-3, 5767145425469417847973279851969, 3125000000000000000000000000000⟩,
   .log ⟨(1054152678469486069564148874939 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(8136552735437532741595721636497 / 100000000000000000000000000000000), (625031443 / 20000000000000000000000000000000)⟩ ⟨(-192964285478335875919877671941113 / 50000000000000000000000000000000), (1852884577 / 1250000000000000000000000000000)⟩ ⟨-6, 1054152678469486069564148874939, 781250000000000000000000000000⟩]
lemma CA2_6_8I1R3Certificates_valid :
    CA2_6_8I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_6_8I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R3Certificates (CA2_6_8I1R3CertificateIndex a)).input
lemma CA2_6_8I1R3P_check : ∀ a : PairSlot, contains (CA2_6_8I1R3Raw a) (CA2_6_8I1R3P a) = true := by
  decide +kernel
lemma CA2_6_8I1R3P_sound (a : PairSlot) :
    (CA2_6_8I1R3P a).Encloses (CA2_6_8I1R3Value a) :=
  contains_sound (CA2_6_8I1R3Raw_sound a) (CA2_6_8I1R3P_check a)
def CA2_6_8I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R3Certificates (CA2_6_8I1R3CertificateIndex a)).output
lemma CA2_6_8I1R3Terms_sound (a : PairSlot) :
    (CA2_6_8I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R3Certificates_valid
    (CA2_6_8I1R3CertificateIndex a) (CA2_6_8I1R3P_sound a)
def CA2_6_8I1R3Entropy : Ball := ⟨(45866849567413292965853906750757 / 50000000000000000000000000000000), (24034877613 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R3Entropy_sound : CA2_6_8I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R3Value CA2_6_8I1R3Terms CA2_6_8I1R3Terms_sound) (by decide +kernel)
def CA2_6_8I1R3Mass : Ball := ⟨(12992758206544429763582252787509 / 25000000000000000000000000000000), (3 / 1562500000000000000000000000000)⟩
lemma CA2_6_8I1R3Mass_sound : CA2_6_8I1R3Mass.Encloses (∑ a, CA2_6_8I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R3P CA2_6_8I1R3Value CA2_6_8I1R3P_sound) (by decide +kernel)
def CA2_6_8I1R3MassTermLogWitness : LogWitness := ⟨-1, 12992758206544429763582252787509, 12500000000000000000000000000000⟩
def CA2_6_8I1R3MassTermLog : Ball := ⟨(-65448368365785218025485415970023 / 100000000000000000000000000000000), (8470329547 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I1R3MassTermLog_sound : CA2_6_8I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R3Mass_sound) (w := CA2_6_8I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R3MassTerm : Ball := ⟨(3401419300757994963401413575821 / 10000000000000000000000000000000), (22010588873 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R3MassTerm_sound : CA2_6_8I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R3Mass_sound) CA2_6_8I1R3MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R3H : Ball := ⟨(7214938265905829537211709717913 / 12500000000000000000000000000000), (70080344099 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R3H_sound : CA2_6_8I1R3H.Encloses (homogeneousEntropy CA2_6_8I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R3Value CA2_6_8I1R3MassTerm_sound CA2_6_8I1R3Entropy_sound) (by decide +kernel)
def CA2_6_8I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA2_6_8I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA2_6_8I1R4Raw_sound (a : PairSlot) :
    (CA2_6_8I1R4Raw a).Encloses (CA2_6_8I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA2_6_8I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2954896846137971690902062987 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(240140821228559693148592536003 / 100000000000000000000000000000000), (81344097 / 100000000000000000000000000000000)⟩ ⟨(-812687662997176937812792579599483 / 100000000000000000000000000000000), (275285711263 / 100000000000000000000000000000000)⟩ ⟨-12, 2954896846137971690902062987, 2441406250000000000000000000⟩,
   .log ⟨(614044372111436108901844232643 / 25000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩ ⟨(4551989418880959818631452637923 / 50000000000000000000000000000000), (3640810781 / 100000000000000000000000000000000)⟩ ⟨(-92664097775797009083015096068037 / 25000000000000000000000000000000), (18528845809 / 12500000000000000000000000000000)⟩ ⟨-6, 614044372111436108901844232643, 390625000000000000000000000000⟩,
   .log ⟨(7531147980704175769209851871551 / 50000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩ ⟨(28512557544393646301591490039757 / 100000000000000000000000000000000), (6379130597 / 50000000000000000000000000000000)⟩ ⟨(-189297552095953313842979960916533 / 100000000000000000000000000000000), (84703295309 / 100000000000000000000000000000000)⟩ ⟨-3, 7531147980704175769209851871551, 6250000000000000000000000000000⟩,
   .log ⟨(617862331104690817659332363237 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(2714585947259703178542502146337 / 50000000000000000000000000000000), (2093399049 / 100000000000000000000000000000000)⟩ ⟨(-439351261697121126206865800526079 / 100000000000000000000000000000000), (169406590111 / 100000000000000000000000000000000)⟩ ⟨-7, 617862331104690817659332363237, 390625000000000000000000000000⟩,
   .log ⟨(5028098869064629967733216613 / 5000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(347046988298046308124279644971 / 50000000000000000000000000000000), (117121557 / 50000000000000000000000000000000)⟩ ⟨(-345107561859266862803994865368403 / 50000000000000000000000000000000), (232934062501 / 100000000000000000000000000000000)⟩ ⟨-10, 5028098869064629967733216613, 4882812500000000000000000000⟩]
lemma CA2_6_8I1R4Certificates_valid :
    CA2_6_8I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_6_8I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R4Certificates (CA2_6_8I1R4CertificateIndex a)).input
lemma CA2_6_8I1R4P_check : ∀ a : PairSlot, contains (CA2_6_8I1R4Raw a) (CA2_6_8I1R4P a) = true := by
  decide +kernel
lemma CA2_6_8I1R4P_sound (a : PairSlot) :
    (CA2_6_8I1R4P a).Encloses (CA2_6_8I1R4Value a) :=
  contains_sound (CA2_6_8I1R4Raw_sound a) (CA2_6_8I1R4P_check a)
def CA2_6_8I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R4Certificates (CA2_6_8I1R4CertificateIndex a)).output
lemma CA2_6_8I1R4Terms_sound (a : PairSlot) :
    (CA2_6_8I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R4Certificates_valid
    (CA2_6_8I1R4CertificateIndex a) (CA2_6_8I1R4P_sound a)
def CA2_6_8I1R4Entropy : Ball := ⟨(11750646925601902058566610707749 / 20000000000000000000000000000000), (12311806081 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R4Entropy_sound : CA2_6_8I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R4Value CA2_6_8I1R4Terms CA2_6_8I1R4Terms_sound) (by decide +kernel)
def CA2_6_8I1R4Mass : Ball := ⟨(11302880088511327856722246324597 / 50000000000000000000000000000000), (141 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R4Mass_sound : CA2_6_8I1R4Mass.Encloses (∑ a, CA2_6_8I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R4P CA2_6_8I1R4Value CA2_6_8I1R4P_sound) (by decide +kernel)
def CA2_6_8I1R4MassTermLogWitness : LogWitness := ⟨-3, 11302880088511327856722246324597, 6250000000000000000000000000000⟩
def CA2_6_8I1R4MassTermLog : Ball := ⟨(-290422936932713047863097462883 / 195312500000000000000000000000), (21175823839 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R4MassTermLog_sound : CA2_6_8I1R4MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R4Mass_sound) (w := CA2_6_8I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R4MassTerm : Ball := ⟨(33613984062502332850118446500137 / 100000000000000000000000000000000), (19147824021 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R4MassTerm_sound : CA2_6_8I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R4Mass_sound) CA2_6_8I1R4MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R4H : Ball := ⟨(1571203160344198590169662939913 / 6250000000000000000000000000000), (43771436183 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R4H_sound : CA2_6_8I1R4H.Encloses (homogeneousEntropy CA2_6_8I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R4Value CA2_6_8I1R4MassTerm_sound CA2_6_8I1R4Entropy_sound) (by decide +kernel)
def CA2_6_8I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA2_6_8I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA2_6_8I1R5Raw_sound (a : PairSlot) :
    (CA2_6_8I1R5Raw a).Encloses (CA2_6_8I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA2_6_8I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(27078558314774540953224986201 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(11121412015766170351601433071 / 5000000000000000000000000000000), (74543411 / 100000000000000000000000000000000)⟩ ⟨(-821418325635019572344764453392313 / 100000000000000000000000000000000), (275285711571 / 100000000000000000000000000000000)⟩ ⟨-12, 27078558314774540953224986201, 24414062500000000000000000000⟩,
   .log ⟨(154399745645881389037673594901 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(3141779208094060806487212302823 / 100000000000000000000000000000000), (73564693 / 6250000000000000000000000000000)⟩ ⟨(-254354305681612672480366648598361 / 50000000000000000000000000000000), (4764560357 / 2500000000000000000000000000000)⟩ ⟨-8, 154399745645881389037673594901, 97656250000000000000000000000⟩,
   .log ⟨(1299058421612978686171861059 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(196480151830395347388024227653 / 50000000000000000000000000000000), (132041443 / 100000000000000000000000000000000)⟩ ⟨(-9453007874851547468820693070053 / 1250000000000000000000000000000), (6352747153 / 2500000000000000000000000000000)⟩ ⟨-11, 1299058421612978686171861059, 1220703125000000000000000000⟩]
lemma CA2_6_8I1R5Certificates_valid :
    CA2_6_8I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA2_6_8I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R5Certificates (CA2_6_8I1R5CertificateIndex a)).input
lemma CA2_6_8I1R5P_check : ∀ a : PairSlot, contains (CA2_6_8I1R5Raw a) (CA2_6_8I1R5P a) = true := by
  decide +kernel
lemma CA2_6_8I1R5P_sound (a : PairSlot) :
    (CA2_6_8I1R5P a).Encloses (CA2_6_8I1R5Value a) :=
  contains_sound (CA2_6_8I1R5Raw_sound a) (CA2_6_8I1R5P_check a)
def CA2_6_8I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R5Certificates (CA2_6_8I1R5CertificateIndex a)).output
lemma CA2_6_8I1R5Terms_sound (a : PairSlot) :
    (CA2_6_8I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R5Certificates_valid
    (CA2_6_8I1R5CertificateIndex a) (CA2_6_8I1R5P_sound a)
def CA2_6_8I1R5Entropy : Ball := ⟨(3757167752070174908295289419549 / 50000000000000000000000000000000), (691809971 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R5Entropy_sound : CA2_6_8I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R5Value CA2_6_8I1R5Terms CA2_6_8I1R5Terms_sound) (by decide +kernel)
def CA2_6_8I1R5Mass : Ball := ⟨(139327975552563848910158761633 / 10000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R5Mass_sound : CA2_6_8I1R5Mass.Encloses (∑ a, CA2_6_8I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R5P CA2_6_8I1R5Value CA2_6_8I1R5P_sound) (by decide +kernel)
def CA2_6_8I1R5MassTermLogWitness : LogWitness := ⟨-7, 139327975552563848910158761633, 78125000000000000000000000000⟩
def CA2_6_8I1R5MassTermLog : Ball := ⟨(-427350968183090038858467330187083 / 100000000000000000000000000000000), (42351647689 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1R5MassTermLog_sound : CA2_6_8I1R5MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R5Mass_sound) (w := CA2_6_8I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R5MassTerm : Ball := ⟨(5954194524737806017155259310491 / 100000000000000000000000000000000), (2360307811 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1R5MassTerm_sound : CA2_6_8I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R5Mass_sound) CA2_6_8I1R5MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R5H : Ball := ⟨(1560140979402543799435319528607 / 100000000000000000000000000000000), (1025509539 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I1R5H_sound : CA2_6_8I1R5H.Encloses (homogeneousEntropy CA2_6_8I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R5Value CA2_6_8I1R5MassTerm_sound CA2_6_8I1R5Entropy_sound) (by decide +kernel)
def CA2_6_8I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA2_6_8I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA2_6_8I1R6Raw_sound (a : PairSlot) :
    (CA2_6_8I1R6Raw a).Encloses (CA2_6_8I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA2_6_8I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1200291507443088968093509091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(12767757428104096652180005201 / 50000000000000000000000000000000), (8641847 / 100000000000000000000000000000000)⟩ ⟨(-16620646616012609894185777136421 / 1562500000000000000000000000000), (359989044267 / 100000000000000000000000000000000)⟩ ⟨-16, 1200291507443088968093509091, 762939453125000000000000000⟩,
   .log ⟨(42409102545603473825261857 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(563490736240623134868651979 / 25000000000000000000000000000000), (1207 / 160000000000000000000000000000)⟩ ⟨(-332175584023906608735495021794391 / 25000000000000000000000000000000), (444692886839 / 100000000000000000000000000000000)⟩ ⟨-20, 42409102545603473825261857, 23841857910156250000000000⟩,
   .log ⟨(10295932270523190320885075407 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(23632193039650510747454854773 / 25000000000000000000000000000000), (8175937 / 25000000000000000000000000000000)⟩ ⟨(-918117657293005291618197560044797 / 100000000000000000000000000000000), (31763737467 / 10000000000000000000000000000000)⟩ ⟨-14, 10295932270523190320885075407, 6103515625000000000000000000⟩]
lemma CA2_6_8I1R6Certificates_valid :
    CA2_6_8I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA2_6_8I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R6Certificates (CA2_6_8I1R6CertificateIndex a)).input
lemma CA2_6_8I1R6P_check : ∀ a : PairSlot, contains (CA2_6_8I1R6Raw a) (CA2_6_8I1R6P a) = true := by
  decide +kernel
lemma CA2_6_8I1R6P_sound (a : PairSlot) :
    (CA2_6_8I1R6P a).Encloses (CA2_6_8I1R6Value a) :=
  contains_sound (CA2_6_8I1R6Raw_sound a) (CA2_6_8I1R6P_check a)
def CA2_6_8I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R6Certificates (CA2_6_8I1R6CertificateIndex a)).output
lemma CA2_6_8I1R6Terms_sound (a : PairSlot) :
    (CA2_6_8I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R6Certificates_valid
    (CA2_6_8I1R6CertificateIndex a) (CA2_6_8I1R6P_sound a)
def CA2_6_8I1R6Entropy : Ball := ⟨(9381732985058963417343040983 / 6250000000000000000000000000000), (201157 / 390625000000000000000000000000)⟩
lemma CA2_6_8I1R6Entropy_sound : CA2_6_8I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R6Value CA2_6_8I1R6Terms CA2_6_8I1R6Terms_sound) (by decide +kernel)
def CA2_6_8I1R6Mass : Ball := ⟨(15436371120660373983861206627 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R6Mass_sound : CA2_6_8I1R6Mass.Encloses (∑ a, CA2_6_8I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R6P CA2_6_8I1R6Value CA2_6_8I1R6P_sound) (by decide +kernel)
def CA2_6_8I1R6MassTermLogWitness : LogWitness := ⟨-13, 15436371120660373983861206627, 12207031250000000000000000000⟩
def CA2_6_8I1R6MassTermLog : Ball := ⟨(-438809948952151772011195872757127 / 50000000000000000000000000000000), (29646157043 / 10000000000000000000000000000000)⟩
lemma CA2_6_8I1R6MassTermLog_sound : CA2_6_8I1R6MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I1R6Mass_sound) (w := CA2_6_8I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I1R6MassTerm : Ball := ⟨(135472664469268970989558269301 / 100000000000000000000000000000000), (22881481 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R6MassTerm_sound : CA2_6_8I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I1R6Mass_sound) CA2_6_8I1R6MassTermLog_sound) (by decide +kernel)
def CA2_6_8I1R6H : Ball := ⟨(14635063291674443687930386427 / 100000000000000000000000000000000), (48629577 / 50000000000000000000000000000000)⟩
lemma CA2_6_8I1R6H_sound : CA2_6_8I1R6H.Encloses (homogeneousEntropy CA2_6_8I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R6Value CA2_6_8I1R6MassTerm_sound CA2_6_8I1R6Entropy_sound) (by decide +kernel)
def CA2_6_8I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA2_6_8I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA2_6_8I1R7Raw_sound (a : PairSlot) :
    (CA2_6_8I1R7Raw a).Encloses (CA2_6_8I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA2_6_8I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R7Certificates_valid :
    CA2_6_8I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R7Certificates (CA2_6_8I1R7CertificateIndex a)).input
lemma CA2_6_8I1R7P_check : ∀ a : PairSlot, contains (CA2_6_8I1R7Raw a) (CA2_6_8I1R7P a) = true := by
  decide +kernel
lemma CA2_6_8I1R7P_sound (a : PairSlot) :
    (CA2_6_8I1R7P a).Encloses (CA2_6_8I1R7Value a) :=
  contains_sound (CA2_6_8I1R7Raw_sound a) (CA2_6_8I1R7P_check a)
def CA2_6_8I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R7Certificates (CA2_6_8I1R7CertificateIndex a)).output
lemma CA2_6_8I1R7Terms_sound (a : PairSlot) :
    (CA2_6_8I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R7Certificates_valid
    (CA2_6_8I1R7CertificateIndex a) (CA2_6_8I1R7P_sound a)
def CA2_6_8I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R7Entropy_sound : CA2_6_8I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R7Value CA2_6_8I1R7Terms CA2_6_8I1R7Terms_sound) (by decide +kernel)
def CA2_6_8I1R7Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R7Mass_sound : CA2_6_8I1R7Mass.Encloses (∑ a, CA2_6_8I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R7P CA2_6_8I1R7Value CA2_6_8I1R7P_sound) (by decide +kernel)
def CA2_6_8I1R7MassTerm : Ball := .exact 0
lemma CA2_6_8I1R7MassTerm_sound : CA2_6_8I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R7Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R7Mass_sound)
def CA2_6_8I1R7H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R7H_sound : CA2_6_8I1R7H.Encloses (homogeneousEntropy CA2_6_8I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R7Value CA2_6_8I1R7MassTerm_sound CA2_6_8I1R7Entropy_sound) (by decide +kernel)
def CA2_6_8I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA2_6_8I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA2_6_8I1R8Raw_sound (a : PairSlot) :
    (CA2_6_8I1R8Raw a).Encloses (CA2_6_8I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA2_6_8I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R8Certificates_valid :
    CA2_6_8I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R8Certificates (CA2_6_8I1R8CertificateIndex a)).input
lemma CA2_6_8I1R8P_check : ∀ a : PairSlot, contains (CA2_6_8I1R8Raw a) (CA2_6_8I1R8P a) = true := by
  decide +kernel
lemma CA2_6_8I1R8P_sound (a : PairSlot) :
    (CA2_6_8I1R8P a).Encloses (CA2_6_8I1R8Value a) :=
  contains_sound (CA2_6_8I1R8Raw_sound a) (CA2_6_8I1R8P_check a)
def CA2_6_8I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R8Certificates (CA2_6_8I1R8CertificateIndex a)).output
lemma CA2_6_8I1R8Terms_sound (a : PairSlot) :
    (CA2_6_8I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R8Certificates_valid
    (CA2_6_8I1R8CertificateIndex a) (CA2_6_8I1R8P_sound a)
def CA2_6_8I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R8Entropy_sound : CA2_6_8I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R8Value CA2_6_8I1R8Terms CA2_6_8I1R8Terms_sound) (by decide +kernel)
def CA2_6_8I1R8Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R8Mass_sound : CA2_6_8I1R8Mass.Encloses (∑ a, CA2_6_8I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R8P CA2_6_8I1R8Value CA2_6_8I1R8P_sound) (by decide +kernel)
def CA2_6_8I1R8MassTerm : Ball := .exact 0
lemma CA2_6_8I1R8MassTerm_sound : CA2_6_8I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R8Mass_sound)
def CA2_6_8I1R8H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R8H_sound : CA2_6_8I1R8H.Encloses (homogeneousEntropy CA2_6_8I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R8Value CA2_6_8I1R8MassTerm_sound CA2_6_8I1R8Entropy_sound) (by decide +kernel)
def CA2_6_8I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA2_6_8I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA2_6_8I1R9Raw_sound (a : PairSlot) :
    (CA2_6_8I1R9Raw a).Encloses (CA2_6_8I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA2_6_8I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R9Certificates_valid :
    CA2_6_8I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R9Certificates (CA2_6_8I1R9CertificateIndex a)).input
lemma CA2_6_8I1R9P_check : ∀ a : PairSlot, contains (CA2_6_8I1R9Raw a) (CA2_6_8I1R9P a) = true := by
  decide +kernel
lemma CA2_6_8I1R9P_sound (a : PairSlot) :
    (CA2_6_8I1R9P a).Encloses (CA2_6_8I1R9Value a) :=
  contains_sound (CA2_6_8I1R9Raw_sound a) (CA2_6_8I1R9P_check a)
def CA2_6_8I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R9Certificates (CA2_6_8I1R9CertificateIndex a)).output
lemma CA2_6_8I1R9Terms_sound (a : PairSlot) :
    (CA2_6_8I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R9Certificates_valid
    (CA2_6_8I1R9CertificateIndex a) (CA2_6_8I1R9P_sound a)
def CA2_6_8I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R9Entropy_sound : CA2_6_8I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R9Value CA2_6_8I1R9Terms CA2_6_8I1R9Terms_sound) (by decide +kernel)
def CA2_6_8I1R9Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R9Mass_sound : CA2_6_8I1R9Mass.Encloses (∑ a, CA2_6_8I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R9P CA2_6_8I1R9Value CA2_6_8I1R9P_sound) (by decide +kernel)
def CA2_6_8I1R9MassTerm : Ball := .exact 0
lemma CA2_6_8I1R9MassTerm_sound : CA2_6_8I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R9Mass_sound)
def CA2_6_8I1R9H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R9H_sound : CA2_6_8I1R9H.Encloses (homogeneousEntropy CA2_6_8I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R9Value CA2_6_8I1R9MassTerm_sound CA2_6_8I1R9Entropy_sound) (by decide +kernel)
def CA2_6_8I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA2_6_8I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA2_6_8I1R10Raw_sound (a : PairSlot) :
    (CA2_6_8I1R10Raw a).Encloses (CA2_6_8I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA2_6_8I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R10Certificates_valid :
    CA2_6_8I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R10Certificates (CA2_6_8I1R10CertificateIndex a)).input
lemma CA2_6_8I1R10P_check : ∀ a : PairSlot, contains (CA2_6_8I1R10Raw a) (CA2_6_8I1R10P a) = true := by
  decide +kernel
lemma CA2_6_8I1R10P_sound (a : PairSlot) :
    (CA2_6_8I1R10P a).Encloses (CA2_6_8I1R10Value a) :=
  contains_sound (CA2_6_8I1R10Raw_sound a) (CA2_6_8I1R10P_check a)
def CA2_6_8I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R10Certificates (CA2_6_8I1R10CertificateIndex a)).output
lemma CA2_6_8I1R10Terms_sound (a : PairSlot) :
    (CA2_6_8I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R10Certificates_valid
    (CA2_6_8I1R10CertificateIndex a) (CA2_6_8I1R10P_sound a)
def CA2_6_8I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R10Entropy_sound : CA2_6_8I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R10Value CA2_6_8I1R10Terms CA2_6_8I1R10Terms_sound) (by decide +kernel)
def CA2_6_8I1R10Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R10Mass_sound : CA2_6_8I1R10Mass.Encloses (∑ a, CA2_6_8I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R10P CA2_6_8I1R10Value CA2_6_8I1R10P_sound) (by decide +kernel)
def CA2_6_8I1R10MassTerm : Ball := .exact 0
lemma CA2_6_8I1R10MassTerm_sound : CA2_6_8I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R10Mass_sound)
def CA2_6_8I1R10H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R10H_sound : CA2_6_8I1R10H.Encloses (homogeneousEntropy CA2_6_8I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R10Value CA2_6_8I1R10MassTerm_sound CA2_6_8I1R10Entropy_sound) (by decide +kernel)
def CA2_6_8I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA2_6_8I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA2_6_8I1R11Raw_sound (a : PairSlot) :
    (CA2_6_8I1R11Raw a).Encloses (CA2_6_8I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA2_6_8I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R11Certificates_valid :
    CA2_6_8I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R11Certificates (CA2_6_8I1R11CertificateIndex a)).input
lemma CA2_6_8I1R11P_check : ∀ a : PairSlot, contains (CA2_6_8I1R11Raw a) (CA2_6_8I1R11P a) = true := by
  decide +kernel
lemma CA2_6_8I1R11P_sound (a : PairSlot) :
    (CA2_6_8I1R11P a).Encloses (CA2_6_8I1R11Value a) :=
  contains_sound (CA2_6_8I1R11Raw_sound a) (CA2_6_8I1R11P_check a)
def CA2_6_8I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R11Certificates (CA2_6_8I1R11CertificateIndex a)).output
lemma CA2_6_8I1R11Terms_sound (a : PairSlot) :
    (CA2_6_8I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R11Certificates_valid
    (CA2_6_8I1R11CertificateIndex a) (CA2_6_8I1R11P_sound a)
def CA2_6_8I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R11Entropy_sound : CA2_6_8I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R11Value CA2_6_8I1R11Terms CA2_6_8I1R11Terms_sound) (by decide +kernel)
def CA2_6_8I1R11Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R11Mass_sound : CA2_6_8I1R11Mass.Encloses (∑ a, CA2_6_8I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R11P CA2_6_8I1R11Value CA2_6_8I1R11P_sound) (by decide +kernel)
def CA2_6_8I1R11MassTerm : Ball := .exact 0
lemma CA2_6_8I1R11MassTerm_sound : CA2_6_8I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R11Mass_sound)
def CA2_6_8I1R11H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R11H_sound : CA2_6_8I1R11H.Encloses (homogeneousEntropy CA2_6_8I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R11Value CA2_6_8I1R11MassTerm_sound CA2_6_8I1R11Entropy_sound) (by decide +kernel)
def CA2_6_8I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA2_6_8I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA2_6_8I1R12Raw_sound (a : PairSlot) :
    (CA2_6_8I1R12Raw a).Encloses (CA2_6_8I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA2_6_8I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R12Certificates_valid :
    CA2_6_8I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R12Certificates (CA2_6_8I1R12CertificateIndex a)).input
lemma CA2_6_8I1R12P_check : ∀ a : PairSlot, contains (CA2_6_8I1R12Raw a) (CA2_6_8I1R12P a) = true := by
  decide +kernel
lemma CA2_6_8I1R12P_sound (a : PairSlot) :
    (CA2_6_8I1R12P a).Encloses (CA2_6_8I1R12Value a) :=
  contains_sound (CA2_6_8I1R12Raw_sound a) (CA2_6_8I1R12P_check a)
def CA2_6_8I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R12Certificates (CA2_6_8I1R12CertificateIndex a)).output
lemma CA2_6_8I1R12Terms_sound (a : PairSlot) :
    (CA2_6_8I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R12Certificates_valid
    (CA2_6_8I1R12CertificateIndex a) (CA2_6_8I1R12P_sound a)
def CA2_6_8I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R12Entropy_sound : CA2_6_8I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R12Value CA2_6_8I1R12Terms CA2_6_8I1R12Terms_sound) (by decide +kernel)
def CA2_6_8I1R12Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R12Mass_sound : CA2_6_8I1R12Mass.Encloses (∑ a, CA2_6_8I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R12P CA2_6_8I1R12Value CA2_6_8I1R12P_sound) (by decide +kernel)
def CA2_6_8I1R12MassTerm : Ball := .exact 0
lemma CA2_6_8I1R12MassTerm_sound : CA2_6_8I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R12Mass_sound)
def CA2_6_8I1R12H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R12H_sound : CA2_6_8I1R12H.Encloses (homogeneousEntropy CA2_6_8I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R12Value CA2_6_8I1R12MassTerm_sound CA2_6_8I1R12Entropy_sound) (by decide +kernel)
def CA2_6_8I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA2_6_8I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA2_6_8I1R13Raw_sound (a : PairSlot) :
    (CA2_6_8I1R13Raw a).Encloses (CA2_6_8I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA2_6_8I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R13Certificates_valid :
    CA2_6_8I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R13Certificates (CA2_6_8I1R13CertificateIndex a)).input
lemma CA2_6_8I1R13P_check : ∀ a : PairSlot, contains (CA2_6_8I1R13Raw a) (CA2_6_8I1R13P a) = true := by
  decide +kernel
lemma CA2_6_8I1R13P_sound (a : PairSlot) :
    (CA2_6_8I1R13P a).Encloses (CA2_6_8I1R13Value a) :=
  contains_sound (CA2_6_8I1R13Raw_sound a) (CA2_6_8I1R13P_check a)
def CA2_6_8I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R13Certificates (CA2_6_8I1R13CertificateIndex a)).output
lemma CA2_6_8I1R13Terms_sound (a : PairSlot) :
    (CA2_6_8I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R13Certificates_valid
    (CA2_6_8I1R13CertificateIndex a) (CA2_6_8I1R13P_sound a)
def CA2_6_8I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R13Entropy_sound : CA2_6_8I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R13Value CA2_6_8I1R13Terms CA2_6_8I1R13Terms_sound) (by decide +kernel)
def CA2_6_8I1R13Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R13Mass_sound : CA2_6_8I1R13Mass.Encloses (∑ a, CA2_6_8I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R13P CA2_6_8I1R13Value CA2_6_8I1R13P_sound) (by decide +kernel)
def CA2_6_8I1R13MassTerm : Ball := .exact 0
lemma CA2_6_8I1R13MassTerm_sound : CA2_6_8I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R13Mass_sound)
def CA2_6_8I1R13H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R13H_sound : CA2_6_8I1R13H.Encloses (homogeneousEntropy CA2_6_8I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R13Value CA2_6_8I1R13MassTerm_sound CA2_6_8I1R13Entropy_sound) (by decide +kernel)
def CA2_6_8I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA2_6_8I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA2_6_8I1R14Raw_sound (a : PairSlot) :
    (CA2_6_8I1R14Raw a).Encloses (CA2_6_8I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA2_6_8I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R14Certificates_valid :
    CA2_6_8I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R14Certificates (CA2_6_8I1R14CertificateIndex a)).input
lemma CA2_6_8I1R14P_check : ∀ a : PairSlot, contains (CA2_6_8I1R14Raw a) (CA2_6_8I1R14P a) = true := by
  decide +kernel
lemma CA2_6_8I1R14P_sound (a : PairSlot) :
    (CA2_6_8I1R14P a).Encloses (CA2_6_8I1R14Value a) :=
  contains_sound (CA2_6_8I1R14Raw_sound a) (CA2_6_8I1R14P_check a)
def CA2_6_8I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R14Certificates (CA2_6_8I1R14CertificateIndex a)).output
lemma CA2_6_8I1R14Terms_sound (a : PairSlot) :
    (CA2_6_8I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R14Certificates_valid
    (CA2_6_8I1R14CertificateIndex a) (CA2_6_8I1R14P_sound a)
def CA2_6_8I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R14Entropy_sound : CA2_6_8I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R14Value CA2_6_8I1R14Terms CA2_6_8I1R14Terms_sound) (by decide +kernel)
def CA2_6_8I1R14Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R14Mass_sound : CA2_6_8I1R14Mass.Encloses (∑ a, CA2_6_8I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R14P CA2_6_8I1R14Value CA2_6_8I1R14P_sound) (by decide +kernel)
def CA2_6_8I1R14MassTerm : Ball := .exact 0
lemma CA2_6_8I1R14MassTerm_sound : CA2_6_8I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R14Mass_sound)
def CA2_6_8I1R14H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R14H_sound : CA2_6_8I1R14H.Encloses (homogeneousEntropy CA2_6_8I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R14Value CA2_6_8I1R14MassTerm_sound CA2_6_8I1R14Entropy_sound) (by decide +kernel)
def CA2_6_8I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA2_6_8I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA2_6_8I1R15Raw_sound (a : PairSlot) :
    (CA2_6_8I1R15Raw a).Encloses (CA2_6_8I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA2_6_8I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R15Certificates_valid :
    CA2_6_8I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R15Certificates (CA2_6_8I1R15CertificateIndex a)).input
lemma CA2_6_8I1R15P_check : ∀ a : PairSlot, contains (CA2_6_8I1R15Raw a) (CA2_6_8I1R15P a) = true := by
  decide +kernel
lemma CA2_6_8I1R15P_sound (a : PairSlot) :
    (CA2_6_8I1R15P a).Encloses (CA2_6_8I1R15Value a) :=
  contains_sound (CA2_6_8I1R15Raw_sound a) (CA2_6_8I1R15P_check a)
def CA2_6_8I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R15Certificates (CA2_6_8I1R15CertificateIndex a)).output
lemma CA2_6_8I1R15Terms_sound (a : PairSlot) :
    (CA2_6_8I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R15Certificates_valid
    (CA2_6_8I1R15CertificateIndex a) (CA2_6_8I1R15P_sound a)
def CA2_6_8I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R15Entropy_sound : CA2_6_8I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R15Value CA2_6_8I1R15Terms CA2_6_8I1R15Terms_sound) (by decide +kernel)
def CA2_6_8I1R15Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R15Mass_sound : CA2_6_8I1R15Mass.Encloses (∑ a, CA2_6_8I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R15P CA2_6_8I1R15Value CA2_6_8I1R15P_sound) (by decide +kernel)
def CA2_6_8I1R15MassTerm : Ball := .exact 0
lemma CA2_6_8I1R15MassTerm_sound : CA2_6_8I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R15Mass_sound)
def CA2_6_8I1R15H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R15H_sound : CA2_6_8I1R15H.Encloses (homogeneousEntropy CA2_6_8I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R15Value CA2_6_8I1R15MassTerm_sound CA2_6_8I1R15Entropy_sound) (by decide +kernel)
def CA2_6_8I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA2_6_8I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 6 8)) A2_6_8Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA2_6_8I1R16Raw_sound (a : PairSlot) :
    (CA2_6_8I1R16Raw a).Encloses (CA2_6_8I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 6 8) (show (shape 2 6 8) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA2_6_8I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_6_8I1R16Certificates_valid :
    CA2_6_8I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_6_8I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R16Certificates (CA2_6_8I1R16CertificateIndex a)).input
lemma CA2_6_8I1R16P_check : ∀ a : PairSlot, contains (CA2_6_8I1R16Raw a) (CA2_6_8I1R16P a) = true := by
  decide +kernel
lemma CA2_6_8I1R16P_sound (a : PairSlot) :
    (CA2_6_8I1R16P a).Encloses (CA2_6_8I1R16Value a) :=
  contains_sound (CA2_6_8I1R16Raw_sound a) (CA2_6_8I1R16P_check a)
def CA2_6_8I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I1R16Certificates (CA2_6_8I1R16CertificateIndex a)).output
lemma CA2_6_8I1R16Terms_sound (a : PairSlot) :
    (CA2_6_8I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I1R16Certificates_valid
    (CA2_6_8I1R16CertificateIndex a) (CA2_6_8I1R16P_sound a)
def CA2_6_8I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R16Entropy_sound : CA2_6_8I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_6_8I1R16Value CA2_6_8I1R16Terms CA2_6_8I1R16Terms_sound) (by decide +kernel)
def CA2_6_8I1R16Mass : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R16Mass_sound : CA2_6_8I1R16Mass.Encloses (∑ a, CA2_6_8I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_6_8I1R16P CA2_6_8I1R16Value CA2_6_8I1R16P_sound) (by decide +kernel)
def CA2_6_8I1R16MassTerm : Ball := .exact 0
lemma CA2_6_8I1R16MassTerm_sound : CA2_6_8I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_6_8I1R16Mass_sound)
def CA2_6_8I1R16H : Ball := ⟨0, 0⟩
lemma CA2_6_8I1R16H_sound : CA2_6_8I1R16H.Encloses (homogeneousEntropy CA2_6_8I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I1R16Value CA2_6_8I1R16MassTerm_sound CA2_6_8I1R16Entropy_sound) (by decide +kernel)
def CA2_6_8I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_6_8I1R0H
  | 1 => CA2_6_8I1R1H
  | 2 => CA2_6_8I1R2H
  | 3 => CA2_6_8I1R3H
  | 4 => CA2_6_8I1R4H
  | 5 => CA2_6_8I1R5H
  | 6 => CA2_6_8I1R6H
  | 7 => CA2_6_8I1R7H
  | 8 => CA2_6_8I1R8H
  | 9 => CA2_6_8I1R9H
  | 10 => CA2_6_8I1R10H
  | 11 => CA2_6_8I1R11H
  | 12 => CA2_6_8I1R12H
  | 13 => CA2_6_8I1R13H
  | 14 => CA2_6_8I1R14H
  | 15 => CA2_6_8I1R15H
  | 16 => CA2_6_8I1R16H
  | _ => (.exact 0)
lemma CA2_6_8I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_6_8I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_6_8I1R0H_sound
  · exact CA2_6_8I1R1H_sound
  · exact CA2_6_8I1R2H_sound
  · exact CA2_6_8I1R3H_sound
  · exact CA2_6_8I1R4H_sound
  · exact CA2_6_8I1R5H_sound
  · exact CA2_6_8I1R6H_sound
  · exact CA2_6_8I1R7H_sound
  · exact CA2_6_8I1R8H_sound
  · exact CA2_6_8I1R9H_sound
  · exact CA2_6_8I1R10H_sound
  · exact CA2_6_8I1R11H_sound
  · exact CA2_6_8I1R12H_sound
  · exact CA2_6_8I1R13H_sound
  · exact CA2_6_8I1R14H_sound
  · exact CA2_6_8I1R15H_sound
  · exact CA2_6_8I1R16H_sound
def CA2_6_8I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | _, _, _ => (.exact 0)
lemma CA2_6_8I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 6 8))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_6_8I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_6_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 0 8) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 1 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 6 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 0 7) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact Z2_6_0H1H_sound
def CA2_6_8I1Singleton : Ball := ⟨(37757724657937222513117 / 500000000000000000000000000000), (1487 / 25000000000000000000000000000000)⟩
lemma CA2_6_8I1Singleton_sound : CA2_6_8I1Singleton.Encloses
    (singletonEntropy (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_6_8I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_6_8Law_sound u) CA2_6_8I1Singles_sound) (by decide +kernel)
def CA2_6_8I1Group : Ball := ⟨(54318682619917483587541367140529 / 50000000000000000000000000000000), (166666091037 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1Group_sound : CA2_6_8I1Group.Encloses
    (groupedEntropy (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_6_8I1Singleton_sound
    (finSumBall_sound 17 CA2_6_8I1ResidualEntropies _ CA2_6_8I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_6_8I1H : Ball := ⟨(56710716895161352451896967881823 / 50000000000000000000000000000000), (490426241337 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I1_sound : CA2_6_8I1H.Encloses (stageACapacity (shape 2 6 8) 1) := by
  have hb := contains_sound (Ball.add_sound CA2_6_8I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_6_8I1Group_sound)))
    (show contains (.add CA2_6_8I1PairH (.neg (.mul (.exact 2) CA2_6_8I1Group))) CA2_6_8I1H = true by decide +kernel)
  unfold CA2_6_8I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
