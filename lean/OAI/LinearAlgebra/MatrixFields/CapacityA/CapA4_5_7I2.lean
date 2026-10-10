import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA4_5_7I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_5_7I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA4_5_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA4_5_7I2R0Raw_sound (a : PairSlot) :
    (CA4_5_7I2R0Raw a).Encloses (CA4_5_7I2R0Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA4_5_7I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(244308754727999724283630797 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(373459546953319618009331341 / 6250000000000000000000000000000), (982967 / 50000000000000000000000000000000)⟩ ⟨(-1222910074979865424709459157630799 / 100000000000000000000000000000000), (201170529647 / 50000000000000000000000000000000)⟩ ⟨-18, 244308754727999724283630797, 190734863281250000000000000⟩]
lemma CA4_5_7I2R0Certificates_valid :
    CA4_5_7I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_5_7I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R0Certificates (CA4_5_7I2R0CertificateIndex a)).input
lemma CA4_5_7I2R0P_check : ∀ a : PairSlot, contains (CA4_5_7I2R0Raw a) (CA4_5_7I2R0P a) = true := by
  decide +kernel
lemma CA4_5_7I2R0P_sound (a : PairSlot) :
    (CA4_5_7I2R0P a).Encloses (CA4_5_7I2R0Value a) :=
  contains_sound (CA4_5_7I2R0Raw_sound a) (CA4_5_7I2R0P_check a)
def CA4_5_7I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R0Certificates (CA4_5_7I2R0CertificateIndex a)).output
lemma CA4_5_7I2R0Terms_sound (a : PairSlot) :
    (CA4_5_7I2R0Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R0Certificates_valid
    (CA4_5_7I2R0CertificateIndex a) (CA4_5_7I2R0P_sound a)
def CA4_5_7I2R0Entropy : Ball := ⟨(373459546953319618009331341 / 6250000000000000000000000000000), (982967 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R0Entropy_sound : CA4_5_7I2R0Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R0Value CA4_5_7I2R0Terms CA4_5_7I2R0Terms_sound) (by decide +kernel)
def CA4_5_7I2R0Mass : Ball := ⟨(244308754727999724283630797 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R0Mass_sound : CA4_5_7I2R0Mass.Encloses (∑ a, CA4_5_7I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R0P CA4_5_7I2R0Value CA4_5_7I2R0P_sound) (by decide +kernel)
def CA4_5_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 244308754727999724283630797, 190734863281250000000000000⟩
def CA4_5_7I2R0MassTermLog : Ball := ⟨(-1222910074979865424709459157630799 / 100000000000000000000000000000000), (201170529647 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R0MassTermLog_sound : CA4_5_7I2R0MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R0Mass_sound) (w := CA4_5_7I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R0MassTerm : Ball := ⟨(373459546953319618009331341 / 6250000000000000000000000000000), (982967 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R0MassTerm_sound : CA4_5_7I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R0Mass_sound) CA4_5_7I2R0MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R0H : Ball := ⟨0, (982967 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2R0H_sound : CA4_5_7I2R0H.Encloses (homogeneousEntropy CA4_5_7I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R0Value CA4_5_7I2R0MassTerm_sound CA4_5_7I2R0Entropy_sound) (by decide +kernel)
def CA4_5_7I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA4_5_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA4_5_7I2R1Raw_sound (a : PairSlot) :
    (CA4_5_7I2R1Raw a).Encloses (CA4_5_7I2R1Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA4_5_7I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2512377436904649203704730017 / 4000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(463082674732548310216718970043 / 100000000000000000000000000000000), (159605011 / 100000000000000000000000000000000)⟩ ⟨(-184320503730954107044470613908181 / 25000000000000000000000000000000), (63527472243 / 25000000000000000000000000000000)⟩ ⟨-11, 2512377436904649203704730017, 1953125000000000000000000000⟩]
lemma CA4_5_7I2R1Certificates_valid :
    CA4_5_7I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA4_5_7I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R1Certificates (CA4_5_7I2R1CertificateIndex a)).input
lemma CA4_5_7I2R1P_check : ∀ a : PairSlot, contains (CA4_5_7I2R1Raw a) (CA4_5_7I2R1P a) = true := by
  decide +kernel
lemma CA4_5_7I2R1P_sound (a : PairSlot) :
    (CA4_5_7I2R1P a).Encloses (CA4_5_7I2R1Value a) :=
  contains_sound (CA4_5_7I2R1Raw_sound a) (CA4_5_7I2R1P_check a)
def CA4_5_7I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R1Certificates (CA4_5_7I2R1CertificateIndex a)).output
lemma CA4_5_7I2R1Terms_sound (a : PairSlot) :
    (CA4_5_7I2R1Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R1Certificates_valid
    (CA4_5_7I2R1CertificateIndex a) (CA4_5_7I2R1P_sound a)
def CA4_5_7I2R1Entropy : Ball := ⟨(463082674732548310216718970043 / 50000000000000000000000000000000), (159605011 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R1Entropy_sound : CA4_5_7I2R1Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R1Value CA4_5_7I2R1Terms CA4_5_7I2R1Terms_sound) (by decide +kernel)
def CA4_5_7I2R1Mass : Ball := ⟨(2512377436904649203704730017 / 2000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R1Mass_sound : CA4_5_7I2R1Mass.Encloses (∑ a, CA4_5_7I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R1P CA4_5_7I2R1Value CA4_5_7I2R1P_sound) (by decide +kernel)
def CA4_5_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 2512377436904649203704730017, 1953125000000000000000000000⟩
def CA4_5_7I2R1MassTermLog : Ball := ⟨(-333983648433910948618079631291197 / 50000000000000000000000000000000), (232934065289 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R1MassTermLog_sound : CA4_5_7I2R1MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R1Mass_sound) (w := CA4_5_7I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R1MassTerm : Ball := ⟨(419546491310226323073778343693 / 50000000000000000000000000000000), (146304593 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R1MassTerm_sound : CA4_5_7I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R1Mass_sound) CA4_5_7I2R1MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R1H : Ball := ⟨(870723668446439742858812527 / 1000000000000000000000000000000), (76477401 / 12500000000000000000000000000000)⟩
lemma CA4_5_7I2R1H_sound : CA4_5_7I2R1H.Encloses (homogeneousEntropy CA4_5_7I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R1Value CA4_5_7I2R1MassTerm_sound CA4_5_7I2R1Entropy_sound) (by decide +kernel)
def CA4_5_7I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA4_5_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA4_5_7I2R2Raw_sound (a : PairSlot) :
    (CA4_5_7I2R2Raw a).Encloses (CA4_5_7I2R2Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA4_5_7I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(11861293865407860378199682309 / 1250000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(4419630394880539011440438632171 / 100000000000000000000000000000000), (803752559 / 50000000000000000000000000000000)⟩ ⟨(-465761834778613164915189054701271 / 100000000000000000000000000000000), (84703295153 / 50000000000000000000000000000000)⟩ ⟨-7, 11861293865407860378199682309, 9765625000000000000000000000⟩,
   .log ⟨(17361489450416797219897770733 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(246600175055478176600599481 / 48828125000000000000000000000), (44117263 / 25000000000000000000000000000000)⟩ ⟨(-727237660046348846356521279330671 / 100000000000000000000000000000000), (50821977127 / 20000000000000000000000000000000)⟩ ⟨-11, 17361489450416797219897770733, 12207031250000000000000000000⟩,
   .log ⟨(3476671813135011662133058136131 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(2919617487324360121442435864997 / 25000000000000000000000000000000), (4417283451 / 100000000000000000000000000000000)⟩ ⟨(-83977368133912525867429162989171 / 25000000000000000000000000000000), (127054942701 / 100000000000000000000000000000000)⟩ ⟨-5, 3476671813135011662133058136131, 3125000000000000000000000000000⟩]
lemma CA4_5_7I2R2Certificates_valid :
    CA4_5_7I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_5_7I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R2Certificates (CA4_5_7I2R2CertificateIndex a)).input
lemma CA4_5_7I2R2P_check : ∀ a : PairSlot, contains (CA4_5_7I2R2Raw a) (CA4_5_7I2R2P a) = true := by
  decide +kernel
lemma CA4_5_7I2R2P_sound (a : PairSlot) :
    (CA4_5_7I2R2P a).Encloses (CA4_5_7I2R2Value a) :=
  contains_sound (CA4_5_7I2R2Raw_sound a) (CA4_5_7I2R2P_check a)
def CA4_5_7I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R2Certificates (CA4_5_7I2R2CertificateIndex a)).output
lemma CA4_5_7I2R2Terms_sound (a : PairSlot) :
    (CA4_5_7I2R2Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R2Certificates_valid
    (CA4_5_7I2R2CertificateIndex a) (CA4_5_7I2R2P_sound a)
def CA4_5_7I2R2Entropy : Ball := ⟨(10763902528042878560003338099253 / 50000000000000000000000000000000), (7985231791 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R2Entropy_sound : CA4_5_7I2R2Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R2Value CA4_5_7I2R2Terms CA4_5_7I2R2Terms_sound) (by decide +kernel)
def CA4_5_7I2R2Mass : Ball := ⟨(1102674149440720740080837894287 / 20000000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R2Mass_sound : CA4_5_7I2R2Mass.Encloses (∑ a, CA4_5_7I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R2P CA4_5_7I2R2Value CA4_5_7I2R2P_sound) (by decide +kernel)
def CA4_5_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 1102674149440720740080837894287, 625000000000000000000000000000⟩
def CA4_5_7I2R2MassTermLog : Ball := ⟨(-144899699950644721659372497607277 / 50000000000000000000000000000000), (25410988561 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I2R2MassTermLog_sound : CA4_5_7I2R2MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R2Mass_sound) (w := CA4_5_7I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R2MassTerm : Ball := ⟨(639108613589171253827319714027 / 4000000000000000000000000000000), (7005010163 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R2MassTerm_sound : CA4_5_7I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R2Mass_sound) CA4_5_7I2R2MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R2H : Ball := ⟨(5550089716356475774323683347831 / 100000000000000000000000000000000), (7495120977 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R2H_sound : CA4_5_7I2R2H.Encloses (homogeneousEntropy CA4_5_7I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R2Value CA4_5_7I2R2MassTerm_sound CA4_5_7I2R2Entropy_sound) (by decide +kernel)
def CA4_5_7I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA4_5_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA4_5_7I2R3Raw_sound (a : PairSlot) :
    (CA4_5_7I2R3Raw a).Encloses (CA4_5_7I2R3Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA4_5_7I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(116038587245685451541394719653 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(746935275772026258957873496579 / 25000000000000000000000000000000), (276436431 / 25000000000000000000000000000000)⟩ ⟨(-128739119201884081430611870402243 / 25000000000000000000000000000000), (47645603459 / 25000000000000000000000000000000)⟩ ⟨-8, 116038587245685451541394719653, 78125000000000000000000000000⟩,
   .log ⟨(20460621977683097735074437540931 / 100000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩ ⟨(507253354513740914667508186421 / 1562500000000000000000000000000), (17330821089 / 100000000000000000000000000000000)⟩ ⟨(-79333401311770809819707962449341 / 50000000000000000000000000000000), (16940659003 / 20000000000000000000000000000000)⟩ ⟨-3, 20460621977683097735074437540931, 12500000000000000000000000000000⟩,
   .log ⟨(1061521307796356016541019948227 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(4825110191937311571603185667661 / 100000000000000000000000000000000), (56196471 / 3125000000000000000000000000000)⟩ ⟨(-454546711073930566895028232307551 / 100000000000000000000000000000000), (84703294967 / 50000000000000000000000000000000)⟩ ⟨-7, 1061521307796356016541019948227, 781250000000000000000000000000⟩]
lemma CA4_5_7I2R3Certificates_valid :
    CA4_5_7I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_5_7I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R3Certificates (CA4_5_7I2R3CertificateIndex a)).input
lemma CA4_5_7I2R3P_check : ∀ a : PairSlot, contains (CA4_5_7I2R3Raw a) (CA4_5_7I2R3P a) = true := by
  decide +kernel
lemma CA4_5_7I2R3P_sound (a : PairSlot) :
    (CA4_5_7I2R3P a).Encloses (CA4_5_7I2R3Value a) :=
  contains_sound (CA4_5_7I2R3Raw_sound a) (CA4_5_7I2R3P_check a)
def CA4_5_7I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R3Certificates (CA4_5_7I2R3CertificateIndex a)).output
lemma CA4_5_7I2R3Terms_sound (a : PairSlot) :
    (CA4_5_7I2R3Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R3Certificates_valid
    (CA4_5_7I2R3CertificateIndex a) (CA4_5_7I2R3P_sound a)
def CA4_5_7I2R3Entropy : Ball := ⟨(40277065983904835146155203584921 / 50000000000000000000000000000000), (4046970777 / 10000000000000000000000000000000)⟩
lemma CA4_5_7I2R3Entropy_sound : CA4_5_7I2R3Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R3Value CA4_5_7I2R3Terms CA4_5_7I2R3Terms_sound) (by decide +kernel)
def CA4_5_7I2R3Mass : Ball := ⟨(22102336221707881009322431087423 / 50000000000000000000000000000000), (67 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R3Mass_sound : CA4_5_7I2R3Mass.Encloses (∑ a, CA4_5_7I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R3P CA4_5_7I2R3Value CA4_5_7I2R3P_sound) (by decide +kernel)
def CA4_5_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 22102336221707881009322431087423, 12500000000000000000000000000000⟩
def CA4_5_7I2R3MassTermLog : Ball := ⟨(-81633969110199724265404696715543 / 100000000000000000000000000000000), (7940933919 / 12500000000000000000000000000000)⟩
lemma CA4_5_7I2R3MassTermLog_sound : CA4_5_7I2R3MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R3Mass_sound) (w := CA4_5_7I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R3MassTerm : Ball := ⟨(36086028647722992852483823757497 / 100000000000000000000000000000000), (28082110733 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R3MassTerm_sound : CA4_5_7I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R3Mass_sound) CA4_5_7I2R3MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R3H : Ball := ⟨(8893620664017335487965316682469 / 20000000000000000000000000000000), (68551818503 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R3H_sound : CA4_5_7I2R3H.Encloses (homogeneousEntropy CA4_5_7I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R3Value CA4_5_7I2R3MassTerm_sound CA4_5_7I2R3Entropy_sound) (by decide +kernel)
def CA4_5_7I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA4_5_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA4_5_7I2R4Raw_sound (a : PairSlot) :
    (CA4_5_7I2R4Raw a).Encloses (CA4_5_7I2R4Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA4_5_7I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(226473706787275519218486833 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(84331311552445100421913750733 / 100000000000000000000000000000000), (5754923 / 20000000000000000000000000000000)⟩ ⟨(-930917243647809581534875730636993 / 100000000000000000000000000000000), (317637366283 / 100000000000000000000000000000000)⟩ ⟨-14, 226473706787275519218486833, 152587890625000000000000000⟩,
   .log ⟨(3177125346425778831075447458091 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(10958519703244693898392362883243 / 100000000000000000000000000000000), (4036694841 / 100000000000000000000000000000000)⟩ ⟨(-6898386754285835075843605989883 / 2000000000000000000000000000000), (127054942601 / 100000000000000000000000000000000)⟩ ⟨-5, 3177125346425778831075447458091, 3125000000000000000000000000000⟩,
   .log ⟨(8284523162059862942498959658483 / 25000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩ ⟨(36600583587959685855884743349303 / 100000000000000000000000000000000), (5262948107 / 25000000000000000000000000000000)⟩ ⟨(-110448673001414244079839114916649 / 100000000000000000000000000000000), (15881867839 / 25000000000000000000000000000000)⟩ ⟨-2, 8284523162059862942498959658483, 6250000000000000000000000000000⟩,
   .log ⟨(768235467440488083710341295643 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(400988376646451096965158174859 / 6250000000000000000000000000000), (1301441523 / 50000000000000000000000000000000)⟩ ⟨(-208784100001222061083697270247223 / 50000000000000000000000000000000), (169406589919 / 100000000000000000000000000000000)⟩ ⟨-7, 768235467440488083710341295643, 390625000000000000000000000000⟩,
   .log ⟨(7439805246988084802149349047 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(267963025525865227547179212149 / 50000000000000000000000000000000), (94526411 / 50000000000000000000000000000000)⟩ ⟨(-720349569995388840128291954778389 / 100000000000000000000000000000000), (63527471721 / 25000000000000000000000000000000)⟩ ⟨-11, 7439805246988084802149349047, 4882812500000000000000000000⟩]
lemma CA4_5_7I2R4Certificates_valid :
    CA4_5_7I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA4_5_7I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R4Certificates (CA4_5_7I2R4CertificateIndex a)).input
lemma CA4_5_7I2R4P_check : ∀ a : PairSlot, contains (CA4_5_7I2R4Raw a) (CA4_5_7I2R4P a) = true := by
  decide +kernel
lemma CA4_5_7I2R4P_sound (a : PairSlot) :
    (CA4_5_7I2R4P a).Encloses (CA4_5_7I2R4Value a) :=
  contains_sound (CA4_5_7I2R4Raw_sound a) (CA4_5_7I2R4P_check a)
def CA4_5_7I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R4Certificates (CA4_5_7I2R4CertificateIndex a)).output
lemma CA4_5_7I2R4Terms_sound (a : PairSlot) :
    (CA4_5_7I2R4Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R4Certificates_valid
    (CA4_5_7I2R4CertificateIndex a) (CA4_5_7I2R4P_sound a)
def CA4_5_7I2R4Entropy : Ball := ⟨(72053839721292129411492716637041 / 100000000000000000000000000000000), (17288775127 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R4Entropy_sound : CA4_5_7I2R4Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R4Value CA4_5_7I2R4Terms CA4_5_7I2R4Terms_sound) (by decide +kernel)
def CA4_5_7I2R4Mass : Ball := ⟨(10664450289966456164136767792449 / 25000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
lemma CA4_5_7I2R4Mass_sound : CA4_5_7I2R4Mass.Encloses (∑ a, CA4_5_7I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R4P CA4_5_7I2R4Value CA4_5_7I2R4P_sound) (by decide +kernel)
def CA4_5_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 10664450289966456164136767792449, 6250000000000000000000000000000⟩
def CA4_5_7I2R4MassTermLog : Ball := ⟨(-21299000441064703795460550474203 / 25000000000000000000000000000000), (12705494281 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I2R4MassTermLog_sound : CA4_5_7I2R4MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R4Mass_sound) (w := CA4_5_7I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R4MassTerm : Ball := ⟨(18171370514376652650033390669629 / 50000000000000000000000000000000), (6774855641 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2R4MassTerm_sound : CA4_5_7I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R4Mass_sound) CA4_5_7I2R4MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R4H : Ball := ⟨(35711098692538824111425935297783 / 100000000000000000000000000000000), (30838486409 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R4H_sound : CA4_5_7I2R4H.Encloses (homogeneousEntropy CA4_5_7I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R4Value CA4_5_7I2R4MassTerm_sound CA4_5_7I2R4Entropy_sound) (by decide +kernel)
def CA4_5_7I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA4_5_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA4_5_7I2R5Raw_sound (a : PairSlot) :
    (CA4_5_7I2R5Raw a).Encloses (CA4_5_7I2R5Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA4_5_7I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(144697917097217142068111639 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(36996206736220144249603357241 / 100000000000000000000000000000000), (6128201 / 50000000000000000000000000000000)⟩ ⟨(-25567891700447747738730852352753 / 2500000000000000000000000000000), (338813206571 / 100000000000000000000000000000000)⟩ ⟨-15, 144697917097217142068111639, 122070312500000000000000000⟩,
   .log ⟨(549793017508480599404902018279 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(4197218009805251425058918058719 / 50000000000000000000000000000000), (3259849659 / 100000000000000000000000000000000)⟩ ⟨(-19085446141285838610089690603983 / 5000000000000000000000000000000), (74115383163 / 50000000000000000000000000000000)⟩ ⟨-6, 549793017508480599404902018279, 390625000000000000000000000000⟩,
   .log ⟨(82151359982399290296125908147 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(72954125688653551987601937681 / 12500000000000000000000000000000), (104377367 / 50000000000000000000000000000000)⟩ ⟨(-177609051643901643944605201016889 / 25000000000000000000000000000000), (254109885413 / 100000000000000000000000000000000)⟩ ⟨-11, 82151359982399290296125908147, 48828125000000000000000000000⟩]
lemma CA4_5_7I2R5Certificates_valid :
    CA4_5_7I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA4_5_7I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R5Certificates (CA4_5_7I2R5CertificateIndex a)).input
lemma CA4_5_7I2R5P_check : ∀ a : PairSlot, contains (CA4_5_7I2R5Raw a) (CA4_5_7I2R5P a) = true := by
  decide +kernel
lemma CA4_5_7I2R5P_sound (a : PairSlot) :
    (CA4_5_7I2R5P a).Encloses (CA4_5_7I2R5Value a) :=
  contains_sound (CA4_5_7I2R5Raw_sound a) (CA4_5_7I2R5P_check a)
def CA4_5_7I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R5Certificates (CA4_5_7I2R5CertificateIndex a)).output
lemma CA4_5_7I2R5Terms_sound (a : PairSlot) :
    (CA4_5_7I2R5Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R5Certificates_valid
    (CA4_5_7I2R5CertificateIndex a) (CA4_5_7I2R5P_sound a)
def CA4_5_7I2R5Entropy : Ball := ⟨(9015065231855951410268254976127 / 50000000000000000000000000000000), (696172159 / 10000000000000000000000000000000)⟩
lemma CA4_5_7I2R5Entropy_sound : CA4_5_7I2R5Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R5Value CA4_5_7I2R5Terms CA4_5_7I2R5Terms_sound) (by decide +kernel)
def CA4_5_7I2R5Mass : Ball := ⟨(1142470438971876058233718386119 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2R5Mass_sound : CA4_5_7I2R5Mass.Encloses (∑ a, CA4_5_7I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R5P CA4_5_7I2R5Value CA4_5_7I2R5P_sound) (by decide +kernel)
def CA4_5_7I2R5MassTermLogWitness : LogWitness := ⟨-5, 1142470438971876058233718386119, 781250000000000000000000000000⟩
def CA4_5_7I2R5MassTermLog : Ball := ⟨(-308568285540194419975053007221709 / 100000000000000000000000000000000), (12705494271 / 10000000000000000000000000000000)⟩
lemma CA4_5_7I2R5MassTermLog_sound : CA4_5_7I2R5MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R5Mass_sound) (w := CA4_5_7I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R5MassTerm : Ball := ⟨(14101205785356204585631815735069 / 100000000000000000000000000000000), (2903130367 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R5MassTerm_sound : CA4_5_7I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R5Mass_sound) CA4_5_7I2R5MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R5H : Ball := ⟨(785784935671139646980938843437 / 20000000000000000000000000000000), (3191995581 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2R5H_sound : CA4_5_7I2R5H.Encloses (homogeneousEntropy CA4_5_7I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R5Value CA4_5_7I2R5MassTerm_sound CA4_5_7I2R5Entropy_sound) (by decide +kernel)
def CA4_5_7I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA4_5_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA4_5_7I2R6Raw_sound (a : PairSlot) :
    (CA4_5_7I2R6Raw a).Encloses (CA4_5_7I2R6Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA4_5_7I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(304080552630759022733618587 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7304161393171340453107880699 / 100000000000000000000000000000000), (2446893 / 100000000000000000000000000000000)⟩ ⟨(-9608192737061599125806395148961 / 800000000000000000000000000000), (402340814407 / 100000000000000000000000000000000)⟩ ⟨-18, 304080552630759022733618587, 190734863281250000000000000⟩,
   .log ⟨(38316563574980860658657 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(415400474632440168347527 / 50000000000000000000000000000000), (291 / 100000000000000000000000000000000)⟩ ⟨(-433651075018303139410633388816849 / 20000000000000000000000000000000), (350706009461 / 50000000000000000000000000000000)⟩ ⟨-32, 38316563574980860658657, 23283064365386962890625⟩,
   .log ⟨(1275415133808368728054689087 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(458204765293789606800601001 / 97656250000000000000000000000), (81023907 / 50000000000000000000000000000000)⟩ ⟨(-36788153693912351224511622022271 / 5000000000000000000000000000000), (63527471833 / 25000000000000000000000000000000)⟩ ⟨-11, 1275415133808368728054689087, 976562500000000000000000000⟩]
lemma CA4_5_7I2R6Certificates_valid :
    CA4_5_7I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA4_5_7I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R6Certificates (CA4_5_7I2R6CertificateIndex a)).input
lemma CA4_5_7I2R6P_check : ∀ a : PairSlot, contains (CA4_5_7I2R6Raw a) (CA4_5_7I2R6P a) = true := by
  decide +kernel
lemma CA4_5_7I2R6P_sound (a : PairSlot) :
    (CA4_5_7I2R6P a).Encloses (CA4_5_7I2R6Value a) :=
  contains_sound (CA4_5_7I2R6Raw_sound a) (CA4_5_7I2R6P_check a)
def CA4_5_7I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R6Certificates (CA4_5_7I2R6CertificateIndex a)).output
lemma CA4_5_7I2R6Terms_sound (a : PairSlot) :
    (CA4_5_7I2R6Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R6Certificates_valid
    (CA4_5_7I2R6CertificateIndex a) (CA4_5_7I2R6P_sound a)
def CA4_5_7I2R6Entropy : Ball := ⟨(48381166404908176803070457653 / 10000000000000000000000000000000), (83471091 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R6Entropy_sound : CA4_5_7I2R6Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R6Value CA4_5_7I2R6Terms CA4_5_7I2R6Terms_sound) (by decide +kernel)
def CA4_5_7I2R6Mass : Ball := ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2R6Mass_sound : CA4_5_7I2R6Mass.Encloses (∑ a, CA4_5_7I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R6P CA4_5_7I2R6Value CA4_5_7I2R6P_sound) (by decide +kernel)
def CA4_5_7I2R6MassTermLogWitness : LogWitness := ⟨-11, 16246788883517155613847561503, 12207031250000000000000000000⟩
def CA4_5_7I2R6MassTermLog : Ball := ⟨(-733873582176963528087673936985231 / 100000000000000000000000000000000), (63527473357 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2R6MassTermLog_sound : CA4_5_7I2R6MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I2R6Mass_sound) (w := CA4_5_7I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I2R6MassTerm : Ball := ⟨(119230891568196048297085156129 / 25000000000000000000000000000000), (165138837 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R6MassTerm_sound : CA4_5_7I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I2R6Mass_sound) CA4_5_7I2R6MassTermLog_sound) (by decide +kernel)
def CA4_5_7I2R6H : Ball := ⟨(3444048888148787421181976007 / 50000000000000000000000000000000), (332081019 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2R6H_sound : CA4_5_7I2R6H.Encloses (homogeneousEntropy CA4_5_7I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R6Value CA4_5_7I2R6MassTerm_sound CA4_5_7I2R6Entropy_sound) (by decide +kernel)
def CA4_5_7I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA4_5_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA4_5_7I2R7Raw_sound (a : PairSlot) :
    (CA4_5_7I2R7Raw a).Encloses (CA4_5_7I2R7Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA4_5_7I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R7Certificates_valid :
    CA4_5_7I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R7Certificates (CA4_5_7I2R7CertificateIndex a)).input
lemma CA4_5_7I2R7P_check : ∀ a : PairSlot, contains (CA4_5_7I2R7Raw a) (CA4_5_7I2R7P a) = true := by
  decide +kernel
lemma CA4_5_7I2R7P_sound (a : PairSlot) :
    (CA4_5_7I2R7P a).Encloses (CA4_5_7I2R7Value a) :=
  contains_sound (CA4_5_7I2R7Raw_sound a) (CA4_5_7I2R7P_check a)
def CA4_5_7I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R7Certificates (CA4_5_7I2R7CertificateIndex a)).output
lemma CA4_5_7I2R7Terms_sound (a : PairSlot) :
    (CA4_5_7I2R7Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R7Certificates_valid
    (CA4_5_7I2R7CertificateIndex a) (CA4_5_7I2R7P_sound a)
def CA4_5_7I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R7Entropy_sound : CA4_5_7I2R7Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R7Value CA4_5_7I2R7Terms CA4_5_7I2R7Terms_sound) (by decide +kernel)
def CA4_5_7I2R7Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R7Mass_sound : CA4_5_7I2R7Mass.Encloses (∑ a, CA4_5_7I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R7P CA4_5_7I2R7Value CA4_5_7I2R7P_sound) (by decide +kernel)
def CA4_5_7I2R7MassTerm : Ball := .exact 0
lemma CA4_5_7I2R7MassTerm_sound : CA4_5_7I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R7Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R7Mass_sound)
def CA4_5_7I2R7H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R7H_sound : CA4_5_7I2R7H.Encloses (homogeneousEntropy CA4_5_7I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R7Value CA4_5_7I2R7MassTerm_sound CA4_5_7I2R7Entropy_sound) (by decide +kernel)
def CA4_5_7I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA4_5_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA4_5_7I2R8Raw_sound (a : PairSlot) :
    (CA4_5_7I2R8Raw a).Encloses (CA4_5_7I2R8Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA4_5_7I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R8Certificates_valid :
    CA4_5_7I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R8Certificates (CA4_5_7I2R8CertificateIndex a)).input
lemma CA4_5_7I2R8P_check : ∀ a : PairSlot, contains (CA4_5_7I2R8Raw a) (CA4_5_7I2R8P a) = true := by
  decide +kernel
lemma CA4_5_7I2R8P_sound (a : PairSlot) :
    (CA4_5_7I2R8P a).Encloses (CA4_5_7I2R8Value a) :=
  contains_sound (CA4_5_7I2R8Raw_sound a) (CA4_5_7I2R8P_check a)
def CA4_5_7I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R8Certificates (CA4_5_7I2R8CertificateIndex a)).output
lemma CA4_5_7I2R8Terms_sound (a : PairSlot) :
    (CA4_5_7I2R8Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R8Certificates_valid
    (CA4_5_7I2R8CertificateIndex a) (CA4_5_7I2R8P_sound a)
def CA4_5_7I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R8Entropy_sound : CA4_5_7I2R8Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R8Value CA4_5_7I2R8Terms CA4_5_7I2R8Terms_sound) (by decide +kernel)
def CA4_5_7I2R8Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R8Mass_sound : CA4_5_7I2R8Mass.Encloses (∑ a, CA4_5_7I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R8P CA4_5_7I2R8Value CA4_5_7I2R8P_sound) (by decide +kernel)
def CA4_5_7I2R8MassTerm : Ball := .exact 0
lemma CA4_5_7I2R8MassTerm_sound : CA4_5_7I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R8Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R8Mass_sound)
def CA4_5_7I2R8H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R8H_sound : CA4_5_7I2R8H.Encloses (homogeneousEntropy CA4_5_7I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R8Value CA4_5_7I2R8MassTerm_sound CA4_5_7I2R8Entropy_sound) (by decide +kernel)
def CA4_5_7I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA4_5_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA4_5_7I2R9Raw_sound (a : PairSlot) :
    (CA4_5_7I2R9Raw a).Encloses (CA4_5_7I2R9Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA4_5_7I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R9Certificates_valid :
    CA4_5_7I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R9Certificates (CA4_5_7I2R9CertificateIndex a)).input
lemma CA4_5_7I2R9P_check : ∀ a : PairSlot, contains (CA4_5_7I2R9Raw a) (CA4_5_7I2R9P a) = true := by
  decide +kernel
lemma CA4_5_7I2R9P_sound (a : PairSlot) :
    (CA4_5_7I2R9P a).Encloses (CA4_5_7I2R9Value a) :=
  contains_sound (CA4_5_7I2R9Raw_sound a) (CA4_5_7I2R9P_check a)
def CA4_5_7I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R9Certificates (CA4_5_7I2R9CertificateIndex a)).output
lemma CA4_5_7I2R9Terms_sound (a : PairSlot) :
    (CA4_5_7I2R9Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R9Certificates_valid
    (CA4_5_7I2R9CertificateIndex a) (CA4_5_7I2R9P_sound a)
def CA4_5_7I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R9Entropy_sound : CA4_5_7I2R9Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R9Value CA4_5_7I2R9Terms CA4_5_7I2R9Terms_sound) (by decide +kernel)
def CA4_5_7I2R9Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R9Mass_sound : CA4_5_7I2R9Mass.Encloses (∑ a, CA4_5_7I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R9P CA4_5_7I2R9Value CA4_5_7I2R9P_sound) (by decide +kernel)
def CA4_5_7I2R9MassTerm : Ball := .exact 0
lemma CA4_5_7I2R9MassTerm_sound : CA4_5_7I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R9Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R9Mass_sound)
def CA4_5_7I2R9H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R9H_sound : CA4_5_7I2R9H.Encloses (homogeneousEntropy CA4_5_7I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R9Value CA4_5_7I2R9MassTerm_sound CA4_5_7I2R9Entropy_sound) (by decide +kernel)
def CA4_5_7I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA4_5_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA4_5_7I2R10Raw_sound (a : PairSlot) :
    (CA4_5_7I2R10Raw a).Encloses (CA4_5_7I2R10Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA4_5_7I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R10Certificates_valid :
    CA4_5_7I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R10Certificates (CA4_5_7I2R10CertificateIndex a)).input
lemma CA4_5_7I2R10P_check : ∀ a : PairSlot, contains (CA4_5_7I2R10Raw a) (CA4_5_7I2R10P a) = true := by
  decide +kernel
lemma CA4_5_7I2R10P_sound (a : PairSlot) :
    (CA4_5_7I2R10P a).Encloses (CA4_5_7I2R10Value a) :=
  contains_sound (CA4_5_7I2R10Raw_sound a) (CA4_5_7I2R10P_check a)
def CA4_5_7I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R10Certificates (CA4_5_7I2R10CertificateIndex a)).output
lemma CA4_5_7I2R10Terms_sound (a : PairSlot) :
    (CA4_5_7I2R10Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R10Certificates_valid
    (CA4_5_7I2R10CertificateIndex a) (CA4_5_7I2R10P_sound a)
def CA4_5_7I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R10Entropy_sound : CA4_5_7I2R10Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R10Value CA4_5_7I2R10Terms CA4_5_7I2R10Terms_sound) (by decide +kernel)
def CA4_5_7I2R10Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R10Mass_sound : CA4_5_7I2R10Mass.Encloses (∑ a, CA4_5_7I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R10P CA4_5_7I2R10Value CA4_5_7I2R10P_sound) (by decide +kernel)
def CA4_5_7I2R10MassTerm : Ball := .exact 0
lemma CA4_5_7I2R10MassTerm_sound : CA4_5_7I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R10Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R10Mass_sound)
def CA4_5_7I2R10H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R10H_sound : CA4_5_7I2R10H.Encloses (homogeneousEntropy CA4_5_7I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R10Value CA4_5_7I2R10MassTerm_sound CA4_5_7I2R10Entropy_sound) (by decide +kernel)
def CA4_5_7I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA4_5_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA4_5_7I2R11Raw_sound (a : PairSlot) :
    (CA4_5_7I2R11Raw a).Encloses (CA4_5_7I2R11Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA4_5_7I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R11Certificates_valid :
    CA4_5_7I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R11Certificates (CA4_5_7I2R11CertificateIndex a)).input
lemma CA4_5_7I2R11P_check : ∀ a : PairSlot, contains (CA4_5_7I2R11Raw a) (CA4_5_7I2R11P a) = true := by
  decide +kernel
lemma CA4_5_7I2R11P_sound (a : PairSlot) :
    (CA4_5_7I2R11P a).Encloses (CA4_5_7I2R11Value a) :=
  contains_sound (CA4_5_7I2R11Raw_sound a) (CA4_5_7I2R11P_check a)
def CA4_5_7I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R11Certificates (CA4_5_7I2R11CertificateIndex a)).output
lemma CA4_5_7I2R11Terms_sound (a : PairSlot) :
    (CA4_5_7I2R11Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R11Certificates_valid
    (CA4_5_7I2R11CertificateIndex a) (CA4_5_7I2R11P_sound a)
def CA4_5_7I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R11Entropy_sound : CA4_5_7I2R11Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R11Value CA4_5_7I2R11Terms CA4_5_7I2R11Terms_sound) (by decide +kernel)
def CA4_5_7I2R11Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R11Mass_sound : CA4_5_7I2R11Mass.Encloses (∑ a, CA4_5_7I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R11P CA4_5_7I2R11Value CA4_5_7I2R11P_sound) (by decide +kernel)
def CA4_5_7I2R11MassTerm : Ball := .exact 0
lemma CA4_5_7I2R11MassTerm_sound : CA4_5_7I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R11Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R11Mass_sound)
def CA4_5_7I2R11H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R11H_sound : CA4_5_7I2R11H.Encloses (homogeneousEntropy CA4_5_7I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R11Value CA4_5_7I2R11MassTerm_sound CA4_5_7I2R11Entropy_sound) (by decide +kernel)
def CA4_5_7I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA4_5_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA4_5_7I2R12Raw_sound (a : PairSlot) :
    (CA4_5_7I2R12Raw a).Encloses (CA4_5_7I2R12Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA4_5_7I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R12Certificates_valid :
    CA4_5_7I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R12Certificates (CA4_5_7I2R12CertificateIndex a)).input
lemma CA4_5_7I2R12P_check : ∀ a : PairSlot, contains (CA4_5_7I2R12Raw a) (CA4_5_7I2R12P a) = true := by
  decide +kernel
lemma CA4_5_7I2R12P_sound (a : PairSlot) :
    (CA4_5_7I2R12P a).Encloses (CA4_5_7I2R12Value a) :=
  contains_sound (CA4_5_7I2R12Raw_sound a) (CA4_5_7I2R12P_check a)
def CA4_5_7I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R12Certificates (CA4_5_7I2R12CertificateIndex a)).output
lemma CA4_5_7I2R12Terms_sound (a : PairSlot) :
    (CA4_5_7I2R12Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R12Certificates_valid
    (CA4_5_7I2R12CertificateIndex a) (CA4_5_7I2R12P_sound a)
def CA4_5_7I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R12Entropy_sound : CA4_5_7I2R12Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R12Value CA4_5_7I2R12Terms CA4_5_7I2R12Terms_sound) (by decide +kernel)
def CA4_5_7I2R12Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R12Mass_sound : CA4_5_7I2R12Mass.Encloses (∑ a, CA4_5_7I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R12P CA4_5_7I2R12Value CA4_5_7I2R12P_sound) (by decide +kernel)
def CA4_5_7I2R12MassTerm : Ball := .exact 0
lemma CA4_5_7I2R12MassTerm_sound : CA4_5_7I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R12Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R12Mass_sound)
def CA4_5_7I2R12H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R12H_sound : CA4_5_7I2R12H.Encloses (homogeneousEntropy CA4_5_7I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R12Value CA4_5_7I2R12MassTerm_sound CA4_5_7I2R12Entropy_sound) (by decide +kernel)
def CA4_5_7I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA4_5_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA4_5_7I2R13Raw_sound (a : PairSlot) :
    (CA4_5_7I2R13Raw a).Encloses (CA4_5_7I2R13Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA4_5_7I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R13Certificates_valid :
    CA4_5_7I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R13Certificates (CA4_5_7I2R13CertificateIndex a)).input
lemma CA4_5_7I2R13P_check : ∀ a : PairSlot, contains (CA4_5_7I2R13Raw a) (CA4_5_7I2R13P a) = true := by
  decide +kernel
lemma CA4_5_7I2R13P_sound (a : PairSlot) :
    (CA4_5_7I2R13P a).Encloses (CA4_5_7I2R13Value a) :=
  contains_sound (CA4_5_7I2R13Raw_sound a) (CA4_5_7I2R13P_check a)
def CA4_5_7I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R13Certificates (CA4_5_7I2R13CertificateIndex a)).output
lemma CA4_5_7I2R13Terms_sound (a : PairSlot) :
    (CA4_5_7I2R13Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R13Certificates_valid
    (CA4_5_7I2R13CertificateIndex a) (CA4_5_7I2R13P_sound a)
def CA4_5_7I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R13Entropy_sound : CA4_5_7I2R13Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R13Value CA4_5_7I2R13Terms CA4_5_7I2R13Terms_sound) (by decide +kernel)
def CA4_5_7I2R13Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R13Mass_sound : CA4_5_7I2R13Mass.Encloses (∑ a, CA4_5_7I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R13P CA4_5_7I2R13Value CA4_5_7I2R13P_sound) (by decide +kernel)
def CA4_5_7I2R13MassTerm : Ball := .exact 0
lemma CA4_5_7I2R13MassTerm_sound : CA4_5_7I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R13Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R13Mass_sound)
def CA4_5_7I2R13H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R13H_sound : CA4_5_7I2R13H.Encloses (homogeneousEntropy CA4_5_7I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R13Value CA4_5_7I2R13MassTerm_sound CA4_5_7I2R13Entropy_sound) (by decide +kernel)
def CA4_5_7I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA4_5_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA4_5_7I2R14Raw_sound (a : PairSlot) :
    (CA4_5_7I2R14Raw a).Encloses (CA4_5_7I2R14Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA4_5_7I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R14Certificates_valid :
    CA4_5_7I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R14Certificates (CA4_5_7I2R14CertificateIndex a)).input
lemma CA4_5_7I2R14P_check : ∀ a : PairSlot, contains (CA4_5_7I2R14Raw a) (CA4_5_7I2R14P a) = true := by
  decide +kernel
lemma CA4_5_7I2R14P_sound (a : PairSlot) :
    (CA4_5_7I2R14P a).Encloses (CA4_5_7I2R14Value a) :=
  contains_sound (CA4_5_7I2R14Raw_sound a) (CA4_5_7I2R14P_check a)
def CA4_5_7I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R14Certificates (CA4_5_7I2R14CertificateIndex a)).output
lemma CA4_5_7I2R14Terms_sound (a : PairSlot) :
    (CA4_5_7I2R14Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R14Certificates_valid
    (CA4_5_7I2R14CertificateIndex a) (CA4_5_7I2R14P_sound a)
def CA4_5_7I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R14Entropy_sound : CA4_5_7I2R14Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R14Value CA4_5_7I2R14Terms CA4_5_7I2R14Terms_sound) (by decide +kernel)
def CA4_5_7I2R14Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R14Mass_sound : CA4_5_7I2R14Mass.Encloses (∑ a, CA4_5_7I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R14P CA4_5_7I2R14Value CA4_5_7I2R14P_sound) (by decide +kernel)
def CA4_5_7I2R14MassTerm : Ball := .exact 0
lemma CA4_5_7I2R14MassTerm_sound : CA4_5_7I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R14Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R14Mass_sound)
def CA4_5_7I2R14H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R14H_sound : CA4_5_7I2R14H.Encloses (homogeneousEntropy CA4_5_7I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R14Value CA4_5_7I2R14MassTerm_sound CA4_5_7I2R14Entropy_sound) (by decide +kernel)
def CA4_5_7I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA4_5_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA4_5_7I2R15Raw_sound (a : PairSlot) :
    (CA4_5_7I2R15Raw a).Encloses (CA4_5_7I2R15Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA4_5_7I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R15Certificates_valid :
    CA4_5_7I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R15Certificates (CA4_5_7I2R15CertificateIndex a)).input
lemma CA4_5_7I2R15P_check : ∀ a : PairSlot, contains (CA4_5_7I2R15Raw a) (CA4_5_7I2R15P a) = true := by
  decide +kernel
lemma CA4_5_7I2R15P_sound (a : PairSlot) :
    (CA4_5_7I2R15P a).Encloses (CA4_5_7I2R15Value a) :=
  contains_sound (CA4_5_7I2R15Raw_sound a) (CA4_5_7I2R15P_check a)
def CA4_5_7I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R15Certificates (CA4_5_7I2R15CertificateIndex a)).output
lemma CA4_5_7I2R15Terms_sound (a : PairSlot) :
    (CA4_5_7I2R15Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R15Certificates_valid
    (CA4_5_7I2R15CertificateIndex a) (CA4_5_7I2R15P_sound a)
def CA4_5_7I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R15Entropy_sound : CA4_5_7I2R15Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R15Value CA4_5_7I2R15Terms CA4_5_7I2R15Terms_sound) (by decide +kernel)
def CA4_5_7I2R15Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R15Mass_sound : CA4_5_7I2R15Mass.Encloses (∑ a, CA4_5_7I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R15P CA4_5_7I2R15Value CA4_5_7I2R15P_sound) (by decide +kernel)
def CA4_5_7I2R15MassTerm : Ball := .exact 0
lemma CA4_5_7I2R15MassTerm_sound : CA4_5_7I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R15Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R15Mass_sound)
def CA4_5_7I2R15H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R15H_sound : CA4_5_7I2R15H.Encloses (homogeneousEntropy CA4_5_7I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R15Value CA4_5_7I2R15MassTerm_sound CA4_5_7I2R15Entropy_sound) (by decide +kernel)
def CA4_5_7I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA4_5_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 5 7)) A4_5_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA4_5_7I2R16Raw_sound (a : PairSlot) :
    (CA4_5_7I2R16Raw a).Encloses (CA4_5_7I2R16Value a) := by
  exact residualBall_sound_on (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 5 7) (show (shape 4 5 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA4_5_7I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_5_7I2R16Certificates_valid :
    CA4_5_7I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_5_7I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R16Certificates (CA4_5_7I2R16CertificateIndex a)).input
lemma CA4_5_7I2R16P_check : ∀ a : PairSlot, contains (CA4_5_7I2R16Raw a) (CA4_5_7I2R16P a) = true := by
  decide +kernel
lemma CA4_5_7I2R16P_sound (a : PairSlot) :
    (CA4_5_7I2R16P a).Encloses (CA4_5_7I2R16Value a) :=
  contains_sound (CA4_5_7I2R16Raw_sound a) (CA4_5_7I2R16P_check a)
def CA4_5_7I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I2R16Certificates (CA4_5_7I2R16CertificateIndex a)).output
lemma CA4_5_7I2R16Terms_sound (a : PairSlot) :
    (CA4_5_7I2R16Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I2R16Certificates_valid
    (CA4_5_7I2R16CertificateIndex a) (CA4_5_7I2R16P_sound a)
def CA4_5_7I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R16Entropy_sound : CA4_5_7I2R16Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_5_7I2R16Value CA4_5_7I2R16Terms CA4_5_7I2R16Terms_sound) (by decide +kernel)
def CA4_5_7I2R16Mass : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R16Mass_sound : CA4_5_7I2R16Mass.Encloses (∑ a, CA4_5_7I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_5_7I2R16P CA4_5_7I2R16Value CA4_5_7I2R16P_sound) (by decide +kernel)
def CA4_5_7I2R16MassTerm : Ball := .exact 0
lemma CA4_5_7I2R16MassTerm_sound : CA4_5_7I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I2R16Value a))) :=
  entropyTerm_zero_ball (CA4_5_7I2R16Mass_sound)
def CA4_5_7I2R16H : Ball := ⟨0, 0⟩
lemma CA4_5_7I2R16H_sound : CA4_5_7I2R16H.Encloses (homogeneousEntropy CA4_5_7I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I2R16Value CA4_5_7I2R16MassTerm_sound CA4_5_7I2R16Entropy_sound) (by decide +kernel)
def CA4_5_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_5_7I2R0H
  | 1 => CA4_5_7I2R1H
  | 2 => CA4_5_7I2R2H
  | 3 => CA4_5_7I2R3H
  | 4 => CA4_5_7I2R4H
  | 5 => CA4_5_7I2R5H
  | 6 => CA4_5_7I2R6H
  | 7 => CA4_5_7I2R7H
  | 8 => CA4_5_7I2R8H
  | 9 => CA4_5_7I2R9H
  | 10 => CA4_5_7I2R10H
  | 11 => CA4_5_7I2R11H
  | 12 => CA4_5_7I2R12H
  | 13 => CA4_5_7I2R13H
  | 14 => CA4_5_7I2R14H
  | 15 => CA4_5_7I2R15H
  | 16 => CA4_5_7I2R16H
  | _ => (.exact 0)
lemma CA4_5_7I2ResidualEntropies_sound (k : Fin 17) :
    (CA4_5_7I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_5_7I2R0H_sound
  · exact CA4_5_7I2R1H_sound
  · exact CA4_5_7I2R2H_sound
  · exact CA4_5_7I2R3H_sound
  · exact CA4_5_7I2R4H_sound
  · exact CA4_5_7I2R5H_sound
  · exact CA4_5_7I2R6H_sound
  · exact CA4_5_7I2R7H_sound
  · exact CA4_5_7I2R8H_sound
  · exact CA4_5_7I2R9H_sound
  · exact CA4_5_7I2R10H_sound
  · exact CA4_5_7I2R11H_sound
  · exact CA4_5_7I2R12H_sound
  · exact CA4_5_7I2R13H_sound
  · exact CA4_5_7I2R14H_sound
  · exact CA4_5_7I2R15H_sound
  · exact CA4_5_7I2R16H_sound
def CA4_5_7I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | 4, 0, 4 => Z4_0_4H2H
  | _, _, _ => (.exact 0)
lemma CA4_5_7I2Singles_sound (u : Shape) (hu : u ∈ below (shape 4 5 7))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA4_5_7I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A4_5_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 5 0) by decide +kernel) hd |>.elim
  · exact Z4_0_4H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 4 4 0) by decide +kernel) hd |>.elim
def CA4_5_7I2Singleton : Ball := ⟨(1736985044719429942832526678359 / 50000000000000000000000000000000), (714924641 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I2Singleton_sound : CA4_5_7I2Singleton.Encloses
    (singletonEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA4_5_7I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A4_5_7Law_sound u) CA4_5_7I2Singles_sound) (by decide +kernel)
def CA4_5_7I2Group : Ball := ⟨(2913317092543671156102318588643 / 3125000000000000000000000000000), (80897273129 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I2Group_sound : CA4_5_7I2Group.Encloses
    (groupedEntropy (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_5_7I2Singleton_sound
    (finSumBall_sound 17 CA4_5_7I2ResidualEntropies _ CA4_5_7I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_5_7I2H : Ball := ⟨(13279825312184419225649811606321 / 12500000000000000000000000000000), (461940268267 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I2_sound : CA4_5_7I2H.Encloses (stageACapacity (shape 4 5 7) 2) := by
  have hb := contains_sound (Ball.add_sound CA4_5_7I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_5_7I2Group_sound)))
    (show contains (.add CA4_5_7I2PairH (.neg (.mul (.exact 2) CA4_5_7I2Group))) CA4_5_7I2H = true by decide +kernel)
  unfold CA4_5_7I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
