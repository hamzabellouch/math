import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA4_6_6I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_6_6I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA4_6_6I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA4_6_6I1R0Raw_sound (a : PairSlot) :
    (CA4_6_6I1R0Raw a).Encloses (CA4_6_6I1R0Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA4_6_6I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15773965556059223716466861929 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(69047100494242373905364798197 / 50000000000000000000000000000000), (4676377 / 10000000000000000000000000000000)⟩ ⟨(-437728231679315675174532705087319 / 50000000000000000000000000000000), (14823077529 / 5000000000000000000000000000000)⟩ ⟨-13, 15773965556059223716466861929, 12207031250000000000000000000⟩]
lemma CA4_6_6I1R0Certificates_valid :
    CA4_6_6I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA4_6_6I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R0Certificates (CA4_6_6I1R0CertificateIndex a)).input
lemma CA4_6_6I1R0P_check : ∀ a : PairSlot, contains (CA4_6_6I1R0Raw a) (CA4_6_6I1R0P a) = true := by
  decide +kernel
lemma CA4_6_6I1R0P_sound (a : PairSlot) :
    (CA4_6_6I1R0P a).Encloses (CA4_6_6I1R0Value a) :=
  contains_sound (CA4_6_6I1R0Raw_sound a) (CA4_6_6I1R0P_check a)
def CA4_6_6I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R0Certificates (CA4_6_6I1R0CertificateIndex a)).output
lemma CA4_6_6I1R0Terms_sound (a : PairSlot) :
    (CA4_6_6I1R0Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R0Certificates_valid
    (CA4_6_6I1R0CertificateIndex a) (CA4_6_6I1R0P_sound a)
def CA4_6_6I1R0Entropy : Ball := ⟨(69047100494242373905364798197 / 50000000000000000000000000000000), (4676377 / 10000000000000000000000000000000)⟩
lemma CA4_6_6I1R0Entropy_sound : CA4_6_6I1R0Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R0Value CA4_6_6I1R0Terms CA4_6_6I1R0Terms_sound) (by decide +kernel)
def CA4_6_6I1R0Mass : Ball := ⟨(15773965556059223716466861929 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R0Mass_sound : CA4_6_6I1R0Mass.Encloses (∑ a, CA4_6_6I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R0P CA4_6_6I1R0Value CA4_6_6I1R0P_sound) (by decide +kernel)
def CA4_6_6I1R0MassTermLogWitness : LogWitness := ⟨-13, 15773965556059223716466861929, 12207031250000000000000000000⟩
def CA4_6_6I1R0MassTermLog : Ball := ⟨(-437728231679315675174532705087319 / 50000000000000000000000000000000), (14823077529 / 5000000000000000000000000000000)⟩
lemma CA4_6_6I1R0MassTermLog_sound : CA4_6_6I1R0MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R0Mass_sound) (w := CA4_6_6I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R0MassTerm : Ball := ⟨(69047100494242373905364798197 / 50000000000000000000000000000000), (4676377 / 10000000000000000000000000000000)⟩
lemma CA4_6_6I1R0MassTerm_sound : CA4_6_6I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R0Mass_sound) CA4_6_6I1R0MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R0H : Ball := ⟨0, (4676377 / 5000000000000000000000000000000)⟩
lemma CA4_6_6I1R0H_sound : CA4_6_6I1R0H.Encloses (homogeneousEntropy CA4_6_6I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R0Value CA4_6_6I1R0MassTerm_sound CA4_6_6I1R0Entropy_sound) (by decide +kernel)
def CA4_6_6I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA4_6_6I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA4_6_6I1R1Raw_sound (a : PairSlot) :
    (CA4_6_6I1R1Raw a).Encloses (CA4_6_6I1R1Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA4_6_6I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(85018587892439093136197242101 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(848589911628194458485256767603 / 25000000000000000000000000000000), (648121927 / 50000000000000000000000000000000)⟩ ⟨(-99812280192395620102401815789463 / 20000000000000000000000000000000), (5955700443 / 3125000000000000000000000000000)⟩ ⟨-8, 85018587892439093136197242101, 48828125000000000000000000000⟩]
lemma CA4_6_6I1R1Certificates_valid :
    CA4_6_6I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 1 => 1
  | 1, 0 => 1
  | _, _ => 0
def CA4_6_6I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R1Certificates (CA4_6_6I1R1CertificateIndex a)).input
lemma CA4_6_6I1R1P_check : ∀ a : PairSlot, contains (CA4_6_6I1R1Raw a) (CA4_6_6I1R1P a) = true := by
  decide +kernel
lemma CA4_6_6I1R1P_sound (a : PairSlot) :
    (CA4_6_6I1R1P a).Encloses (CA4_6_6I1R1Value a) :=
  contains_sound (CA4_6_6I1R1Raw_sound a) (CA4_6_6I1R1P_check a)
def CA4_6_6I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R1Certificates (CA4_6_6I1R1CertificateIndex a)).output
lemma CA4_6_6I1R1Terms_sound (a : PairSlot) :
    (CA4_6_6I1R1Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R1Certificates_valid
    (CA4_6_6I1R1CertificateIndex a) (CA4_6_6I1R1P_sound a)
def CA4_6_6I1R1Entropy : Ball := ⟨(848589911628194458485256767603 / 12500000000000000000000000000000), (648121927 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I1R1Entropy_sound : CA4_6_6I1R1Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R1Value CA4_6_6I1R1Terms CA4_6_6I1R1Terms_sound) (by decide +kernel)
def CA4_6_6I1R1Mass : Ball := ⟨(85018587892439093136197242101 / 6250000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R1Mass_sound : CA4_6_6I1R1Mass.Encloses (∑ a, CA4_6_6I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R1P CA4_6_6I1R1Value CA4_6_6I1R1P_sound) (by decide +kernel)
def CA4_6_6I1R1MassTermLogWitness : LogWitness := ⟨-7, 85018587892439093136197242101, 48828125000000000000000000000⟩
def CA4_6_6I1R1MassTermLog : Ball := ⟨(-85949336581196713914057177179397 / 20000000000000000000000000000000), (169406590493 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R1MassTermLog_sound : CA4_6_6I1R1MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R1Mass_sound) (w := CA4_6_6I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R1MassTerm : Ball := ⟨(116916659622804854083157751421 / 2000000000000000000000000000000), (2304433517 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R1MassTerm_sound : CA4_6_6I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R1Mass_sound) CA4_6_6I1R1MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R1H : Ball := ⟨(471443155942656481862083284887 / 50000000000000000000000000000000), (195876849 / 4000000000000000000000000000000)⟩
lemma CA4_6_6I1R1H_sound : CA4_6_6I1R1H.Encloses (homogeneousEntropy CA4_6_6I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R1Value CA4_6_6I1R1MassTerm_sound CA4_6_6I1R1Entropy_sound) (by decide +kernel)
def CA4_6_6I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA4_6_6I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA4_6_6I1R2Raw_sound (a : PairSlot) :
    (CA4_6_6I1R2Raw a).Encloses (CA4_6_6I1R2Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA4_6_6I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3927628248579179230197115299127 / 100000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩ ⟨(6357130338196642077599139921997 / 50000000000000000000000000000000), (4990245933 / 100000000000000000000000000000000)⟩ ⟨(-6474268882750128912606853797771 / 2000000000000000000000000000000), (1985233483 / 1562500000000000000000000000000)⟩ ⟨-5, 3927628248579179230197115299127, 3125000000000000000000000000000⟩,
   .log ⟨(148915355886952601084273077897 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(866151308917933645944085708067 / 50000000000000000000000000000000), (126136217 / 20000000000000000000000000000000)⟩ ⟨(-116328004423595181413166850775563 / 20000000000000000000000000000000), (211758237837 / 100000000000000000000000000000000)⟩ ⟨-9, 148915355886952601084273077897, 97656250000000000000000000000⟩,
   .log ⟨(7222314512261821528821625985319 / 50000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩ ⟨(27948154852403997103055724563901 / 100000000000000000000000000000000), (12235076949 / 100000000000000000000000000000000)⟩ ⟨(-193484753432950661454840799555697 / 100000000000000000000000000000000), (84703295327 / 100000000000000000000000000000000)⟩ ⟨-3, 7222314512261821528821625985319, 6250000000000000000000000000000⟩]
lemma CA4_6_6I1R2Certificates_valid :
    CA4_6_6I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA4_6_6I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R2Certificates (CA4_6_6I1R2CertificateIndex a)).input
lemma CA4_6_6I1R2P_check : ∀ a : PairSlot, contains (CA4_6_6I1R2Raw a) (CA4_6_6I1R2P a) = true := by
  decide +kernel
lemma CA4_6_6I1R2P_sound (a : PairSlot) :
    (CA4_6_6I1R2P a).Encloses (CA4_6_6I1R2Value a) :=
  contains_sound (CA4_6_6I1R2Raw_sound a) (CA4_6_6I1R2P_check a)
def CA4_6_6I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R2Certificates (CA4_6_6I1R2CertificateIndex a)).output
lemma CA4_6_6I1R2Terms_sound (a : PairSlot) :
    (CA4_6_6I1R2Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R2Certificates_valid
    (CA4_6_6I1R2CertificateIndex a) (CA4_6_6I1R2P_sound a)
def CA4_6_6I1R2Entropy : Ball := ⟨(56841281440862299997228627084157 / 100000000000000000000000000000000), (4695386197 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I1R2Entropy_sound : CA4_6_6I1R2Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R2Value CA4_6_6I1R2Terms CA4_6_6I1R2Terms_sound) (by decide +kernel)
def CA4_6_6I1R2Mass : Ball := ⟨(143097168407686324514841093003 / 625000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I1R2Mass_sound : CA4_6_6I1R2Mass.Encloses (∑ a, CA4_6_6I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R2P CA4_6_6I1R2Value CA4_6_6I1R2P_sound) (by decide +kernel)
def CA4_6_6I1R2MassTermLogWitness : LogWitness := ⟨-3, 143097168407686324514841093003, 78125000000000000000000000000⟩
def CA4_6_6I1R2MassTermLog : Ball := ⟨(-73711387543860233702273399980243 / 50000000000000000000000000000000), (84703295413 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R2MassTermLog_sound : CA4_6_6I1R2MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R2Mass_sound) (w := CA4_6_6I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R2MassTerm : Ball := ⟨(33753250678169599658428471925163 / 100000000000000000000000000000000), (4848320749 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I1R2MassTerm_sound : CA4_6_6I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R2Mass_sound) CA4_6_6I1R2MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R2H : Ball := ⟨(11544015381346350169400077579497 / 50000000000000000000000000000000), (42870213981 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R2H_sound : CA4_6_6I1R2H.Encloses (homogeneousEntropy CA4_6_6I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R2Value CA4_6_6I1R2MassTerm_sound CA4_6_6I1R2Entropy_sound) (by decide +kernel)
def CA4_6_6I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA4_6_6I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA4_6_6I1R3Raw_sound (a : PairSlot) :
    (CA4_6_6I1R3Raw a).Encloses (CA4_6_6I1R3Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA4_6_6I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(171471744879298233733151873831 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(1708617377034878150805047333371 / 50000000000000000000000000000000), (653589997 / 50000000000000000000000000000000)⟩ ⟨(-249110630185399039528940815840401 / 50000000000000000000000000000000), (95291207011 / 50000000000000000000000000000000)⟩ ⟨-8, 171471744879298233733151873831, 97656250000000000000000000000⟩,
   .log ⟨(23394597168243240399713481862367 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩ ⟨(8496128594841533449942219230593 / 25000000000000000000000000000000), (990799741 / 5000000000000000000000000000000)⟩ ⟨(-145266508052970749767308041011161 / 100000000000000000000000000000000), (84703295129 / 100000000000000000000000000000000)⟩ ⟨-3, 23394597168243240399713481862367, 12500000000000000000000000000000⟩,
   .log ⟨(329579507034934005816742605257 / 20000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(6765723360675774378114648377973 / 100000000000000000000000000000000), (2442691177 / 100000000000000000000000000000000)⟩ ⟨(-410566993169186146742910496645879 / 100000000000000000000000000000000), (74115383133 / 50000000000000000000000000000000)⟩ ⟨-6, 329579507034934005816742605257, 312500000000000000000000000000⟩]
lemma CA4_6_6I1R3Certificates_valid :
    CA4_6_6I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA4_6_6I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R3Certificates (CA4_6_6I1R3CertificateIndex a)).input
lemma CA4_6_6I1R3P_check : ∀ a : PairSlot, contains (CA4_6_6I1R3Raw a) (CA4_6_6I1R3P a) = true := by
  decide +kernel
lemma CA4_6_6I1R3P_sound (a : PairSlot) :
    (CA4_6_6I1R3P a).Encloses (CA4_6_6I1R3Value a) :=
  contains_sound (CA4_6_6I1R3Raw_sound a) (CA4_6_6I1R3P_check a)
def CA4_6_6I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R3Certificates (CA4_6_6I1R3CertificateIndex a)).output
lemma CA4_6_6I1R3Terms_sound (a : PairSlot) :
    (CA4_6_6I1R3Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R3Certificates_valid
    (CA4_6_6I1R3CertificateIndex a) (CA4_6_6I1R3P_sound a)
def CA4_6_6I1R3Entropy : Ball := ⟨(44167472494111664479493619967087 / 50000000000000000000000000000000), (23565865991 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R3Entropy_sound : CA4_6_6I1R3Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R3Value CA4_6_6I1R3Terms CA4_6_6I1R3Terms_sound) (by decide +kernel)
def CA4_6_6I1R3Mass : Ball := ⟨(3216047710366887920466225297997 / 6250000000000000000000000000000), (107 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R3Mass_sound : CA4_6_6I1R3Mass.Encloses (∑ a, CA4_6_6I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R3P CA4_6_6I1R3Value CA4_6_6I1R3P_sound) (by decide +kernel)
def CA4_6_6I1R3MassTermLogWitness : LogWitness := ⟨-1, 3216047710366887920466225297997, 3125000000000000000000000000000⟩
def CA4_6_6I1R3MassTermLog : Ball := ⟨(-16610706930713633064934840352097 / 25000000000000000000000000000000), (42351647781 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R3MassTermLog_sound : CA4_6_6I1R3MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R3Mass_sound) (w := CA4_6_6I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R3MassTerm : Ball := ⟨(34189328634942064644830345826001 / 100000000000000000000000000000000), (21792787323 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R3MassTerm_sound : CA4_6_6I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R3Mass_sound) CA4_6_6I1R3MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R3H : Ball := ⟨(54145616353281264314156894108173 / 100000000000000000000000000000000), (13784903861 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I1R3H_sound : CA4_6_6I1R3H.Encloses (homogeneousEntropy CA4_6_6I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R3Value CA4_6_6I1R3MassTerm_sound CA4_6_6I1R3Entropy_sound) (by decide +kernel)
def CA4_6_6I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA4_6_6I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA4_6_6I1R4Raw_sound (a : PairSlot) :
    (CA4_6_6I1R4Raw a).Encloses (CA4_6_6I1R4Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA4_6_6I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(10264217402454907457895936341 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(11783657290823565372434024863 / 12500000000000000000000000000000), (32603 / 100000000000000000000000000000)⟩ ⟨(-459213082840792180331679723458093 / 50000000000000000000000000000000), (317637364987 / 100000000000000000000000000000000)⟩ ⟨-14, 10264217402454907457895936341, 6103515625000000000000000000⟩,
   .log ⟨(1880250476688399864795208175819 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(1867918471183757579202867080319 / 25000000000000000000000000000000), (557421951 / 20000000000000000000000000000000)⟩ ⟨(-15895060742959207526817365160531 / 4000000000000000000000000000000), (74115383289 / 50000000000000000000000000000000)⟩ ⟨-6, 1880250476688399864795208175819, 1562500000000000000000000000000⟩,
   .log ⟨(4309934616831163963269990063673 / 25000000000000000000000000000000), (51 / 50000000000000000000000000000000)⟩ ⟨(7576662881564488862285429189061 / 25000000000000000000000000000000), (14602626767 / 100000000000000000000000000000000)⟩ ⟨(-175795309097639025620586427413949 / 100000000000000000000000000000000), (84703295323 / 100000000000000000000000000000000)⟩ ⟨-3, 4309934616831163963269990063673, 3125000000000000000000000000000⟩,
   .log ⟨(113640784216833638854226749691 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(2136647417192110385904686834403 / 50000000000000000000000000000000), (308023971 / 20000000000000000000000000000000)⟩ ⟨(-94008829308818173817478303915327 / 20000000000000000000000000000000), (169406590233 / 100000000000000000000000000000000)⟩ ⟨-7, 113640784216833638854226749691, 97656250000000000000000000000⟩,
   .log ⟨(11438790751530144583616577951 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2198999089973185030179928287 / 625000000000000000000000000000), (62978717 / 50000000000000000000000000000000)⟩ ⟨(-768962082702327337779670801763771 / 100000000000000000000000000000000), (17205356879 / 6250000000000000000000000000000)⟩ ⟨-12, 11438790751530144583616577951, 6103515625000000000000000000⟩]
lemma CA4_6_6I1R4Certificates_valid :
    CA4_6_6I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA4_6_6I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R4Certificates (CA4_6_6I1R4CertificateIndex a)).input
lemma CA4_6_6I1R4P_check : ∀ a : PairSlot, contains (CA4_6_6I1R4Raw a) (CA4_6_6I1R4P a) = true := by
  decide +kernel
lemma CA4_6_6I1R4P_sound (a : PairSlot) :
    (CA4_6_6I1R4P a).Encloses (CA4_6_6I1R4Value a) :=
  contains_sound (CA4_6_6I1R4Raw_sound a) (CA4_6_6I1R4P_check a)
def CA4_6_6I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R4Certificates (CA4_6_6I1R4CertificateIndex a)).output
lemma CA4_6_6I1R4Terms_sound (a : PairSlot) :
    (CA4_6_6I1R4Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R4Certificates_valid
    (CA4_6_6I1R4CertificateIndex a) (CA4_6_6I1R4P_sound a)
def CA4_6_6I1R4Entropy : Ball := ⟨(6792120916943168034646391707517 / 12500000000000000000000000000000), (23448249421 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R4Entropy_sound : CA4_6_6I1R4Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R4Value CA4_6_6I1R4Terms CA4_6_6I1R4Terms_sound) (by decide +kernel)
def CA4_6_6I1R4Mass : Ball := ⟨(1430298472873864012349266424117 / 6250000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R4Mass_sound : CA4_6_6I1R4Mass.Encloses (∑ a, CA4_6_6I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R4P CA4_6_6I1R4Value CA4_6_6I1R4P_sound) (by decide +kernel)
def CA4_6_6I1R4MassTermLogWitness : LogWitness := ⟨-3, 1430298472873864012349266424117, 781250000000000000000000000000⟩
def CA4_6_6I1R4MassTermLog : Ball := ⟨(-29493966379330907074674043622459 / 20000000000000000000000000000000), (84703295383 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R4MassTermLog_sound : CA4_6_6I1R4MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R4Mass_sound) (w := CA4_6_6I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R4MassTerm : Ball := ⟨(33748140057080067657293397594779 / 100000000000000000000000000000000), (9692079633 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R4MassTerm_sound : CA4_6_6I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R4Mass_sound) CA4_6_6I1R4MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R4H : Ball := ⟨(20588827278465276619877736065357 / 100000000000000000000000000000000), (42832408687 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R4H_sound : CA4_6_6I1R4H.Encloses (homogeneousEntropy CA4_6_6I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R4Value CA4_6_6I1R4MassTerm_sound CA4_6_6I1R4Entropy_sound) (by decide +kernel)
def CA4_6_6I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA4_6_6I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA4_6_6I1R5Raw_sound (a : PairSlot) :
    (CA4_6_6I1R5Raw a).Encloses (CA4_6_6I1R5Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA4_6_6I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3825868585720216092964071611 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2688773179135836767367696879 / 2000000000000000000000000000000), (1814757 / 4000000000000000000000000000000)⟩ ⟨(-219621139527920902374457498962489 / 25000000000000000000000000000000), (18528846131 / 6250000000000000000000000000000)⟩ ⟨-13, 3825868585720216092964071611, 3051757812500000000000000000⟩,
   .log ⟨(31332244156975329096401611801 / 5000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(635736931320862753580964465469 / 20000000000000000000000000000000), (1194274983 / 100000000000000000000000000000000)⟩ ⟨(-253627272968305742089183828342649 / 50000000000000000000000000000000), (23822801783 / 12500000000000000000000000000000)⟩ ⟨-8, 31332244156975329096401611801, 19531250000000000000000000000⟩,
   .log ⟨(35706451602411539604070028661 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(56684663738269144205581058141 / 20000000000000000000000000000000), (6143423 / 6250000000000000000000000000000)⟩ ⟨(-31750376301430512188351838480739 / 4000000000000000000000000000000), (275285710679 / 100000000000000000000000000000000)⟩ ⟨-12, 35706451602411539604070028661, 24414062500000000000000000000⟩]
lemma CA4_6_6I1R5Certificates_valid :
    CA4_6_6I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA4_6_6I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R5Certificates (CA4_6_6I1R5CertificateIndex a)).input
lemma CA4_6_6I1R5P_check : ∀ a : PairSlot, contains (CA4_6_6I1R5Raw a) (CA4_6_6I1R5P a) = true := by
  decide +kernel
lemma CA4_6_6I1R5P_sound (a : PairSlot) :
    (CA4_6_6I1R5P a).Encloses (CA4_6_6I1R5Value a) :=
  contains_sound (CA4_6_6I1R5Raw_sound a) (CA4_6_6I1R5P_check a)
def CA4_6_6I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R5Certificates (CA4_6_6I1R5CertificateIndex a)).output
lemma CA4_6_6I1R5Terms_sound (a : PairSlot) :
    (CA4_6_6I1R5Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R5Certificates_valid
    (CA4_6_6I1R5CertificateIndex a) (CA4_6_6I1R5P_sound a)
def CA4_6_6I1R5Entropy : Ball := ⟨(1798273317126225663650556231 / 25000000000000000000000000000), (334484669 / 12500000000000000000000000000000)⟩
lemma CA4_6_6I1R5Entropy_sound : CA4_6_6I1R5Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R5Value CA4_6_6I1R5Terms CA4_6_6I1R5Terms_sound) (by decide +kernel)
def CA4_6_6I1R5Mass : Ball := ⟨(5421238472678391887231668409 / 400000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R5Mass_sound : CA4_6_6I1R5Mass.Encloses (∑ a, CA4_6_6I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R5P CA4_6_6I1R5Value CA4_6_6I1R5P_sound) (by decide +kernel)
def CA4_6_6I1R5MassTermLogWitness : LogWitness := ⟨-7, 5421238472678391887231668409, 3125000000000000000000000000⟩
def CA4_6_6I1R5MassTermLog : Ball := ⟨(-430114025726452064064942892187163 / 100000000000000000000000000000000), (21175823849 / 12500000000000000000000000000000)⟩
lemma CA4_6_6I1R5MassTermLog_sound : CA4_6_6I1R5MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R5Mass_sound) (w := CA4_6_6I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R5MassTerm : Ball := ⟨(2914688379883531929262569133991 / 50000000000000000000000000000000), (2295983897 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R5MassTerm_sound : CA4_6_6I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R5Mass_sound) CA4_6_6I1R5MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R5H : Ball := ⟨(681858254368919398038543328009 / 50000000000000000000000000000000), (4971861249 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1R5H_sound : CA4_6_6I1R5H.Encloses (homogeneousEntropy CA4_6_6I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R5Value CA4_6_6I1R5MassTerm_sound CA4_6_6I1R5Entropy_sound) (by decide +kernel)
def CA4_6_6I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA4_6_6I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA4_6_6I1R6Raw_sound (a : PairSlot) :
    (CA4_6_6I1R6Raw a).Encloses (CA4_6_6I1R6Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA4_6_6I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2216061498608268849636149949 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(23749960873281983223153963687 / 100000000000000000000000000000000), (797759 / 10000000000000000000000000000000)⟩ ⟨(-267929848609768229357052599996109 / 25000000000000000000000000000000), (44998630967 / 12500000000000000000000000000000)⟩ ⟨-16, 2216061498608268849636149949, 1525878906250000000000000000⟩,
   .log ⟨(143464820076889544050307539 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1930260461968944409326252621 / 100000000000000000000000000000000), (79749 / 12500000000000000000000000000000)⟩ ⟨(-672729544753350350985395320593371 / 50000000000000000000000000000000), (222346497189 / 50000000000000000000000000000000)⟩ ⟨-20, 143464820076889544050307539, 95367431640625000000000000⟩,
   .log ⟨(10693526489845127047010417541 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(97773980750015420343107907517 / 100000000000000000000000000000000), (530729 / 1562500000000000000000000000000)⟩ ⟨(-91432869075383445547072618074003 / 10000000000000000000000000000000), (317637373947 / 100000000000000000000000000000000)⟩ ⟨-14, 10693526489845127047010417541, 6103515625000000000000000000⟩]
lemma CA4_6_6I1R6Certificates_valid :
    CA4_6_6I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA4_6_6I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R6Certificates (CA4_6_6I1R6CertificateIndex a)).input
lemma CA4_6_6I1R6P_check : ∀ a : PairSlot, contains (CA4_6_6I1R6Raw a) (CA4_6_6I1R6P a) = true := by
  decide +kernel
lemma CA4_6_6I1R6P_sound (a : PairSlot) :
    (CA4_6_6I1R6P a).Encloses (CA4_6_6I1R6Value a) :=
  contains_sound (CA4_6_6I1R6Raw_sound a) (CA4_6_6I1R6P_check a)
def CA4_6_6I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R6Certificates (CA4_6_6I1R6CertificateIndex a)).output
lemma CA4_6_6I1R6Terms_sound (a : PairSlot) :
    (CA4_6_6I1R6Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R6Certificates_valid
    (CA4_6_6I1R6CertificateIndex a) (CA4_6_6I1R6P_sound a)
def CA4_6_6I1R6Entropy : Ball := ⟨(149134423420517275608068340133 / 100000000000000000000000000000000), (2559891 / 5000000000000000000000000000000)⟩
lemma CA4_6_6I1R6Entropy_sound : CA4_6_6I1R6Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R6Value CA4_6_6I1R6Terms CA4_6_6I1R6Terms_sound) (by decide +kernel)
def CA4_6_6I1R6Mass : Ball := ⟨(15412579127215443834383332517 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I1R6Mass_sound : CA4_6_6I1R6Mass.Encloses (∑ a, CA4_6_6I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R6P CA4_6_6I1R6Value CA4_6_6I1R6P_sound) (by decide +kernel)
def CA4_6_6I1R6MassTermLogWitness : LogWitness := ⟨-13, 15412579127215443834383332517, 12207031250000000000000000000⟩
def CA4_6_6I1R6MassTermLog : Ball := ⟨(-438887073126462491403995506839213 / 50000000000000000000000000000000), (29646157049 / 10000000000000000000000000000000)⟩
lemma CA4_6_6I1R6MassTermLog_sound : CA4_6_6I1R6MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I1R6Mass_sound) (w := CA4_6_6I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I1R6MassTerm : Ball := ⟨(135287634849471878805145624111 / 100000000000000000000000000000000), (11423107 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I1R6MassTerm_sound : CA4_6_6I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I1R6Mass_sound) CA4_6_6I1R6MassTermLog_sound) (by decide +kernel)
def CA4_6_6I1R6H : Ball := ⟨(6923394285522698401461358011 / 50000000000000000000000000000000), (12111281 / 12500000000000000000000000000000)⟩
lemma CA4_6_6I1R6H_sound : CA4_6_6I1R6H.Encloses (homogeneousEntropy CA4_6_6I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R6Value CA4_6_6I1R6MassTerm_sound CA4_6_6I1R6Entropy_sound) (by decide +kernel)
def CA4_6_6I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA4_6_6I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA4_6_6I1R7Raw_sound (a : PairSlot) :
    (CA4_6_6I1R7Raw a).Encloses (CA4_6_6I1R7Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA4_6_6I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R7Certificates_valid :
    CA4_6_6I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R7Certificates (CA4_6_6I1R7CertificateIndex a)).input
lemma CA4_6_6I1R7P_check : ∀ a : PairSlot, contains (CA4_6_6I1R7Raw a) (CA4_6_6I1R7P a) = true := by
  decide +kernel
lemma CA4_6_6I1R7P_sound (a : PairSlot) :
    (CA4_6_6I1R7P a).Encloses (CA4_6_6I1R7Value a) :=
  contains_sound (CA4_6_6I1R7Raw_sound a) (CA4_6_6I1R7P_check a)
def CA4_6_6I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R7Certificates (CA4_6_6I1R7CertificateIndex a)).output
lemma CA4_6_6I1R7Terms_sound (a : PairSlot) :
    (CA4_6_6I1R7Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R7Certificates_valid
    (CA4_6_6I1R7CertificateIndex a) (CA4_6_6I1R7P_sound a)
def CA4_6_6I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R7Entropy_sound : CA4_6_6I1R7Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R7Value CA4_6_6I1R7Terms CA4_6_6I1R7Terms_sound) (by decide +kernel)
def CA4_6_6I1R7Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R7Mass_sound : CA4_6_6I1R7Mass.Encloses (∑ a, CA4_6_6I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R7P CA4_6_6I1R7Value CA4_6_6I1R7P_sound) (by decide +kernel)
def CA4_6_6I1R7MassTerm : Ball := .exact 0
lemma CA4_6_6I1R7MassTerm_sound : CA4_6_6I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R7Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R7Mass_sound)
def CA4_6_6I1R7H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R7H_sound : CA4_6_6I1R7H.Encloses (homogeneousEntropy CA4_6_6I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R7Value CA4_6_6I1R7MassTerm_sound CA4_6_6I1R7Entropy_sound) (by decide +kernel)
def CA4_6_6I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA4_6_6I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA4_6_6I1R8Raw_sound (a : PairSlot) :
    (CA4_6_6I1R8Raw a).Encloses (CA4_6_6I1R8Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA4_6_6I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R8Certificates_valid :
    CA4_6_6I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R8Certificates (CA4_6_6I1R8CertificateIndex a)).input
lemma CA4_6_6I1R8P_check : ∀ a : PairSlot, contains (CA4_6_6I1R8Raw a) (CA4_6_6I1R8P a) = true := by
  decide +kernel
lemma CA4_6_6I1R8P_sound (a : PairSlot) :
    (CA4_6_6I1R8P a).Encloses (CA4_6_6I1R8Value a) :=
  contains_sound (CA4_6_6I1R8Raw_sound a) (CA4_6_6I1R8P_check a)
def CA4_6_6I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R8Certificates (CA4_6_6I1R8CertificateIndex a)).output
lemma CA4_6_6I1R8Terms_sound (a : PairSlot) :
    (CA4_6_6I1R8Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R8Certificates_valid
    (CA4_6_6I1R8CertificateIndex a) (CA4_6_6I1R8P_sound a)
def CA4_6_6I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R8Entropy_sound : CA4_6_6I1R8Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R8Value CA4_6_6I1R8Terms CA4_6_6I1R8Terms_sound) (by decide +kernel)
def CA4_6_6I1R8Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R8Mass_sound : CA4_6_6I1R8Mass.Encloses (∑ a, CA4_6_6I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R8P CA4_6_6I1R8Value CA4_6_6I1R8P_sound) (by decide +kernel)
def CA4_6_6I1R8MassTerm : Ball := .exact 0
lemma CA4_6_6I1R8MassTerm_sound : CA4_6_6I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R8Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R8Mass_sound)
def CA4_6_6I1R8H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R8H_sound : CA4_6_6I1R8H.Encloses (homogeneousEntropy CA4_6_6I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R8Value CA4_6_6I1R8MassTerm_sound CA4_6_6I1R8Entropy_sound) (by decide +kernel)
def CA4_6_6I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA4_6_6I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA4_6_6I1R9Raw_sound (a : PairSlot) :
    (CA4_6_6I1R9Raw a).Encloses (CA4_6_6I1R9Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA4_6_6I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R9Certificates_valid :
    CA4_6_6I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R9Certificates (CA4_6_6I1R9CertificateIndex a)).input
lemma CA4_6_6I1R9P_check : ∀ a : PairSlot, contains (CA4_6_6I1R9Raw a) (CA4_6_6I1R9P a) = true := by
  decide +kernel
lemma CA4_6_6I1R9P_sound (a : PairSlot) :
    (CA4_6_6I1R9P a).Encloses (CA4_6_6I1R9Value a) :=
  contains_sound (CA4_6_6I1R9Raw_sound a) (CA4_6_6I1R9P_check a)
def CA4_6_6I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R9Certificates (CA4_6_6I1R9CertificateIndex a)).output
lemma CA4_6_6I1R9Terms_sound (a : PairSlot) :
    (CA4_6_6I1R9Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R9Certificates_valid
    (CA4_6_6I1R9CertificateIndex a) (CA4_6_6I1R9P_sound a)
def CA4_6_6I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R9Entropy_sound : CA4_6_6I1R9Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R9Value CA4_6_6I1R9Terms CA4_6_6I1R9Terms_sound) (by decide +kernel)
def CA4_6_6I1R9Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R9Mass_sound : CA4_6_6I1R9Mass.Encloses (∑ a, CA4_6_6I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R9P CA4_6_6I1R9Value CA4_6_6I1R9P_sound) (by decide +kernel)
def CA4_6_6I1R9MassTerm : Ball := .exact 0
lemma CA4_6_6I1R9MassTerm_sound : CA4_6_6I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R9Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R9Mass_sound)
def CA4_6_6I1R9H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R9H_sound : CA4_6_6I1R9H.Encloses (homogeneousEntropy CA4_6_6I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R9Value CA4_6_6I1R9MassTerm_sound CA4_6_6I1R9Entropy_sound) (by decide +kernel)
def CA4_6_6I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA4_6_6I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA4_6_6I1R10Raw_sound (a : PairSlot) :
    (CA4_6_6I1R10Raw a).Encloses (CA4_6_6I1R10Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA4_6_6I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R10Certificates_valid :
    CA4_6_6I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R10Certificates (CA4_6_6I1R10CertificateIndex a)).input
lemma CA4_6_6I1R10P_check : ∀ a : PairSlot, contains (CA4_6_6I1R10Raw a) (CA4_6_6I1R10P a) = true := by
  decide +kernel
lemma CA4_6_6I1R10P_sound (a : PairSlot) :
    (CA4_6_6I1R10P a).Encloses (CA4_6_6I1R10Value a) :=
  contains_sound (CA4_6_6I1R10Raw_sound a) (CA4_6_6I1R10P_check a)
def CA4_6_6I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R10Certificates (CA4_6_6I1R10CertificateIndex a)).output
lemma CA4_6_6I1R10Terms_sound (a : PairSlot) :
    (CA4_6_6I1R10Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R10Certificates_valid
    (CA4_6_6I1R10CertificateIndex a) (CA4_6_6I1R10P_sound a)
def CA4_6_6I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R10Entropy_sound : CA4_6_6I1R10Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R10Value CA4_6_6I1R10Terms CA4_6_6I1R10Terms_sound) (by decide +kernel)
def CA4_6_6I1R10Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R10Mass_sound : CA4_6_6I1R10Mass.Encloses (∑ a, CA4_6_6I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R10P CA4_6_6I1R10Value CA4_6_6I1R10P_sound) (by decide +kernel)
def CA4_6_6I1R10MassTerm : Ball := .exact 0
lemma CA4_6_6I1R10MassTerm_sound : CA4_6_6I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R10Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R10Mass_sound)
def CA4_6_6I1R10H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R10H_sound : CA4_6_6I1R10H.Encloses (homogeneousEntropy CA4_6_6I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R10Value CA4_6_6I1R10MassTerm_sound CA4_6_6I1R10Entropy_sound) (by decide +kernel)
def CA4_6_6I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA4_6_6I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA4_6_6I1R11Raw_sound (a : PairSlot) :
    (CA4_6_6I1R11Raw a).Encloses (CA4_6_6I1R11Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA4_6_6I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R11Certificates_valid :
    CA4_6_6I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R11Certificates (CA4_6_6I1R11CertificateIndex a)).input
lemma CA4_6_6I1R11P_check : ∀ a : PairSlot, contains (CA4_6_6I1R11Raw a) (CA4_6_6I1R11P a) = true := by
  decide +kernel
lemma CA4_6_6I1R11P_sound (a : PairSlot) :
    (CA4_6_6I1R11P a).Encloses (CA4_6_6I1R11Value a) :=
  contains_sound (CA4_6_6I1R11Raw_sound a) (CA4_6_6I1R11P_check a)
def CA4_6_6I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R11Certificates (CA4_6_6I1R11CertificateIndex a)).output
lemma CA4_6_6I1R11Terms_sound (a : PairSlot) :
    (CA4_6_6I1R11Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R11Certificates_valid
    (CA4_6_6I1R11CertificateIndex a) (CA4_6_6I1R11P_sound a)
def CA4_6_6I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R11Entropy_sound : CA4_6_6I1R11Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R11Value CA4_6_6I1R11Terms CA4_6_6I1R11Terms_sound) (by decide +kernel)
def CA4_6_6I1R11Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R11Mass_sound : CA4_6_6I1R11Mass.Encloses (∑ a, CA4_6_6I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R11P CA4_6_6I1R11Value CA4_6_6I1R11P_sound) (by decide +kernel)
def CA4_6_6I1R11MassTerm : Ball := .exact 0
lemma CA4_6_6I1R11MassTerm_sound : CA4_6_6I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R11Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R11Mass_sound)
def CA4_6_6I1R11H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R11H_sound : CA4_6_6I1R11H.Encloses (homogeneousEntropy CA4_6_6I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R11Value CA4_6_6I1R11MassTerm_sound CA4_6_6I1R11Entropy_sound) (by decide +kernel)
def CA4_6_6I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA4_6_6I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA4_6_6I1R12Raw_sound (a : PairSlot) :
    (CA4_6_6I1R12Raw a).Encloses (CA4_6_6I1R12Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA4_6_6I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R12Certificates_valid :
    CA4_6_6I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R12Certificates (CA4_6_6I1R12CertificateIndex a)).input
lemma CA4_6_6I1R12P_check : ∀ a : PairSlot, contains (CA4_6_6I1R12Raw a) (CA4_6_6I1R12P a) = true := by
  decide +kernel
lemma CA4_6_6I1R12P_sound (a : PairSlot) :
    (CA4_6_6I1R12P a).Encloses (CA4_6_6I1R12Value a) :=
  contains_sound (CA4_6_6I1R12Raw_sound a) (CA4_6_6I1R12P_check a)
def CA4_6_6I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R12Certificates (CA4_6_6I1R12CertificateIndex a)).output
lemma CA4_6_6I1R12Terms_sound (a : PairSlot) :
    (CA4_6_6I1R12Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R12Certificates_valid
    (CA4_6_6I1R12CertificateIndex a) (CA4_6_6I1R12P_sound a)
def CA4_6_6I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R12Entropy_sound : CA4_6_6I1R12Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R12Value CA4_6_6I1R12Terms CA4_6_6I1R12Terms_sound) (by decide +kernel)
def CA4_6_6I1R12Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R12Mass_sound : CA4_6_6I1R12Mass.Encloses (∑ a, CA4_6_6I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R12P CA4_6_6I1R12Value CA4_6_6I1R12P_sound) (by decide +kernel)
def CA4_6_6I1R12MassTerm : Ball := .exact 0
lemma CA4_6_6I1R12MassTerm_sound : CA4_6_6I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R12Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R12Mass_sound)
def CA4_6_6I1R12H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R12H_sound : CA4_6_6I1R12H.Encloses (homogeneousEntropy CA4_6_6I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R12Value CA4_6_6I1R12MassTerm_sound CA4_6_6I1R12Entropy_sound) (by decide +kernel)
def CA4_6_6I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA4_6_6I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA4_6_6I1R13Raw_sound (a : PairSlot) :
    (CA4_6_6I1R13Raw a).Encloses (CA4_6_6I1R13Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA4_6_6I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R13Certificates_valid :
    CA4_6_6I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R13Certificates (CA4_6_6I1R13CertificateIndex a)).input
lemma CA4_6_6I1R13P_check : ∀ a : PairSlot, contains (CA4_6_6I1R13Raw a) (CA4_6_6I1R13P a) = true := by
  decide +kernel
lemma CA4_6_6I1R13P_sound (a : PairSlot) :
    (CA4_6_6I1R13P a).Encloses (CA4_6_6I1R13Value a) :=
  contains_sound (CA4_6_6I1R13Raw_sound a) (CA4_6_6I1R13P_check a)
def CA4_6_6I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R13Certificates (CA4_6_6I1R13CertificateIndex a)).output
lemma CA4_6_6I1R13Terms_sound (a : PairSlot) :
    (CA4_6_6I1R13Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R13Certificates_valid
    (CA4_6_6I1R13CertificateIndex a) (CA4_6_6I1R13P_sound a)
def CA4_6_6I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R13Entropy_sound : CA4_6_6I1R13Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R13Value CA4_6_6I1R13Terms CA4_6_6I1R13Terms_sound) (by decide +kernel)
def CA4_6_6I1R13Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R13Mass_sound : CA4_6_6I1R13Mass.Encloses (∑ a, CA4_6_6I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R13P CA4_6_6I1R13Value CA4_6_6I1R13P_sound) (by decide +kernel)
def CA4_6_6I1R13MassTerm : Ball := .exact 0
lemma CA4_6_6I1R13MassTerm_sound : CA4_6_6I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R13Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R13Mass_sound)
def CA4_6_6I1R13H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R13H_sound : CA4_6_6I1R13H.Encloses (homogeneousEntropy CA4_6_6I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R13Value CA4_6_6I1R13MassTerm_sound CA4_6_6I1R13Entropy_sound) (by decide +kernel)
def CA4_6_6I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA4_6_6I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA4_6_6I1R14Raw_sound (a : PairSlot) :
    (CA4_6_6I1R14Raw a).Encloses (CA4_6_6I1R14Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA4_6_6I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R14Certificates_valid :
    CA4_6_6I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R14Certificates (CA4_6_6I1R14CertificateIndex a)).input
lemma CA4_6_6I1R14P_check : ∀ a : PairSlot, contains (CA4_6_6I1R14Raw a) (CA4_6_6I1R14P a) = true := by
  decide +kernel
lemma CA4_6_6I1R14P_sound (a : PairSlot) :
    (CA4_6_6I1R14P a).Encloses (CA4_6_6I1R14Value a) :=
  contains_sound (CA4_6_6I1R14Raw_sound a) (CA4_6_6I1R14P_check a)
def CA4_6_6I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R14Certificates (CA4_6_6I1R14CertificateIndex a)).output
lemma CA4_6_6I1R14Terms_sound (a : PairSlot) :
    (CA4_6_6I1R14Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R14Certificates_valid
    (CA4_6_6I1R14CertificateIndex a) (CA4_6_6I1R14P_sound a)
def CA4_6_6I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R14Entropy_sound : CA4_6_6I1R14Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R14Value CA4_6_6I1R14Terms CA4_6_6I1R14Terms_sound) (by decide +kernel)
def CA4_6_6I1R14Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R14Mass_sound : CA4_6_6I1R14Mass.Encloses (∑ a, CA4_6_6I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R14P CA4_6_6I1R14Value CA4_6_6I1R14P_sound) (by decide +kernel)
def CA4_6_6I1R14MassTerm : Ball := .exact 0
lemma CA4_6_6I1R14MassTerm_sound : CA4_6_6I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R14Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R14Mass_sound)
def CA4_6_6I1R14H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R14H_sound : CA4_6_6I1R14H.Encloses (homogeneousEntropy CA4_6_6I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R14Value CA4_6_6I1R14MassTerm_sound CA4_6_6I1R14Entropy_sound) (by decide +kernel)
def CA4_6_6I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA4_6_6I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA4_6_6I1R15Raw_sound (a : PairSlot) :
    (CA4_6_6I1R15Raw a).Encloses (CA4_6_6I1R15Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA4_6_6I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R15Certificates_valid :
    CA4_6_6I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R15Certificates (CA4_6_6I1R15CertificateIndex a)).input
lemma CA4_6_6I1R15P_check : ∀ a : PairSlot, contains (CA4_6_6I1R15Raw a) (CA4_6_6I1R15P a) = true := by
  decide +kernel
lemma CA4_6_6I1R15P_sound (a : PairSlot) :
    (CA4_6_6I1R15P a).Encloses (CA4_6_6I1R15Value a) :=
  contains_sound (CA4_6_6I1R15Raw_sound a) (CA4_6_6I1R15P_check a)
def CA4_6_6I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R15Certificates (CA4_6_6I1R15CertificateIndex a)).output
lemma CA4_6_6I1R15Terms_sound (a : PairSlot) :
    (CA4_6_6I1R15Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R15Certificates_valid
    (CA4_6_6I1R15CertificateIndex a) (CA4_6_6I1R15P_sound a)
def CA4_6_6I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R15Entropy_sound : CA4_6_6I1R15Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R15Value CA4_6_6I1R15Terms CA4_6_6I1R15Terms_sound) (by decide +kernel)
def CA4_6_6I1R15Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R15Mass_sound : CA4_6_6I1R15Mass.Encloses (∑ a, CA4_6_6I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R15P CA4_6_6I1R15Value CA4_6_6I1R15P_sound) (by decide +kernel)
def CA4_6_6I1R15MassTerm : Ball := .exact 0
lemma CA4_6_6I1R15MassTerm_sound : CA4_6_6I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R15Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R15Mass_sound)
def CA4_6_6I1R15H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R15H_sound : CA4_6_6I1R15H.Encloses (homogeneousEntropy CA4_6_6I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R15Value CA4_6_6I1R15MassTerm_sound CA4_6_6I1R15Entropy_sound) (by decide +kernel)
def CA4_6_6I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA4_6_6I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 4 6 6)) A4_6_6Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA4_6_6I1R16Raw_sound (a : PairSlot) :
    (CA4_6_6I1R16Raw a).Encloses (CA4_6_6I1R16Value a) := by
  exact residualBall_sound_on (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 4 6 6) (show (shape 4 6 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA4_6_6I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA4_6_6I1R16Certificates_valid :
    CA4_6_6I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA4_6_6I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R16Certificates (CA4_6_6I1R16CertificateIndex a)).input
lemma CA4_6_6I1R16P_check : ∀ a : PairSlot, contains (CA4_6_6I1R16Raw a) (CA4_6_6I1R16P a) = true := by
  decide +kernel
lemma CA4_6_6I1R16P_sound (a : PairSlot) :
    (CA4_6_6I1R16P a).Encloses (CA4_6_6I1R16Value a) :=
  contains_sound (CA4_6_6I1R16Raw_sound a) (CA4_6_6I1R16P_check a)
def CA4_6_6I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I1R16Certificates (CA4_6_6I1R16CertificateIndex a)).output
lemma CA4_6_6I1R16Terms_sound (a : PairSlot) :
    (CA4_6_6I1R16Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I1R16Certificates_valid
    (CA4_6_6I1R16CertificateIndex a) (CA4_6_6I1R16P_sound a)
def CA4_6_6I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R16Entropy_sound : CA4_6_6I1R16Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA4_6_6I1R16Value CA4_6_6I1R16Terms CA4_6_6I1R16Terms_sound) (by decide +kernel)
def CA4_6_6I1R16Mass : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R16Mass_sound : CA4_6_6I1R16Mass.Encloses (∑ a, CA4_6_6I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA4_6_6I1R16P CA4_6_6I1R16Value CA4_6_6I1R16P_sound) (by decide +kernel)
def CA4_6_6I1R16MassTerm : Ball := .exact 0
lemma CA4_6_6I1R16MassTerm_sound : CA4_6_6I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I1R16Value a))) :=
  entropyTerm_zero_ball (CA4_6_6I1R16Mass_sound)
def CA4_6_6I1R16H : Ball := ⟨0, 0⟩
lemma CA4_6_6I1R16H_sound : CA4_6_6I1R16H.Encloses (homogeneousEntropy CA4_6_6I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I1R16Value CA4_6_6I1R16MassTerm_sound CA4_6_6I1R16Entropy_sound) (by decide +kernel)
def CA4_6_6I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA4_6_6I1R0H
  | 1 => CA4_6_6I1R1H
  | 2 => CA4_6_6I1R2H
  | 3 => CA4_6_6I1R3H
  | 4 => CA4_6_6I1R4H
  | 5 => CA4_6_6I1R5H
  | 6 => CA4_6_6I1R6H
  | 7 => CA4_6_6I1R7H
  | 8 => CA4_6_6I1R8H
  | 9 => CA4_6_6I1R9H
  | 10 => CA4_6_6I1R10H
  | 11 => CA4_6_6I1R11H
  | 12 => CA4_6_6I1R12H
  | 13 => CA4_6_6I1R13H
  | 14 => CA4_6_6I1R14H
  | 15 => CA4_6_6I1R15H
  | 16 => CA4_6_6I1R16H
  | _ => (.exact 0)
lemma CA4_6_6I1ResidualEntropies_sound (k : Fin 17) :
    (CA4_6_6I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA4_6_6I1R0H_sound
  · exact CA4_6_6I1R1H_sound
  · exact CA4_6_6I1R2H_sound
  · exact CA4_6_6I1R3H_sound
  · exact CA4_6_6I1R4H_sound
  · exact CA4_6_6I1R5H_sound
  · exact CA4_6_6I1R6H_sound
  · exact CA4_6_6I1R7H_sound
  · exact CA4_6_6I1R8H_sound
  · exact CA4_6_6I1R9H_sound
  · exact CA4_6_6I1R10H_sound
  · exact CA4_6_6I1R11H_sound
  · exact CA4_6_6I1R12H_sound
  · exact CA4_6_6I1R13H_sound
  · exact CA4_6_6I1R14H_sound
  · exact CA4_6_6I1R15H_sound
  · exact CA4_6_6I1R16H_sound
def CA4_6_6I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | 3, 5, 0 => Z3_5_0H1H
  | 4, 4, 0 => Z4_4_0H1H
  | _, _, _ => (.exact 0)
lemma CA4_6_6I1Singles_sound (u : Shape) (hu : u ∈ below (shape 4 6 6))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA4_6_6I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 2 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 3 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 4 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 5 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 0 6 2) by decide +kernel) hd |>.elim
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact Z3_5_0H1H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 0 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 1 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 2 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 4 3 1) by decide +kernel) hd |>.elim
  · exact Z4_4_0H1H_sound
def CA4_6_6I1Singleton : Ball := ⟨(1242243551352522190804190177 / 6250000000000000000000000000000), (16424641 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I1Singleton_sound : CA4_6_6I1Singleton.Encloses
    (singletonEntropy (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA4_6_6I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A4_6_6Law_sound u) CA4_6_6I1Singles_sound) (by decide +kernel)
def CA4_6_6I1Group : Ball := ⟨(10016279990045507878449182831717 / 10000000000000000000000000000000), (41175691719 / 25000000000000000000000000000000)⟩
lemma CA4_6_6I1Group_sound : CA4_6_6I1Group.Encloses
    (groupedEntropy (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA4_6_6I1Singleton_sound
    (finSumBall_sound 17 CA4_6_6I1ResidualEntropies _ CA4_6_6I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA4_6_6I1H : Ball := ⟨(113664929699492447966129481449713 / 100000000000000000000000000000000), (101052621527 / 20000000000000000000000000000000)⟩
lemma CA4_6_6I1_sound : CA4_6_6I1H.Encloses (stageACapacity (shape 4 6 6) 1) := by
  have hb := contains_sound (Ball.add_sound CA4_6_6I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA4_6_6I1Group_sound)))
    (show contains (.add CA4_6_6I1PairH (.neg (.mul (.exact 2) CA4_6_6I1Group))) CA4_6_6I1H = true by decide +kernel)
  unfold CA4_6_6I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
