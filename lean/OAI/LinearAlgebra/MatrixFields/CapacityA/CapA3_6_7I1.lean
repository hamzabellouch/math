import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA3_6_7I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_6_7I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA3_6_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA3_6_7I1R0Raw_sound (a : PairSlot) :
    (CA3_6_7I1R0Raw a).Encloses (CA3_6_7I1R0Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA3_6_7I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15881943617078418930441913137 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(138931155109136038320014250681 / 100000000000000000000000000000000), (47083883 / 100000000000000000000000000000000)⟩ ⟨(-874774262261820556491951653914897 / 100000000000000000000000000000000), (296461550451 / 100000000000000000000000000000000)⟩ ⟨-13, 15881943617078418930441913137, 12207031250000000000000000000⟩]
lemma CA3_6_7I1R0Certificates_valid :
    CA3_6_7I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_6_7I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R0Certificates (CA3_6_7I1R0CertificateIndex a)).input
lemma CA3_6_7I1R0P_check : ∀ a : PairSlot, contains (CA3_6_7I1R0Raw a) (CA3_6_7I1R0P a) = true := by
  decide +kernel
lemma CA3_6_7I1R0P_sound (a : PairSlot) :
    (CA3_6_7I1R0P a).Encloses (CA3_6_7I1R0Value a) :=
  contains_sound (CA3_6_7I1R0Raw_sound a) (CA3_6_7I1R0P_check a)
def CA3_6_7I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R0Certificates (CA3_6_7I1R0CertificateIndex a)).output
lemma CA3_6_7I1R0Terms_sound (a : PairSlot) :
    (CA3_6_7I1R0Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R0Certificates_valid
    (CA3_6_7I1R0CertificateIndex a) (CA3_6_7I1R0P_sound a)
def CA3_6_7I1R0Entropy : Ball := ⟨(138931155109136038320014250681 / 100000000000000000000000000000000), (47083883 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R0Entropy_sound : CA3_6_7I1R0Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R0Value CA3_6_7I1R0Terms CA3_6_7I1R0Terms_sound) (by decide +kernel)
def CA3_6_7I1R0Mass : Ball := ⟨(15881943617078418930441913137 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R0Mass_sound : CA3_6_7I1R0Mass.Encloses (∑ a, CA3_6_7I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R0P CA3_6_7I1R0Value CA3_6_7I1R0P_sound) (by decide +kernel)
def CA3_6_7I1R0MassTermLogWitness : LogWitness := ⟨-13, 15881943617078418930441913137, 12207031250000000000000000000⟩
def CA3_6_7I1R0MassTermLog : Ball := ⟨(-874774262261820556491951653914897 / 100000000000000000000000000000000), (296461550451 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R0MassTermLog_sound : CA3_6_7I1R0MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R0Mass_sound) (w := CA3_6_7I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R0MassTerm : Ball := ⟨(138931155109136038320014250681 / 100000000000000000000000000000000), (47083883 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R0MassTerm_sound : CA3_6_7I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R0Mass_sound) CA3_6_7I1R0MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R0H : Ball := ⟨0, (47083883 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R0H_sound : CA3_6_7I1R0H.Encloses (homogeneousEntropy CA3_6_7I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R0Value CA3_6_7I1R0MassTerm_sound CA3_6_7I1R0Entropy_sound) (by decide +kernel)
def CA3_6_7I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA3_6_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA3_6_7I1R1Raw_sound (a : PairSlot) :
    (CA3_6_7I1R1Raw a).Encloses (CA3_6_7I1R1Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA3_6_7I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(138476711256890786760421812117 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1721537416766707285586801572237 / 50000000000000000000000000000000), (1319561321 / 100000000000000000000000000000000)⟩ ⟨(-124319634770430849342773192542109 / 25000000000000000000000000000000), (190582413869 / 100000000000000000000000000000000)⟩ ⟨-8, 138476711256890786760421812117, 78125000000000000000000000000⟩]
lemma CA3_6_7I1R1Certificates_valid :
    CA3_6_7I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_6_7I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R1Certificates (CA3_6_7I1R1CertificateIndex a)).input
lemma CA3_6_7I1R1P_check : ∀ a : PairSlot, contains (CA3_6_7I1R1Raw a) (CA3_6_7I1R1P a) = true := by
  decide +kernel
lemma CA3_6_7I1R1P_sound (a : PairSlot) :
    (CA3_6_7I1R1P a).Encloses (CA3_6_7I1R1Value a) :=
  contains_sound (CA3_6_7I1R1Raw_sound a) (CA3_6_7I1R1P_check a)
def CA3_6_7I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R1Certificates (CA3_6_7I1R1CertificateIndex a)).output
lemma CA3_6_7I1R1Terms_sound (a : PairSlot) :
    (CA3_6_7I1R1Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R1Certificates_valid
    (CA3_6_7I1R1CertificateIndex a) (CA3_6_7I1R1P_sound a)
def CA3_6_7I1R1Entropy : Ball := ⟨(1721537416766707285586801572237 / 25000000000000000000000000000000), (1319561321 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R1Entropy_sound : CA3_6_7I1R1Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R1Value CA3_6_7I1R1Terms CA3_6_7I1R1Terms_sound) (by decide +kernel)
def CA3_6_7I1R1Mass : Ball := ⟨(138476711256890786760421812117 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I1R1Mass_sound : CA3_6_7I1R1Mass.Encloses (∑ a, CA3_6_7I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R1P CA3_6_7I1R1Value CA3_6_7I1R1P_sound) (by decide +kernel)
def CA3_6_7I1R1MassTermLogWitness : LogWitness := ⟨-7, 138476711256890786760421812117, 78125000000000000000000000000⟩
def CA3_6_7I1R1MassTermLog : Ball := ⟨(-213981910512864433214684788559053 / 50000000000000000000000000000000), (84703295093 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R1MassTermLog_sound : CA3_6_7I1R1MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R1Mass_sound) (w := CA3_6_7I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R1MassTerm : Ball := ⟨(5926302247257554248919325186761 / 100000000000000000000000000000000), (2345886791 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R1MassTerm_sound : CA3_6_7I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R1Mass_sound) CA3_6_7I1R1MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R1H : Ball := ⟨(959847419809274893427881102187 / 100000000000000000000000000000000), (4985009433 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R1H_sound : CA3_6_7I1R1H.Encloses (homogeneousEntropy CA3_6_7I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R1Value CA3_6_7I1R1MassTerm_sound CA3_6_7I1R1Entropy_sound) (by decide +kernel)
def CA3_6_7I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA3_6_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA3_6_7I1R2Raw_sound (a : PairSlot) :
    (CA3_6_7I1R2Raw a).Encloses (CA3_6_7I1R2Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA3_6_7I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1936089788641060189129286819729 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩ ⟨(12589821288125774712078513172711 / 100000000000000000000000000000000), (4919795623 / 100000000000000000000000000000000)⟩ ⟨(-325135263921890724740271087645451 / 100000000000000000000000000000000), (127054942717 / 100000000000000000000000000000000)⟩ ⟨-5, 1936089788641060189129286819729, 1562500000000000000000000000000⟩,
   .log ⟨(333731048993478231219649289233 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1903131355665175153841589552209 / 100000000000000000000000000000000), (353351503 / 50000000000000000000000000000000)⟩ ⟨(-142564750972748577517317797128361 / 25000000000000000000000000000000), (211758237729 / 100000000000000000000000000000000)⟩ ⟨-9, 333731048993478231219649289233, 195312500000000000000000000000⟩,
   .log ⟨(719939496830067873823141073131 / 5000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩ ⟨(2790522948334547780259183485403 / 10000000000000000000000000000000), (3049062413 / 25000000000000000000000000000000)⟩ ⟨(-193802601511749920210944298725863 / 100000000000000000000000000000000), (84703295141 / 100000000000000000000000000000000)⟩ ⟨-3, 719939496830067873823141073131, 625000000000000000000000000000⟩]
lemma CA3_6_7I1R2Certificates_valid :
    CA3_6_7I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_6_7I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R2Certificates (CA3_6_7I1R2CertificateIndex a)).input
lemma CA3_6_7I1R2P_check : ∀ a : PairSlot, contains (CA3_6_7I1R2Raw a) (CA3_6_7I1R2P a) = true := by
  decide +kernel
lemma CA3_6_7I1R2P_sound (a : PairSlot) :
    (CA3_6_7I1R2P a).Encloses (CA3_6_7I1R2Value a) :=
  contains_sound (CA3_6_7I1R2Raw_sound a) (CA3_6_7I1R2P_check a)
def CA3_6_7I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R2Certificates (CA3_6_7I1R2CertificateIndex a)).output
lemma CA3_6_7I1R2Terms_sound (a : PairSlot) :
    (CA3_6_7I1R2Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R2Certificates_valid
    (CA3_6_7I1R2CertificateIndex a) (CA3_6_7I1R2P_sound a)
def CA3_6_7I1R2Entropy : Ball := ⟨(5689113477092737753443204030387 / 10000000000000000000000000000000), (2344924691 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I1R2Entropy_sound : CA3_6_7I1R2Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R2Value CA3_6_7I1R2Terms CA3_6_7I1R2Terms_sound) (by decide +kernel)
def CA3_6_7I1R2Mass : Ball := ⟨(11405305594576277347709633660001 / 50000000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R2Mass_sound : CA3_6_7I1R2Mass.Encloses (∑ a, CA3_6_7I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R2P CA3_6_7I1R2Value CA3_6_7I1R2P_sound) (by decide +kernel)
def CA3_6_7I1R2MassTermLogWitness : LogWitness := ⟨-3, 11405305594576277347709633660001, 6250000000000000000000000000000⟩
def CA3_6_7I1R2MassTermLog : Ball := ⟨(-147794435526109069104234588319341 / 100000000000000000000000000000000), (84703295227 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R2MassTermLog_sound : CA3_6_7I1R2MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R2Mass_sound) (w := CA3_6_7I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R2MassTerm : Ball := ⟨(33712814047063493684397758180661 / 100000000000000000000000000000000), (19321339507 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R2MassTerm_sound : CA3_6_7I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R2Mass_sound) CA3_6_7I1R2MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R2H : Ball := ⟨(23178320723863883850034282123209 / 100000000000000000000000000000000), (42770586417 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R2H_sound : CA3_6_7I1R2H.Encloses (homogeneousEntropy CA3_6_7I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R2Value CA3_6_7I1R2MassTerm_sound CA3_6_7I1R2Entropy_sound) (by decide +kernel)
def CA3_6_7I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA3_6_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA3_6_7I1R3Raw_sound (a : PairSlot) :
    (CA3_6_7I1R3Raw a).Encloses (CA3_6_7I1R3Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA3_6_7I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(714025282738029143876321607229 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(141148720482341921721354289019 / 4000000000000000000000000000000), (1360806639 / 100000000000000000000000000000000)⟩ ⟨(-247100354663016174472392982140359 / 50000000000000000000000000000000), (190582413707 / 100000000000000000000000000000000)⟩ ⟨-8, 714025282738029143876321607229, 390625000000000000000000000000⟩,
   .log ⟨(185451678816837647798748676809 / 800000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩ ⟨(33887060699442188012228079032257 / 100000000000000000000000000000000), (19635460383 / 100000000000000000000000000000000)⟩ ⟨(-73090868555384557148862175438797 / 50000000000000000000000000000000), (84703294943 / 100000000000000000000000000000000)⟩ ⟨-3, 185451678816837647798748676809, 100000000000000000000000000000⟩,
   .log ⟨(946627309909361949663083218669 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(7510300286690600210744680743823 / 100000000000000000000000000000000), (2806385847 / 100000000000000000000000000000000)⟩ ⟨(-396687281682677179831631117519803 / 100000000000000000000000000000000), (29646153209 / 20000000000000000000000000000000)⟩ ⟨-6, 946627309909361949663083218669, 781250000000000000000000000000⟩]
lemma CA3_6_7I1R3Certificates_valid :
    CA3_6_7I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_6_7I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R3Certificates (CA3_6_7I1R3CertificateIndex a)).input
lemma CA3_6_7I1R3P_check : ∀ a : PairSlot, contains (CA3_6_7I1R3Raw a) (CA3_6_7I1R3P a) = true := by
  decide +kernel
lemma CA3_6_7I1R3P_sound (a : PairSlot) :
    (CA3_6_7I1R3P a).Encloses (CA3_6_7I1R3Value a) :=
  contains_sound (CA3_6_7I1R3Raw_sound a) (CA3_6_7I1R3P_check a)
def CA3_6_7I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R3Certificates (CA3_6_7I1R3CertificateIndex a)).output
lemma CA3_6_7I1R3Terms_sound (a : PairSlot) :
    (CA3_6_7I1R3Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R3Certificates_valid
    (CA3_6_7I1R3CertificateIndex a) (CA3_6_7I1R3P_sound a)
def CA3_6_7I1R3Entropy : Ball := ⟨(8985215799638267253201323400311 / 10000000000000000000000000000000), (23802652869 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R3Entropy_sound : CA3_6_7I1R3Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R3Value CA3_6_7I1R3Terms CA3_6_7I1R3Terms_sound) (by decide +kernel)
def CA3_6_7I1R3Mass : Ball := ⟨(6447184938665364754511518161423 / 12500000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
lemma CA3_6_7I1R3Mass_sound : CA3_6_7I1R3Mass.Encloses (∑ a, CA3_6_7I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R3P CA3_6_7I1R3Value CA3_6_7I1R3P_sound) (by decide +kernel)
def CA3_6_7I1R3MassTermLogWitness : LogWitness := ⟨-1, 6447184938665364754511518161423, 6250000000000000000000000000000⟩
def CA3_6_7I1R3MassTermLog : Ball := ⟨(-16552126309689593680616697644509 / 25000000000000000000000000000000), (4235164759 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I1R3MassTermLog_sound : CA3_6_7I1R3MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R3Mass_sound) (w := CA3_6_7I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R3MassTerm : Ball := ⟨(34148678222949591453344708204229 / 100000000000000000000000000000000), (4368782487 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I1R3MassTerm_sound : CA3_6_7I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R3Mass_sound) CA3_6_7I1R3MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R3H : Ball := ⟨(55703479773433081078668525798881 / 100000000000000000000000000000000), (69449218173 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R3H_sound : CA3_6_7I1R3H.Encloses (homogeneousEntropy CA3_6_7I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R3Value CA3_6_7I1R3MassTerm_sound CA3_6_7I1R3Entropy_sound) (by decide +kernel)
def CA3_6_7I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA3_6_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA3_6_7I1R4Raw_sound (a : PairSlot) :
    (CA3_6_7I1R4Raw a).Encloses (CA3_6_7I1R4Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA3_6_7I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(17449206100240973783884489231 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4718718634275632143782608717 / 3125000000000000000000000000000), (25865097 / 50000000000000000000000000000000)⟩ ⟨(-432681565652247440412769657972123 / 50000000000000000000000000000000), (74115384323 / 25000000000000000000000000000000)⟩ ⟨-13, 17449206100240973783884489231, 12207031250000000000000000000⟩,
   .log ⟨(1048473505461301894896392378231 / 50000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(8104045327752314063857938746523 / 100000000000000000000000000000000), (3108320671 / 100000000000000000000000000000000)⟩ ⟨(-386468770338013383674099311727149 / 100000000000000000000000000000000), (148230766353 / 100000000000000000000000000000000)⟩ ⟨-6, 1048473505461301894896392378231, 781250000000000000000000000000⟩,
   .log ⟨(8205414907246693647788954606813 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩ ⟨(2965812287040774310021676538197 / 10000000000000000000000000000000), (13900513723 / 100000000000000000000000000000000)⟩ ⟨(-45180717863844516577247368990531 / 25000000000000000000000000000000), (16940659023 / 20000000000000000000000000000000)⟩ ⟨-3, 8205414907246693647788954606813, 6250000000000000000000000000000⟩,
   .log ⟨(1057609165379279431510471778151 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(4811232601866174416802018871507 / 100000000000000000000000000000000), (358331929 / 20000000000000000000000000000000)⟩ ⟨(-227457966485226697727280208609967 / 50000000000000000000000000000000), (10587911871 / 6250000000000000000000000000000)⟩ ⟨-7, 1057609165379279431510471778151, 781250000000000000000000000000⟩,
   .log ⟨(871415778983109526048063417 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(417815475405063423742098832997 / 100000000000000000000000000000000), (70859321 / 50000000000000000000000000000000)⟩ ⟨(-749167843944980252131526535566319 / 100000000000000000000000000000000), (63527471497 / 25000000000000000000000000000000)⟩ ⟨-11, 871415778983109526048063417, 762939453125000000000000000⟩]
lemma CA3_6_7I1R4Certificates_valid :
    CA3_6_7I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_6_7I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R4Certificates (CA3_6_7I1R4CertificateIndex a)).input
lemma CA3_6_7I1R4P_check : ∀ a : PairSlot, contains (CA3_6_7I1R4Raw a) (CA3_6_7I1R4P a) = true := by
  decide +kernel
lemma CA3_6_7I1R4P_sound (a : PairSlot) :
    (CA3_6_7I1R4P a).Encloses (CA3_6_7I1R4Value a) :=
  contains_sound (CA3_6_7I1R4Raw_sound a) (CA3_6_7I1R4P_check a)
def CA3_6_7I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R4Certificates (CA3_6_7I1R4CertificateIndex a)).output
lemma CA3_6_7I1R4Terms_sound (a : PairSlot) :
    (CA3_6_7I1R4Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R4Certificates_valid
    (CA3_6_7I1R4CertificateIndex a) (CA3_6_7I1R4P_sound a)
def CA3_6_7I1R4Entropy : Ball := ⟨(11241698439528684788496173281783 / 20000000000000000000000000000000), (4789130677 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I1R4Entropy_sound : CA3_6_7I1R4Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R4Value CA3_6_7I1R4Terms CA3_6_7I1R4Terms_sound) (by decide +kernel)
def CA3_6_7I1R4Mass : Ball := ⟨(11405305594576277347709633660001 / 50000000000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
lemma CA3_6_7I1R4Mass_sound : CA3_6_7I1R4Mass.Encloses (∑ a, CA3_6_7I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R4P CA3_6_7I1R4Value CA3_6_7I1R4P_sound) (by decide +kernel)
def CA3_6_7I1R4MassTermLogWitness : LogWitness := ⟨-3, 11405305594576277347709633660001, 6250000000000000000000000000000⟩
def CA3_6_7I1R4MassTermLog : Ball := ⟨(-147794435526109069104234588319341 / 100000000000000000000000000000000), (8470329517 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I1R4MassTermLog_sound : CA3_6_7I1R4MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R4Mass_sound) (w := CA3_6_7I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R4MassTerm : Ball := ⟨(33712814047063493684397758180661 / 100000000000000000000000000000000), (9660669737 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R4MassTerm_sound : CA3_6_7I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R4Mass_sound) CA3_6_7I1R4MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R4H : Ball := ⟨(11247839075289965129041554114127 / 50000000000000000000000000000000), (43266992859 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R4H_sound : CA3_6_7I1R4H.Encloses (homogeneousEntropy CA3_6_7I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R4Value CA3_6_7I1R4MassTerm_sound CA3_6_7I1R4Entropy_sound) (by decide +kernel)
def CA3_6_7I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA3_6_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA3_6_7I1R5Raw_sound (a : PairSlot) :
    (CA3_6_7I1R5Raw a).Encloses (CA3_6_7I1R5Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA3_6_7I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5855664538841071292921855903 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(195795190306519324931963928669 / 100000000000000000000000000000000), (69439181 / 100000000000000000000000000000000)⟩ ⟨(-104490270173326845688227714298293 / 12500000000000000000000000000000), (296461535831 / 100000000000000000000000000000000)⟩ ⟨-13, 5855664538841071292921855903, 3051757812500000000000000000⟩,
   .log ⟨(621791820519049148452018590401 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(315890149744856668311079715781 / 10000000000000000000000000000000), (592512947 / 50000000000000000000000000000000)⟩ ⟨(-508032012195276362745904241780051 / 100000000000000000000000000000000), (190582414111 / 100000000000000000000000000000000)⟩ ⟨-8, 621791820519049148452018590401, 390625000000000000000000000000⟩,
   .log ⟨(2347338985398713592823333543 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(22487245902897101440296024941 / 6250000000000000000000000000000), (16154723 / 12500000000000000000000000000000)⟩ ⟨(-153278217029757001386507162984137 / 20000000000000000000000000000000), (275285710009 / 100000000000000000000000000000000)⟩ ⟨-12, 2347338985398713592823333543, 1220703125000000000000000000⟩]
lemma CA3_6_7I1R5Certificates_valid :
    CA3_6_7I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA3_6_7I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R5Certificates (CA3_6_7I1R5CertificateIndex a)).input
lemma CA3_6_7I1R5P_check : ∀ a : PairSlot, contains (CA3_6_7I1R5Raw a) (CA3_6_7I1R5P a) = true := by
  decide +kernel
lemma CA3_6_7I1R5P_sound (a : PairSlot) :
    (CA3_6_7I1R5P a).Encloses (CA3_6_7I1R5Value a) :=
  contains_sound (CA3_6_7I1R5Raw_sound a) (CA3_6_7I1R5P_check a)
def CA3_6_7I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R5Certificates (CA3_6_7I1R5CertificateIndex a)).output
lemma CA3_6_7I1R5Terms_sound (a : PairSlot) :
    (CA3_6_7I1R5Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R5Certificates_valid
    (CA3_6_7I1R5CertificateIndex a) (CA3_6_7I1R5P_sound a)
def CA3_6_7I1R5Entropy : Ball := ⟨(742898524440287926217499497107 / 10000000000000000000000000000000), (1383702859 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R5Entropy_sound : CA3_6_7I1R5Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R5Value CA3_6_7I1R5Terms CA3_6_7I1R5Terms_sound) (by decide +kernel)
def CA3_6_7I1R5Mass : Ball := ⟨(692161258382387705480172684873 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
lemma CA3_6_7I1R5Mass_sound : CA3_6_7I1R5Mass.Encloses (∑ a, CA3_6_7I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R5P CA3_6_7I1R5Value CA3_6_7I1R5P_sound) (by decide +kernel)
def CA3_6_7I1R5MassTermLogWitness : LogWitness := ⟨-7, 692161258382387705480172684873, 390625000000000000000000000000⟩
def CA3_6_7I1R5MassTermLog : Ball := ⟨(-427995932359594196573051346155393 / 100000000000000000000000000000000), (169406590619 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R5MassTermLog_sound : CA3_6_7I1R5MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R5Mass_sound) (w := CA3_6_7I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R5MassTerm : Ball := ⟨(1184968812498240039997339696673 / 20000000000000000000000000000000), (146570853 / 6250000000000000000000000000000)⟩
lemma CA3_6_7I1R5MassTerm_sound : CA3_6_7I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R5Mass_sound) CA3_6_7I1R5MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R5H : Ball := ⟨(300828236382335812437659297541 / 20000000000000000000000000000000), (2556269683 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R5H_sound : CA3_6_7I1R5H.Encloses (homogeneousEntropy CA3_6_7I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R5Value CA3_6_7I1R5MassTerm_sound CA3_6_7I1R5Entropy_sound) (by decide +kernel)
def CA3_6_7I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA3_6_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA3_6_7I1R6Raw_sound (a : PairSlot) :
    (CA3_6_7I1R6Raw a).Encloses (CA3_6_7I1R6Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA3_6_7I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1202706634504621470994420091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(25582060191803512816614429623 / 100000000000000000000000000000000), (1731847 / 20000000000000000000000000000000)⟩ ⟨(-132940046734362282703330741886437 / 12500000000000000000000000000000), (359989044183 / 100000000000000000000000000000000)⟩ ⟨-16, 1202706634504621470994420091, 762939453125000000000000000⟩,
   .log ⟨(33207121215600932422330309 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(276210161386504860547519753 / 12500000000000000000000000000000), (738363 / 100000000000000000000000000000000)⟩ ⟨(-1330847848415065571539999428640029 / 100000000000000000000000000000000), (444692899623 / 100000000000000000000000000000000)⟩ ⟨-20, 33207121215600932422330309, 19073486328125000000000000⟩,
   .log ⟨(2668391126036809870753132659 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(48805702964877537274965377389 / 50000000000000000000000000000000), (33903249 / 100000000000000000000000000000000)⟩ ⟨(-114314442344715213282645359303173 / 12500000000000000000000000000000), (317637373983 / 100000000000000000000000000000000)⟩ ⟨-14, 2668391126036809870753132659, 1525878906250000000000000000⟩]
lemma CA3_6_7I1R6Certificates_valid :
    CA3_6_7I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA3_6_7I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R6Certificates (CA3_6_7I1R6CertificateIndex a)).input
lemma CA3_6_7I1R6P_check : ∀ a : PairSlot, contains (CA3_6_7I1R6Raw a) (CA3_6_7I1R6P a) = true := by
  decide +kernel
lemma CA3_6_7I1R6P_sound (a : PairSlot) :
    (CA3_6_7I1R6P a).Encloses (CA3_6_7I1R6Value a) :=
  contains_sound (CA3_6_7I1R6Raw_sound a) (CA3_6_7I1R6P_check a)
def CA3_6_7I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R6Certificates (CA3_6_7I1R6CertificateIndex a)).output
lemma CA3_6_7I1R6Terms_sound (a : PairSlot) :
    (CA3_6_7I1R6Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R6Certificates_valid
    (CA3_6_7I1R6CertificateIndex a) (CA3_6_7I1R6P_sound a)
def CA3_6_7I1R6Entropy : Ball := ⟨(19149361111943272243989991259 / 12500000000000000000000000000000), (10539689 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I1R6Entropy_sound : CA3_6_7I1R6Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R6Value CA3_6_7I1R6Terms CA3_6_7I1R6Terms_sound) (by decide +kernel)
def CA3_6_7I1R6Mass : Ball := ⟨(1581646225432173469121351409 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1R6Mass_sound : CA3_6_7I1R6Mass.Encloses (∑ a, CA3_6_7I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R6P CA3_6_7I1R6Value CA3_6_7I1R6P_sound) (by decide +kernel)
def CA3_6_7I1R6MassTermLogWitness : LogWitness := ⟨-13, 1581646225432173469121351409, 1220703125000000000000000000⟩
def CA3_6_7I1R6MassTermLog : Ball := ⟨(-218796853813083489409265359694123 / 25000000000000000000000000000000), (296461569497 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1R6MassTermLog_sound : CA3_6_7I1R6MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I1R6Mass_sound) (w := CA3_6_7I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I1R6MassTerm : Ball := ⟨(138423687187959420791691804753 / 100000000000000000000000000000000), (9377957 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I1R6MassTerm_sound : CA3_6_7I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I1R6Mass_sound) CA3_6_7I1R6MassTermLog_sound) (by decide +kernel)
def CA3_6_7I1R6H : Ball := ⟨(14771201707586757160228125319 / 100000000000000000000000000000000), (9958823 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I1R6H_sound : CA3_6_7I1R6H.Encloses (homogeneousEntropy CA3_6_7I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R6Value CA3_6_7I1R6MassTerm_sound CA3_6_7I1R6Entropy_sound) (by decide +kernel)
def CA3_6_7I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA3_6_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA3_6_7I1R7Raw_sound (a : PairSlot) :
    (CA3_6_7I1R7Raw a).Encloses (CA3_6_7I1R7Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA3_6_7I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R7Certificates_valid :
    CA3_6_7I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R7Certificates (CA3_6_7I1R7CertificateIndex a)).input
lemma CA3_6_7I1R7P_check : ∀ a : PairSlot, contains (CA3_6_7I1R7Raw a) (CA3_6_7I1R7P a) = true := by
  decide +kernel
lemma CA3_6_7I1R7P_sound (a : PairSlot) :
    (CA3_6_7I1R7P a).Encloses (CA3_6_7I1R7Value a) :=
  contains_sound (CA3_6_7I1R7Raw_sound a) (CA3_6_7I1R7P_check a)
def CA3_6_7I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R7Certificates (CA3_6_7I1R7CertificateIndex a)).output
lemma CA3_6_7I1R7Terms_sound (a : PairSlot) :
    (CA3_6_7I1R7Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R7Certificates_valid
    (CA3_6_7I1R7CertificateIndex a) (CA3_6_7I1R7P_sound a)
def CA3_6_7I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R7Entropy_sound : CA3_6_7I1R7Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R7Value CA3_6_7I1R7Terms CA3_6_7I1R7Terms_sound) (by decide +kernel)
def CA3_6_7I1R7Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R7Mass_sound : CA3_6_7I1R7Mass.Encloses (∑ a, CA3_6_7I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R7P CA3_6_7I1R7Value CA3_6_7I1R7P_sound) (by decide +kernel)
def CA3_6_7I1R7MassTerm : Ball := .exact 0
lemma CA3_6_7I1R7MassTerm_sound : CA3_6_7I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R7Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R7Mass_sound)
def CA3_6_7I1R7H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R7H_sound : CA3_6_7I1R7H.Encloses (homogeneousEntropy CA3_6_7I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R7Value CA3_6_7I1R7MassTerm_sound CA3_6_7I1R7Entropy_sound) (by decide +kernel)
def CA3_6_7I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA3_6_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA3_6_7I1R8Raw_sound (a : PairSlot) :
    (CA3_6_7I1R8Raw a).Encloses (CA3_6_7I1R8Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA3_6_7I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R8Certificates_valid :
    CA3_6_7I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R8Certificates (CA3_6_7I1R8CertificateIndex a)).input
lemma CA3_6_7I1R8P_check : ∀ a : PairSlot, contains (CA3_6_7I1R8Raw a) (CA3_6_7I1R8P a) = true := by
  decide +kernel
lemma CA3_6_7I1R8P_sound (a : PairSlot) :
    (CA3_6_7I1R8P a).Encloses (CA3_6_7I1R8Value a) :=
  contains_sound (CA3_6_7I1R8Raw_sound a) (CA3_6_7I1R8P_check a)
def CA3_6_7I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R8Certificates (CA3_6_7I1R8CertificateIndex a)).output
lemma CA3_6_7I1R8Terms_sound (a : PairSlot) :
    (CA3_6_7I1R8Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R8Certificates_valid
    (CA3_6_7I1R8CertificateIndex a) (CA3_6_7I1R8P_sound a)
def CA3_6_7I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R8Entropy_sound : CA3_6_7I1R8Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R8Value CA3_6_7I1R8Terms CA3_6_7I1R8Terms_sound) (by decide +kernel)
def CA3_6_7I1R8Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R8Mass_sound : CA3_6_7I1R8Mass.Encloses (∑ a, CA3_6_7I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R8P CA3_6_7I1R8Value CA3_6_7I1R8P_sound) (by decide +kernel)
def CA3_6_7I1R8MassTerm : Ball := .exact 0
lemma CA3_6_7I1R8MassTerm_sound : CA3_6_7I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R8Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R8Mass_sound)
def CA3_6_7I1R8H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R8H_sound : CA3_6_7I1R8H.Encloses (homogeneousEntropy CA3_6_7I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R8Value CA3_6_7I1R8MassTerm_sound CA3_6_7I1R8Entropy_sound) (by decide +kernel)
def CA3_6_7I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA3_6_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA3_6_7I1R9Raw_sound (a : PairSlot) :
    (CA3_6_7I1R9Raw a).Encloses (CA3_6_7I1R9Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA3_6_7I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R9Certificates_valid :
    CA3_6_7I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R9Certificates (CA3_6_7I1R9CertificateIndex a)).input
lemma CA3_6_7I1R9P_check : ∀ a : PairSlot, contains (CA3_6_7I1R9Raw a) (CA3_6_7I1R9P a) = true := by
  decide +kernel
lemma CA3_6_7I1R9P_sound (a : PairSlot) :
    (CA3_6_7I1R9P a).Encloses (CA3_6_7I1R9Value a) :=
  contains_sound (CA3_6_7I1R9Raw_sound a) (CA3_6_7I1R9P_check a)
def CA3_6_7I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R9Certificates (CA3_6_7I1R9CertificateIndex a)).output
lemma CA3_6_7I1R9Terms_sound (a : PairSlot) :
    (CA3_6_7I1R9Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R9Certificates_valid
    (CA3_6_7I1R9CertificateIndex a) (CA3_6_7I1R9P_sound a)
def CA3_6_7I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R9Entropy_sound : CA3_6_7I1R9Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R9Value CA3_6_7I1R9Terms CA3_6_7I1R9Terms_sound) (by decide +kernel)
def CA3_6_7I1R9Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R9Mass_sound : CA3_6_7I1R9Mass.Encloses (∑ a, CA3_6_7I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R9P CA3_6_7I1R9Value CA3_6_7I1R9P_sound) (by decide +kernel)
def CA3_6_7I1R9MassTerm : Ball := .exact 0
lemma CA3_6_7I1R9MassTerm_sound : CA3_6_7I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R9Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R9Mass_sound)
def CA3_6_7I1R9H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R9H_sound : CA3_6_7I1R9H.Encloses (homogeneousEntropy CA3_6_7I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R9Value CA3_6_7I1R9MassTerm_sound CA3_6_7I1R9Entropy_sound) (by decide +kernel)
def CA3_6_7I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA3_6_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA3_6_7I1R10Raw_sound (a : PairSlot) :
    (CA3_6_7I1R10Raw a).Encloses (CA3_6_7I1R10Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA3_6_7I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R10Certificates_valid :
    CA3_6_7I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R10Certificates (CA3_6_7I1R10CertificateIndex a)).input
lemma CA3_6_7I1R10P_check : ∀ a : PairSlot, contains (CA3_6_7I1R10Raw a) (CA3_6_7I1R10P a) = true := by
  decide +kernel
lemma CA3_6_7I1R10P_sound (a : PairSlot) :
    (CA3_6_7I1R10P a).Encloses (CA3_6_7I1R10Value a) :=
  contains_sound (CA3_6_7I1R10Raw_sound a) (CA3_6_7I1R10P_check a)
def CA3_6_7I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R10Certificates (CA3_6_7I1R10CertificateIndex a)).output
lemma CA3_6_7I1R10Terms_sound (a : PairSlot) :
    (CA3_6_7I1R10Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R10Certificates_valid
    (CA3_6_7I1R10CertificateIndex a) (CA3_6_7I1R10P_sound a)
def CA3_6_7I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R10Entropy_sound : CA3_6_7I1R10Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R10Value CA3_6_7I1R10Terms CA3_6_7I1R10Terms_sound) (by decide +kernel)
def CA3_6_7I1R10Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R10Mass_sound : CA3_6_7I1R10Mass.Encloses (∑ a, CA3_6_7I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R10P CA3_6_7I1R10Value CA3_6_7I1R10P_sound) (by decide +kernel)
def CA3_6_7I1R10MassTerm : Ball := .exact 0
lemma CA3_6_7I1R10MassTerm_sound : CA3_6_7I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R10Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R10Mass_sound)
def CA3_6_7I1R10H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R10H_sound : CA3_6_7I1R10H.Encloses (homogeneousEntropy CA3_6_7I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R10Value CA3_6_7I1R10MassTerm_sound CA3_6_7I1R10Entropy_sound) (by decide +kernel)
def CA3_6_7I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA3_6_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA3_6_7I1R11Raw_sound (a : PairSlot) :
    (CA3_6_7I1R11Raw a).Encloses (CA3_6_7I1R11Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA3_6_7I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R11Certificates_valid :
    CA3_6_7I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R11Certificates (CA3_6_7I1R11CertificateIndex a)).input
lemma CA3_6_7I1R11P_check : ∀ a : PairSlot, contains (CA3_6_7I1R11Raw a) (CA3_6_7I1R11P a) = true := by
  decide +kernel
lemma CA3_6_7I1R11P_sound (a : PairSlot) :
    (CA3_6_7I1R11P a).Encloses (CA3_6_7I1R11Value a) :=
  contains_sound (CA3_6_7I1R11Raw_sound a) (CA3_6_7I1R11P_check a)
def CA3_6_7I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R11Certificates (CA3_6_7I1R11CertificateIndex a)).output
lemma CA3_6_7I1R11Terms_sound (a : PairSlot) :
    (CA3_6_7I1R11Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R11Certificates_valid
    (CA3_6_7I1R11CertificateIndex a) (CA3_6_7I1R11P_sound a)
def CA3_6_7I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R11Entropy_sound : CA3_6_7I1R11Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R11Value CA3_6_7I1R11Terms CA3_6_7I1R11Terms_sound) (by decide +kernel)
def CA3_6_7I1R11Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R11Mass_sound : CA3_6_7I1R11Mass.Encloses (∑ a, CA3_6_7I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R11P CA3_6_7I1R11Value CA3_6_7I1R11P_sound) (by decide +kernel)
def CA3_6_7I1R11MassTerm : Ball := .exact 0
lemma CA3_6_7I1R11MassTerm_sound : CA3_6_7I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R11Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R11Mass_sound)
def CA3_6_7I1R11H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R11H_sound : CA3_6_7I1R11H.Encloses (homogeneousEntropy CA3_6_7I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R11Value CA3_6_7I1R11MassTerm_sound CA3_6_7I1R11Entropy_sound) (by decide +kernel)
def CA3_6_7I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA3_6_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA3_6_7I1R12Raw_sound (a : PairSlot) :
    (CA3_6_7I1R12Raw a).Encloses (CA3_6_7I1R12Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA3_6_7I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R12Certificates_valid :
    CA3_6_7I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R12Certificates (CA3_6_7I1R12CertificateIndex a)).input
lemma CA3_6_7I1R12P_check : ∀ a : PairSlot, contains (CA3_6_7I1R12Raw a) (CA3_6_7I1R12P a) = true := by
  decide +kernel
lemma CA3_6_7I1R12P_sound (a : PairSlot) :
    (CA3_6_7I1R12P a).Encloses (CA3_6_7I1R12Value a) :=
  contains_sound (CA3_6_7I1R12Raw_sound a) (CA3_6_7I1R12P_check a)
def CA3_6_7I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R12Certificates (CA3_6_7I1R12CertificateIndex a)).output
lemma CA3_6_7I1R12Terms_sound (a : PairSlot) :
    (CA3_6_7I1R12Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R12Certificates_valid
    (CA3_6_7I1R12CertificateIndex a) (CA3_6_7I1R12P_sound a)
def CA3_6_7I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R12Entropy_sound : CA3_6_7I1R12Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R12Value CA3_6_7I1R12Terms CA3_6_7I1R12Terms_sound) (by decide +kernel)
def CA3_6_7I1R12Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R12Mass_sound : CA3_6_7I1R12Mass.Encloses (∑ a, CA3_6_7I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R12P CA3_6_7I1R12Value CA3_6_7I1R12P_sound) (by decide +kernel)
def CA3_6_7I1R12MassTerm : Ball := .exact 0
lemma CA3_6_7I1R12MassTerm_sound : CA3_6_7I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R12Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R12Mass_sound)
def CA3_6_7I1R12H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R12H_sound : CA3_6_7I1R12H.Encloses (homogeneousEntropy CA3_6_7I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R12Value CA3_6_7I1R12MassTerm_sound CA3_6_7I1R12Entropy_sound) (by decide +kernel)
def CA3_6_7I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA3_6_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA3_6_7I1R13Raw_sound (a : PairSlot) :
    (CA3_6_7I1R13Raw a).Encloses (CA3_6_7I1R13Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA3_6_7I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R13Certificates_valid :
    CA3_6_7I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R13Certificates (CA3_6_7I1R13CertificateIndex a)).input
lemma CA3_6_7I1R13P_check : ∀ a : PairSlot, contains (CA3_6_7I1R13Raw a) (CA3_6_7I1R13P a) = true := by
  decide +kernel
lemma CA3_6_7I1R13P_sound (a : PairSlot) :
    (CA3_6_7I1R13P a).Encloses (CA3_6_7I1R13Value a) :=
  contains_sound (CA3_6_7I1R13Raw_sound a) (CA3_6_7I1R13P_check a)
def CA3_6_7I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R13Certificates (CA3_6_7I1R13CertificateIndex a)).output
lemma CA3_6_7I1R13Terms_sound (a : PairSlot) :
    (CA3_6_7I1R13Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R13Certificates_valid
    (CA3_6_7I1R13CertificateIndex a) (CA3_6_7I1R13P_sound a)
def CA3_6_7I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R13Entropy_sound : CA3_6_7I1R13Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R13Value CA3_6_7I1R13Terms CA3_6_7I1R13Terms_sound) (by decide +kernel)
def CA3_6_7I1R13Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R13Mass_sound : CA3_6_7I1R13Mass.Encloses (∑ a, CA3_6_7I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R13P CA3_6_7I1R13Value CA3_6_7I1R13P_sound) (by decide +kernel)
def CA3_6_7I1R13MassTerm : Ball := .exact 0
lemma CA3_6_7I1R13MassTerm_sound : CA3_6_7I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R13Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R13Mass_sound)
def CA3_6_7I1R13H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R13H_sound : CA3_6_7I1R13H.Encloses (homogeneousEntropy CA3_6_7I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R13Value CA3_6_7I1R13MassTerm_sound CA3_6_7I1R13Entropy_sound) (by decide +kernel)
def CA3_6_7I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA3_6_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA3_6_7I1R14Raw_sound (a : PairSlot) :
    (CA3_6_7I1R14Raw a).Encloses (CA3_6_7I1R14Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA3_6_7I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R14Certificates_valid :
    CA3_6_7I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R14Certificates (CA3_6_7I1R14CertificateIndex a)).input
lemma CA3_6_7I1R14P_check : ∀ a : PairSlot, contains (CA3_6_7I1R14Raw a) (CA3_6_7I1R14P a) = true := by
  decide +kernel
lemma CA3_6_7I1R14P_sound (a : PairSlot) :
    (CA3_6_7I1R14P a).Encloses (CA3_6_7I1R14Value a) :=
  contains_sound (CA3_6_7I1R14Raw_sound a) (CA3_6_7I1R14P_check a)
def CA3_6_7I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R14Certificates (CA3_6_7I1R14CertificateIndex a)).output
lemma CA3_6_7I1R14Terms_sound (a : PairSlot) :
    (CA3_6_7I1R14Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R14Certificates_valid
    (CA3_6_7I1R14CertificateIndex a) (CA3_6_7I1R14P_sound a)
def CA3_6_7I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R14Entropy_sound : CA3_6_7I1R14Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R14Value CA3_6_7I1R14Terms CA3_6_7I1R14Terms_sound) (by decide +kernel)
def CA3_6_7I1R14Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R14Mass_sound : CA3_6_7I1R14Mass.Encloses (∑ a, CA3_6_7I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R14P CA3_6_7I1R14Value CA3_6_7I1R14P_sound) (by decide +kernel)
def CA3_6_7I1R14MassTerm : Ball := .exact 0
lemma CA3_6_7I1R14MassTerm_sound : CA3_6_7I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R14Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R14Mass_sound)
def CA3_6_7I1R14H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R14H_sound : CA3_6_7I1R14H.Encloses (homogeneousEntropy CA3_6_7I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R14Value CA3_6_7I1R14MassTerm_sound CA3_6_7I1R14Entropy_sound) (by decide +kernel)
def CA3_6_7I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA3_6_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA3_6_7I1R15Raw_sound (a : PairSlot) :
    (CA3_6_7I1R15Raw a).Encloses (CA3_6_7I1R15Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA3_6_7I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R15Certificates_valid :
    CA3_6_7I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R15Certificates (CA3_6_7I1R15CertificateIndex a)).input
lemma CA3_6_7I1R15P_check : ∀ a : PairSlot, contains (CA3_6_7I1R15Raw a) (CA3_6_7I1R15P a) = true := by
  decide +kernel
lemma CA3_6_7I1R15P_sound (a : PairSlot) :
    (CA3_6_7I1R15P a).Encloses (CA3_6_7I1R15Value a) :=
  contains_sound (CA3_6_7I1R15Raw_sound a) (CA3_6_7I1R15P_check a)
def CA3_6_7I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R15Certificates (CA3_6_7I1R15CertificateIndex a)).output
lemma CA3_6_7I1R15Terms_sound (a : PairSlot) :
    (CA3_6_7I1R15Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R15Certificates_valid
    (CA3_6_7I1R15CertificateIndex a) (CA3_6_7I1R15P_sound a)
def CA3_6_7I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R15Entropy_sound : CA3_6_7I1R15Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R15Value CA3_6_7I1R15Terms CA3_6_7I1R15Terms_sound) (by decide +kernel)
def CA3_6_7I1R15Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R15Mass_sound : CA3_6_7I1R15Mass.Encloses (∑ a, CA3_6_7I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R15P CA3_6_7I1R15Value CA3_6_7I1R15P_sound) (by decide +kernel)
def CA3_6_7I1R15MassTerm : Ball := .exact 0
lemma CA3_6_7I1R15MassTerm_sound : CA3_6_7I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R15Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R15Mass_sound)
def CA3_6_7I1R15H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R15H_sound : CA3_6_7I1R15H.Encloses (homogeneousEntropy CA3_6_7I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R15Value CA3_6_7I1R15MassTerm_sound CA3_6_7I1R15Entropy_sound) (by decide +kernel)
def CA3_6_7I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA3_6_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA3_6_7I1R16Raw_sound (a : PairSlot) :
    (CA3_6_7I1R16Raw a).Encloses (CA3_6_7I1R16Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA3_6_7I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I1R16Certificates_valid :
    CA3_6_7I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R16Certificates (CA3_6_7I1R16CertificateIndex a)).input
lemma CA3_6_7I1R16P_check : ∀ a : PairSlot, contains (CA3_6_7I1R16Raw a) (CA3_6_7I1R16P a) = true := by
  decide +kernel
lemma CA3_6_7I1R16P_sound (a : PairSlot) :
    (CA3_6_7I1R16P a).Encloses (CA3_6_7I1R16Value a) :=
  contains_sound (CA3_6_7I1R16Raw_sound a) (CA3_6_7I1R16P_check a)
def CA3_6_7I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I1R16Certificates (CA3_6_7I1R16CertificateIndex a)).output
lemma CA3_6_7I1R16Terms_sound (a : PairSlot) :
    (CA3_6_7I1R16Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I1R16Certificates_valid
    (CA3_6_7I1R16CertificateIndex a) (CA3_6_7I1R16P_sound a)
def CA3_6_7I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R16Entropy_sound : CA3_6_7I1R16Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I1R16Value CA3_6_7I1R16Terms CA3_6_7I1R16Terms_sound) (by decide +kernel)
def CA3_6_7I1R16Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R16Mass_sound : CA3_6_7I1R16Mass.Encloses (∑ a, CA3_6_7I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I1R16P CA3_6_7I1R16Value CA3_6_7I1R16P_sound) (by decide +kernel)
def CA3_6_7I1R16MassTerm : Ball := .exact 0
lemma CA3_6_7I1R16MassTerm_sound : CA3_6_7I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I1R16Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I1R16Mass_sound)
def CA3_6_7I1R16H : Ball := ⟨0, 0⟩
lemma CA3_6_7I1R16H_sound : CA3_6_7I1R16H.Encloses (homogeneousEntropy CA3_6_7I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I1R16Value CA3_6_7I1R16MassTerm_sound CA3_6_7I1R16Entropy_sound) (by decide +kernel)
def CA3_6_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_6_7I1R0H
  | 1 => CA3_6_7I1R1H
  | 2 => CA3_6_7I1R2H
  | 3 => CA3_6_7I1R3H
  | 4 => CA3_6_7I1R4H
  | 5 => CA3_6_7I1R5H
  | 6 => CA3_6_7I1R6H
  | 7 => CA3_6_7I1R7H
  | 8 => CA3_6_7I1R8H
  | 9 => CA3_6_7I1R9H
  | 10 => CA3_6_7I1R10H
  | 11 => CA3_6_7I1R11H
  | 12 => CA3_6_7I1R12H
  | 13 => CA3_6_7I1R13H
  | 14 => CA3_6_7I1R14H
  | 15 => CA3_6_7I1R15H
  | 16 => CA3_6_7I1R16H
  | _ => (.exact 0)
lemma CA3_6_7I1ResidualEntropies_sound (k : Fin 17) :
    (CA3_6_7I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_6_7I1R0H_sound
  · exact CA3_6_7I1R1H_sound
  · exact CA3_6_7I1R2H_sound
  · exact CA3_6_7I1R3H_sound
  · exact CA3_6_7I1R4H_sound
  · exact CA3_6_7I1R5H_sound
  · exact CA3_6_7I1R6H_sound
  · exact CA3_6_7I1R7H_sound
  · exact CA3_6_7I1R8H_sound
  · exact CA3_6_7I1R9H_sound
  · exact CA3_6_7I1R10H_sound
  · exact CA3_6_7I1R11H_sound
  · exact CA3_6_7I1R12H_sound
  · exact CA3_6_7I1R13H_sound
  · exact CA3_6_7I1R14H_sound
  · exact CA3_6_7I1R15H_sound
  · exact CA3_6_7I1R16H_sound
def CA3_6_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 6, 0 => Z2_6_0H1H
  | 3, 5, 0 => Z3_5_0H1H
  | _, _, _ => (.exact 0)
lemma CA3_6_7I1Singles_sound (u : Shape) (hu : u ∈ below (shape 3 6 7))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA3_6_7I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A3_6_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 0 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact Z3_5_0H1H_sound
def CA3_6_7I1Singleton : Ball := ⟨(149742991488449009400997643 / 25000000000000000000000000000000), (237491 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1Singleton_sound : CA3_6_7I1Singleton.Encloses
    (singletonEntropy (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA3_6_7I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A3_6_7Law_sound u) CA3_6_7I1Singles_sound) (by decide +kernel)
def CA3_6_7I1Group : Ball := ⟨(103856837423271389695599925856127 / 100000000000000000000000000000000), (82889288613 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I1Group_sound : CA3_6_7I1Group.Encloses
    (groupedEntropy (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_6_7I1Singleton_sound
    (finSumBall_sound 17 CA3_6_7I1ResidualEntropies _ CA3_6_7I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_6_7I1H : Ball := ⟨(11370342936710396139452809161553 / 10000000000000000000000000000000), (508165588943 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I1_sound : CA3_6_7I1H.Encloses (stageACapacity (shape 3 6 7) 1) := by
  have hb := contains_sound (Ball.add_sound CA3_6_7I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_6_7I1Group_sound)))
    (show contains (.add CA3_6_7I1PairH (.neg (.mul (.exact 2) CA3_6_7I1Group))) CA3_6_7I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
