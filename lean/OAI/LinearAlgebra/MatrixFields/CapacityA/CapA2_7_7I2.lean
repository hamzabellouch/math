import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_7_7I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_7_7I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA2_7_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA2_7_7I2R0Raw_sound (a : PairSlot) :
    (CA2_7_7I2R0Raw a).Encloses (CA2_7_7I2R0Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA2_7_7I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(502109287941468832085436601 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(3063334356907513434862083549 / 50000000000000000000000000000000), (2020217 / 100000000000000000000000000000000)⟩ ⟨(-244037258857845153364503487992193 / 20000000000000000000000000000000), (50292631037 / 12500000000000000000000000000000)⟩ ⟨-18, 502109287941468832085436601, 381469726562500000000000000⟩]
lemma CA2_7_7I2R0Certificates_valid :
    CA2_7_7I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_7_7I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R0Certificates (CA2_7_7I2R0CertificateIndex a)).input
lemma CA2_7_7I2R0P_check : ∀ a : PairSlot, contains (CA2_7_7I2R0Raw a) (CA2_7_7I2R0P a) = true := by
  decide +kernel
lemma CA2_7_7I2R0P_sound (a : PairSlot) :
    (CA2_7_7I2R0P a).Encloses (CA2_7_7I2R0Value a) :=
  contains_sound (CA2_7_7I2R0Raw_sound a) (CA2_7_7I2R0P_check a)
def CA2_7_7I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R0Certificates (CA2_7_7I2R0CertificateIndex a)).output
lemma CA2_7_7I2R0Terms_sound (a : PairSlot) :
    (CA2_7_7I2R0Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R0Certificates_valid
    (CA2_7_7I2R0CertificateIndex a) (CA2_7_7I2R0P_sound a)
def CA2_7_7I2R0Entropy : Ball := ⟨(3063334356907513434862083549 / 50000000000000000000000000000000), (2020217 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R0Entropy_sound : CA2_7_7I2R0Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R0Value CA2_7_7I2R0Terms CA2_7_7I2R0Terms_sound) (by decide +kernel)
def CA2_7_7I2R0Mass : Ball := ⟨(502109287941468832085436601 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R0Mass_sound : CA2_7_7I2R0Mass.Encloses (∑ a, CA2_7_7I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R0P CA2_7_7I2R0Value CA2_7_7I2R0P_sound) (by decide +kernel)
def CA2_7_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 502109287941468832085436601, 381469726562500000000000000⟩
def CA2_7_7I2R0MassTermLog : Ball := ⟨(-244037258857845153364503487992193 / 20000000000000000000000000000000), (50292631037 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I2R0MassTermLog_sound : CA2_7_7I2R0MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R0Mass_sound) (w := CA2_7_7I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R0MassTerm : Ball := ⟨(3063334356907513434862083549 / 50000000000000000000000000000000), (2020217 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R0MassTerm_sound : CA2_7_7I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R0Mass_sound) CA2_7_7I2R0MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R0H : Ball := ⟨0, (2020217 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R0H_sound : CA2_7_7I2R0H.Encloses (homogeneousEntropy CA2_7_7I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R0Value CA2_7_7I2R0MassTerm_sound CA2_7_7I2R0Entropy_sound) (by decide +kernel)
def CA2_7_7I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA2_7_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA2_7_7I2R1Raw_sound (a : PairSlot) :
    (CA2_7_7I2R1Raw a).Encloses (CA2_7_7I2R1Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA2_7_7I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61021004836896843510631497413 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(112914904520571858587520645573 / 25000000000000000000000000000000), (77530211 / 50000000000000000000000000000000)⟩ ⟨(-370085365924020147984039148650649 / 50000000000000000000000000000000), (254109887473 / 100000000000000000000000000000000)⟩ ⟨-11, 61021004836896843510631497413, 48828125000000000000000000000⟩]
lemma CA2_7_7I2R1Certificates_valid :
    CA2_7_7I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_7_7I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R1Certificates (CA2_7_7I2R1CertificateIndex a)).input
lemma CA2_7_7I2R1P_check : ∀ a : PairSlot, contains (CA2_7_7I2R1Raw a) (CA2_7_7I2R1P a) = true := by
  decide +kernel
lemma CA2_7_7I2R1P_sound (a : PairSlot) :
    (CA2_7_7I2R1P a).Encloses (CA2_7_7I2R1Value a) :=
  contains_sound (CA2_7_7I2R1Raw_sound a) (CA2_7_7I2R1P_check a)
def CA2_7_7I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R1Certificates (CA2_7_7I2R1CertificateIndex a)).output
lemma CA2_7_7I2R1Terms_sound (a : PairSlot) :
    (CA2_7_7I2R1Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R1Certificates_valid
    (CA2_7_7I2R1CertificateIndex a) (CA2_7_7I2R1P_sound a)
def CA2_7_7I2R1Entropy : Ball := ⟨(112914904520571858587520645573 / 12500000000000000000000000000000), (77530211 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R1Entropy_sound : CA2_7_7I2R1Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R1Value CA2_7_7I2R1Terms CA2_7_7I2R1Terms_sound) (by decide +kernel)
def CA2_7_7I2R1Mass : Ball := ⟨(61021004836896843510631497413 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R1Mass_sound : CA2_7_7I2R1Mass.Encloses (∑ a, CA2_7_7I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R1P CA2_7_7I2R1Value CA2_7_7I2R1P_sound) (by decide +kernel)
def CA2_7_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 61021004836896843510631497413, 48828125000000000000000000000⟩
def CA2_7_7I2R1MassTermLog : Ball := ⟨(-83857001724005720628294388031371 / 12500000000000000000000000000000), (23293406379 / 10000000000000000000000000000000)⟩
lemma CA2_7_7I2R1MassTermLog_sound : CA2_7_7I2R1MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R1Mass_sound) (w := CA2_7_7I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R1MassTerm : Ball := ⟨(818726161249315203770880901103 / 100000000000000000000000000000000), (888367 / 312500000000000000000000000000)⟩
lemma CA2_7_7I2R1MassTerm_sound : CA2_7_7I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R1Mass_sound) CA2_7_7I2R1MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R1H : Ball := ⟨(84593074915259664929284263481 / 100000000000000000000000000000000), (148599571 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R1H_sound : CA2_7_7I2R1H.Encloses (homogeneousEntropy CA2_7_7I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R1Value CA2_7_7I2R1MassTerm_sound CA2_7_7I2R1Entropy_sound) (by decide +kernel)
def CA2_7_7I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA2_7_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA2_7_7I2R2Raw_sound (a : PairSlot) :
    (CA2_7_7I2R2Raw a).Encloses (CA2_7_7I2R2Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA2_7_7I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(461021550444907393413351550401 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(4321001467844565078070936299133 / 100000000000000000000000000000000), (1562001811 / 100000000000000000000000000000000)⟩ ⟨(-46863334953372529309297799122213 / 10000000000000000000000000000000), (84703295111 / 50000000000000000000000000000000)⟩ ⟨-7, 461021550444907393413351550401, 390625000000000000000000000000⟩,
   .log ⟨(24386991200266839911037879939 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(169064798213358252125773084711 / 25000000000000000000000000000000), (247879037 / 100000000000000000000000000000000)⟩ ⟨(-346629063062745441837771588922581 / 50000000000000000000000000000000), (127054943123 / 50000000000000000000000000000000)⟩ ⟨-11, 24386991200266839911037879939, 12207031250000000000000000000⟩,
   .log ⟨(3483774427281869882558098408561 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(5847609219356964929723995082299 / 50000000000000000000000000000000), (221315383 / 5000000000000000000000000000000)⟩ ⟨(-335705387442057754048834480698173 / 100000000000000000000000000000000), (63527471307 / 50000000000000000000000000000000)⟩ ⟨-5, 3483774427281869882558098408561, 3125000000000000000000000000000⟩]
lemma CA2_7_7I2R2Certificates_valid :
    CA2_7_7I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_7_7I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R2Certificates (CA2_7_7I2R2CertificateIndex a)).input
lemma CA2_7_7I2R2P_check : ∀ a : PairSlot, contains (CA2_7_7I2R2Raw a) (CA2_7_7I2R2P a) = true := by
  decide +kernel
lemma CA2_7_7I2R2P_sound (a : PairSlot) :
    (CA2_7_7I2R2P a).Encloses (CA2_7_7I2R2Value a) :=
  contains_sound (CA2_7_7I2R2Raw_sound a) (CA2_7_7I2R2P_check a)
def CA2_7_7I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R2Certificates (CA2_7_7I2R2CertificateIndex a)).output
lemma CA2_7_7I2R2Terms_sound (a : PairSlot) :
    (CA2_7_7I2R2Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R2Certificates_valid
    (CA2_7_7I2R2CertificateIndex a) (CA2_7_7I2R2P_sound a)
def CA2_7_7I2R2Entropy : Ball := ⟨(2711217470013740754074505930069 / 12500000000000000000000000000000), (2011517339 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R2Entropy_sound : CA2_7_7I2R2Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R2Value CA2_7_7I2R2Terms CA2_7_7I2R2Terms_sound) (by decide +kernel)
def CA2_7_7I2R2Mass : Ball := ⟨(5522956558663634175499807649677 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R2Mass_sound : CA2_7_7I2R2Mass.Encloses (∑ a, CA2_7_7I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R2P CA2_7_7I2R2Value CA2_7_7I2R2P_sound) (by decide +kernel)
def CA2_7_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 5522956558663634175499807649677, 3125000000000000000000000000000⟩
def CA2_7_7I2R2MassTermLog : Ball := ⟨(-1158502744253016410078641519441 / 400000000000000000000000000000), (127054942749 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R2MassTermLog_sound : CA2_7_7I2R2MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R2Mass_sound) (w := CA2_7_7I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R2MassTerm : Ball := ⟨(15995900824005039517055163864603 / 100000000000000000000000000000000), (3508594699 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R2MassTerm_sound : CA2_7_7I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R2Mass_sound) CA2_7_7I2R2MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R2H : Ball := ⟨(5693838936104886515540883575949 / 100000000000000000000000000000000), (7531629377 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R2H_sound : CA2_7_7I2R2H.Encloses (homogeneousEntropy CA2_7_7I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R2Value CA2_7_7I2R2MassTerm_sound CA2_7_7I2R2Entropy_sound) (by decide +kernel)
def CA2_7_7I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA2_7_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA2_7_7I2R3Raw_sound (a : PairSlot) :
    (CA2_7_7I2R3Raw a).Encloses (CA2_7_7I2R3Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA2_7_7I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(131095704406984719407700239349 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(2753378685052309096502096580713 / 100000000000000000000000000000000), (499690727 / 50000000000000000000000000000000)⟩ ⟨(-21002813917567312255242342477773 / 4000000000000000000000000000000), (190582413909 / 100000000000000000000000000000000)⟩ ⟨-8, 131095704406984719407700239349, 97656250000000000000000000000⟩,
   .log ⟨(2270939017850000493846381468481 / 12500000000000000000000000000000), (39 / 100000000000000000000000000000000)⟩ ⟨(30985332075472481453487574065897 / 100000000000000000000000000000000), (7694240731 / 50000000000000000000000000000000)⟩ ⟨(-170553523409931108265824846279181 / 100000000000000000000000000000000), (42351647473 / 50000000000000000000000000000000)⟩ ⟨-3, 2270939017850000493846381468481, 1562500000000000000000000000000⟩,
   .log ⟨(1354896351343567252040316827981 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1165602488999341910841382973429 / 20000000000000000000000000000000), (573820929 / 25000000000000000000000000000000)⟩ ⟨(-107536130701389604624485476198019 / 25000000000000000000000000000000), (33881317937 / 20000000000000000000000000000000)⟩ ⟨-7, 1354896351343567252040316827981, 781250000000000000000000000000⟩]
lemma CA2_7_7I2R3Certificates_valid :
    CA2_7_7I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_7_7I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R3Certificates (CA2_7_7I2R3CertificateIndex a)).input
lemma CA2_7_7I2R3P_check : ∀ a : PairSlot, contains (CA2_7_7I2R3Raw a) (CA2_7_7I2R3P a) = true := by
  decide +kernel
lemma CA2_7_7I2R3P_sound (a : PairSlot) :
    (CA2_7_7I2R3P a).Encloses (CA2_7_7I2R3Value a) :=
  contains_sound (CA2_7_7I2R3Raw_sound a) (CA2_7_7I2R3P_check a)
def CA2_7_7I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R3Certificates (CA2_7_7I2R3CertificateIndex a)).output
lemma CA2_7_7I2R3Terms_sound (a : PairSlot) :
    (CA2_7_7I2R3Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R3Certificates_valid
    (CA2_7_7I2R3CertificateIndex a) (CA2_7_7I2R3P_sound a)
def CA2_7_7I2R3Entropy : Ball := ⟨(7913344641104300020839317102751 / 10000000000000000000000000000000), (2335393329 / 6250000000000000000000000000000)⟩
lemma CA2_7_7I2R3Entropy_sound : CA2_7_7I2R3Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R3Value CA2_7_7I2R3Terms CA2_7_7I2R3Terms_sound) (by decide +kernel)
def CA2_7_7I2R3Mass : Ball := ⟨(801871652470860403217686781329 / 2000000000000000000000000000000), (23 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I2R3Mass_sound : CA2_7_7I2R3Mass.Encloses (∑ a, CA2_7_7I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R3P CA2_7_7I2R3Value CA2_7_7I2R3P_sound) (by decide +kernel)
def CA2_7_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 801871652470860403217686781329, 500000000000000000000000000000⟩
def CA2_7_7I2R3MassTermLog : Ball := ⟨(-18279077976160747981294955766949 / 20000000000000000000000000000000), (31763735639 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R3MassTermLog_sound : CA2_7_7I2R3MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R3Mass_sound) (w := CA2_7_7I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R3MassTerm : Ball := ⟨(36643686155969324069048097794141 / 100000000000000000000000000000000), (2547043927 / 10000000000000000000000000000000)⟩
lemma CA2_7_7I2R3MassTerm_sound : CA2_7_7I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R3Mass_sound) CA2_7_7I2R3MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R3H : Ball := ⟨(42489760255073676139345073233369 / 100000000000000000000000000000000), (31418366267 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R3H_sound : CA2_7_7I2R3H.Encloses (homogeneousEntropy CA2_7_7I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R3Value CA2_7_7I2R3MassTerm_sound CA2_7_7I2R3Entropy_sound) (by decide +kernel)
def CA2_7_7I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA2_7_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA2_7_7I2R4Raw_sound (a : PairSlot) :
    (CA2_7_7I2R4Raw a).Encloses (CA2_7_7I2R4Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA2_7_7I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5277967175821923079897539329 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(25992363903925895922513432917 / 50000000000000000000000000000000), (894123 / 5000000000000000000000000000000)⟩ ⟨(-246234611149113273170862319465459 / 25000000000000000000000000000000), (169406598937 / 50000000000000000000000000000000)⟩ ⟨-15, 5277967175821923079897539329, 3051757812500000000000000000⟩,
   .log ⟨(2038260987631875115742940545529 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(7935099222952918042652310790589 / 100000000000000000000000000000000), (302132991 / 10000000000000000000000000000000)⟩ ⟨(-389307319872329085824439203688361 / 100000000000000000000000000000000), (148230766173 / 100000000000000000000000000000000)⟩ ⟨-6, 2038260987631875115742940545529, 1562500000000000000000000000000⟩,
   .log ⟨(10796235779384559959949417266089 / 50000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩ ⟨(33097490387073889598235127180257 / 100000000000000000000000000000000), (18289534931 / 100000000000000000000000000000000)⟩ ⟨(-76641273549883082343996926940597 / 50000000000000000000000000000000), (42351647463 / 50000000000000000000000000000000)⟩ ⟨-3, 10796235779384559959949417266089, 6250000000000000000000000000000⟩,
   .log ⟨(108499099170855725901779589871 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(613507953043183359593479737449 / 12500000000000000000000000000000), (459511563 / 25000000000000000000000000000000)⟩ ⟨(-226179925080144666452584544784981 / 50000000000000000000000000000000), (8470329487 / 5000000000000000000000000000000)⟩ ⟨-7, 108499099170855725901779589871, 78125000000000000000000000000⟩,
   .log ⟨(15492620375214302470057270997 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(135909967504824284589811746589 / 100000000000000000000000000000000), (4592967 / 10000000000000000000000000000000)⟩ ⟨(-438628082962189999951851555532183 / 50000000000000000000000000000000), (9264423063 / 3125000000000000000000000000000)⟩ ⟨-13, 15492620375214302470057270997, 12207031250000000000000000000⟩]
lemma CA2_7_7I2R4Certificates_valid :
    CA2_7_7I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_7_7I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R4Certificates (CA2_7_7I2R4CertificateIndex a)).input
lemma CA2_7_7I2R4P_check : ∀ a : PairSlot, contains (CA2_7_7I2R4Raw a) (CA2_7_7I2R4P a) = true := by
  decide +kernel
lemma CA2_7_7I2R4P_sound (a : PairSlot) :
    (CA2_7_7I2R4P a).Encloses (CA2_7_7I2R4Value a) :=
  contains_sound (CA2_7_7I2R4Raw_sound a) (CA2_7_7I2R4P_check a)
def CA2_7_7I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R4Certificates (CA2_7_7I2R4CertificateIndex a)).output
lemma CA2_7_7I2R4Terms_sound (a : PairSlot) :
    (CA2_7_7I2R4Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R4Certificates_valid
    (CA2_7_7I2R4CertificateIndex a) (CA2_7_7I2R4P_sound a)
def CA2_7_7I2R4Entropy : Ball := ⟨(14755923876197796826328822509719 / 25000000000000000000000000000000), (5617996369 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I2R4Entropy_sound : CA2_7_7I2R4Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R4Value CA2_7_7I2R4Terms CA2_7_7I2R4Terms_sound) (by decide +kernel)
def CA2_7_7I2R4Mass : Ball := ⟨(27865024072176842818050159770311 / 100000000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R4Mass_sound : CA2_7_7I2R4Mass.Encloses (∑ a, CA2_7_7I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R4P CA2_7_7I2R4Value CA2_7_7I2R4P_sound) (by decide +kernel)
def CA2_7_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 27865024072176842818050159770311, 25000000000000000000000000000000⟩
def CA2_7_7I2R4MassTermLog : Ball := ⟨(-25555958021623995984140828497229 / 20000000000000000000000000000000), (63527471289 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R4MassTermLog_sound : CA2_7_7I2R4MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R4Mass_sound) (w := CA2_7_7I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R4MassTerm : Ball := ⟨(178029346365023383066357772421 / 500000000000000000000000000000), (8850972627 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R4MassTerm_sound : CA2_7_7I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R4Mass_sound) CA2_7_7I2R4MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R4H : Ball := ⟨(5854456557946627673010933888669 / 25000000000000000000000000000000), (45791927099 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R4H_sound : CA2_7_7I2R4H.Encloses (homogeneousEntropy CA2_7_7I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R4Value CA2_7_7I2R4MassTerm_sound CA2_7_7I2R4Entropy_sound) (by decide +kernel)
def CA2_7_7I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA2_7_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA2_7_7I2R5Raw_sound (a : PairSlot) :
    (CA2_7_7I2R5Raw a).Encloses (CA2_7_7I2R5Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA2_7_7I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(147261181015888131340596841 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3342543549552779568172383377 / 25000000000000000000000000000000), (1122619 / 25000000000000000000000000000000)⟩ ⟨(-283725786260683812153665541671581 / 25000000000000000000000000000000), (381164911177 / 100000000000000000000000000000000)⟩ ⟨-17, 147261181015888131340596841, 95367431640625000000000000⟩,
   .log ⟨(192105488604869140798984184437 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(3741128725067483292783869146183 / 100000000000000000000000000000000), (732238567 / 50000000000000000000000000000000)⟩ ⟨(-97371729257626738127061474219161 / 20000000000000000000000000000000), (95291206899 / 50000000000000000000000000000000)⟩ ⟨-8, 192105488604869140798984184437, 97656250000000000000000000000⟩,
   .log ⟨(28426185916905566073339232999 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(58029320434616063406177313117 / 25000000000000000000000000000000), (78253237 / 100000000000000000000000000000000)⟩ ⟨(-816561470529255613905471137791119 / 100000000000000000000000000000000), (68821427849 / 25000000000000000000000000000000)⟩ ⟨-12, 28426185916905566073339232999, 24414062500000000000000000000⟩]
lemma CA2_7_7I2R5Certificates_valid :
    CA2_7_7I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA2_7_7I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R5Certificates (CA2_7_7I2R5CertificateIndex a)).input
lemma CA2_7_7I2R5P_check : ∀ a : PairSlot, contains (CA2_7_7I2R5Raw a) (CA2_7_7I2R5P a) = true := by
  decide +kernel
lemma CA2_7_7I2R5P_sound (a : PairSlot) :
    (CA2_7_7I2R5P a).Encloses (CA2_7_7I2R5Value a) :=
  contains_sound (CA2_7_7I2R5Raw_sound a) (CA2_7_7I2R5P_check a)
def CA2_7_7I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R5Certificates (CA2_7_7I2R5CertificateIndex a)).output
lemma CA2_7_7I2R5Terms_sound (a : PairSlot) :
    (CA2_7_7I2R5Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R5Certificates_valid
    (CA2_7_7I2R5CertificateIndex a) (CA2_7_7I2R5P_sound a)
def CA2_7_7I2R5Entropy : Ball := ⟨(3986616181004158664681267932159 / 50000000000000000000000000000000), (1547220847 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R5Entropy_sound : CA2_7_7I2R5Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R5Value CA2_7_7I2R5Terms CA2_7_7I2R5Terms_sound) (by decide +kernel)
def CA2_7_7I2R5Mass : Ball := ⟨(31921049191380369372800029819 / 2000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R5Mass_sound : CA2_7_7I2R5Mass.Encloses (∑ a, CA2_7_7I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R5P CA2_7_7I2R5Value CA2_7_7I2R5P_sound) (by decide +kernel)
def CA2_7_7I2R5MassTermLogWitness : LogWitness := ⟨-6, 31921049191380369372800029819, 31250000000000000000000000000⟩
def CA2_7_7I2R5MassTermLog : Ball := ⟨(-413763681809651446200549432929053 / 100000000000000000000000000000000), (148230766657 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R5MassTermLog_sound : CA2_7_7I2R5MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R5Mass_sound) (w := CA2_7_7I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R5MassTerm : Ball := ⟨(1650971355081567343108674590919 / 25000000000000000000000000000000), (295730107 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I2R5MassTerm_sound : CA2_7_7I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R5Mass_sound) CA2_7_7I2R5MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R5H : Ball := ⟨(684673470841023978463918750321 / 50000000000000000000000000000000), (109205651 / 2000000000000000000000000000000)⟩
lemma CA2_7_7I2R5H_sound : CA2_7_7I2R5H.Encloses (homogeneousEntropy CA2_7_7I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R5Value CA2_7_7I2R5MassTerm_sound CA2_7_7I2R5Entropy_sound) (by decide +kernel)
def CA2_7_7I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA2_7_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA2_7_7I2R6Raw_sound (a : PairSlot) :
    (CA2_7_7I2R6Raw a).Encloses (CA2_7_7I2R6Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA2_7_7I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(158644053613467679879438893 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(529633875297408340945825551 / 25000000000000000000000000000000), (705493 / 100000000000000000000000000000000)⟩ ⟨(-1335401770778873824862002345811629 / 100000000000000000000000000000000), (111173231921 / 25000000000000000000000000000000)⟩ ⟨-20, 158644053613467679879438893, 95367431640625000000000000⟩,
   .log ⟨(2498801268892056157639 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4603057917178023187341 / 2000000000000000000000000000000), (99 / 100000000000000000000000000000000)⟩ ⟨(-2302633053737689631189372509690703 / 100000000000000000000000000000000), (751158626129 / 100000000000000000000000000000000)⟩ ⟨-34, 39980820302272898522224, 23283064365386962890625⟩,
   .log ⟨(2079393777372476244711147537 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(2894984425979975586826580021 / 2000000000000000000000000000000), (49316841 / 100000000000000000000000000000000)⟩ ⟨(-870140752524420958626435392655381 / 100000000000000000000000000000000), (9264423237 / 3125000000000000000000000000000)⟩ ⟨-13, 2079393777372476244711147537, 1525878906250000000000000000⟩]
lemma CA2_7_7I2R6Certificates_valid :
    CA2_7_7I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA2_7_7I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R6Certificates (CA2_7_7I2R6CertificateIndex a)).input
lemma CA2_7_7I2R6P_check : ∀ a : PairSlot, contains (CA2_7_7I2R6Raw a) (CA2_7_7I2R6P a) = true := by
  decide +kernel
lemma CA2_7_7I2R6P_sound (a : PairSlot) :
    (CA2_7_7I2R6P a).Encloses (CA2_7_7I2R6Value a) :=
  contains_sound (CA2_7_7I2R6Raw_sound a) (CA2_7_7I2R6P_check a)
def CA2_7_7I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R6Certificates (CA2_7_7I2R6CertificateIndex a)).output
lemma CA2_7_7I2R6Terms_sound (a : PairSlot) :
    (CA2_7_7I2R6Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R6Certificates_valid
    (CA2_7_7I2R6CertificateIndex a) (CA2_7_7I2R6P_sound a)
def CA2_7_7I2R6Entropy : Ball := ⟨(74493376303584881935607169779 / 50000000000000000000000000000000), (2029121 / 4000000000000000000000000000000)⟩
lemma CA2_7_7I2R6Entropy_sound : CA2_7_7I2R6Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R6Value CA2_7_7I2R6Terms CA2_7_7I2R6Terms_sound) (by decide +kernel)
def CA2_7_7I2R6Mass : Ball := ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R6Mass_sound : CA2_7_7I2R6Mass.Encloses (∑ a, CA2_7_7I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R6P CA2_7_7I2R6Value CA2_7_7I2R6P_sound) (by decide +kernel)
def CA2_7_7I2R6MassTermLogWitness : LogWitness := ⟨-13, 8476229158308448226948659597, 6103515625000000000000000000⟩
def CA2_7_7I2R6MassTermLog : Ball := ⟨(-108531407602892182777984611149741 / 12500000000000000000000000000000), (148230783477 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I2R6MassTermLog_sound : CA2_7_7I2R6MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I2R6Mass_sound) (w := CA2_7_7I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I2R6MassTerm : Ball := ⟨(18398741634317878500727459383 / 12500000000000000000000000000000), (6282197 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I2R6MassTerm_sound : CA2_7_7I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I2R6Mass_sound) CA2_7_7I2R6MassTermLog_sound) (by decide +kernel)
def CA2_7_7I2R6H : Ball := ⟨(898409766313367932697332247 / 50000000000000000000000000000000), (100985601 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2R6H_sound : CA2_7_7I2R6H.Encloses (homogeneousEntropy CA2_7_7I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R6Value CA2_7_7I2R6MassTerm_sound CA2_7_7I2R6Entropy_sound) (by decide +kernel)
def CA2_7_7I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA2_7_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA2_7_7I2R7Raw_sound (a : PairSlot) :
    (CA2_7_7I2R7Raw a).Encloses (CA2_7_7I2R7Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA2_7_7I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R7Certificates_valid :
    CA2_7_7I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R7Certificates (CA2_7_7I2R7CertificateIndex a)).input
lemma CA2_7_7I2R7P_check : ∀ a : PairSlot, contains (CA2_7_7I2R7Raw a) (CA2_7_7I2R7P a) = true := by
  decide +kernel
lemma CA2_7_7I2R7P_sound (a : PairSlot) :
    (CA2_7_7I2R7P a).Encloses (CA2_7_7I2R7Value a) :=
  contains_sound (CA2_7_7I2R7Raw_sound a) (CA2_7_7I2R7P_check a)
def CA2_7_7I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R7Certificates (CA2_7_7I2R7CertificateIndex a)).output
lemma CA2_7_7I2R7Terms_sound (a : PairSlot) :
    (CA2_7_7I2R7Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R7Certificates_valid
    (CA2_7_7I2R7CertificateIndex a) (CA2_7_7I2R7P_sound a)
def CA2_7_7I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R7Entropy_sound : CA2_7_7I2R7Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R7Value CA2_7_7I2R7Terms CA2_7_7I2R7Terms_sound) (by decide +kernel)
def CA2_7_7I2R7Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R7Mass_sound : CA2_7_7I2R7Mass.Encloses (∑ a, CA2_7_7I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R7P CA2_7_7I2R7Value CA2_7_7I2R7P_sound) (by decide +kernel)
def CA2_7_7I2R7MassTerm : Ball := .exact 0
lemma CA2_7_7I2R7MassTerm_sound : CA2_7_7I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R7Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R7Mass_sound)
def CA2_7_7I2R7H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R7H_sound : CA2_7_7I2R7H.Encloses (homogeneousEntropy CA2_7_7I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R7Value CA2_7_7I2R7MassTerm_sound CA2_7_7I2R7Entropy_sound) (by decide +kernel)
def CA2_7_7I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA2_7_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA2_7_7I2R8Raw_sound (a : PairSlot) :
    (CA2_7_7I2R8Raw a).Encloses (CA2_7_7I2R8Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA2_7_7I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R8Certificates_valid :
    CA2_7_7I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R8Certificates (CA2_7_7I2R8CertificateIndex a)).input
lemma CA2_7_7I2R8P_check : ∀ a : PairSlot, contains (CA2_7_7I2R8Raw a) (CA2_7_7I2R8P a) = true := by
  decide +kernel
lemma CA2_7_7I2R8P_sound (a : PairSlot) :
    (CA2_7_7I2R8P a).Encloses (CA2_7_7I2R8Value a) :=
  contains_sound (CA2_7_7I2R8Raw_sound a) (CA2_7_7I2R8P_check a)
def CA2_7_7I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R8Certificates (CA2_7_7I2R8CertificateIndex a)).output
lemma CA2_7_7I2R8Terms_sound (a : PairSlot) :
    (CA2_7_7I2R8Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R8Certificates_valid
    (CA2_7_7I2R8CertificateIndex a) (CA2_7_7I2R8P_sound a)
def CA2_7_7I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R8Entropy_sound : CA2_7_7I2R8Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R8Value CA2_7_7I2R8Terms CA2_7_7I2R8Terms_sound) (by decide +kernel)
def CA2_7_7I2R8Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R8Mass_sound : CA2_7_7I2R8Mass.Encloses (∑ a, CA2_7_7I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R8P CA2_7_7I2R8Value CA2_7_7I2R8P_sound) (by decide +kernel)
def CA2_7_7I2R8MassTerm : Ball := .exact 0
lemma CA2_7_7I2R8MassTerm_sound : CA2_7_7I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R8Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R8Mass_sound)
def CA2_7_7I2R8H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R8H_sound : CA2_7_7I2R8H.Encloses (homogeneousEntropy CA2_7_7I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R8Value CA2_7_7I2R8MassTerm_sound CA2_7_7I2R8Entropy_sound) (by decide +kernel)
def CA2_7_7I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA2_7_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA2_7_7I2R9Raw_sound (a : PairSlot) :
    (CA2_7_7I2R9Raw a).Encloses (CA2_7_7I2R9Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA2_7_7I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R9Certificates_valid :
    CA2_7_7I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R9Certificates (CA2_7_7I2R9CertificateIndex a)).input
lemma CA2_7_7I2R9P_check : ∀ a : PairSlot, contains (CA2_7_7I2R9Raw a) (CA2_7_7I2R9P a) = true := by
  decide +kernel
lemma CA2_7_7I2R9P_sound (a : PairSlot) :
    (CA2_7_7I2R9P a).Encloses (CA2_7_7I2R9Value a) :=
  contains_sound (CA2_7_7I2R9Raw_sound a) (CA2_7_7I2R9P_check a)
def CA2_7_7I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R9Certificates (CA2_7_7I2R9CertificateIndex a)).output
lemma CA2_7_7I2R9Terms_sound (a : PairSlot) :
    (CA2_7_7I2R9Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R9Certificates_valid
    (CA2_7_7I2R9CertificateIndex a) (CA2_7_7I2R9P_sound a)
def CA2_7_7I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R9Entropy_sound : CA2_7_7I2R9Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R9Value CA2_7_7I2R9Terms CA2_7_7I2R9Terms_sound) (by decide +kernel)
def CA2_7_7I2R9Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R9Mass_sound : CA2_7_7I2R9Mass.Encloses (∑ a, CA2_7_7I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R9P CA2_7_7I2R9Value CA2_7_7I2R9P_sound) (by decide +kernel)
def CA2_7_7I2R9MassTerm : Ball := .exact 0
lemma CA2_7_7I2R9MassTerm_sound : CA2_7_7I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R9Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R9Mass_sound)
def CA2_7_7I2R9H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R9H_sound : CA2_7_7I2R9H.Encloses (homogeneousEntropy CA2_7_7I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R9Value CA2_7_7I2R9MassTerm_sound CA2_7_7I2R9Entropy_sound) (by decide +kernel)
def CA2_7_7I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA2_7_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA2_7_7I2R10Raw_sound (a : PairSlot) :
    (CA2_7_7I2R10Raw a).Encloses (CA2_7_7I2R10Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA2_7_7I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R10Certificates_valid :
    CA2_7_7I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R10Certificates (CA2_7_7I2R10CertificateIndex a)).input
lemma CA2_7_7I2R10P_check : ∀ a : PairSlot, contains (CA2_7_7I2R10Raw a) (CA2_7_7I2R10P a) = true := by
  decide +kernel
lemma CA2_7_7I2R10P_sound (a : PairSlot) :
    (CA2_7_7I2R10P a).Encloses (CA2_7_7I2R10Value a) :=
  contains_sound (CA2_7_7I2R10Raw_sound a) (CA2_7_7I2R10P_check a)
def CA2_7_7I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R10Certificates (CA2_7_7I2R10CertificateIndex a)).output
lemma CA2_7_7I2R10Terms_sound (a : PairSlot) :
    (CA2_7_7I2R10Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R10Certificates_valid
    (CA2_7_7I2R10CertificateIndex a) (CA2_7_7I2R10P_sound a)
def CA2_7_7I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R10Entropy_sound : CA2_7_7I2R10Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R10Value CA2_7_7I2R10Terms CA2_7_7I2R10Terms_sound) (by decide +kernel)
def CA2_7_7I2R10Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R10Mass_sound : CA2_7_7I2R10Mass.Encloses (∑ a, CA2_7_7I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R10P CA2_7_7I2R10Value CA2_7_7I2R10P_sound) (by decide +kernel)
def CA2_7_7I2R10MassTerm : Ball := .exact 0
lemma CA2_7_7I2R10MassTerm_sound : CA2_7_7I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R10Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R10Mass_sound)
def CA2_7_7I2R10H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R10H_sound : CA2_7_7I2R10H.Encloses (homogeneousEntropy CA2_7_7I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R10Value CA2_7_7I2R10MassTerm_sound CA2_7_7I2R10Entropy_sound) (by decide +kernel)
def CA2_7_7I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA2_7_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA2_7_7I2R11Raw_sound (a : PairSlot) :
    (CA2_7_7I2R11Raw a).Encloses (CA2_7_7I2R11Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA2_7_7I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R11Certificates_valid :
    CA2_7_7I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R11Certificates (CA2_7_7I2R11CertificateIndex a)).input
lemma CA2_7_7I2R11P_check : ∀ a : PairSlot, contains (CA2_7_7I2R11Raw a) (CA2_7_7I2R11P a) = true := by
  decide +kernel
lemma CA2_7_7I2R11P_sound (a : PairSlot) :
    (CA2_7_7I2R11P a).Encloses (CA2_7_7I2R11Value a) :=
  contains_sound (CA2_7_7I2R11Raw_sound a) (CA2_7_7I2R11P_check a)
def CA2_7_7I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R11Certificates (CA2_7_7I2R11CertificateIndex a)).output
lemma CA2_7_7I2R11Terms_sound (a : PairSlot) :
    (CA2_7_7I2R11Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R11Certificates_valid
    (CA2_7_7I2R11CertificateIndex a) (CA2_7_7I2R11P_sound a)
def CA2_7_7I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R11Entropy_sound : CA2_7_7I2R11Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R11Value CA2_7_7I2R11Terms CA2_7_7I2R11Terms_sound) (by decide +kernel)
def CA2_7_7I2R11Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R11Mass_sound : CA2_7_7I2R11Mass.Encloses (∑ a, CA2_7_7I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R11P CA2_7_7I2R11Value CA2_7_7I2R11P_sound) (by decide +kernel)
def CA2_7_7I2R11MassTerm : Ball := .exact 0
lemma CA2_7_7I2R11MassTerm_sound : CA2_7_7I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R11Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R11Mass_sound)
def CA2_7_7I2R11H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R11H_sound : CA2_7_7I2R11H.Encloses (homogeneousEntropy CA2_7_7I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R11Value CA2_7_7I2R11MassTerm_sound CA2_7_7I2R11Entropy_sound) (by decide +kernel)
def CA2_7_7I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA2_7_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA2_7_7I2R12Raw_sound (a : PairSlot) :
    (CA2_7_7I2R12Raw a).Encloses (CA2_7_7I2R12Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA2_7_7I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R12Certificates_valid :
    CA2_7_7I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R12Certificates (CA2_7_7I2R12CertificateIndex a)).input
lemma CA2_7_7I2R12P_check : ∀ a : PairSlot, contains (CA2_7_7I2R12Raw a) (CA2_7_7I2R12P a) = true := by
  decide +kernel
lemma CA2_7_7I2R12P_sound (a : PairSlot) :
    (CA2_7_7I2R12P a).Encloses (CA2_7_7I2R12Value a) :=
  contains_sound (CA2_7_7I2R12Raw_sound a) (CA2_7_7I2R12P_check a)
def CA2_7_7I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R12Certificates (CA2_7_7I2R12CertificateIndex a)).output
lemma CA2_7_7I2R12Terms_sound (a : PairSlot) :
    (CA2_7_7I2R12Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R12Certificates_valid
    (CA2_7_7I2R12CertificateIndex a) (CA2_7_7I2R12P_sound a)
def CA2_7_7I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R12Entropy_sound : CA2_7_7I2R12Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R12Value CA2_7_7I2R12Terms CA2_7_7I2R12Terms_sound) (by decide +kernel)
def CA2_7_7I2R12Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R12Mass_sound : CA2_7_7I2R12Mass.Encloses (∑ a, CA2_7_7I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R12P CA2_7_7I2R12Value CA2_7_7I2R12P_sound) (by decide +kernel)
def CA2_7_7I2R12MassTerm : Ball := .exact 0
lemma CA2_7_7I2R12MassTerm_sound : CA2_7_7I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R12Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R12Mass_sound)
def CA2_7_7I2R12H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R12H_sound : CA2_7_7I2R12H.Encloses (homogeneousEntropy CA2_7_7I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R12Value CA2_7_7I2R12MassTerm_sound CA2_7_7I2R12Entropy_sound) (by decide +kernel)
def CA2_7_7I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA2_7_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA2_7_7I2R13Raw_sound (a : PairSlot) :
    (CA2_7_7I2R13Raw a).Encloses (CA2_7_7I2R13Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA2_7_7I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R13Certificates_valid :
    CA2_7_7I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R13Certificates (CA2_7_7I2R13CertificateIndex a)).input
lemma CA2_7_7I2R13P_check : ∀ a : PairSlot, contains (CA2_7_7I2R13Raw a) (CA2_7_7I2R13P a) = true := by
  decide +kernel
lemma CA2_7_7I2R13P_sound (a : PairSlot) :
    (CA2_7_7I2R13P a).Encloses (CA2_7_7I2R13Value a) :=
  contains_sound (CA2_7_7I2R13Raw_sound a) (CA2_7_7I2R13P_check a)
def CA2_7_7I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R13Certificates (CA2_7_7I2R13CertificateIndex a)).output
lemma CA2_7_7I2R13Terms_sound (a : PairSlot) :
    (CA2_7_7I2R13Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R13Certificates_valid
    (CA2_7_7I2R13CertificateIndex a) (CA2_7_7I2R13P_sound a)
def CA2_7_7I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R13Entropy_sound : CA2_7_7I2R13Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R13Value CA2_7_7I2R13Terms CA2_7_7I2R13Terms_sound) (by decide +kernel)
def CA2_7_7I2R13Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R13Mass_sound : CA2_7_7I2R13Mass.Encloses (∑ a, CA2_7_7I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R13P CA2_7_7I2R13Value CA2_7_7I2R13P_sound) (by decide +kernel)
def CA2_7_7I2R13MassTerm : Ball := .exact 0
lemma CA2_7_7I2R13MassTerm_sound : CA2_7_7I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R13Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R13Mass_sound)
def CA2_7_7I2R13H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R13H_sound : CA2_7_7I2R13H.Encloses (homogeneousEntropy CA2_7_7I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R13Value CA2_7_7I2R13MassTerm_sound CA2_7_7I2R13Entropy_sound) (by decide +kernel)
def CA2_7_7I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA2_7_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA2_7_7I2R14Raw_sound (a : PairSlot) :
    (CA2_7_7I2R14Raw a).Encloses (CA2_7_7I2R14Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA2_7_7I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R14Certificates_valid :
    CA2_7_7I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R14Certificates (CA2_7_7I2R14CertificateIndex a)).input
lemma CA2_7_7I2R14P_check : ∀ a : PairSlot, contains (CA2_7_7I2R14Raw a) (CA2_7_7I2R14P a) = true := by
  decide +kernel
lemma CA2_7_7I2R14P_sound (a : PairSlot) :
    (CA2_7_7I2R14P a).Encloses (CA2_7_7I2R14Value a) :=
  contains_sound (CA2_7_7I2R14Raw_sound a) (CA2_7_7I2R14P_check a)
def CA2_7_7I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R14Certificates (CA2_7_7I2R14CertificateIndex a)).output
lemma CA2_7_7I2R14Terms_sound (a : PairSlot) :
    (CA2_7_7I2R14Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R14Certificates_valid
    (CA2_7_7I2R14CertificateIndex a) (CA2_7_7I2R14P_sound a)
def CA2_7_7I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R14Entropy_sound : CA2_7_7I2R14Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R14Value CA2_7_7I2R14Terms CA2_7_7I2R14Terms_sound) (by decide +kernel)
def CA2_7_7I2R14Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R14Mass_sound : CA2_7_7I2R14Mass.Encloses (∑ a, CA2_7_7I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R14P CA2_7_7I2R14Value CA2_7_7I2R14P_sound) (by decide +kernel)
def CA2_7_7I2R14MassTerm : Ball := .exact 0
lemma CA2_7_7I2R14MassTerm_sound : CA2_7_7I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R14Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R14Mass_sound)
def CA2_7_7I2R14H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R14H_sound : CA2_7_7I2R14H.Encloses (homogeneousEntropy CA2_7_7I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R14Value CA2_7_7I2R14MassTerm_sound CA2_7_7I2R14Entropy_sound) (by decide +kernel)
def CA2_7_7I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA2_7_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA2_7_7I2R15Raw_sound (a : PairSlot) :
    (CA2_7_7I2R15Raw a).Encloses (CA2_7_7I2R15Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA2_7_7I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R15Certificates_valid :
    CA2_7_7I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R15Certificates (CA2_7_7I2R15CertificateIndex a)).input
lemma CA2_7_7I2R15P_check : ∀ a : PairSlot, contains (CA2_7_7I2R15Raw a) (CA2_7_7I2R15P a) = true := by
  decide +kernel
lemma CA2_7_7I2R15P_sound (a : PairSlot) :
    (CA2_7_7I2R15P a).Encloses (CA2_7_7I2R15Value a) :=
  contains_sound (CA2_7_7I2R15Raw_sound a) (CA2_7_7I2R15P_check a)
def CA2_7_7I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R15Certificates (CA2_7_7I2R15CertificateIndex a)).output
lemma CA2_7_7I2R15Terms_sound (a : PairSlot) :
    (CA2_7_7I2R15Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R15Certificates_valid
    (CA2_7_7I2R15CertificateIndex a) (CA2_7_7I2R15P_sound a)
def CA2_7_7I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R15Entropy_sound : CA2_7_7I2R15Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R15Value CA2_7_7I2R15Terms CA2_7_7I2R15Terms_sound) (by decide +kernel)
def CA2_7_7I2R15Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R15Mass_sound : CA2_7_7I2R15Mass.Encloses (∑ a, CA2_7_7I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R15P CA2_7_7I2R15Value CA2_7_7I2R15P_sound) (by decide +kernel)
def CA2_7_7I2R15MassTerm : Ball := .exact 0
lemma CA2_7_7I2R15MassTerm_sound : CA2_7_7I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R15Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R15Mass_sound)
def CA2_7_7I2R15H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R15H_sound : CA2_7_7I2R15H.Encloses (homogeneousEntropy CA2_7_7I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R15Value CA2_7_7I2R15MassTerm_sound CA2_7_7I2R15Entropy_sound) (by decide +kernel)
def CA2_7_7I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA2_7_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA2_7_7I2R16Raw_sound (a : PairSlot) :
    (CA2_7_7I2R16Raw a).Encloses (CA2_7_7I2R16Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA2_7_7I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I2R16Certificates_valid :
    CA2_7_7I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R16Certificates (CA2_7_7I2R16CertificateIndex a)).input
lemma CA2_7_7I2R16P_check : ∀ a : PairSlot, contains (CA2_7_7I2R16Raw a) (CA2_7_7I2R16P a) = true := by
  decide +kernel
lemma CA2_7_7I2R16P_sound (a : PairSlot) :
    (CA2_7_7I2R16P a).Encloses (CA2_7_7I2R16Value a) :=
  contains_sound (CA2_7_7I2R16Raw_sound a) (CA2_7_7I2R16P_check a)
def CA2_7_7I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I2R16Certificates (CA2_7_7I2R16CertificateIndex a)).output
lemma CA2_7_7I2R16Terms_sound (a : PairSlot) :
    (CA2_7_7I2R16Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I2R16Certificates_valid
    (CA2_7_7I2R16CertificateIndex a) (CA2_7_7I2R16P_sound a)
def CA2_7_7I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R16Entropy_sound : CA2_7_7I2R16Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I2R16Value CA2_7_7I2R16Terms CA2_7_7I2R16Terms_sound) (by decide +kernel)
def CA2_7_7I2R16Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R16Mass_sound : CA2_7_7I2R16Mass.Encloses (∑ a, CA2_7_7I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I2R16P CA2_7_7I2R16Value CA2_7_7I2R16P_sound) (by decide +kernel)
def CA2_7_7I2R16MassTerm : Ball := .exact 0
lemma CA2_7_7I2R16MassTerm_sound : CA2_7_7I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I2R16Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I2R16Mass_sound)
def CA2_7_7I2R16H : Ball := ⟨0, 0⟩
lemma CA2_7_7I2R16H_sound : CA2_7_7I2R16H.Encloses (homogeneousEntropy CA2_7_7I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I2R16Value CA2_7_7I2R16MassTerm_sound CA2_7_7I2R16Entropy_sound) (by decide +kernel)
def CA2_7_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_7_7I2R0H
  | 1 => CA2_7_7I2R1H
  | 2 => CA2_7_7I2R2H
  | 3 => CA2_7_7I2R3H
  | 4 => CA2_7_7I2R4H
  | 5 => CA2_7_7I2R5H
  | 6 => CA2_7_7I2R6H
  | 7 => CA2_7_7I2R7H
  | 8 => CA2_7_7I2R8H
  | 9 => CA2_7_7I2R9H
  | 10 => CA2_7_7I2R10H
  | 11 => CA2_7_7I2R11H
  | 12 => CA2_7_7I2R12H
  | 13 => CA2_7_7I2R13H
  | 14 => CA2_7_7I2R14H
  | 15 => CA2_7_7I2R15H
  | 16 => CA2_7_7I2R16H
  | _ => (.exact 0)
lemma CA2_7_7I2ResidualEntropies_sound (k : Fin 17) :
    (CA2_7_7I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_7_7I2R0H_sound
  · exact CA2_7_7I2R1H_sound
  · exact CA2_7_7I2R2H_sound
  · exact CA2_7_7I2R3H_sound
  · exact CA2_7_7I2R4H_sound
  · exact CA2_7_7I2R5H_sound
  · exact CA2_7_7I2R6H_sound
  · exact CA2_7_7I2R7H_sound
  · exact CA2_7_7I2R8H_sound
  · exact CA2_7_7I2R9H_sound
  · exact CA2_7_7I2R10H_sound
  · exact CA2_7_7I2R11H_sound
  · exact CA2_7_7I2R12H_sound
  · exact CA2_7_7I2R13H_sound
  · exact CA2_7_7I2R14H_sound
  · exact CA2_7_7I2R15H_sound
  · exact CA2_7_7I2R16H_sound
def CA2_7_7I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 0, 7, 1 => Z0_7_1H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | _, _, _ => (.exact 0)
lemma CA2_7_7I2Singles_sound (u : Shape) (hu : u ∈ below (shape 2 7 7))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA2_7_7I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A2_7_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact Z0_7_1H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 7 0) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 6 0) by decide +kernel) hd |>.elim
def CA2_7_7I2Singleton : Ball := ⟨(3735549344201020389155168425783 / 12500000000000000000000000000000), (3138425543 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I2Singleton_sound : CA2_7_7I2Singleton.Encloses
    (singletonEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA2_7_7I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A2_7_7Law_sound u) CA2_7_7I2Singles_sound) (by decide +kernel)
def CA2_7_7I2Group : Ball := ⟨(823532456101625366543148449591 / 800000000000000000000000000000), (193698787 / 125000000000000000000000000000)⟩
lemma CA2_7_7I2Group_sound : CA2_7_7I2Group.Encloses
    (groupedEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_7_7I2Singleton_sound
    (finSumBall_sound 17 CA2_7_7I2ResidualEntropies _ CA2_7_7I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_7_7I2H : Ball := ⟨(53956368040931955078041468163973 / 50000000000000000000000000000000), (473949701211 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I2_sound : CA2_7_7I2H.Encloses (stageACapacity (shape 2 7 7) 2) := by
  have hb := contains_sound (Ball.add_sound CA2_7_7I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_7_7I2Group_sound)))
    (show contains (.add CA2_7_7I2PairH (.neg (.mul (.exact 2) CA2_7_7I2Group))) CA2_7_7I2H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false]
  change CA2_7_7I2H.Encloses (homogeneousEntropy CA2_7_7I2PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
