import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA3_6_7I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_6_7I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA3_6_7I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA3_6_7I2R0Raw_sound (a : PairSlot) :
    (CA3_6_7I2R0Raw a).Encloses (CA3_6_7I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA3_6_7I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(510077166889140883101150469 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(6215860913120059024385980159 / 100000000000000000000000000000000), (82091 / 4000000000000000000000000000000)⟩ ⟨(-243722374441081436775523471546581 / 20000000000000000000000000000000), (201170521037 / 50000000000000000000000000000000)⟩ ⟨-18, 510077166889140883101150469, 381469726562500000000000000⟩]
lemma CA3_6_7I2R0Certificates_valid :
    CA3_6_7I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA3_6_7I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R0Certificates (CA3_6_7I2R0CertificateIndex a)).input
lemma CA3_6_7I2R0P_check : ∀ a : PairSlot, contains (CA3_6_7I2R0Raw a) (CA3_6_7I2R0P a) = true := by
  decide +kernel
lemma CA3_6_7I2R0P_sound (a : PairSlot) :
    (CA3_6_7I2R0P a).Encloses (CA3_6_7I2R0Value a) :=
  contains_sound (CA3_6_7I2R0Raw_sound a) (CA3_6_7I2R0P_check a)
def CA3_6_7I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R0Certificates (CA3_6_7I2R0CertificateIndex a)).output
lemma CA3_6_7I2R0Terms_sound (a : PairSlot) :
    (CA3_6_7I2R0Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R0Certificates_valid
    (CA3_6_7I2R0CertificateIndex a) (CA3_6_7I2R0P_sound a)
def CA3_6_7I2R0Entropy : Ball := ⟨(6215860913120059024385980159 / 100000000000000000000000000000000), (82091 / 4000000000000000000000000000000)⟩
lemma CA3_6_7I2R0Entropy_sound : CA3_6_7I2R0Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R0Value CA3_6_7I2R0Terms CA3_6_7I2R0Terms_sound) (by decide +kernel)
def CA3_6_7I2R0Mass : Ball := ⟨(510077166889140883101150469 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R0Mass_sound : CA3_6_7I2R0Mass.Encloses (∑ a, CA3_6_7I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R0P CA3_6_7I2R0Value CA3_6_7I2R0P_sound) (by decide +kernel)
def CA3_6_7I2R0MassTermLogWitness : LogWitness := ⟨-18, 510077166889140883101150469, 381469726562500000000000000⟩
def CA3_6_7I2R0MassTermLog : Ball := ⟨(-243722374441081436775523471546581 / 20000000000000000000000000000000), (201170521037 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R0MassTermLog_sound : CA3_6_7I2R0MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R0Mass_sound) (w := CA3_6_7I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R0MassTerm : Ball := ⟨(6215860913120059024385980159 / 100000000000000000000000000000000), (82091 / 4000000000000000000000000000000)⟩
lemma CA3_6_7I2R0MassTerm_sound : CA3_6_7I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R0Mass_sound) CA3_6_7I2R0MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R0H : Ball := ⟨0, (82091 / 2000000000000000000000000000000)⟩
lemma CA3_6_7I2R0H_sound : CA3_6_7I2R0H.Encloses (homogeneousEntropy CA3_6_7I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R0Value CA3_6_7I2R0MassTerm_sound CA3_6_7I2R0Entropy_sound) (by decide +kernel)
def CA3_6_7I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA3_6_7I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA3_6_7I2R1Raw_sound (a : PairSlot) :
    (CA3_6_7I2R1Raw a).Encloses (CA3_6_7I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA3_6_7I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15968760802922606319500670023 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(234932304814444663213154937893 / 50000000000000000000000000000000), (20289103 / 12500000000000000000000000000000)⟩ ⟨(-183899918498565726290099502470069 / 25000000000000000000000000000000), (63527472223 / 25000000000000000000000000000000)⟩ ⟨-11, 15968760802922606319500670023, 12207031250000000000000000000⟩]
lemma CA3_6_7I2R1Certificates_valid :
    CA3_6_7I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA3_6_7I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R1Certificates (CA3_6_7I2R1CertificateIndex a)).input
lemma CA3_6_7I2R1P_check : ∀ a : PairSlot, contains (CA3_6_7I2R1Raw a) (CA3_6_7I2R1P a) = true := by
  decide +kernel
lemma CA3_6_7I2R1P_sound (a : PairSlot) :
    (CA3_6_7I2R1P a).Encloses (CA3_6_7I2R1Value a) :=
  contains_sound (CA3_6_7I2R1Raw_sound a) (CA3_6_7I2R1P_check a)
def CA3_6_7I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R1Certificates (CA3_6_7I2R1CertificateIndex a)).output
lemma CA3_6_7I2R1Terms_sound (a : PairSlot) :
    (CA3_6_7I2R1Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R1Certificates_valid
    (CA3_6_7I2R1CertificateIndex a) (CA3_6_7I2R1P_sound a)
def CA3_6_7I2R1Entropy : Ball := ⟨(234932304814444663213154937893 / 25000000000000000000000000000000), (20289103 / 6250000000000000000000000000000)⟩
lemma CA3_6_7I2R1Entropy_sound : CA3_6_7I2R1Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R1Value CA3_6_7I2R1Terms CA3_6_7I2R1Terms_sound) (by decide +kernel)
def CA3_6_7I2R1Mass : Ball := ⟨(15968760802922606319500670023 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R1Mass_sound : CA3_6_7I2R1Mass.Encloses (∑ a, CA3_6_7I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R1P CA3_6_7I2R1Value CA3_6_7I2R1P_sound) (by decide +kernel)
def CA3_6_7I2R1MassTermLogWitness : LogWitness := ⟨-10, 15968760802922606319500670023, 12207031250000000000000000000⟩
def CA3_6_7I2R1MassTermLog : Ball := ⟨(-333142477969134187109337408414973 / 50000000000000000000000000000000), (232934065209 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R1MassTermLog_sound : CA3_6_7I2R1MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R1Mass_sound) (w := CA3_6_7I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R1MassTerm : Ball := ⟨(34047184281484914742132203749 / 4000000000000000000000000000000), (29757351 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I2R1MassTerm_sound : CA3_6_7I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R1Mass_sound) CA3_6_7I2R1MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R1H : Ball := ⟨(88549612220655784299314657847 / 100000000000000000000000000000000), (311099579 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R1H_sound : CA3_6_7I2R1H.Encloses (homogeneousEntropy CA3_6_7I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R1Value CA3_6_7I2R1MassTerm_sound CA3_6_7I2R1Entropy_sound) (by decide +kernel)
def CA3_6_7I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA3_6_7I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA3_6_7I2R2Raw_sound (a : PairSlot) :
    (CA3_6_7I2R2Raw a).Encloses (CA3_6_7I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA3_6_7I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(477245282311750937119086766437 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(1110012323836117085702419072269 / 25000000000000000000000000000000), (50530311 / 3125000000000000000000000000000)⟩ ⟨(-93034954140082938085692056837717 / 20000000000000000000000000000000), (169406590197 / 100000000000000000000000000000000)⟩ ⟨-7, 477245282311750937119086766437, 390625000000000000000000000000⟩,
   .log ⟨(38152335994765504602303125379 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(547729532373760281308008249659 / 100000000000000000000000000000000), (96948861 / 50000000000000000000000000000000)⟩ ⟨(-22431847802226837266959381505543 / 3125000000000000000000000000000), (127054942753 / 50000000000000000000000000000000)⟩ ⟨-11, 38152335994765504602303125379, 24414062500000000000000000000⟩,
   .log ⟨(879916248847869827298756043493 / 25000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(5889815098456610719804441545373 / 50000000000000000000000000000000), (894381681 / 20000000000000000000000000000000)⟩ ⟨(-66936087453419792162832007461427 / 20000000000000000000000000000000), (127054942637 / 100000000000000000000000000000000)⟩ ⟨-5, 879916248847869827298756043493, 781250000000000000000000000000⟩]
lemma CA3_6_7I2R2Certificates_valid :
    CA3_6_7I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA3_6_7I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R2Certificates (CA3_6_7I2R2CertificateIndex a)).input
lemma CA3_6_7I2R2P_check : ∀ a : PairSlot, contains (CA3_6_7I2R2Raw a) (CA3_6_7I2R2P a) = true := by
  decide +kernel
lemma CA3_6_7I2R2P_sound (a : PairSlot) :
    (CA3_6_7I2R2P a).Encloses (CA3_6_7I2R2Value a) :=
  contains_sound (CA3_6_7I2R2Raw_sound a) (CA3_6_7I2R2P_check a)
def CA3_6_7I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R2Certificates (CA3_6_7I2R2CertificateIndex a)).output
lemma CA3_6_7I2R2Terms_sound (a : PairSlot) :
    (CA3_6_7I2R2Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R2Certificates_valid
    (CA3_6_7I2R2CertificateIndex a) (CA3_6_7I2R2P_sound a)
def CA3_6_7I2R2Entropy : Ball := ⟨(2719398481543709835980531521027 / 12500000000000000000000000000000), (8093643753 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R2Entropy_sound : CA3_6_7I2R2Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R2Value CA3_6_7I2R2Terms CA3_6_7I2R2Terms_sound) (by decide +kernel)
def CA3_6_7I2R2Mass : Ball := ⟨(1395313867154386269020145935309 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I2R2Mass_sound : CA3_6_7I2R2Mass.Encloses (∑ a, CA3_6_7I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R2P CA3_6_7I2R2Value CA3_6_7I2R2P_sound) (by decide +kernel)
def CA3_6_7I2R2MassTermLogWitness : LogWitness := ⟨-5, 1395313867154386269020145935309, 781250000000000000000000000000⟩
def CA3_6_7I2R2MassTermLog : Ball := ⟨(-288575644052640630693851869710027 / 100000000000000000000000000000000), (5082197709 / 4000000000000000000000000000000)⟩
lemma CA3_6_7I2R2MassTermLog_sound : CA3_6_7I2R2MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R2Mass_sound) (w := CA3_6_7I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R2MassTerm : Ball := ⟨(1610614391478630667960520793111 / 10000000000000000000000000000000), (7091261041 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R2MassTerm_sound : CA3_6_7I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R2Mass_sound) CA3_6_7I2R2MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R2H : Ball := ⟨(2824521968781686004119522118553 / 50000000000000000000000000000000), (7592452397 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R2H_sound : CA3_6_7I2R2H.Encloses (homogeneousEntropy CA3_6_7I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R2Value CA3_6_7I2R2MassTerm_sound CA3_6_7I2R2Entropy_sound) (by decide +kernel)
def CA3_6_7I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA3_6_7I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA3_6_7I2R3Raw_sound (a : PairSlot) :
    (CA3_6_7I2R3Raw a).Encloses (CA3_6_7I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA3_6_7I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(567795852019300251504803927923 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(1468082600177086758535443553069 / 50000000000000000000000000000000), (541059531 / 50000000000000000000000000000000)⟩ ⟨(-64639544078915901459433614126637 / 12500000000000000000000000000000), (190582413851 / 100000000000000000000000000000000)⟩ ⟨-8, 567795852019300251504803927923, 390625000000000000000000000000⟩,
   .log ⟨(311100063325647116279805366219 / 1562500000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(32133954095489082123096793032849 / 100000000000000000000000000000000), (4216192091 / 25000000000000000000000000000000)⟩ ⟨(-1260881073557026003992896102513 / 781250000000000000000000000000), (84703294993 / 100000000000000000000000000000000)⟩ ⟨-3, 311100063325647116279805366219, 195312500000000000000000000000⟩,
   .log ⟨(47638226062113775386381662603 / 4000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(527642674996320405337245134667 / 10000000000000000000000000000000), (1008778687 / 50000000000000000000000000000000)⟩ ⟨(-221520706630992528807325566725471 / 50000000000000000000000000000000), (169406589799 / 100000000000000000000000000000000)⟩ ⟨-7, 47638226062113775386381662603, 31250000000000000000000000000⟩]
lemma CA3_6_7I2R3Certificates_valid :
    CA3_6_7I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA3_6_7I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R3Certificates (CA3_6_7I2R3CertificateIndex a)).input
lemma CA3_6_7I2R3P_check : ∀ a : PairSlot, contains (CA3_6_7I2R3Raw a) (CA3_6_7I2R3P a) = true := by
  decide +kernel
lemma CA3_6_7I2R3P_sound (a : PairSlot) :
    (CA3_6_7I2R3P a).Encloses (CA3_6_7I2R3Value a) :=
  contains_sound (CA3_6_7I2R3Raw_sound a) (CA3_6_7I2R3P_check a)
def CA3_6_7I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R3Certificates (CA3_6_7I2R3CertificateIndex a)).output
lemma CA3_6_7I2R3Terms_sound (a : PairSlot) :
    (CA3_6_7I2R3Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R3Certificates_valid
    (CA3_6_7I2R3CertificateIndex a) (CA3_6_7I2R3P_sound a)
def CA3_6_7I2R3Entropy : Ball := ⟨(40346546045806459693540131485657 / 50000000000000000000000000000000), (6238889 / 15625000000000000000000000000)⟩
lemma CA3_6_7I2R3Entropy_sound : CA3_6_7I2R3Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R3Value CA3_6_7I2R3Terms CA3_6_7I2R3Terms_sound) (by decide +kernel)
def CA3_6_7I2R3Mass : Ball := ⟨(10834577778206780039035944465507 / 25000000000000000000000000000000), (3 / 2500000000000000000000000000000)⟩
lemma CA3_6_7I2R3Mass_sound : CA3_6_7I2R3Mass.Encloses (∑ a, CA3_6_7I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R3P CA3_6_7I2R3Value CA3_6_7I2R3P_sound) (by decide +kernel)
def CA3_6_7I2R3MassTermLogWitness : LogWitness := ⟨-2, 10834577778206780039035944465507, 6250000000000000000000000000000⟩
def CA3_6_7I2R3MassTermLog : Ball := ⟨(-41806657948170529576606332041273 / 50000000000000000000000000000000), (31763735663 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R3MassTermLog_sound : CA3_6_7I2R3MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R3Mass_sound) (w := CA3_6_7I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R3MassTerm : Ball := ⟨(9059149743726805557353515876951 / 25000000000000000000000000000000), (13765866633 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R3MassTerm_sound : CA3_6_7I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R3Mass_sound) CA3_6_7I2R3MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R3H : Ball := ⟨(4445649311670569715766619946351 / 10000000000000000000000000000000), (33730311433 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R3H_sound : CA3_6_7I2R3H.Encloses (homogeneousEntropy CA3_6_7I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R3Value CA3_6_7I2R3MassTerm_sound CA3_6_7I2R3Entropy_sound) (by decide +kernel)
def CA3_6_7I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA3_6_7I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA3_6_7I2R4Raw_sound (a : PairSlot) :
    (CA3_6_7I2R4Raw a).Encloses (CA3_6_7I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA3_6_7I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3768749892159534350335996687 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(71553748748950638591755501697 / 100000000000000000000000000000000), (11970963 / 50000000000000000000000000000000)⟩ ⟨(-474651746576565528898713404248329 / 50000000000000000000000000000000), (317637368511 / 100000000000000000000000000000000)⟩ ⟨-14, 3768749892159534350335996687, 3051757812500000000000000000⟩,
   .log ⟨(2792838143596750317951640780591 / 100000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩ ⟨(4996543630377774947215172552777 / 50000000000000000000000000000000), (1034961357 / 25000000000000000000000000000000)⟩ ⟨(-89452796285985042397580038367151 / 25000000000000000000000000000000), (74115383123 / 50000000000000000000000000000000)⟩ ⟨-6, 2792838143596750317951640780591, 1562500000000000000000000000000⟩,
   .log ⟨(29414183677947483565488001407433 / 100000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩ ⟨(17996968127377864700049875330099 / 50000000000000000000000000000000), (9343043593 / 50000000000000000000000000000000)⟩ ⟨(-61184659497691998813411265309479 / 50000000000000000000000000000000), (635274713 / 1000000000000000000000000000000)⟩ ⟨-2, 29414183677947483565488001407433, 25000000000000000000000000000000⟩,
   .log ⟨(282750923241728381146325694403 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(240842778697585860676165656007 / 4000000000000000000000000000000), (1197496753 / 50000000000000000000000000000000)⟩ ⟨(-212946058616124691300388830144329 / 50000000000000000000000000000000), (169406589817 / 100000000000000000000000000000000)⟩ ⟨-7, 282750923241728381146325694403, 156250000000000000000000000000⟩,
   .log ⟨(9088838716492686883361028827 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(174879263863739341370795689247 / 50000000000000000000000000000000), (125101379 / 100000000000000000000000000000000)⟩ ⟨(-384822020323458676893310429719563 / 50000000000000000000000000000000), (275285710079 / 100000000000000000000000000000000)⟩ ⟨-12, 9088838716492686883361028827, 4882812500000000000000000000⟩]
lemma CA3_6_7I2R4Certificates_valid :
    CA3_6_7I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA3_6_7I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R4Certificates (CA3_6_7I2R4CertificateIndex a)).input
lemma CA3_6_7I2R4P_check : ∀ a : PairSlot, contains (CA3_6_7I2R4Raw a) (CA3_6_7I2R4P a) = true := by
  decide +kernel
lemma CA3_6_7I2R4P_sound (a : PairSlot) :
    (CA3_6_7I2R4P a).Encloses (CA3_6_7I2R4Value a) :=
  contains_sound (CA3_6_7I2R4Raw_sound a) (CA3_6_7I2R4P_check a)
def CA3_6_7I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R4Certificates (CA3_6_7I2R4CertificateIndex a)).output
lemma CA3_6_7I2R4Terms_sound (a : PairSlot) :
    (CA3_6_7I2R4Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R4Certificates_valid
    (CA3_6_7I2R4CertificateIndex a) (CA3_6_7I2R4P_sound a)
def CA3_6_7I2R4Entropy : Ball := ⟨(8564389467046437772836728256693 / 12500000000000000000000000000000), (6385750057 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I2R4Entropy_sound : CA3_6_7I2R4Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R4Value CA3_6_7I2R4Terms CA3_6_7I2R4Terms_sound) (by decide +kernel)
def CA3_6_7I2R4Mass : Ball := ⟨(4735986048838671198084086130441 / 12500000000000000000000000000000), (113 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R4Mass_sound : CA3_6_7I2R4Mass.Encloses (∑ a, CA3_6_7I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R4P CA3_6_7I2R4Value CA3_6_7I2R4P_sound) (by decide +kernel)
def CA3_6_7I2R4MassTermLogWitness : LogWitness := ⟨-2, 4735986048838671198084086130441, 3125000000000000000000000000000⟩
def CA3_6_7I2R4MassTermLog : Ball := ⟨(-24263467312493783074333674577909 / 25000000000000000000000000000000), (63527471347 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R4MassTermLog_sound : CA3_6_7I2R4MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R4Mass_sound) (w := CA3_6_7I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R4MassTerm : Ball := ⟨(36771661660295578856776336701901 / 100000000000000000000000000000000), (1504326097 / 6250000000000000000000000000000)⟩
lemma CA3_6_7I2R4MassTerm_sound : CA3_6_7I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R4Mass_sound) CA3_6_7I2R4MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R4H : Ball := ⟨(31743454076075923325917489351643 / 100000000000000000000000000000000), (55997967837 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R4H_sound : CA3_6_7I2R4H.Encloses (homogeneousEntropy CA3_6_7I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R4Value CA3_6_7I2R4MassTerm_sound CA3_6_7I2R4Entropy_sound) (by decide +kernel)
def CA3_6_7I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA3_6_7I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA3_6_7I2R5Raw_sound (a : PairSlot) :
    (CA3_6_7I2R5Raw a).Encloses (CA3_6_7I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA3_6_7I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1216107865961754398594619603 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(25840158610198170353919045319 / 100000000000000000000000000000000), (4377861 / 50000000000000000000000000000000)⟩ ⟨(-33200383747624250480192038192331 / 3125000000000000000000000000000), (14399561749 / 4000000000000000000000000000000)⟩ ⟨-16, 1216107865961754398594619603, 762939453125000000000000000⟩,
   .log ⟨(1564187444353850080428827484441 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩ ⟨(3251792173155456238670031825677 / 50000000000000000000000000000000), (1159303537 / 50000000000000000000000000000000)⟩ ⟨(-207890185085761157122574860119299 / 50000000000000000000000000000000), (37057691589 / 25000000000000000000000000000000)⟩ ⟨-6, 1564187444353850080428827484441, 1562500000000000000000000000000⟩,
   .log ⟨(57974565660091486457204397023 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(432079862146993216554855326163 / 100000000000000000000000000000000), (147319111 / 100000000000000000000000000000000)⟩ ⟨(-372646053685252719502649276073761 / 50000000000000000000000000000000), (1588186787 / 625000000000000000000000000000)⟩ ⟨-11, 57974565660091486457204397023, 48828125000000000000000000000⟩]
lemma CA3_6_7I2R5Certificates_valid :
    CA3_6_7I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA3_6_7I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R5Certificates (CA3_6_7I2R5CertificateIndex a)).input
lemma CA3_6_7I2R5P_check : ∀ a : PairSlot, contains (CA3_6_7I2R5Raw a) (CA3_6_7I2R5P a) = true := by
  decide +kernel
lemma CA3_6_7I2R5P_sound (a : PairSlot) :
    (CA3_6_7I2R5P a).Encloses (CA3_6_7I2R5Value a) :=
  contains_sound (CA3_6_7I2R5Raw_sound a) (CA3_6_7I2R5P_check a)
def CA3_6_7I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R5Certificates (CA3_6_7I2R5CertificateIndex a)).output
lemma CA3_6_7I2R5Terms_sound (a : PairSlot) :
    (CA3_6_7I2R5Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R5Certificates_valid
    (CA3_6_7I2R5CertificateIndex a) (CA3_6_7I2R5P_sound a)
def CA3_6_7I2R5Entropy : Ball := ⟨(1740376091767025966062209505709 / 12500000000000000000000000000000), (2474681907 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R5Entropy_sound : CA3_6_7I2R5Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R5Value CA3_6_7I2R5Terms CA3_6_7I2R5Terms_sound) (by decide +kernel)
def CA3_6_7I2R5Mass : Ball := ⟨(162459422574586507568322112067 / 5000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R5Mass_sound : CA3_6_7I2R5Mass.Encloses (∑ a, CA3_6_7I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R5P CA3_6_7I2R5Value CA3_6_7I2R5P_sound) (by decide +kernel)
def CA3_6_7I2R5MassTermLogWitness : LogWitness := ⟨-5, 162459422574586507568322112067, 156250000000000000000000000000⟩
def CA3_6_7I2R5MassTermLog : Ball := ⟨(-342676492806180126403811039545367 / 100000000000000000000000000000000), (63527471387 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R5MassTermLog_sound : CA3_6_7I2R5MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R5Mass_sound) (w := CA3_6_7I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R5MassTerm : Ball := ⟨(11134205030235294118142875014453 / 100000000000000000000000000000000), (1032063651 / 25000000000000000000000000000000)⟩
lemma CA3_6_7I2R5MassTerm_sound : CA3_6_7I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R5Mass_sound) CA3_6_7I2R5MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R5H : Ball := ⟨(2788803703900913610354801031219 / 100000000000000000000000000000000), (4538809209 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R5H_sound : CA3_6_7I2R5H.Encloses (homogeneousEntropy CA3_6_7I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R5Value CA3_6_7I2R5MassTerm_sound CA3_6_7I2R5Entropy_sound) (by decide +kernel)
def CA3_6_7I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA3_6_7I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA3_6_7I2R6Raw_sound (a : PairSlot) :
    (CA3_6_7I2R6Raw a).Encloses (CA3_6_7I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA3_6_7I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(55691222659172165829909123 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(44523114681774951754400271 / 1250000000000000000000000000000), (589661 / 50000000000000000000000000000000)⟩ ⟨(-639571013971152418277419202643777 / 50000000000000000000000000000000), (423516832783 / 100000000000000000000000000000000)⟩ ⟨-19, 55691222659172165829909123, 38146972656250000000000000⟩,
   .log ⟨(17543840399584406054003 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(39410014844335261591411 / 10000000000000000000000000000000), (151 / 100000000000000000000000000000000)⟩ ⟨(-2246373310901120642882203537001479 / 100000000000000000000000000000000), (181419502869 / 25000000000000000000000000000000)⟩ ⟨-33, 35087680799168812108006, 23283064365386962890625⟩,
   .log ⟨(912451327469080514362939317 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(237640578461297954800636751903 / 100000000000000000000000000000000), (40189579 / 50000000000000000000000000000000)⟩ ⟨(-406940504843925985159635726043001 / 50000000000000000000000000000000), (34410714341 / 12500000000000000000000000000000)⟩ ⟨-12, 912451327469080514362939317, 762939453125000000000000000⟩]
lemma CA3_6_7I2R6Certificates_valid :
    CA3_6_7I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA3_6_7I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R6Certificates (CA3_6_7I2R6CertificateIndex a)).input
lemma CA3_6_7I2R6P_check : ∀ a : PairSlot, contains (CA3_6_7I2R6Raw a) (CA3_6_7I2R6P a) = true := by
  decide +kernel
lemma CA3_6_7I2R6P_sound (a : PairSlot) :
    (CA3_6_7I2R6P a).Encloses (CA3_6_7I2R6Value a) :=
  contains_sound (CA3_6_7I2R6Raw_sound a) (CA3_6_7I2R6P_check a)
def CA3_6_7I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R6Certificates (CA3_6_7I2R6CertificateIndex a)).output
lemma CA3_6_7I2R6Terms_sound (a : PairSlot) :
    (CA3_6_7I2R6Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R6Certificates_valid
    (CA3_6_7I2R6CertificateIndex a) (CA3_6_7I2R6P_sound a)
def CA3_6_7I2R6Entropy : Ball := ⟨(244765065010678833786572623483 / 100000000000000000000000000000000), (10342263 / 12500000000000000000000000000000)⟩
lemma CA3_6_7I2R6Entropy_sound : CA3_6_7I2R6Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R6Value CA3_6_7I2R6Terms CA3_6_7I2R6Terms_sound) (by decide +kernel)
def CA3_6_7I2R6Mass : Ball := ⟨(1487769489664154864336262869 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I2R6Mass_sound : CA3_6_7I2R6Mass.Encloses (∑ a, CA3_6_7I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R6P CA3_6_7I2R6Value CA3_6_7I2R6P_sound) (by decide +kernel)
def CA3_6_7I2R6MassTermLogWitness : LogWitness := ⟨-12, 1487769489664154864336262869, 1220703125000000000000000000⟩
def CA3_6_7I2R6MassTermLog : Ball := ⟨(-811991517986568473916712948623463 / 100000000000000000000000000000000), (275285728043 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R6MassTermLog_sound : CA3_6_7I2R6MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I2R6Mass_sound) (w := CA3_6_7I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I2R6MassTerm : Ball := ⟨(241611241265299880754628677639 / 100000000000000000000000000000000), (81912391 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2R6MassTerm_sound : CA3_6_7I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I2R6Mass_sound) CA3_6_7I2R6MassTermLog_sound) (by decide +kernel)
def CA3_6_7I2R6H : Ball := ⟨(788455936344738257985986461 / 25000000000000000000000000000000), (32930099 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I2R6H_sound : CA3_6_7I2R6H.Encloses (homogeneousEntropy CA3_6_7I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R6Value CA3_6_7I2R6MassTerm_sound CA3_6_7I2R6Entropy_sound) (by decide +kernel)
def CA3_6_7I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA3_6_7I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA3_6_7I2R7Raw_sound (a : PairSlot) :
    (CA3_6_7I2R7Raw a).Encloses (CA3_6_7I2R7Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA3_6_7I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R7Certificates_valid :
    CA3_6_7I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R7Certificates (CA3_6_7I2R7CertificateIndex a)).input
lemma CA3_6_7I2R7P_check : ∀ a : PairSlot, contains (CA3_6_7I2R7Raw a) (CA3_6_7I2R7P a) = true := by
  decide +kernel
lemma CA3_6_7I2R7P_sound (a : PairSlot) :
    (CA3_6_7I2R7P a).Encloses (CA3_6_7I2R7Value a) :=
  contains_sound (CA3_6_7I2R7Raw_sound a) (CA3_6_7I2R7P_check a)
def CA3_6_7I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R7Certificates (CA3_6_7I2R7CertificateIndex a)).output
lemma CA3_6_7I2R7Terms_sound (a : PairSlot) :
    (CA3_6_7I2R7Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R7Certificates_valid
    (CA3_6_7I2R7CertificateIndex a) (CA3_6_7I2R7P_sound a)
def CA3_6_7I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R7Entropy_sound : CA3_6_7I2R7Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R7Value CA3_6_7I2R7Terms CA3_6_7I2R7Terms_sound) (by decide +kernel)
def CA3_6_7I2R7Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R7Mass_sound : CA3_6_7I2R7Mass.Encloses (∑ a, CA3_6_7I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R7P CA3_6_7I2R7Value CA3_6_7I2R7P_sound) (by decide +kernel)
def CA3_6_7I2R7MassTerm : Ball := .exact 0
lemma CA3_6_7I2R7MassTerm_sound : CA3_6_7I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R7Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R7Mass_sound)
def CA3_6_7I2R7H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R7H_sound : CA3_6_7I2R7H.Encloses (homogeneousEntropy CA3_6_7I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R7Value CA3_6_7I2R7MassTerm_sound CA3_6_7I2R7Entropy_sound) (by decide +kernel)
def CA3_6_7I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA3_6_7I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA3_6_7I2R8Raw_sound (a : PairSlot) :
    (CA3_6_7I2R8Raw a).Encloses (CA3_6_7I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA3_6_7I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R8Certificates_valid :
    CA3_6_7I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R8Certificates (CA3_6_7I2R8CertificateIndex a)).input
lemma CA3_6_7I2R8P_check : ∀ a : PairSlot, contains (CA3_6_7I2R8Raw a) (CA3_6_7I2R8P a) = true := by
  decide +kernel
lemma CA3_6_7I2R8P_sound (a : PairSlot) :
    (CA3_6_7I2R8P a).Encloses (CA3_6_7I2R8Value a) :=
  contains_sound (CA3_6_7I2R8Raw_sound a) (CA3_6_7I2R8P_check a)
def CA3_6_7I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R8Certificates (CA3_6_7I2R8CertificateIndex a)).output
lemma CA3_6_7I2R8Terms_sound (a : PairSlot) :
    (CA3_6_7I2R8Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R8Certificates_valid
    (CA3_6_7I2R8CertificateIndex a) (CA3_6_7I2R8P_sound a)
def CA3_6_7I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R8Entropy_sound : CA3_6_7I2R8Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R8Value CA3_6_7I2R8Terms CA3_6_7I2R8Terms_sound) (by decide +kernel)
def CA3_6_7I2R8Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R8Mass_sound : CA3_6_7I2R8Mass.Encloses (∑ a, CA3_6_7I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R8P CA3_6_7I2R8Value CA3_6_7I2R8P_sound) (by decide +kernel)
def CA3_6_7I2R8MassTerm : Ball := .exact 0
lemma CA3_6_7I2R8MassTerm_sound : CA3_6_7I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R8Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R8Mass_sound)
def CA3_6_7I2R8H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R8H_sound : CA3_6_7I2R8H.Encloses (homogeneousEntropy CA3_6_7I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R8Value CA3_6_7I2R8MassTerm_sound CA3_6_7I2R8Entropy_sound) (by decide +kernel)
def CA3_6_7I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA3_6_7I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA3_6_7I2R9Raw_sound (a : PairSlot) :
    (CA3_6_7I2R9Raw a).Encloses (CA3_6_7I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA3_6_7I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R9Certificates_valid :
    CA3_6_7I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R9Certificates (CA3_6_7I2R9CertificateIndex a)).input
lemma CA3_6_7I2R9P_check : ∀ a : PairSlot, contains (CA3_6_7I2R9Raw a) (CA3_6_7I2R9P a) = true := by
  decide +kernel
lemma CA3_6_7I2R9P_sound (a : PairSlot) :
    (CA3_6_7I2R9P a).Encloses (CA3_6_7I2R9Value a) :=
  contains_sound (CA3_6_7I2R9Raw_sound a) (CA3_6_7I2R9P_check a)
def CA3_6_7I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R9Certificates (CA3_6_7I2R9CertificateIndex a)).output
lemma CA3_6_7I2R9Terms_sound (a : PairSlot) :
    (CA3_6_7I2R9Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R9Certificates_valid
    (CA3_6_7I2R9CertificateIndex a) (CA3_6_7I2R9P_sound a)
def CA3_6_7I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R9Entropy_sound : CA3_6_7I2R9Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R9Value CA3_6_7I2R9Terms CA3_6_7I2R9Terms_sound) (by decide +kernel)
def CA3_6_7I2R9Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R9Mass_sound : CA3_6_7I2R9Mass.Encloses (∑ a, CA3_6_7I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R9P CA3_6_7I2R9Value CA3_6_7I2R9P_sound) (by decide +kernel)
def CA3_6_7I2R9MassTerm : Ball := .exact 0
lemma CA3_6_7I2R9MassTerm_sound : CA3_6_7I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R9Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R9Mass_sound)
def CA3_6_7I2R9H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R9H_sound : CA3_6_7I2R9H.Encloses (homogeneousEntropy CA3_6_7I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R9Value CA3_6_7I2R9MassTerm_sound CA3_6_7I2R9Entropy_sound) (by decide +kernel)
def CA3_6_7I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA3_6_7I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA3_6_7I2R10Raw_sound (a : PairSlot) :
    (CA3_6_7I2R10Raw a).Encloses (CA3_6_7I2R10Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA3_6_7I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R10Certificates_valid :
    CA3_6_7I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R10Certificates (CA3_6_7I2R10CertificateIndex a)).input
lemma CA3_6_7I2R10P_check : ∀ a : PairSlot, contains (CA3_6_7I2R10Raw a) (CA3_6_7I2R10P a) = true := by
  decide +kernel
lemma CA3_6_7I2R10P_sound (a : PairSlot) :
    (CA3_6_7I2R10P a).Encloses (CA3_6_7I2R10Value a) :=
  contains_sound (CA3_6_7I2R10Raw_sound a) (CA3_6_7I2R10P_check a)
def CA3_6_7I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R10Certificates (CA3_6_7I2R10CertificateIndex a)).output
lemma CA3_6_7I2R10Terms_sound (a : PairSlot) :
    (CA3_6_7I2R10Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R10Certificates_valid
    (CA3_6_7I2R10CertificateIndex a) (CA3_6_7I2R10P_sound a)
def CA3_6_7I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R10Entropy_sound : CA3_6_7I2R10Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R10Value CA3_6_7I2R10Terms CA3_6_7I2R10Terms_sound) (by decide +kernel)
def CA3_6_7I2R10Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R10Mass_sound : CA3_6_7I2R10Mass.Encloses (∑ a, CA3_6_7I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R10P CA3_6_7I2R10Value CA3_6_7I2R10P_sound) (by decide +kernel)
def CA3_6_7I2R10MassTerm : Ball := .exact 0
lemma CA3_6_7I2R10MassTerm_sound : CA3_6_7I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R10Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R10Mass_sound)
def CA3_6_7I2R10H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R10H_sound : CA3_6_7I2R10H.Encloses (homogeneousEntropy CA3_6_7I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R10Value CA3_6_7I2R10MassTerm_sound CA3_6_7I2R10Entropy_sound) (by decide +kernel)
def CA3_6_7I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA3_6_7I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA3_6_7I2R11Raw_sound (a : PairSlot) :
    (CA3_6_7I2R11Raw a).Encloses (CA3_6_7I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA3_6_7I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R11Certificates_valid :
    CA3_6_7I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R11Certificates (CA3_6_7I2R11CertificateIndex a)).input
lemma CA3_6_7I2R11P_check : ∀ a : PairSlot, contains (CA3_6_7I2R11Raw a) (CA3_6_7I2R11P a) = true := by
  decide +kernel
lemma CA3_6_7I2R11P_sound (a : PairSlot) :
    (CA3_6_7I2R11P a).Encloses (CA3_6_7I2R11Value a) :=
  contains_sound (CA3_6_7I2R11Raw_sound a) (CA3_6_7I2R11P_check a)
def CA3_6_7I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R11Certificates (CA3_6_7I2R11CertificateIndex a)).output
lemma CA3_6_7I2R11Terms_sound (a : PairSlot) :
    (CA3_6_7I2R11Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R11Certificates_valid
    (CA3_6_7I2R11CertificateIndex a) (CA3_6_7I2R11P_sound a)
def CA3_6_7I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R11Entropy_sound : CA3_6_7I2R11Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R11Value CA3_6_7I2R11Terms CA3_6_7I2R11Terms_sound) (by decide +kernel)
def CA3_6_7I2R11Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R11Mass_sound : CA3_6_7I2R11Mass.Encloses (∑ a, CA3_6_7I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R11P CA3_6_7I2R11Value CA3_6_7I2R11P_sound) (by decide +kernel)
def CA3_6_7I2R11MassTerm : Ball := .exact 0
lemma CA3_6_7I2R11MassTerm_sound : CA3_6_7I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R11Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R11Mass_sound)
def CA3_6_7I2R11H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R11H_sound : CA3_6_7I2R11H.Encloses (homogeneousEntropy CA3_6_7I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R11Value CA3_6_7I2R11MassTerm_sound CA3_6_7I2R11Entropy_sound) (by decide +kernel)
def CA3_6_7I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA3_6_7I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA3_6_7I2R12Raw_sound (a : PairSlot) :
    (CA3_6_7I2R12Raw a).Encloses (CA3_6_7I2R12Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA3_6_7I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R12Certificates_valid :
    CA3_6_7I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R12Certificates (CA3_6_7I2R12CertificateIndex a)).input
lemma CA3_6_7I2R12P_check : ∀ a : PairSlot, contains (CA3_6_7I2R12Raw a) (CA3_6_7I2R12P a) = true := by
  decide +kernel
lemma CA3_6_7I2R12P_sound (a : PairSlot) :
    (CA3_6_7I2R12P a).Encloses (CA3_6_7I2R12Value a) :=
  contains_sound (CA3_6_7I2R12Raw_sound a) (CA3_6_7I2R12P_check a)
def CA3_6_7I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R12Certificates (CA3_6_7I2R12CertificateIndex a)).output
lemma CA3_6_7I2R12Terms_sound (a : PairSlot) :
    (CA3_6_7I2R12Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R12Certificates_valid
    (CA3_6_7I2R12CertificateIndex a) (CA3_6_7I2R12P_sound a)
def CA3_6_7I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R12Entropy_sound : CA3_6_7I2R12Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R12Value CA3_6_7I2R12Terms CA3_6_7I2R12Terms_sound) (by decide +kernel)
def CA3_6_7I2R12Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R12Mass_sound : CA3_6_7I2R12Mass.Encloses (∑ a, CA3_6_7I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R12P CA3_6_7I2R12Value CA3_6_7I2R12P_sound) (by decide +kernel)
def CA3_6_7I2R12MassTerm : Ball := .exact 0
lemma CA3_6_7I2R12MassTerm_sound : CA3_6_7I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R12Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R12Mass_sound)
def CA3_6_7I2R12H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R12H_sound : CA3_6_7I2R12H.Encloses (homogeneousEntropy CA3_6_7I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R12Value CA3_6_7I2R12MassTerm_sound CA3_6_7I2R12Entropy_sound) (by decide +kernel)
def CA3_6_7I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA3_6_7I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA3_6_7I2R13Raw_sound (a : PairSlot) :
    (CA3_6_7I2R13Raw a).Encloses (CA3_6_7I2R13Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA3_6_7I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R13Certificates_valid :
    CA3_6_7I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R13Certificates (CA3_6_7I2R13CertificateIndex a)).input
lemma CA3_6_7I2R13P_check : ∀ a : PairSlot, contains (CA3_6_7I2R13Raw a) (CA3_6_7I2R13P a) = true := by
  decide +kernel
lemma CA3_6_7I2R13P_sound (a : PairSlot) :
    (CA3_6_7I2R13P a).Encloses (CA3_6_7I2R13Value a) :=
  contains_sound (CA3_6_7I2R13Raw_sound a) (CA3_6_7I2R13P_check a)
def CA3_6_7I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R13Certificates (CA3_6_7I2R13CertificateIndex a)).output
lemma CA3_6_7I2R13Terms_sound (a : PairSlot) :
    (CA3_6_7I2R13Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R13Certificates_valid
    (CA3_6_7I2R13CertificateIndex a) (CA3_6_7I2R13P_sound a)
def CA3_6_7I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R13Entropy_sound : CA3_6_7I2R13Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R13Value CA3_6_7I2R13Terms CA3_6_7I2R13Terms_sound) (by decide +kernel)
def CA3_6_7I2R13Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R13Mass_sound : CA3_6_7I2R13Mass.Encloses (∑ a, CA3_6_7I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R13P CA3_6_7I2R13Value CA3_6_7I2R13P_sound) (by decide +kernel)
def CA3_6_7I2R13MassTerm : Ball := .exact 0
lemma CA3_6_7I2R13MassTerm_sound : CA3_6_7I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R13Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R13Mass_sound)
def CA3_6_7I2R13H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R13H_sound : CA3_6_7I2R13H.Encloses (homogeneousEntropy CA3_6_7I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R13Value CA3_6_7I2R13MassTerm_sound CA3_6_7I2R13Entropy_sound) (by decide +kernel)
def CA3_6_7I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA3_6_7I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA3_6_7I2R14Raw_sound (a : PairSlot) :
    (CA3_6_7I2R14Raw a).Encloses (CA3_6_7I2R14Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA3_6_7I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R14Certificates_valid :
    CA3_6_7I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R14Certificates (CA3_6_7I2R14CertificateIndex a)).input
lemma CA3_6_7I2R14P_check : ∀ a : PairSlot, contains (CA3_6_7I2R14Raw a) (CA3_6_7I2R14P a) = true := by
  decide +kernel
lemma CA3_6_7I2R14P_sound (a : PairSlot) :
    (CA3_6_7I2R14P a).Encloses (CA3_6_7I2R14Value a) :=
  contains_sound (CA3_6_7I2R14Raw_sound a) (CA3_6_7I2R14P_check a)
def CA3_6_7I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R14Certificates (CA3_6_7I2R14CertificateIndex a)).output
lemma CA3_6_7I2R14Terms_sound (a : PairSlot) :
    (CA3_6_7I2R14Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R14Certificates_valid
    (CA3_6_7I2R14CertificateIndex a) (CA3_6_7I2R14P_sound a)
def CA3_6_7I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R14Entropy_sound : CA3_6_7I2R14Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R14Value CA3_6_7I2R14Terms CA3_6_7I2R14Terms_sound) (by decide +kernel)
def CA3_6_7I2R14Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R14Mass_sound : CA3_6_7I2R14Mass.Encloses (∑ a, CA3_6_7I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R14P CA3_6_7I2R14Value CA3_6_7I2R14P_sound) (by decide +kernel)
def CA3_6_7I2R14MassTerm : Ball := .exact 0
lemma CA3_6_7I2R14MassTerm_sound : CA3_6_7I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R14Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R14Mass_sound)
def CA3_6_7I2R14H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R14H_sound : CA3_6_7I2R14H.Encloses (homogeneousEntropy CA3_6_7I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R14Value CA3_6_7I2R14MassTerm_sound CA3_6_7I2R14Entropy_sound) (by decide +kernel)
def CA3_6_7I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA3_6_7I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA3_6_7I2R15Raw_sound (a : PairSlot) :
    (CA3_6_7I2R15Raw a).Encloses (CA3_6_7I2R15Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA3_6_7I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R15Certificates_valid :
    CA3_6_7I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R15Certificates (CA3_6_7I2R15CertificateIndex a)).input
lemma CA3_6_7I2R15P_check : ∀ a : PairSlot, contains (CA3_6_7I2R15Raw a) (CA3_6_7I2R15P a) = true := by
  decide +kernel
lemma CA3_6_7I2R15P_sound (a : PairSlot) :
    (CA3_6_7I2R15P a).Encloses (CA3_6_7I2R15Value a) :=
  contains_sound (CA3_6_7I2R15Raw_sound a) (CA3_6_7I2R15P_check a)
def CA3_6_7I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R15Certificates (CA3_6_7I2R15CertificateIndex a)).output
lemma CA3_6_7I2R15Terms_sound (a : PairSlot) :
    (CA3_6_7I2R15Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R15Certificates_valid
    (CA3_6_7I2R15CertificateIndex a) (CA3_6_7I2R15P_sound a)
def CA3_6_7I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R15Entropy_sound : CA3_6_7I2R15Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R15Value CA3_6_7I2R15Terms CA3_6_7I2R15Terms_sound) (by decide +kernel)
def CA3_6_7I2R15Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R15Mass_sound : CA3_6_7I2R15Mass.Encloses (∑ a, CA3_6_7I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R15P CA3_6_7I2R15Value CA3_6_7I2R15P_sound) (by decide +kernel)
def CA3_6_7I2R15MassTerm : Ball := .exact 0
lemma CA3_6_7I2R15MassTerm_sound : CA3_6_7I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R15Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R15Mass_sound)
def CA3_6_7I2R15H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R15H_sound : CA3_6_7I2R15H.Encloses (homogeneousEntropy CA3_6_7I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R15Value CA3_6_7I2R15MassTerm_sound CA3_6_7I2R15Entropy_sound) (by decide +kernel)
def CA3_6_7I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA3_6_7I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 3 6 7)) A3_6_7Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA3_6_7I2R16Raw_sound (a : PairSlot) :
    (CA3_6_7I2R16Raw a).Encloses (CA3_6_7I2R16Value a) := by
  exact residualBall_sound_on (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 3 6 7) (show (shape 3 6 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA3_6_7I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA3_6_7I2R16Certificates_valid :
    CA3_6_7I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA3_6_7I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R16Certificates (CA3_6_7I2R16CertificateIndex a)).input
lemma CA3_6_7I2R16P_check : ∀ a : PairSlot, contains (CA3_6_7I2R16Raw a) (CA3_6_7I2R16P a) = true := by
  decide +kernel
lemma CA3_6_7I2R16P_sound (a : PairSlot) :
    (CA3_6_7I2R16P a).Encloses (CA3_6_7I2R16Value a) :=
  contains_sound (CA3_6_7I2R16Raw_sound a) (CA3_6_7I2R16P_check a)
def CA3_6_7I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I2R16Certificates (CA3_6_7I2R16CertificateIndex a)).output
lemma CA3_6_7I2R16Terms_sound (a : PairSlot) :
    (CA3_6_7I2R16Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I2R16Certificates_valid
    (CA3_6_7I2R16CertificateIndex a) (CA3_6_7I2R16P_sound a)
def CA3_6_7I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R16Entropy_sound : CA3_6_7I2R16Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA3_6_7I2R16Value CA3_6_7I2R16Terms CA3_6_7I2R16Terms_sound) (by decide +kernel)
def CA3_6_7I2R16Mass : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R16Mass_sound : CA3_6_7I2R16Mass.Encloses (∑ a, CA3_6_7I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA3_6_7I2R16P CA3_6_7I2R16Value CA3_6_7I2R16P_sound) (by decide +kernel)
def CA3_6_7I2R16MassTerm : Ball := .exact 0
lemma CA3_6_7I2R16MassTerm_sound : CA3_6_7I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I2R16Value a))) :=
  entropyTerm_zero_ball (CA3_6_7I2R16Mass_sound)
def CA3_6_7I2R16H : Ball := ⟨0, 0⟩
lemma CA3_6_7I2R16H_sound : CA3_6_7I2R16H.Encloses (homogeneousEntropy CA3_6_7I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I2R16Value CA3_6_7I2R16MassTerm_sound CA3_6_7I2R16Entropy_sound) (by decide +kernel)
def CA3_6_7I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA3_6_7I2R0H
  | 1 => CA3_6_7I2R1H
  | 2 => CA3_6_7I2R2H
  | 3 => CA3_6_7I2R3H
  | 4 => CA3_6_7I2R4H
  | 5 => CA3_6_7I2R5H
  | 6 => CA3_6_7I2R6H
  | 7 => CA3_6_7I2R7H
  | 8 => CA3_6_7I2R8H
  | 9 => CA3_6_7I2R9H
  | 10 => CA3_6_7I2R10H
  | 11 => CA3_6_7I2R11H
  | 12 => CA3_6_7I2R12H
  | 13 => CA3_6_7I2R13H
  | 14 => CA3_6_7I2R14H
  | 15 => CA3_6_7I2R15H
  | 16 => CA3_6_7I2R16H
  | _ => (.exact 0)
lemma CA3_6_7I2ResidualEntropies_sound (k : Fin 17) :
    (CA3_6_7I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA3_6_7I2R0H_sound
  · exact CA3_6_7I2R1H_sound
  · exact CA3_6_7I2R2H_sound
  · exact CA3_6_7I2R3H_sound
  · exact CA3_6_7I2R4H_sound
  · exact CA3_6_7I2R5H_sound
  · exact CA3_6_7I2R6H_sound
  · exact CA3_6_7I2R7H_sound
  · exact CA3_6_7I2R8H_sound
  · exact CA3_6_7I2R9H_sound
  · exact CA3_6_7I2R10H_sound
  · exact CA3_6_7I2R11H_sound
  · exact CA3_6_7I2R12H_sound
  · exact CA3_6_7I2R13H_sound
  · exact CA3_6_7I2R14H_sound
  · exact CA3_6_7I2R15H_sound
  · exact CA3_6_7I2R16H_sound
def CA3_6_7I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 1, 0, 7 => Z1_0_7H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | _, _, _ => (.exact 0)
lemma CA3_6_7I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 6 7))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA3_6_7I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A3_6_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_1_7H2H_sound
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
  · exact Z0_6_2H2H_sound
  · exact Z1_0_7H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 1 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 2 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 3 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 4 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 5 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 1 6 1) by decide +kernel) hd |>.elim
  · exact Z2_0_6H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 2 6 0) by decide +kernel) hd |>.elim
  · exact Z3_0_5H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 1 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 2 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 3 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 4 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 3 5 0) by decide +kernel) hd |>.elim
def CA3_6_7I2Singleton : Ball := ⟨(2956785446459103303223532671727 / 25000000000000000000000000000000), (992338599 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I2Singleton_sound : CA3_6_7I2Singleton.Encloses
    (singletonEntropy (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA3_6_7I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A3_6_7Law_sound u) CA3_6_7I2Singles_sound) (by decide +kernel)
def CA3_6_7I2Group : Ball := ⟨(96556640056048354052402923374077 / 100000000000000000000000000000000), (39608863527 / 25000000000000000000000000000000)⟩
lemma CA3_6_7I2Group_sound : CA3_6_7I2Group.Encloses
    (groupedEntropy (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA3_6_7I2Singleton_sound
    (finSumBall_sound 17 CA3_6_7I2ResidualEntropies _ CA3_6_7I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA3_6_7I2H : Ball := ⟨(53605050537661449114373976696383 / 50000000000000000000000000000000), (455932049331 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I2_sound : CA3_6_7I2H.Encloses (stageACapacity (shape 3 6 7) 2) := by
  have hb := contains_sound (Ball.add_sound CA3_6_7I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA3_6_7I2Group_sound)))
    (show contains (.add CA3_6_7I2PairH (.neg (.mul (.exact 2) CA3_6_7I2Group))) CA3_6_7I2H = true by decide +kernel)
  unfold CA3_6_7I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
