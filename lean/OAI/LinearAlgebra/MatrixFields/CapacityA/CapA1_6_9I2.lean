import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA1_6_9I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_6_9I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA1_6_9I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA1_6_9I2R0Raw_sound (a : PairSlot) :
    (CA1_6_9I2R0Raw a).Encloses (CA1_6_9I2R0Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA1_6_9I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R0Certificates_valid :
    CA1_6_9I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R0Certificates (CA1_6_9I2R0CertificateIndex a)).input
lemma CA1_6_9I2R0P_check : ∀ a : PairSlot, contains (CA1_6_9I2R0Raw a) (CA1_6_9I2R0P a) = true := by
  decide +kernel
lemma CA1_6_9I2R0P_sound (a : PairSlot) :
    (CA1_6_9I2R0P a).Encloses (CA1_6_9I2R0Value a) :=
  contains_sound (CA1_6_9I2R0Raw_sound a) (CA1_6_9I2R0P_check a)
def CA1_6_9I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R0Certificates (CA1_6_9I2R0CertificateIndex a)).output
lemma CA1_6_9I2R0Terms_sound (a : PairSlot) :
    (CA1_6_9I2R0Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R0Certificates_valid
    (CA1_6_9I2R0CertificateIndex a) (CA1_6_9I2R0P_sound a)
def CA1_6_9I2R0Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R0Entropy_sound : CA1_6_9I2R0Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R0Value CA1_6_9I2R0Terms CA1_6_9I2R0Terms_sound) (by decide +kernel)
def CA1_6_9I2R0Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R0Mass_sound : CA1_6_9I2R0Mass.Encloses (∑ a, CA1_6_9I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R0P CA1_6_9I2R0Value CA1_6_9I2R0P_sound) (by decide +kernel)
def CA1_6_9I2R0MassTerm : Ball := .exact 0
lemma CA1_6_9I2R0MassTerm_sound : CA1_6_9I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R0Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R0Mass_sound)
def CA1_6_9I2R0H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R0H_sound : CA1_6_9I2R0H.Encloses (homogeneousEntropy CA1_6_9I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R0Value CA1_6_9I2R0MassTerm_sound CA1_6_9I2R0Entropy_sound) (by decide +kernel)
def CA1_6_9I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA1_6_9I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA1_6_9I2R1Raw_sound (a : PairSlot) :
    (CA1_6_9I2R1Raw a).Encloses (CA1_6_9I2R1Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA1_6_9I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15382325296305947711052937 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(175988165289010751885124581 / 20000000000000000000000000000000), (286661 / 100000000000000000000000000000000)⟩ ⟨(-715058362028310178292855577849303 / 50000000000000000000000000000000), (465869746267 / 100000000000000000000000000000000)⟩ ⟨-21, 15382325296305947711052937, 11920928955078125000000000⟩]
lemma CA1_6_9I2R1Certificates_valid :
    CA1_6_9I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_6_9I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R1Certificates (CA1_6_9I2R1CertificateIndex a)).input
lemma CA1_6_9I2R1P_check : ∀ a : PairSlot, contains (CA1_6_9I2R1Raw a) (CA1_6_9I2R1P a) = true := by
  decide +kernel
lemma CA1_6_9I2R1P_sound (a : PairSlot) :
    (CA1_6_9I2R1P a).Encloses (CA1_6_9I2R1Value a) :=
  contains_sound (CA1_6_9I2R1Raw_sound a) (CA1_6_9I2R1P_check a)
def CA1_6_9I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R1Certificates (CA1_6_9I2R1CertificateIndex a)).output
lemma CA1_6_9I2R1Terms_sound (a : PairSlot) :
    (CA1_6_9I2R1Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R1Certificates_valid
    (CA1_6_9I2R1CertificateIndex a) (CA1_6_9I2R1P_sound a)
def CA1_6_9I2R1Entropy : Ball := ⟨(175988165289010751885124581 / 10000000000000000000000000000000), (286661 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R1Entropy_sound : CA1_6_9I2R1Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R1Value CA1_6_9I2R1Terms CA1_6_9I2R1Terms_sound) (by decide +kernel)
def CA1_6_9I2R1Mass : Ball := ⟨(15382325296305947711052937 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R1Mass_sound : CA1_6_9I2R1Mass.Encloses (∑ a, CA1_6_9I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R1P CA1_6_9I2R1Value CA1_6_9I2R1P_sound) (by decide +kernel)
def CA1_6_9I2R1MassTermLogWitness : LogWitness := ⟨-20, 15382325296305947711052937, 11920928955078125000000000⟩
def CA1_6_9I2R1MassTermLog : Ball := ⟨(-340200501500156456410996990662069 / 25000000000000000000000000000000), (55586740323 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I2R1MassTermLog_sound : CA1_6_9I2R1MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R1Mass_sound) (w := CA1_6_9I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R1MassTerm : Ball := ⟨(1674583929613384375085323043 / 100000000000000000000000000000000), (273631 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R1MassTerm_sound : CA1_6_9I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R1Mass_sound) CA1_6_9I2R1MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R1H : Ball := ⟨(85297723276723143765922767 / 100000000000000000000000000000000), (140073 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I2R1H_sound : CA1_6_9I2R1H.Encloses (homogeneousEntropy CA1_6_9I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R1Value CA1_6_9I2R1MassTerm_sound CA1_6_9I2R1Entropy_sound) (by decide +kernel)
def CA1_6_9I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA1_6_9I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA1_6_9I2R2Raw_sound (a : PairSlot) :
    (CA1_6_9I2R2Raw a).Encloses (CA1_6_9I2R2Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA1_6_9I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1967664415920849334251689419 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(9077465887398263442569774983 / 10000000000000000000000000000000), (31250197 / 100000000000000000000000000000000)⟩ ⟨(-230666007220293473135349718557659 / 25000000000000000000000000000000), (317637365409 / 100000000000000000000000000000000)⟩ ⟨-14, 1967664415920849334251689419, 1220703125000000000000000000⟩,
   .log ⟨(236563311141533721982429851 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1677385714010515046244526493 / 12500000000000000000000000000000), (2254247 / 50000000000000000000000000000000)⟩ ⟨(-28362567397561494462781291018621 / 2500000000000000000000000000000), (381164910837 / 100000000000000000000000000000000)⟩ ⟨-17, 236563311141533721982429851, 152587890625000000000000000⟩,
   .log ⟨(37536856304181027501326567191 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(148037894805379859615916769287 / 50000000000000000000000000000000), (10333361 / 10000000000000000000000000000000)⟩ ⟨(-394380108994078757733136660996807 / 50000000000000000000000000000000), (275285710543 / 100000000000000000000000000000000)⟩ ⟨-12, 37536856304181027501326567191, 24414062500000000000000000000⟩]
lemma CA1_6_9I2R2Certificates_valid :
    CA1_6_9I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_6_9I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R2Certificates (CA1_6_9I2R2CertificateIndex a)).input
lemma CA1_6_9I2R2P_check : ∀ a : PairSlot, contains (CA1_6_9I2R2Raw a) (CA1_6_9I2R2P a) = true := by
  decide +kernel
lemma CA1_6_9I2R2P_sound (a : PairSlot) :
    (CA1_6_9I2R2P a).Encloses (CA1_6_9I2R2Value a) :=
  contains_sound (CA1_6_9I2R2Raw_sound a) (CA1_6_9I2R2P_check a)
def CA1_6_9I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R2Certificates (CA1_6_9I2R2CertificateIndex a)).output
lemma CA1_6_9I2R2Terms_sound (a : PairSlot) :
    (CA1_6_9I2R2Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R2Certificates_valid
    (CA1_6_9I2R2CertificateIndex a) (CA1_6_9I2R2P_sound a)
def CA1_6_9I2R2Entropy : Ball := ⟨(252231639391446614411570731061 / 50000000000000000000000000000000), (10928187 / 6250000000000000000000000000000)⟩
lemma CA1_6_9I2R2Entropy_sound : CA1_6_9I2R2Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R2Value CA1_6_9I2R2Terms CA1_6_9I2R2Terms_sound) (by decide +kernel)
def CA1_6_9I2R2Mass : Ball := ⟨(59579133574804858063667759891 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I2R2Mass_sound : CA1_6_9I2R2Mass.Encloses (∑ a, CA1_6_9I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R2P CA1_6_9I2R2Value CA1_6_9I2R2P_sound) (by decide +kernel)
def CA1_6_9I2R2MassTermLogWitness : LogWitness := ⟨-11, 59579133574804858063667759891, 48828125000000000000000000000⟩
def CA1_6_9I2R2MassTermLog : Ball := ⟨(-742562006000625825643988134828249 / 100000000000000000000000000000000), (254109892587 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R2MassTermLog_sound : CA1_6_9I2R2MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R2Mass_sound) (w := CA1_6_9I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R2MassTerm : Ball := ⟨(22120600471543166305970057429 / 5000000000000000000000000000000), (15139651 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I2R2MassTerm_sound : CA1_6_9I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R2Mass_sound) CA1_6_9I2R2MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R2H : Ball := ⟨(31025634676014951351870156771 / 50000000000000000000000000000000), (163123751 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R2H_sound : CA1_6_9I2R2H.Encloses (homogeneousEntropy CA1_6_9I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R2Value CA1_6_9I2R2MassTerm_sound CA1_6_9I2R2Entropy_sound) (by decide +kernel)
def CA1_6_9I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA1_6_9I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA1_6_9I2R3Raw_sound (a : PairSlot) :
    (CA1_6_9I2R3Raw a).Encloses (CA1_6_9I2R3Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA1_6_9I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(47639572620445901729347554581 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(45550944730904560016893522953 / 12500000000000000000000000000000), (8196559 / 6250000000000000000000000000000)⟩ ⟨(-382463084577337735485603822228969 / 50000000000000000000000000000000), (137642854989 / 50000000000000000000000000000000)⟩ ⟨-12, 47639572620445901729347554581, 24414062500000000000000000000⟩,
   .log ⟨(404985042186294983709925891827 / 25000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(3339329250362934946673635828707 / 50000000000000000000000000000000), (1200624877 / 50000000000000000000000000000000)⟩ ⟨(-103069524257479493504067476311811 / 25000000000000000000000000000000), (37057691553 / 25000000000000000000000000000000)⟩ ⟨-6, 404985042186294983709925891827, 390625000000000000000000000000⟩,
   .log ⟨(78457363860611206788924191831 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(15831771560782973034392613207 / 1562500000000000000000000000000), (365507863 / 100000000000000000000000000000000)⟩ ⟨(-645722294270706890661498213531627 / 100000000000000000000000000000000), (232934061787 / 100000000000000000000000000000000)⟩ ⟨-10, 78457363860611206788924191831, 48828125000000000000000000000⟩]
lemma CA1_6_9I2R3Certificates_valid :
    CA1_6_9I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_6_9I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R3Certificates (CA1_6_9I2R3CertificateIndex a)).input
lemma CA1_6_9I2R3P_check : ∀ a : PairSlot, contains (CA1_6_9I2R3Raw a) (CA1_6_9I2R3P a) = true := by
  decide +kernel
lemma CA1_6_9I2R3P_sound (a : PairSlot) :
    (CA1_6_9I2R3P a).Encloses (CA1_6_9I2R3Value a) :=
  contains_sound (CA1_6_9I2R3Raw_sound a) (CA1_6_9I2R3P_check a)
def CA1_6_9I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R3Certificates (CA1_6_9I2R3CertificateIndex a)).output
lemma CA1_6_9I2R3Terms_sound (a : PairSlot) :
    (CA1_6_9I2R3Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R3Certificates_valid
    (CA1_6_9I2R3CertificateIndex a) (CA1_6_9I2R3P_sound a)
def CA1_6_9I2R3Entropy : Ball := ⟨(4028149719231608323841773543143 / 25000000000000000000000000000000), (2897902561 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R3Entropy_sound : CA1_6_9I2R3Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R3Value CA1_6_9I2R3Terms CA1_6_9I2R3Terms_sound) (by decide +kernel)
def CA1_6_9I2R3Mass : Ball := ⟨(1824494469086848250146899505551 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
lemma CA1_6_9I2R3Mass_sound : CA1_6_9I2R3Mass.Encloses (∑ a, CA1_6_9I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R3P CA1_6_9I2R3Value CA1_6_9I2R3P_sound) (by decide +kernel)
def CA1_6_9I2R3MassTermLogWitness : LogWitness := ⟨-5, 1824494469086848250146899505551, 1562500000000000000000000000000⟩
def CA1_6_9I2R3MassTermLog : Ball := ⟨(-165536003000312912821994124701353 / 50000000000000000000000000000000), (25410988529 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I2R3MassTermLog_sound : CA1_6_9I2R3MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R3Mass_sound) (w := CA1_6_9I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R3MassTerm : Ball := ⟨(1208078087635259307639586179963 / 10000000000000000000000000000000), (463622087 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I2R3MassTerm_sound : CA1_6_9I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R3Mass_sound) CA1_6_9I2R3MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R3H : Ball := ⟨(2015909000286920109485616186471 / 50000000000000000000000000000000), (1304003249 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I2R3H_sound : CA1_6_9I2R3H.Encloses (homogeneousEntropy CA1_6_9I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R3Value CA1_6_9I2R3MassTerm_sound CA1_6_9I2R3Entropy_sound) (by decide +kernel)
def CA1_6_9I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA1_6_9I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA1_6_9I2R4Raw_sound (a : PairSlot) :
    (CA1_6_9I2R4Raw a).Encloses (CA1_6_9I2R4Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA1_6_9I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2430534116665658559357617653 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(48278512173544068138928239363 / 100000000000000000000000000000000), (257343 / 1562500000000000000000000000000)⟩ ⟨(-993166725011356917556399735208013 / 100000000000000000000000000000000), (338813199499 / 100000000000000000000000000000000)⟩ ⟨-15, 2430534116665658559357617653, 1525878906250000000000000000⟩,
   .log ⟨(962949217498128365494858418103 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(3803435256577646695635444709003 / 50000000000000000000000000000000), (2854774029 / 100000000000000000000000000000000)⟩ ⟨(-197488880382471427455807499445087 / 50000000000000000000000000000000), (37057691523 / 25000000000000000000000000000000)⟩ ⟨-6, 962949217498128365494858418103, 781250000000000000000000000000⟩,
   .log ⟨(4093220773158589283453798912321 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩ ⟨(32467430003058226294756699721411 / 100000000000000000000000000000000), (4333866083 / 25000000000000000000000000000000)⟩ ⟨(-39660003457380450449429580641009 / 25000000000000000000000000000000), (42351647417 / 50000000000000000000000000000000)⟩ ⟨-3, 4093220773158589283453798912321, 2500000000000000000000000000000⟩,
   .log ⟨(1061167029337240682905698619983 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(2411927025093196302256514455281 / 50000000000000000000000000000000), (359537377 / 20000000000000000000000000000000)⟩ ⟨(-227290045620771148198607657163703 / 50000000000000000000000000000000), (42351647413 / 25000000000000000000000000000000)⟩ ⟨-7, 1061167029337240682905698619983, 781250000000000000000000000000⟩,
   .log ⟨(1264315461666651412057543429 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(13383092011192096452737170241 / 50000000000000000000000000000000), (4551403 / 50000000000000000000000000000000)⟩ ⟨(-211704948914413794328644497200899 / 20000000000000000000000000000000), (179994521079 / 50000000000000000000000000000000)⟩ ⟨-16, 1264315461666651412057543429, 762939453125000000000000000⟩]
lemma CA1_6_9I2R4Certificates_valid :
    CA1_6_9I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_6_9I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R4Certificates (CA1_6_9I2R4CertificateIndex a)).input
lemma CA1_6_9I2R4P_check : ∀ a : PairSlot, contains (CA1_6_9I2R4Raw a) (CA1_6_9I2R4P a) = true := by
  decide +kernel
lemma CA1_6_9I2R4P_sound (a : PairSlot) :
    (CA1_6_9I2R4P a).Encloses (CA1_6_9I2R4Value a) :=
  contains_sound (CA1_6_9I2R4Raw_sound a) (CA1_6_9I2R4P_check a)
def CA1_6_9I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R4Certificates (CA1_6_9I2R4CertificateIndex a)).output
lemma CA1_6_9I2R4Terms_sound (a : PairSlot) :
    (CA1_6_9I2R4Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R4Certificates_valid
    (CA1_6_9I2R4CertificateIndex a) (CA1_6_9I2R4P_sound a)
def CA1_6_9I2R4Entropy : Ball := ⟨(11490440467622214123101573439551 / 20000000000000000000000000000000), (2668242887 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I2R4Entropy_sound : CA1_6_9I2R4Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R4Value CA1_6_9I2R4Terms CA1_6_9I2R4Terms_sound) (by decide +kernel)
def CA1_6_9I2R4Mass : Ball := ⟨(26452485561849937182121371031453 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
lemma CA1_6_9I2R4Mass_sound : CA1_6_9I2R4Mass.Encloses (∑ a, CA1_6_9I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R4P CA1_6_9I2R4Value CA1_6_9I2R4P_sound) (by decide +kernel)
def CA1_6_9I2R4MassTermLogWitness : LogWitness := ⟨-2, 26452485561849937182121371031453, 25000000000000000000000000000000⟩
def CA1_6_9I2R4MassTermLog : Ball := ⟨(-132982006000625825643988306689287 / 100000000000000000000000000000000), (79409339 / 125000000000000000000000000000)⟩
lemma CA1_6_9I2R4MassTermLog_sound : CA1_6_9I2R4MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R4Mass_sound) (w := CA1_6_9I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R4MassTerm : Ball := ⟨(7035409187434792722528646753737 / 20000000000000000000000000000000), (16804595201 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R4MassTerm_sound : CA1_6_9I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R4Mass_sound) CA1_6_9I2R4MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R4H : Ball := ⟨(2227515640093710700286463342907 / 10000000000000000000000000000000), (43487024071 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R4H_sound : CA1_6_9I2R4H.Encloses (homogeneousEntropy CA1_6_9I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R4Value CA1_6_9I2R4MassTerm_sound CA1_6_9I2R4Entropy_sound) (by decide +kernel)
def CA1_6_9I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA1_6_9I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA1_6_9I2R5Raw_sound (a : PairSlot) :
    (CA1_6_9I2R5Raw a).Encloses (CA1_6_9I2R5Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA1_6_9I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5230646719901306559878843 / 39062500000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(119421215364038691133498363387 / 100000000000000000000000000000000), (992439 / 2500000000000000000000000000000)⟩ ⟨(-178367665604676125594917184952803 / 20000000000000000000000000000000), (296461539029 / 100000000000000000000000000000000)⟩ ⟨-13, 5230646719901306559878843, 4768371582031250000000000⟩,
   .log ⟨(4446714786534358028185757328621 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩ ⟨(10760415824659170996692001674603 / 50000000000000000000000000000000), (4708142459 / 50000000000000000000000000000000)⟩ ⟨(-241985743210787991177003382232591 / 100000000000000000000000000000000), (105879118707 / 100000000000000000000000000000000)⟩ ⟨-4, 4446714786534358028185757328621, 3125000000000000000000000000000⟩,
   .log ⟨(82050376313928551286274993721 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(938541057060807284277361877919 / 50000000000000000000000000000000), (138998747 / 20000000000000000000000000000000)⟩ ⟨(-71491221249088608811744699231191 / 12500000000000000000000000000000), (211758237439 / 100000000000000000000000000000000)⟩ ⟨-9, 82050376313928551286274993721, 48828125000000000000000000000⟩]
lemma CA1_6_9I2R5Certificates_valid :
    CA1_6_9I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA1_6_9I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R5Certificates (CA1_6_9I2R5CertificateIndex a)).input
lemma CA1_6_9I2R5P_check : ∀ a : PairSlot, contains (CA1_6_9I2R5Raw a) (CA1_6_9I2R5P a) = true := by
  decide +kernel
lemma CA1_6_9I2R5P_sound (a : PairSlot) :
    (CA1_6_9I2R5P a).Encloses (CA1_6_9I2R5Value a) :=
  contains_sound (CA1_6_9I2R5Raw_sound a) (CA1_6_9I2R5P_check a)
def CA1_6_9I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R5Certificates (CA1_6_9I2R5CertificateIndex a)).output
lemma CA1_6_9I2R5Terms_sound (a : PairSlot) :
    (CA1_6_9I2R5Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R5Certificates_valid
    (CA1_6_9I2R5CertificateIndex a) (CA1_6_9I2R5P_sound a)
def CA1_6_9I2R5Entropy : Ball := ⟨(23517334978803995253072225468431 / 50000000000000000000000000000000), (10150976213 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R5Entropy_sound : CA1_6_9I2R5Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R5Value CA1_6_9I2R5Terms CA1_6_9I2R5Terms_sound) (by decide +kernel)
def CA1_6_9I2R5Mass : Ball := ⟨(4617510766963688803154952235103 / 25000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I2R5Mass_sound : CA1_6_9I2R5Mass.Encloses (∑ a, CA1_6_9I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R5P CA1_6_9I2R5Value CA1_6_9I2R5P_sound) (by decide +kernel)
def CA1_6_9I2R5MassTermLogWitness : LogWitness := ⟨-3, 4617510766963688803154952235103, 3125000000000000000000000000000⟩
def CA1_6_9I2R5MassTermLog : Ball := ⟨(-42225501500156456410997071898441 / 25000000000000000000000000000000), (16940659009 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I2R5MassTermLog_sound : CA1_6_9I2R5MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R5Mass_sound) (w := CA1_6_9I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R5MassTerm : Ball := ⟨(31196273250786212986478738546041 / 100000000000000000000000000000000), (15644735173 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R5MassTerm_sound : CA1_6_9I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R5Mass_sound) CA1_6_9I2R5MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R5H : Ball := ⟨(15838396706821777519665712390821 / 100000000000000000000000000000000), (35946687599 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R5H_sound : CA1_6_9I2R5H.Encloses (homogeneousEntropy CA1_6_9I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R5Value CA1_6_9I2R5MassTerm_sound CA1_6_9I2R5Entropy_sound) (by decide +kernel)
def CA1_6_9I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA1_6_9I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA1_6_9I2R6Raw_sound (a : PairSlot) :
    (CA1_6_9I2R6Raw a).Encloses (CA1_6_9I2R6Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA1_6_9I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6327170418027537211250852597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(28392940486801011288001427499 / 25000000000000000000000000000000), (37515263 / 100000000000000000000000000000000)⟩ ⟨(-179498503191272437656422737403447 / 20000000000000000000000000000000), (37057692433 / 12500000000000000000000000000000)⟩ ⟨-13, 6327170418027537211250852597, 6103515625000000000000000000⟩,
   .log ⟨(398636850457313655069073 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(7433476221723436291366273 / 50000000000000000000000000000000), (1187 / 25000000000000000000000000000000)⟩ ⟨(-932361899457588997304740056174253 / 50000000000000000000000000000000), (148262122641 / 25000000000000000000000000000000)⟩ ⟨-27, 398636850457313655069073, 372529029846191406250000⟩,
   .log ⟨(1326913022802868439058073980313 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩ ⟨(89614625494726809618503117817 / 1562500000000000000000000000000), (449575627 / 20000000000000000000000000000000)⟩ ⟨(-432231497701909322046546714671963 / 100000000000000000000000000000000), (169406589991 / 100000000000000000000000000000000)⟩ ⟨-7, 1326913022802868439058073980313, 781250000000000000000000000000⟩]
lemma CA1_6_9I2R6Certificates_valid :
    CA1_6_9I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA1_6_9I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R6Certificates (CA1_6_9I2R6CertificateIndex a)).input
lemma CA1_6_9I2R6P_check : ∀ a : PairSlot, contains (CA1_6_9I2R6Raw a) (CA1_6_9I2R6P a) = true := by
  decide +kernel
lemma CA1_6_9I2R6P_sound (a : PairSlot) :
    (CA1_6_9I2R6P a).Encloses (CA1_6_9I2R6Value a) :=
  contains_sound (CA1_6_9I2R6Raw_sound a) (CA1_6_9I2R6P_check a)
def CA1_6_9I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R6Certificates (CA1_6_9I2R6CertificateIndex a)).output
lemma CA1_6_9I2R6Terms_sound (a : PairSlot) :
    (CA1_6_9I2R6Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R6Certificates_valid
    (CA1_6_9I2R6CertificateIndex a) (CA1_6_9I2R6P_sound a)
def CA1_6_9I2R6Entropy : Ball := ⟨(1490627322365452699908344106343 / 25000000000000000000000000000000), (2322918157 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R6Entropy_sound : CA1_6_9I2R6Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R6Value CA1_6_9I2R6Terms CA1_6_9I2R6Terms_sound) (by decide +kernel)
def CA1_6_9I2R6Mass : Ball := ⟨(1352223299022380417157697666993 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R6Mass_sound : CA1_6_9I2R6Mass.Encloses (∑ a, CA1_6_9I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R6P CA1_6_9I2R6Value CA1_6_9I2R6P_sound) (by decide +kernel)
def CA1_6_9I2R6MassTermLogWitness : LogWitness := ⟨-7, 1352223299022380417157697666993, 781250000000000000000000000000⟩
def CA1_6_9I2R6MassTermLog : Ball := ⟨(-430342006000625825643988211212169 / 100000000000000000000000000000000), (169406590277 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R6MassTermLog_sound : CA1_6_9I2R6MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I2R6Mass_sound) (w := CA1_6_9I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I2R6MassTerm : Ball := ⟨(5819184870620752836316869770767 / 100000000000000000000000000000000), (286344429 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I2R6MassTerm_sound : CA1_6_9I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I2R6Mass_sound) CA1_6_9I2R6MassTermLog_sound) (by decide +kernel)
def CA1_6_9I2R6H : Ball := ⟨(28664883768211592663301330921 / 20000000000000000000000000000000), (4613673589 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2R6H_sound : CA1_6_9I2R6H.Encloses (homogeneousEntropy CA1_6_9I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R6Value CA1_6_9I2R6MassTerm_sound CA1_6_9I2R6Entropy_sound) (by decide +kernel)
def CA1_6_9I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA1_6_9I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA1_6_9I2R7Raw_sound (a : PairSlot) :
    (CA1_6_9I2R7Raw a).Encloses (CA1_6_9I2R7Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA1_6_9I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R7Certificates_valid :
    CA1_6_9I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R7Certificates (CA1_6_9I2R7CertificateIndex a)).input
lemma CA1_6_9I2R7P_check : ∀ a : PairSlot, contains (CA1_6_9I2R7Raw a) (CA1_6_9I2R7P a) = true := by
  decide +kernel
lemma CA1_6_9I2R7P_sound (a : PairSlot) :
    (CA1_6_9I2R7P a).Encloses (CA1_6_9I2R7Value a) :=
  contains_sound (CA1_6_9I2R7Raw_sound a) (CA1_6_9I2R7P_check a)
def CA1_6_9I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R7Certificates (CA1_6_9I2R7CertificateIndex a)).output
lemma CA1_6_9I2R7Terms_sound (a : PairSlot) :
    (CA1_6_9I2R7Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R7Certificates_valid
    (CA1_6_9I2R7CertificateIndex a) (CA1_6_9I2R7P_sound a)
def CA1_6_9I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R7Entropy_sound : CA1_6_9I2R7Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R7Value CA1_6_9I2R7Terms CA1_6_9I2R7Terms_sound) (by decide +kernel)
def CA1_6_9I2R7Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R7Mass_sound : CA1_6_9I2R7Mass.Encloses (∑ a, CA1_6_9I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R7P CA1_6_9I2R7Value CA1_6_9I2R7P_sound) (by decide +kernel)
def CA1_6_9I2R7MassTerm : Ball := .exact 0
lemma CA1_6_9I2R7MassTerm_sound : CA1_6_9I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R7Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R7Mass_sound)
def CA1_6_9I2R7H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R7H_sound : CA1_6_9I2R7H.Encloses (homogeneousEntropy CA1_6_9I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R7Value CA1_6_9I2R7MassTerm_sound CA1_6_9I2R7Entropy_sound) (by decide +kernel)
def CA1_6_9I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA1_6_9I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA1_6_9I2R8Raw_sound (a : PairSlot) :
    (CA1_6_9I2R8Raw a).Encloses (CA1_6_9I2R8Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA1_6_9I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R8Certificates_valid :
    CA1_6_9I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R8Certificates (CA1_6_9I2R8CertificateIndex a)).input
lemma CA1_6_9I2R8P_check : ∀ a : PairSlot, contains (CA1_6_9I2R8Raw a) (CA1_6_9I2R8P a) = true := by
  decide +kernel
lemma CA1_6_9I2R8P_sound (a : PairSlot) :
    (CA1_6_9I2R8P a).Encloses (CA1_6_9I2R8Value a) :=
  contains_sound (CA1_6_9I2R8Raw_sound a) (CA1_6_9I2R8P_check a)
def CA1_6_9I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R8Certificates (CA1_6_9I2R8CertificateIndex a)).output
lemma CA1_6_9I2R8Terms_sound (a : PairSlot) :
    (CA1_6_9I2R8Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R8Certificates_valid
    (CA1_6_9I2R8CertificateIndex a) (CA1_6_9I2R8P_sound a)
def CA1_6_9I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R8Entropy_sound : CA1_6_9I2R8Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R8Value CA1_6_9I2R8Terms CA1_6_9I2R8Terms_sound) (by decide +kernel)
def CA1_6_9I2R8Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R8Mass_sound : CA1_6_9I2R8Mass.Encloses (∑ a, CA1_6_9I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R8P CA1_6_9I2R8Value CA1_6_9I2R8P_sound) (by decide +kernel)
def CA1_6_9I2R8MassTerm : Ball := .exact 0
lemma CA1_6_9I2R8MassTerm_sound : CA1_6_9I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R8Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R8Mass_sound)
def CA1_6_9I2R8H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R8H_sound : CA1_6_9I2R8H.Encloses (homogeneousEntropy CA1_6_9I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R8Value CA1_6_9I2R8MassTerm_sound CA1_6_9I2R8Entropy_sound) (by decide +kernel)
def CA1_6_9I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA1_6_9I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA1_6_9I2R9Raw_sound (a : PairSlot) :
    (CA1_6_9I2R9Raw a).Encloses (CA1_6_9I2R9Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA1_6_9I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R9Certificates_valid :
    CA1_6_9I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R9Certificates (CA1_6_9I2R9CertificateIndex a)).input
lemma CA1_6_9I2R9P_check : ∀ a : PairSlot, contains (CA1_6_9I2R9Raw a) (CA1_6_9I2R9P a) = true := by
  decide +kernel
lemma CA1_6_9I2R9P_sound (a : PairSlot) :
    (CA1_6_9I2R9P a).Encloses (CA1_6_9I2R9Value a) :=
  contains_sound (CA1_6_9I2R9Raw_sound a) (CA1_6_9I2R9P_check a)
def CA1_6_9I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R9Certificates (CA1_6_9I2R9CertificateIndex a)).output
lemma CA1_6_9I2R9Terms_sound (a : PairSlot) :
    (CA1_6_9I2R9Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R9Certificates_valid
    (CA1_6_9I2R9CertificateIndex a) (CA1_6_9I2R9P_sound a)
def CA1_6_9I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R9Entropy_sound : CA1_6_9I2R9Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R9Value CA1_6_9I2R9Terms CA1_6_9I2R9Terms_sound) (by decide +kernel)
def CA1_6_9I2R9Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R9Mass_sound : CA1_6_9I2R9Mass.Encloses (∑ a, CA1_6_9I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R9P CA1_6_9I2R9Value CA1_6_9I2R9P_sound) (by decide +kernel)
def CA1_6_9I2R9MassTerm : Ball := .exact 0
lemma CA1_6_9I2R9MassTerm_sound : CA1_6_9I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R9Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R9Mass_sound)
def CA1_6_9I2R9H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R9H_sound : CA1_6_9I2R9H.Encloses (homogeneousEntropy CA1_6_9I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R9Value CA1_6_9I2R9MassTerm_sound CA1_6_9I2R9Entropy_sound) (by decide +kernel)
def CA1_6_9I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA1_6_9I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA1_6_9I2R10Raw_sound (a : PairSlot) :
    (CA1_6_9I2R10Raw a).Encloses (CA1_6_9I2R10Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA1_6_9I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R10Certificates_valid :
    CA1_6_9I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R10Certificates (CA1_6_9I2R10CertificateIndex a)).input
lemma CA1_6_9I2R10P_check : ∀ a : PairSlot, contains (CA1_6_9I2R10Raw a) (CA1_6_9I2R10P a) = true := by
  decide +kernel
lemma CA1_6_9I2R10P_sound (a : PairSlot) :
    (CA1_6_9I2R10P a).Encloses (CA1_6_9I2R10Value a) :=
  contains_sound (CA1_6_9I2R10Raw_sound a) (CA1_6_9I2R10P_check a)
def CA1_6_9I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R10Certificates (CA1_6_9I2R10CertificateIndex a)).output
lemma CA1_6_9I2R10Terms_sound (a : PairSlot) :
    (CA1_6_9I2R10Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R10Certificates_valid
    (CA1_6_9I2R10CertificateIndex a) (CA1_6_9I2R10P_sound a)
def CA1_6_9I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R10Entropy_sound : CA1_6_9I2R10Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R10Value CA1_6_9I2R10Terms CA1_6_9I2R10Terms_sound) (by decide +kernel)
def CA1_6_9I2R10Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R10Mass_sound : CA1_6_9I2R10Mass.Encloses (∑ a, CA1_6_9I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R10P CA1_6_9I2R10Value CA1_6_9I2R10P_sound) (by decide +kernel)
def CA1_6_9I2R10MassTerm : Ball := .exact 0
lemma CA1_6_9I2R10MassTerm_sound : CA1_6_9I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R10Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R10Mass_sound)
def CA1_6_9I2R10H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R10H_sound : CA1_6_9I2R10H.Encloses (homogeneousEntropy CA1_6_9I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R10Value CA1_6_9I2R10MassTerm_sound CA1_6_9I2R10Entropy_sound) (by decide +kernel)
def CA1_6_9I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA1_6_9I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA1_6_9I2R11Raw_sound (a : PairSlot) :
    (CA1_6_9I2R11Raw a).Encloses (CA1_6_9I2R11Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA1_6_9I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R11Certificates_valid :
    CA1_6_9I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R11Certificates (CA1_6_9I2R11CertificateIndex a)).input
lemma CA1_6_9I2R11P_check : ∀ a : PairSlot, contains (CA1_6_9I2R11Raw a) (CA1_6_9I2R11P a) = true := by
  decide +kernel
lemma CA1_6_9I2R11P_sound (a : PairSlot) :
    (CA1_6_9I2R11P a).Encloses (CA1_6_9I2R11Value a) :=
  contains_sound (CA1_6_9I2R11Raw_sound a) (CA1_6_9I2R11P_check a)
def CA1_6_9I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R11Certificates (CA1_6_9I2R11CertificateIndex a)).output
lemma CA1_6_9I2R11Terms_sound (a : PairSlot) :
    (CA1_6_9I2R11Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R11Certificates_valid
    (CA1_6_9I2R11CertificateIndex a) (CA1_6_9I2R11P_sound a)
def CA1_6_9I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R11Entropy_sound : CA1_6_9I2R11Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R11Value CA1_6_9I2R11Terms CA1_6_9I2R11Terms_sound) (by decide +kernel)
def CA1_6_9I2R11Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R11Mass_sound : CA1_6_9I2R11Mass.Encloses (∑ a, CA1_6_9I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R11P CA1_6_9I2R11Value CA1_6_9I2R11P_sound) (by decide +kernel)
def CA1_6_9I2R11MassTerm : Ball := .exact 0
lemma CA1_6_9I2R11MassTerm_sound : CA1_6_9I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R11Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R11Mass_sound)
def CA1_6_9I2R11H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R11H_sound : CA1_6_9I2R11H.Encloses (homogeneousEntropy CA1_6_9I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R11Value CA1_6_9I2R11MassTerm_sound CA1_6_9I2R11Entropy_sound) (by decide +kernel)
def CA1_6_9I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA1_6_9I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA1_6_9I2R12Raw_sound (a : PairSlot) :
    (CA1_6_9I2R12Raw a).Encloses (CA1_6_9I2R12Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA1_6_9I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R12Certificates_valid :
    CA1_6_9I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R12Certificates (CA1_6_9I2R12CertificateIndex a)).input
lemma CA1_6_9I2R12P_check : ∀ a : PairSlot, contains (CA1_6_9I2R12Raw a) (CA1_6_9I2R12P a) = true := by
  decide +kernel
lemma CA1_6_9I2R12P_sound (a : PairSlot) :
    (CA1_6_9I2R12P a).Encloses (CA1_6_9I2R12Value a) :=
  contains_sound (CA1_6_9I2R12Raw_sound a) (CA1_6_9I2R12P_check a)
def CA1_6_9I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R12Certificates (CA1_6_9I2R12CertificateIndex a)).output
lemma CA1_6_9I2R12Terms_sound (a : PairSlot) :
    (CA1_6_9I2R12Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R12Certificates_valid
    (CA1_6_9I2R12CertificateIndex a) (CA1_6_9I2R12P_sound a)
def CA1_6_9I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R12Entropy_sound : CA1_6_9I2R12Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R12Value CA1_6_9I2R12Terms CA1_6_9I2R12Terms_sound) (by decide +kernel)
def CA1_6_9I2R12Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R12Mass_sound : CA1_6_9I2R12Mass.Encloses (∑ a, CA1_6_9I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R12P CA1_6_9I2R12Value CA1_6_9I2R12P_sound) (by decide +kernel)
def CA1_6_9I2R12MassTerm : Ball := .exact 0
lemma CA1_6_9I2R12MassTerm_sound : CA1_6_9I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R12Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R12Mass_sound)
def CA1_6_9I2R12H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R12H_sound : CA1_6_9I2R12H.Encloses (homogeneousEntropy CA1_6_9I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R12Value CA1_6_9I2R12MassTerm_sound CA1_6_9I2R12Entropy_sound) (by decide +kernel)
def CA1_6_9I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA1_6_9I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA1_6_9I2R13Raw_sound (a : PairSlot) :
    (CA1_6_9I2R13Raw a).Encloses (CA1_6_9I2R13Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA1_6_9I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R13Certificates_valid :
    CA1_6_9I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R13Certificates (CA1_6_9I2R13CertificateIndex a)).input
lemma CA1_6_9I2R13P_check : ∀ a : PairSlot, contains (CA1_6_9I2R13Raw a) (CA1_6_9I2R13P a) = true := by
  decide +kernel
lemma CA1_6_9I2R13P_sound (a : PairSlot) :
    (CA1_6_9I2R13P a).Encloses (CA1_6_9I2R13Value a) :=
  contains_sound (CA1_6_9I2R13Raw_sound a) (CA1_6_9I2R13P_check a)
def CA1_6_9I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R13Certificates (CA1_6_9I2R13CertificateIndex a)).output
lemma CA1_6_9I2R13Terms_sound (a : PairSlot) :
    (CA1_6_9I2R13Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R13Certificates_valid
    (CA1_6_9I2R13CertificateIndex a) (CA1_6_9I2R13P_sound a)
def CA1_6_9I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R13Entropy_sound : CA1_6_9I2R13Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R13Value CA1_6_9I2R13Terms CA1_6_9I2R13Terms_sound) (by decide +kernel)
def CA1_6_9I2R13Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R13Mass_sound : CA1_6_9I2R13Mass.Encloses (∑ a, CA1_6_9I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R13P CA1_6_9I2R13Value CA1_6_9I2R13P_sound) (by decide +kernel)
def CA1_6_9I2R13MassTerm : Ball := .exact 0
lemma CA1_6_9I2R13MassTerm_sound : CA1_6_9I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R13Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R13Mass_sound)
def CA1_6_9I2R13H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R13H_sound : CA1_6_9I2R13H.Encloses (homogeneousEntropy CA1_6_9I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R13Value CA1_6_9I2R13MassTerm_sound CA1_6_9I2R13Entropy_sound) (by decide +kernel)
def CA1_6_9I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA1_6_9I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA1_6_9I2R14Raw_sound (a : PairSlot) :
    (CA1_6_9I2R14Raw a).Encloses (CA1_6_9I2R14Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA1_6_9I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R14Certificates_valid :
    CA1_6_9I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R14Certificates (CA1_6_9I2R14CertificateIndex a)).input
lemma CA1_6_9I2R14P_check : ∀ a : PairSlot, contains (CA1_6_9I2R14Raw a) (CA1_6_9I2R14P a) = true := by
  decide +kernel
lemma CA1_6_9I2R14P_sound (a : PairSlot) :
    (CA1_6_9I2R14P a).Encloses (CA1_6_9I2R14Value a) :=
  contains_sound (CA1_6_9I2R14Raw_sound a) (CA1_6_9I2R14P_check a)
def CA1_6_9I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R14Certificates (CA1_6_9I2R14CertificateIndex a)).output
lemma CA1_6_9I2R14Terms_sound (a : PairSlot) :
    (CA1_6_9I2R14Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R14Certificates_valid
    (CA1_6_9I2R14CertificateIndex a) (CA1_6_9I2R14P_sound a)
def CA1_6_9I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R14Entropy_sound : CA1_6_9I2R14Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R14Value CA1_6_9I2R14Terms CA1_6_9I2R14Terms_sound) (by decide +kernel)
def CA1_6_9I2R14Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R14Mass_sound : CA1_6_9I2R14Mass.Encloses (∑ a, CA1_6_9I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R14P CA1_6_9I2R14Value CA1_6_9I2R14P_sound) (by decide +kernel)
def CA1_6_9I2R14MassTerm : Ball := .exact 0
lemma CA1_6_9I2R14MassTerm_sound : CA1_6_9I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R14Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R14Mass_sound)
def CA1_6_9I2R14H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R14H_sound : CA1_6_9I2R14H.Encloses (homogeneousEntropy CA1_6_9I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R14Value CA1_6_9I2R14MassTerm_sound CA1_6_9I2R14Entropy_sound) (by decide +kernel)
def CA1_6_9I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA1_6_9I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA1_6_9I2R15Raw_sound (a : PairSlot) :
    (CA1_6_9I2R15Raw a).Encloses (CA1_6_9I2R15Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA1_6_9I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R15Certificates_valid :
    CA1_6_9I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R15Certificates (CA1_6_9I2R15CertificateIndex a)).input
lemma CA1_6_9I2R15P_check : ∀ a : PairSlot, contains (CA1_6_9I2R15Raw a) (CA1_6_9I2R15P a) = true := by
  decide +kernel
lemma CA1_6_9I2R15P_sound (a : PairSlot) :
    (CA1_6_9I2R15P a).Encloses (CA1_6_9I2R15Value a) :=
  contains_sound (CA1_6_9I2R15Raw_sound a) (CA1_6_9I2R15P_check a)
def CA1_6_9I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R15Certificates (CA1_6_9I2R15CertificateIndex a)).output
lemma CA1_6_9I2R15Terms_sound (a : PairSlot) :
    (CA1_6_9I2R15Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R15Certificates_valid
    (CA1_6_9I2R15CertificateIndex a) (CA1_6_9I2R15P_sound a)
def CA1_6_9I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R15Entropy_sound : CA1_6_9I2R15Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R15Value CA1_6_9I2R15Terms CA1_6_9I2R15Terms_sound) (by decide +kernel)
def CA1_6_9I2R15Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R15Mass_sound : CA1_6_9I2R15Mass.Encloses (∑ a, CA1_6_9I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R15P CA1_6_9I2R15Value CA1_6_9I2R15P_sound) (by decide +kernel)
def CA1_6_9I2R15MassTerm : Ball := .exact 0
lemma CA1_6_9I2R15MassTerm_sound : CA1_6_9I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R15Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R15Mass_sound)
def CA1_6_9I2R15H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R15H_sound : CA1_6_9I2R15H.Encloses (homogeneousEntropy CA1_6_9I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R15Value CA1_6_9I2R15MassTerm_sound CA1_6_9I2R15Entropy_sound) (by decide +kernel)
def CA1_6_9I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA1_6_9I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA1_6_9I2R16Raw_sound (a : PairSlot) :
    (CA1_6_9I2R16Raw a).Encloses (CA1_6_9I2R16Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA1_6_9I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I2R16Certificates_valid :
    CA1_6_9I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R16Certificates (CA1_6_9I2R16CertificateIndex a)).input
lemma CA1_6_9I2R16P_check : ∀ a : PairSlot, contains (CA1_6_9I2R16Raw a) (CA1_6_9I2R16P a) = true := by
  decide +kernel
lemma CA1_6_9I2R16P_sound (a : PairSlot) :
    (CA1_6_9I2R16P a).Encloses (CA1_6_9I2R16Value a) :=
  contains_sound (CA1_6_9I2R16Raw_sound a) (CA1_6_9I2R16P_check a)
def CA1_6_9I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I2R16Certificates (CA1_6_9I2R16CertificateIndex a)).output
lemma CA1_6_9I2R16Terms_sound (a : PairSlot) :
    (CA1_6_9I2R16Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I2R16Certificates_valid
    (CA1_6_9I2R16CertificateIndex a) (CA1_6_9I2R16P_sound a)
def CA1_6_9I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R16Entropy_sound : CA1_6_9I2R16Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I2R16Value CA1_6_9I2R16Terms CA1_6_9I2R16Terms_sound) (by decide +kernel)
def CA1_6_9I2R16Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R16Mass_sound : CA1_6_9I2R16Mass.Encloses (∑ a, CA1_6_9I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I2R16P CA1_6_9I2R16Value CA1_6_9I2R16P_sound) (by decide +kernel)
def CA1_6_9I2R16MassTerm : Ball := .exact 0
lemma CA1_6_9I2R16MassTerm_sound : CA1_6_9I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I2R16Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I2R16Mass_sound)
def CA1_6_9I2R16H : Ball := ⟨0, 0⟩
lemma CA1_6_9I2R16H_sound : CA1_6_9I2R16H.Encloses (homogeneousEntropy CA1_6_9I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I2R16Value CA1_6_9I2R16MassTerm_sound CA1_6_9I2R16Entropy_sound) (by decide +kernel)
def CA1_6_9I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_6_9I2R0H
  | 1 => CA1_6_9I2R1H
  | 2 => CA1_6_9I2R2H
  | 3 => CA1_6_9I2R3H
  | 4 => CA1_6_9I2R4H
  | 5 => CA1_6_9I2R5H
  | 6 => CA1_6_9I2R6H
  | 7 => CA1_6_9I2R7H
  | 8 => CA1_6_9I2R8H
  | 9 => CA1_6_9I2R9H
  | 10 => CA1_6_9I2R10H
  | 11 => CA1_6_9I2R11H
  | 12 => CA1_6_9I2R12H
  | 13 => CA1_6_9I2R13H
  | 14 => CA1_6_9I2R14H
  | 15 => CA1_6_9I2R15H
  | 16 => CA1_6_9I2R16H
  | _ => (.exact 0)
lemma CA1_6_9I2ResidualEntropies_sound (k : Fin 17) :
    (CA1_6_9I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_6_9I2R0H_sound
  · exact CA1_6_9I2R1H_sound
  · exact CA1_6_9I2R2H_sound
  · exact CA1_6_9I2R3H_sound
  · exact CA1_6_9I2R4H_sound
  · exact CA1_6_9I2R5H_sound
  · exact CA1_6_9I2R6H_sound
  · exact CA1_6_9I2R7H_sound
  · exact CA1_6_9I2R8H_sound
  · exact CA1_6_9I2R9H_sound
  · exact CA1_6_9I2R10H_sound
  · exact CA1_6_9I2R11H_sound
  · exact CA1_6_9I2R12H_sound
  · exact CA1_6_9I2R13H_sound
  · exact CA1_6_9I2R14H_sound
  · exact CA1_6_9I2R15H_sound
  · exact CA1_6_9I2R16H_sound
def CA1_6_9I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8H2H
  | 0, 1, 7 => Z0_1_7H2H
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 0, 6, 2 => Z0_6_2H2H
  | 1, 0, 7 => Z1_0_7H2H
  | _, _, _ => (.exact 0)
lemma CA1_6_9I2Singles_sound (u : Shape) (hu : u ∈ below (shape 1 6 9))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA1_6_9I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A1_6_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8H2H_sound
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
def CA1_6_9I2Singleton : Ball := ⟨(29824973448744012139609014923727 / 50000000000000000000000000000000), (4955604441 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I2Singleton_sound : CA1_6_9I2Singleton.Encloses
    (singletonEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA1_6_9I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A1_6_9Law_sound u) CA1_6_9I2Singles_sound) (by decide +kernel)
def CA1_6_9I2Group : Ball := ⟨(102000778991737113609883620931201 / 100000000000000000000000000000000), (144362823747 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I2Group_sound : CA1_6_9I2Group.Encloses
    (groupedEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_6_9I2Singleton_sound
    (finSumBall_sound 17 CA1_6_9I2ResidualEntropies _ CA1_6_9I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_6_9I2H : Ball := ⟨(53639880102499874118198500923321 / 50000000000000000000000000000000), (86553573677 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I2_sound : CA1_6_9I2H.Encloses (stageACapacity (shape 1 6 9) 2) := by
  have hb := contains_sound (Ball.add_sound CA1_6_9I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_6_9I2Group_sound)))
    (show contains (.add CA1_6_9I2PairH (.neg (.mul (.exact 2) CA1_6_9I2Group))) CA1_6_9I2H = true by decide +kernel)
  unfold CA1_6_9I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
