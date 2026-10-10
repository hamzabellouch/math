import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA5_5_6I2Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA5_5_6I2R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 0 a
def CA5_5_6I2R0Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 0 a
lemma CA5_5_6I2R0Raw_sound (a : PairSlot) :
    (CA5_5_6I2R0Raw a).Encloses (CA5_5_6I2R0Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 0 a
def CA5_5_6I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(15575375530790721635899474223 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(68276483212391443391781487719 / 50000000000000000000000000000000), (46175027 / 100000000000000000000000000000000)⟩ ⟨(-87672342894611700539772651333191 / 10000000000000000000000000000000), (296461550823 / 100000000000000000000000000000000)⟩ ⟨-13, 15575375530790721635899474223, 12207031250000000000000000000⟩]
lemma CA5_5_6I2R0Certificates_valid :
    CA5_5_6I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA5_5_6I2R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R0Certificates (CA5_5_6I2R0CertificateIndex a)).input
lemma CA5_5_6I2R0P_check : ∀ a : PairSlot, contains (CA5_5_6I2R0Raw a) (CA5_5_6I2R0P a) = true := by
  decide +kernel
lemma CA5_5_6I2R0P_sound (a : PairSlot) :
    (CA5_5_6I2R0P a).Encloses (CA5_5_6I2R0Value a) :=
  contains_sound (CA5_5_6I2R0Raw_sound a) (CA5_5_6I2R0P_check a)
def CA5_5_6I2R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R0Certificates (CA5_5_6I2R0CertificateIndex a)).output
lemma CA5_5_6I2R0Terms_sound (a : PairSlot) :
    (CA5_5_6I2R0Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R0Certificates_valid
    (CA5_5_6I2R0CertificateIndex a) (CA5_5_6I2R0P_sound a)
def CA5_5_6I2R0Entropy : Ball := ⟨(68276483212391443391781487719 / 50000000000000000000000000000000), (46175027 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R0Entropy_sound : CA5_5_6I2R0Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R0Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R0Value CA5_5_6I2R0Terms CA5_5_6I2R0Terms_sound) (by decide +kernel)
def CA5_5_6I2R0Mass : Ball := ⟨(15575375530790721635899474223 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R0Mass_sound : CA5_5_6I2R0Mass.Encloses (∑ a, CA5_5_6I2R0Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R0P CA5_5_6I2R0Value CA5_5_6I2R0P_sound) (by decide +kernel)
def CA5_5_6I2R0MassTermLogWitness : LogWitness := ⟨-13, 15575375530790721635899474223, 12207031250000000000000000000⟩
def CA5_5_6I2R0MassTermLog : Ball := ⟨(-87672342894611700539772651333191 / 10000000000000000000000000000000), (296461550823 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R0MassTermLog_sound : CA5_5_6I2R0MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R0Mass_sound) (w := CA5_5_6I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R0MassTerm : Ball := ⟨(68276483212391443391781487719 / 50000000000000000000000000000000), (46175027 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R0MassTerm_sound : CA5_5_6I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R0Mass_sound) CA5_5_6I2R0MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R0H : Ball := ⟨0, (46175027 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R0H_sound : CA5_5_6I2R0H.Encloses (homogeneousEntropy CA5_5_6I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R0Value CA5_5_6I2R0MassTerm_sound CA5_5_6I2R0Entropy_sound) (by decide +kernel)
def CA5_5_6I2R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 1 a
def CA5_5_6I2R1Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 1 a
lemma CA5_5_6I2R1Raw_sound (a : PairSlot) :
    (CA5_5_6I2R1Raw a).Encloses (CA5_5_6I2R1Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 1 a
def CA5_5_6I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(135103909759799156335132177059 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(168793534463164199850227551857 / 5000000000000000000000000000000), (80463843 / 6250000000000000000000000000000)⟩ ⟨(-499744336824187333009094186636727 / 100000000000000000000000000000000), (190582413887 / 100000000000000000000000000000000)⟩ ⟨-8, 135103909759799156335132177059, 78125000000000000000000000000⟩]
lemma CA5_5_6I2R1Certificates_valid :
    CA5_5_6I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA5_5_6I2R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R1Certificates (CA5_5_6I2R1CertificateIndex a)).input
lemma CA5_5_6I2R1P_check : ∀ a : PairSlot, contains (CA5_5_6I2R1Raw a) (CA5_5_6I2R1P a) = true := by
  decide +kernel
lemma CA5_5_6I2R1P_sound (a : PairSlot) :
    (CA5_5_6I2R1P a).Encloses (CA5_5_6I2R1Value a) :=
  contains_sound (CA5_5_6I2R1Raw_sound a) (CA5_5_6I2R1P_check a)
def CA5_5_6I2R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R1Certificates (CA5_5_6I2R1CertificateIndex a)).output
lemma CA5_5_6I2R1Terms_sound (a : PairSlot) :
    (CA5_5_6I2R1Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R1Certificates_valid
    (CA5_5_6I2R1CertificateIndex a) (CA5_5_6I2R1P_sound a)
def CA5_5_6I2R1Entropy : Ball := ⟨(168793534463164199850227551857 / 2500000000000000000000000000000), (80463843 / 3125000000000000000000000000000)⟩
lemma CA5_5_6I2R1Entropy_sound : CA5_5_6I2R1Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R1Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R1Value CA5_5_6I2R1Terms CA5_5_6I2R1Terms_sound) (by decide +kernel)
def CA5_5_6I2R1Mass : Ball := ⟨(135103909759799156335132177059 / 10000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I2R1Mass_sound : CA5_5_6I2R1Mass.Encloses (∑ a, CA5_5_6I2R1Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R1P CA5_5_6I2R1Value CA5_5_6I2R1P_sound) (by decide +kernel)
def CA5_5_6I2R1MassTermLogWitness : LogWitness := ⟨-7, 135103909759799156335132177059, 78125000000000000000000000000⟩
def CA5_5_6I2R1MassTermLog : Ball := ⟨(-430429618768192802067370993586397 / 100000000000000000000000000000000), (42351647551 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I2R1MassTermLog_sound : CA5_5_6I2R1MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R1Mass_sound) (w := CA5_5_6I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R1MassTerm : Ball := ⟨(2907636218600133681334528422563 / 50000000000000000000000000000000), (2288749311 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R1MassTerm_sound : CA5_5_6I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R1Mass_sound) CA5_5_6I2R1MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R1H : Ball := ⟨(468234470663150315670022614577 / 50000000000000000000000000000000), (4863592287 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R1H_sound : CA5_5_6I2R1H.Encloses (homogeneousEntropy CA5_5_6I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R1Value CA5_5_6I2R1MassTerm_sound CA5_5_6I2R1Entropy_sound) (by decide +kernel)
def CA5_5_6I2R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 2 a
def CA5_5_6I2R2Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 2 a
lemma CA5_5_6I2R2Raw_sound (a : PairSlot) :
    (CA5_5_6I2R2Raw a).Encloses (CA5_5_6I2R2Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 2 a
def CA5_5_6I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3951118845839213081490416122221 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩ ⟨(6383371096603122616951384715983 / 50000000000000000000000000000000), (1255022967 / 25000000000000000000000000000000)⟩ ⟨(-80779284876804331676718801287667 / 25000000000000000000000000000000), (12705494273 / 10000000000000000000000000000000)⟩ ⟨-5, 3951118845839213081490416122221, 3125000000000000000000000000000⟩,
   .log ⟨(281558190561078073003273087287 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(1653474778941073973050826271497 / 100000000000000000000000000000000), (596222681 / 100000000000000000000000000000000)⟩ ⟨(-587258632272815276852410766544829 / 100000000000000000000000000000000), (42351647579 / 20000000000000000000000000000000)⟩ ⟨-9, 281558190561078073003273087287, 195312500000000000000000000000⟩,
   .log ⟨(722452624872225808991855817413 / 5000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩ ⟨(1747018090494493839300854826657 / 6250000000000000000000000000000), (2447764741 / 20000000000000000000000000000000)⟩ ⟨(-38690826893812712680788923223139 / 20000000000000000000000000000000), (2117582379 / 2500000000000000000000000000000)⟩ ⟨-3, 722452624872225808991855817413, 625000000000000000000000000000⟩]
lemma CA5_5_6I2R2Certificates_valid :
    CA5_5_6I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA5_5_6I2R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R2Certificates (CA5_5_6I2R2CertificateIndex a)).input
lemma CA5_5_6I2R2P_check : ∀ a : PairSlot, contains (CA5_5_6I2R2Raw a) (CA5_5_6I2R2P a) = true := by
  decide +kernel
lemma CA5_5_6I2R2P_sound (a : PairSlot) :
    (CA5_5_6I2R2P a).Encloses (CA5_5_6I2R2Value a) :=
  contains_sound (CA5_5_6I2R2Raw_sound a) (CA5_5_6I2R2P_check a)
def CA5_5_6I2R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R2Certificates (CA5_5_6I2R2CertificateIndex a)).output
lemma CA5_5_6I2R2Terms_sound (a : PairSlot) :
    (CA5_5_6I2R2Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R2Certificates_valid
    (CA5_5_6I2R2CertificateIndex a) (CA5_5_6I2R2P_sound a)
def CA5_5_6I2R2Entropy : Ball := ⟨(28396361696103269921360434316719 / 50000000000000000000000000000000), (23471452803 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R2Entropy_sound : CA5_5_6I2R2Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R2Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R2Value CA5_5_6I2R2Terms CA5_5_6I2R2Terms_sound) (by decide +kernel)
def CA5_5_6I2R2Mass : Ball := ⟨(5728601642561274622206123691819 / 25000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R2Mass_sound : CA5_5_6I2R2Mass.Encloses (∑ a, CA5_5_6I2R2Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R2P CA5_5_6I2R2Value CA5_5_6I2R2P_sound) (by decide +kernel)
def CA5_5_6I2R2MassTermLogWitness : LogWitness := ⟨-3, 5728601642561274622206123691819, 3125000000000000000000000000000⟩
def CA5_5_6I2R2MassTermLog : Ball := ⟨(-147340436536233278409874066759607 / 100000000000000000000000000000000), (84703295247 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R2MassTermLog_sound : CA5_5_6I2R2MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R2Mass_sound) (w := CA5_5_6I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R2MassTerm : Ball := ⟨(8440546667571611990464074052287 / 25000000000000000000000000000000), (9704628813 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R2MassTerm_sound : CA5_5_6I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R2Mass_sound) CA5_5_6I2R2MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R2H : Ball := ⟨(2303053672192009188086457242429 / 10000000000000000000000000000000), (42880710429 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R2H_sound : CA5_5_6I2R2H.Encloses (homogeneousEntropy CA5_5_6I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R2Value CA5_5_6I2R2MassTerm_sound CA5_5_6I2R2Entropy_sound) (by decide +kernel)
def CA5_5_6I2R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 3 a
def CA5_5_6I2R3Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 3 a
lemma CA5_5_6I2R3Raw_sound (a : PairSlot) :
    (CA5_5_6I2R3Raw a).Encloses (CA5_5_6I2R3Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 3 a
def CA5_5_6I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4218292811255398071967879579 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1686750574245760453707469062551 / 50000000000000000000000000000000), (321572977 / 25000000000000000000000000000000)⟩ ⟨(-249916057531780527769469189548311 / 50000000000000000000000000000000), (2977850217 / 1562500000000000000000000000000)⟩ ⟨-8, 4218292811255398071967879579, 2441406250000000000000000000⟩,
   .log ⟨(11910576392475085462818371511423 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩ ⟨(3417373592137605936813181049017 / 10000000000000000000000000000000), (10088650697 / 50000000000000000000000000000000)⟩ ⟨(-5738384910232637840030721913069 / 4000000000000000000000000000000), (3388131799 / 4000000000000000000000000000000)⟩ ⟨-3, 11910576392475085462818371511423, 6250000000000000000000000000000⟩,
   .log ⟨(596096822416447657692314672391 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(5280672936385669574238866191791 / 100000000000000000000000000000000), (1009827311 / 50000000000000000000000000000000)⟩ ⟨(-442937517682023788694542460294741 / 100000000000000000000000000000000), (169406589883 / 100000000000000000000000000000000)⟩ ⟨-7, 596096822416447657692314672391, 390625000000000000000000000000⟩]
lemma CA5_5_6I2R3Certificates_valid :
    CA5_5_6I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA5_5_6I2R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R3Certificates (CA5_5_6I2R3CertificateIndex a)).input
lemma CA5_5_6I2R3P_check : ∀ a : PairSlot, contains (CA5_5_6I2R3Raw a) (CA5_5_6I2R3P a) = true := by
  decide +kernel
lemma CA5_5_6I2R3P_sound (a : PairSlot) :
    (CA5_5_6I2R3P a).Encloses (CA5_5_6I2R3Value a) :=
  contains_sound (CA5_5_6I2R3Raw_sound a) (CA5_5_6I2R3P_check a)
def CA5_5_6I2R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R3Certificates (CA5_5_6I2R3CertificateIndex a)).output
lemma CA5_5_6I2R3Terms_sound (a : PairSlot) :
    (CA5_5_6I2R3Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R3Certificates_valid
    (CA5_5_6I2R3CertificateIndex a) (CA5_5_6I2R3P_sound a)
def CA5_5_6I2R3Entropy : Ball := ⟨(42827910006253249849785614807063 / 50000000000000000000000000000000), (5870811981 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I2R3Entropy_sound : CA5_5_6I2R3Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R3Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R3Value CA5_5_6I2R3Terms CA5_5_6I2R3Terms_sound) (by decide +kernel)
def CA5_5_6I2R3Mass : Ball := ⟨(6422068319895982483134058275067 / 12500000000000000000000000000000), (17 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I2R3Mass_sound : CA5_5_6I2R3Mass.Encloses (∑ a, CA5_5_6I2R3Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R3P CA5_5_6I2R3Value CA5_5_6I2R3P_sound) (by decide +kernel)
def CA5_5_6I2R3MassTermLogWitness : LogWitness := ⟨-1, 6422068319895982483134058275067, 6250000000000000000000000000000⟩
def CA5_5_6I2R3MassTermLog : Ball := ⟨(-66598841028332232150207658845161 / 100000000000000000000000000000000), (4235164763 / 10000000000000000000000000000000)⟩
lemma CA5_5_6I2R3MassTermLog_sound : CA5_5_6I2R3MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R3Mass_sound) (w := CA5_5_6I2R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R3MassTerm : Ball := ⟨(34216184568787296356545389408101 / 100000000000000000000000000000000), (10879407027 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R3MassTerm_sound : CA5_5_6I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R3Mass_sound) CA5_5_6I2R3MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R3H : Ball := ⟨(2057585417748768133721033608241 / 4000000000000000000000000000000), (34362654951 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R3H_sound : CA5_5_6I2R3H.Encloses (homogeneousEntropy CA5_5_6I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R3Value CA5_5_6I2R3MassTerm_sound CA5_5_6I2R3Entropy_sound) (by decide +kernel)
def CA5_5_6I2R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 4 a
def CA5_5_6I2R4Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 4 a
lemma CA5_5_6I2R4Raw_sound (a : PairSlot) :
    (CA5_5_6I2R4Raw a).Encloses (CA5_5_6I2R4Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 4 a
def CA5_5_6I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(4960161490237224639411177757 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(24581288476501505831839546427 / 50000000000000000000000000000000), (4201423 / 25000000000000000000000000000000)⟩ ⟨(-7929189732998271827579135213163 / 800000000000000000000000000000), (21175824943 / 6250000000000000000000000000000)⟩ ⟨-15, 4960161490237224639411177757, 3051757812500000000000000000⟩,
   .log ⟨(337922164090609540743223917433 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(6894747510716945775985992392651 / 100000000000000000000000000000000), (1252261557 / 50000000000000000000000000000000)⟩ ⟨(-204033598366403889138484168240683 / 50000000000000000000000000000000), (148230766431 / 100000000000000000000000000000000)⟩ ⟨-6, 337922164090609540743223917433, 312500000000000000000000000000⟩,
   .log ⟨(17515991896721353725343536815071 / 100000000000000000000000000000000), (77 / 100000000000000000000000000000000)⟩ ⟨(15256918511132685778460382634431 / 50000000000000000000000000000000), (14836622453 / 100000000000000000000000000000000)⟩ ⟨(-5443924686470538360330274896351 / 3125000000000000000000000000000), (84703295171 / 100000000000000000000000000000000)⟩ ⟨-3, 17515991896721353725343536815071, 12500000000000000000000000000000⟩,
   .log ⟨(806108168804297215259309824889 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(485751464616018194882233335333 / 12500000000000000000000000000000), (682800193 / 50000000000000000000000000000000)⟩ ⟨(-241035376349819092734654105203851 / 50000000000000000000000000000000), (169406590083 / 100000000000000000000000000000000)⟩ ⟨-7, 806108168804297215259309824889, 781250000000000000000000000000⟩,
   .log ⟨(8522171377249288492257505981 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(33069503641589594789331568149 / 10000000000000000000000000000000), (117301609 / 100000000000000000000000000000000)⟩ ⟨(-97010204846008031883965721999079 / 12500000000000000000000000000000), (11011428409 / 4000000000000000000000000000000)⟩ ⟨-12, 8522171377249288492257505981, 4882812500000000000000000000⟩]
lemma CA5_5_6I2R4Certificates_valid :
    CA5_5_6I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA5_5_6I2R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R4Certificates (CA5_5_6I2R4CertificateIndex a)).input
lemma CA5_5_6I2R4P_check : ∀ a : PairSlot, contains (CA5_5_6I2R4Raw a) (CA5_5_6I2R4P a) = true := by
  decide +kernel
lemma CA5_5_6I2R4P_sound (a : PairSlot) :
    (CA5_5_6I2R4P a).Encloses (CA5_5_6I2R4Value a) :=
  contains_sound (CA5_5_6I2R4Raw_sound a) (CA5_5_6I2R4P_check a)
def CA5_5_6I2R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R4Certificates (CA5_5_6I2R4CertificateIndex a)).output
lemma CA5_5_6I2R4Terms_sound (a : PairSlot) :
    (CA5_5_6I2R4Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R4Certificates_valid
    (CA5_5_6I2R4CertificateIndex a) (CA5_5_6I2R4P_sound a)
def CA5_5_6I2R4Entropy : Ball := ⟨(5250437566787745619822915728669 / 10000000000000000000000000000000), (11363891223 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R4Entropy_sound : CA5_5_6I2R4Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R4Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R4Value CA5_5_6I2R4Terms CA5_5_6I2R4Terms_sound) (by decide +kernel)
def CA5_5_6I2R4Mass : Ball := ⟨(11279980527551382227517252762299 / 50000000000000000000000000000000), (7 / 6250000000000000000000000000000)⟩
lemma CA5_5_6I2R4Mass_sound : CA5_5_6I2R4Mass.Encloses (∑ a, CA5_5_6I2R4Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R4P CA5_5_6I2R4Value CA5_5_6I2R4P_sound) (by decide +kernel)
def CA5_5_6I2R4MassTermLogWitness : LogWitness := ⟨-3, 11279980527551382227517252762299, 6250000000000000000000000000000⟩
def CA5_5_6I2R4MassTermLog : Ball := ⟨(-74449674282031453783921025571407 / 50000000000000000000000000000000), (21175823807 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I2R4MassTermLog_sound : CA5_5_6I2R4MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R4Mass_sound) (w := CA5_5_6I2R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R4MassTerm : Ball := ⟨(4198954380919288659638450314487 / 12500000000000000000000000000000), (19109030583 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R4MassTerm_sound : CA5_5_6I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R4Mass_sound) CA5_5_6I2R4MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R4H : Ball := ⟨(9456370310261573460560777385397 / 50000000000000000000000000000000), (41836813029 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R4H_sound : CA5_5_6I2R4H.Encloses (homogeneousEntropy CA5_5_6I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R4Value CA5_5_6I2R4MassTerm_sound CA5_5_6I2R4Entropy_sound) (by decide +kernel)
def CA5_5_6I2R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 5 a
def CA5_5_6I2R5Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 5 a
lemma CA5_5_6I2R5Raw_sound (a : PairSlot) :
    (CA5_5_6I2R5Raw a).Encloses (CA5_5_6I2R5Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 5 a
def CA5_5_6I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1004140529770394352762712983 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(11556445985644917048012031137 / 100000000000000000000000000000000), (956861 / 25000000000000000000000000000000)⟩ ⟨(-1150879348360473112736059622484469 / 100000000000000000000000000000000), (381164925881 / 100000000000000000000000000000000)⟩ ⟨-17, 1004140529770394352762712983, 762939453125000000000000000⟩,
   .log ⟨(591268702244544564569689056257 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(3033595660817007418639026556429 / 100000000000000000000000000000000), (563427093 / 50000000000000000000000000000000)⟩ ⟨(-513065489396111085148890990305593 / 100000000000000000000000000000000), (190582413823 / 100000000000000000000000000000000)⟩ ⟨-8, 591268702244544564569689056257, 390625000000000000000000000000⟩,
   .log ⟨(4437911231578676666863887363 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(46671868898246297818604784281 / 25000000000000000000000000000000), (16445877 / 25000000000000000000000000000000)⟩ ⟨(-84133037301233156853611154534429 / 10000000000000000000000000000000), (74115384017 / 25000000000000000000000000000000)⟩ ⟨-13, 4437911231578676666863887363, 2441406250000000000000000000⟩]
lemma CA5_5_6I2R5Certificates_valid :
    CA5_5_6I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 1 => 1
  | 4, 2 => 2
  | 4, 3 => 3
  | 2, 4 => 2
  | 3, 4 => 3
  | 1, 5 => 1
  | _, _ => 0
def CA5_5_6I2R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R5Certificates (CA5_5_6I2R5CertificateIndex a)).input
lemma CA5_5_6I2R5P_check : ∀ a : PairSlot, contains (CA5_5_6I2R5Raw a) (CA5_5_6I2R5P a) = true := by
  decide +kernel
lemma CA5_5_6I2R5P_sound (a : PairSlot) :
    (CA5_5_6I2R5P a).Encloses (CA5_5_6I2R5Value a) :=
  contains_sound (CA5_5_6I2R5Raw_sound a) (CA5_5_6I2R5P_check a)
def CA5_5_6I2R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R5Certificates (CA5_5_6I2R5CertificateIndex a)).output
lemma CA5_5_6I2R5Terms_sound (a : PairSlot) :
    (CA5_5_6I2R5Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R5Certificates_valid
    (CA5_5_6I2R5CertificateIndex a) (CA5_5_6I2R5P_sound a)
def CA5_5_6I2R5Entropy : Ball := ⟨(323183958239563752696145772469 / 5000000000000000000000000000000), (598232569 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I2R5Entropy_sound : CA5_5_6I2R5Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R5Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R5Value CA5_5_6I2R5Terms CA5_5_6I2R5Terms_sound) (by decide +kernel)
def CA5_5_6I2R5Mass : Ball := ⟨(122892479786441668451354241211 / 10000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
lemma CA5_5_6I2R5Mass_sound : CA5_5_6I2R5Mass.Encloses (∑ a, CA5_5_6I2R5Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R5P CA5_5_6I2R5Value CA5_5_6I2R5P_sound) (by decide +kernel)
def CA5_5_6I2R5MassTermLogWitness : LogWitness := ⟨-7, 122892479786441668451354241211, 78125000000000000000000000000⟩
def CA5_5_6I2R5MassTermLog : Ball := ⟨(-439903054697170788664264893857777 / 100000000000000000000000000000000), (4235164761 / 2500000000000000000000000000000)⟩
lemma CA5_5_6I2R5MassTermLog_sound : CA5_5_6I2R5MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R5Mass_sound) (w := CA5_5_6I2R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R5MassTerm : Ball := ⟨(540607772573660047982269508961 / 10000000000000000000000000000000), (2081879653 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R5MassTerm_sound : CA5_5_6I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R5Mass_sound) CA5_5_6I2R5MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R5H : Ball := ⟨(105760143905467457410022035977 / 10000000000000000000000000000000), (4474809929 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R5H_sound : CA5_5_6I2R5H.Encloses (homogeneousEntropy CA5_5_6I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R5Value CA5_5_6I2R5MassTerm_sound CA5_5_6I2R5Entropy_sound) (by decide +kernel)
def CA5_5_6I2R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 6 a
def CA5_5_6I2R6Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 6 a
lemma CA5_5_6I2R6Raw_sound (a : PairSlot) :
    (CA5_5_6I2R6Raw a).Encloses (CA5_5_6I2R6Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 6 a
def CA5_5_6I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(94926009128879850262804749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(329098577781607517737011613 / 25000000000000000000000000000000), (221123 / 50000000000000000000000000000000)⟩ ⟨(-1386758300708900602244217122892999 / 100000000000000000000000000000000), (232934587239 / 50000000000000000000000000000000)⟩ ⟨-21, 94926009128879850262804749, 47683715820312500000000000⟩,
   .log ⟨(1196143072037424471053 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(140785416607620007360333 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(-1176994791833858204285792444680329 / 50000000000000000000000000000000), (94734279593 / 12500000000000000000000000000000)⟩ ⟨-34, 4784572288149697884212, 4656612873077392578125⟩,
   .log ⟨(9953782606908316684892791569 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(45861918112041811093778610697 / 50000000000000000000000000000000), (31616953 / 100000000000000000000000000000000)⟩ ⟨(-230374320613611934002162538946137 / 25000000000000000000000000000000), (317637375337 / 100000000000000000000000000000000)⟩ ⟨-14, 9953782606908316684892791569, 6103515625000000000000000000⟩]
lemma CA5_5_6I2R6Certificates_valid :
    CA5_5_6I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 2 => 1
  | 5, 3 => 2
  | 4, 4 => 3
  | 2, 5 => 1
  | 3, 5 => 2
  | _, _ => 0
def CA5_5_6I2R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R6Certificates (CA5_5_6I2R6CertificateIndex a)).input
lemma CA5_5_6I2R6P_check : ∀ a : PairSlot, contains (CA5_5_6I2R6Raw a) (CA5_5_6I2R6P a) = true := by
  decide +kernel
lemma CA5_5_6I2R6P_sound (a : PairSlot) :
    (CA5_5_6I2R6P a).Encloses (CA5_5_6I2R6Value a) :=
  contains_sound (CA5_5_6I2R6Raw_sound a) (CA5_5_6I2R6P_check a)
def CA5_5_6I2R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R6Certificates (CA5_5_6I2R6CertificateIndex a)).output
lemma CA5_5_6I2R6Terms_sound (a : PairSlot) :
    (CA5_5_6I2R6Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R6Certificates_valid
    (CA5_5_6I2R6CertificateIndex a) (CA5_5_6I2R6P_sound a)
def CA5_5_6I2R6Entropy : Ball := ⟨(23589226604292424392367008741 / 25000000000000000000000000000000), (32501583 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R6Entropy_sound : CA5_5_6I2R6Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R6Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R6Value CA5_5_6I2R6Terms CA5_5_6I2R6Terms_sound) (by decide +kernel)
def CA5_5_6I2R6Mass : Ball := ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2R6Mass_sound : CA5_5_6I2R6Mass.Encloses (∑ a, CA5_5_6I2R6Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R6P CA5_5_6I2R6Value CA5_5_6I2R6P_sound) (by decide +kernel)
def CA5_5_6I2R6MassTermLogWitness : LogWitness := ⟨-14, 10143646586596796759663111597, 6103515625000000000000000000⟩
def CA5_5_6I2R6MassTermLog : Ball := ⟨(-919607790753164239606091652322159 / 100000000000000000000000000000000), (63527482879 / 20000000000000000000000000000000)⟩
lemma CA5_5_6I2R6MassTermLog_sound : CA5_5_6I2R6MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I2R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I2R6Mass_sound) (w := CA5_5_6I2R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I2R6MassTerm : Ball := ⟨(46640882138405778787300293759 / 50000000000000000000000000000000), (32220073 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2R6MassTerm_sound : CA5_5_6I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I2R6Mass_sound) CA5_5_6I2R6MassTermLog_sound) (by decide +kernel)
def CA5_5_6I2R6H : Ball := ⟨(537571070179069997433723723 / 50000000000000000000000000000000), (8090207 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I2R6H_sound : CA5_5_6I2R6H.Encloses (homogeneousEntropy CA5_5_6I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R6Value CA5_5_6I2R6MassTerm_sound CA5_5_6I2R6Entropy_sound) (by decide +kernel)
def CA5_5_6I2R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 7 a
def CA5_5_6I2R7Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 7 a
lemma CA5_5_6I2R7Raw_sound (a : PairSlot) :
    (CA5_5_6I2R7Raw a).Encloses (CA5_5_6I2R7Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 7 a
def CA5_5_6I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R7Certificates_valid :
    CA5_5_6I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R7Certificates (CA5_5_6I2R7CertificateIndex a)).input
lemma CA5_5_6I2R7P_check : ∀ a : PairSlot, contains (CA5_5_6I2R7Raw a) (CA5_5_6I2R7P a) = true := by
  decide +kernel
lemma CA5_5_6I2R7P_sound (a : PairSlot) :
    (CA5_5_6I2R7P a).Encloses (CA5_5_6I2R7Value a) :=
  contains_sound (CA5_5_6I2R7Raw_sound a) (CA5_5_6I2R7P_check a)
def CA5_5_6I2R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R7Certificates (CA5_5_6I2R7CertificateIndex a)).output
lemma CA5_5_6I2R7Terms_sound (a : PairSlot) :
    (CA5_5_6I2R7Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R7Certificates_valid
    (CA5_5_6I2R7CertificateIndex a) (CA5_5_6I2R7P_sound a)
def CA5_5_6I2R7Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R7Entropy_sound : CA5_5_6I2R7Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R7Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R7Value CA5_5_6I2R7Terms CA5_5_6I2R7Terms_sound) (by decide +kernel)
def CA5_5_6I2R7Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R7Mass_sound : CA5_5_6I2R7Mass.Encloses (∑ a, CA5_5_6I2R7Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R7P CA5_5_6I2R7Value CA5_5_6I2R7P_sound) (by decide +kernel)
def CA5_5_6I2R7MassTerm : Ball := .exact 0
lemma CA5_5_6I2R7MassTerm_sound : CA5_5_6I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R7Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R7Mass_sound)
def CA5_5_6I2R7H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R7H_sound : CA5_5_6I2R7H.Encloses (homogeneousEntropy CA5_5_6I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R7Value CA5_5_6I2R7MassTerm_sound CA5_5_6I2R7Entropy_sound) (by decide +kernel)
def CA5_5_6I2R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 8 a
def CA5_5_6I2R8Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 8 a
lemma CA5_5_6I2R8Raw_sound (a : PairSlot) :
    (CA5_5_6I2R8Raw a).Encloses (CA5_5_6I2R8Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 8 a
def CA5_5_6I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R8Certificates_valid :
    CA5_5_6I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R8Certificates (CA5_5_6I2R8CertificateIndex a)).input
lemma CA5_5_6I2R8P_check : ∀ a : PairSlot, contains (CA5_5_6I2R8Raw a) (CA5_5_6I2R8P a) = true := by
  decide +kernel
lemma CA5_5_6I2R8P_sound (a : PairSlot) :
    (CA5_5_6I2R8P a).Encloses (CA5_5_6I2R8Value a) :=
  contains_sound (CA5_5_6I2R8Raw_sound a) (CA5_5_6I2R8P_check a)
def CA5_5_6I2R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R8Certificates (CA5_5_6I2R8CertificateIndex a)).output
lemma CA5_5_6I2R8Terms_sound (a : PairSlot) :
    (CA5_5_6I2R8Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R8Certificates_valid
    (CA5_5_6I2R8CertificateIndex a) (CA5_5_6I2R8P_sound a)
def CA5_5_6I2R8Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R8Entropy_sound : CA5_5_6I2R8Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R8Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R8Value CA5_5_6I2R8Terms CA5_5_6I2R8Terms_sound) (by decide +kernel)
def CA5_5_6I2R8Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R8Mass_sound : CA5_5_6I2R8Mass.Encloses (∑ a, CA5_5_6I2R8Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R8P CA5_5_6I2R8Value CA5_5_6I2R8P_sound) (by decide +kernel)
def CA5_5_6I2R8MassTerm : Ball := .exact 0
lemma CA5_5_6I2R8MassTerm_sound : CA5_5_6I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R8Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R8Mass_sound)
def CA5_5_6I2R8H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R8H_sound : CA5_5_6I2R8H.Encloses (homogeneousEntropy CA5_5_6I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R8Value CA5_5_6I2R8MassTerm_sound CA5_5_6I2R8Entropy_sound) (by decide +kernel)
def CA5_5_6I2R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 9 a
def CA5_5_6I2R9Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 9 a
lemma CA5_5_6I2R9Raw_sound (a : PairSlot) :
    (CA5_5_6I2R9Raw a).Encloses (CA5_5_6I2R9Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 9 a
def CA5_5_6I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R9Certificates_valid :
    CA5_5_6I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R9Certificates (CA5_5_6I2R9CertificateIndex a)).input
lemma CA5_5_6I2R9P_check : ∀ a : PairSlot, contains (CA5_5_6I2R9Raw a) (CA5_5_6I2R9P a) = true := by
  decide +kernel
lemma CA5_5_6I2R9P_sound (a : PairSlot) :
    (CA5_5_6I2R9P a).Encloses (CA5_5_6I2R9Value a) :=
  contains_sound (CA5_5_6I2R9Raw_sound a) (CA5_5_6I2R9P_check a)
def CA5_5_6I2R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R9Certificates (CA5_5_6I2R9CertificateIndex a)).output
lemma CA5_5_6I2R9Terms_sound (a : PairSlot) :
    (CA5_5_6I2R9Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R9Certificates_valid
    (CA5_5_6I2R9CertificateIndex a) (CA5_5_6I2R9P_sound a)
def CA5_5_6I2R9Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R9Entropy_sound : CA5_5_6I2R9Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R9Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R9Value CA5_5_6I2R9Terms CA5_5_6I2R9Terms_sound) (by decide +kernel)
def CA5_5_6I2R9Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R9Mass_sound : CA5_5_6I2R9Mass.Encloses (∑ a, CA5_5_6I2R9Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R9P CA5_5_6I2R9Value CA5_5_6I2R9P_sound) (by decide +kernel)
def CA5_5_6I2R9MassTerm : Ball := .exact 0
lemma CA5_5_6I2R9MassTerm_sound : CA5_5_6I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R9Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R9Mass_sound)
def CA5_5_6I2R9H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R9H_sound : CA5_5_6I2R9H.Encloses (homogeneousEntropy CA5_5_6I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R9Value CA5_5_6I2R9MassTerm_sound CA5_5_6I2R9Entropy_sound) (by decide +kernel)
def CA5_5_6I2R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 10 a
def CA5_5_6I2R10Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 10 a
lemma CA5_5_6I2R10Raw_sound (a : PairSlot) :
    (CA5_5_6I2R10Raw a).Encloses (CA5_5_6I2R10Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 10 a
def CA5_5_6I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R10Certificates_valid :
    CA5_5_6I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R10Certificates (CA5_5_6I2R10CertificateIndex a)).input
lemma CA5_5_6I2R10P_check : ∀ a : PairSlot, contains (CA5_5_6I2R10Raw a) (CA5_5_6I2R10P a) = true := by
  decide +kernel
lemma CA5_5_6I2R10P_sound (a : PairSlot) :
    (CA5_5_6I2R10P a).Encloses (CA5_5_6I2R10Value a) :=
  contains_sound (CA5_5_6I2R10Raw_sound a) (CA5_5_6I2R10P_check a)
def CA5_5_6I2R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R10Certificates (CA5_5_6I2R10CertificateIndex a)).output
lemma CA5_5_6I2R10Terms_sound (a : PairSlot) :
    (CA5_5_6I2R10Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R10Certificates_valid
    (CA5_5_6I2R10CertificateIndex a) (CA5_5_6I2R10P_sound a)
def CA5_5_6I2R10Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R10Entropy_sound : CA5_5_6I2R10Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R10Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R10Value CA5_5_6I2R10Terms CA5_5_6I2R10Terms_sound) (by decide +kernel)
def CA5_5_6I2R10Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R10Mass_sound : CA5_5_6I2R10Mass.Encloses (∑ a, CA5_5_6I2R10Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R10P CA5_5_6I2R10Value CA5_5_6I2R10P_sound) (by decide +kernel)
def CA5_5_6I2R10MassTerm : Ball := .exact 0
lemma CA5_5_6I2R10MassTerm_sound : CA5_5_6I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R10Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R10Mass_sound)
def CA5_5_6I2R10H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R10H_sound : CA5_5_6I2R10H.Encloses (homogeneousEntropy CA5_5_6I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R10Value CA5_5_6I2R10MassTerm_sound CA5_5_6I2R10Entropy_sound) (by decide +kernel)
def CA5_5_6I2R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 11 a
def CA5_5_6I2R11Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 11 a
lemma CA5_5_6I2R11Raw_sound (a : PairSlot) :
    (CA5_5_6I2R11Raw a).Encloses (CA5_5_6I2R11Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 11 a
def CA5_5_6I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R11Certificates_valid :
    CA5_5_6I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R11Certificates (CA5_5_6I2R11CertificateIndex a)).input
lemma CA5_5_6I2R11P_check : ∀ a : PairSlot, contains (CA5_5_6I2R11Raw a) (CA5_5_6I2R11P a) = true := by
  decide +kernel
lemma CA5_5_6I2R11P_sound (a : PairSlot) :
    (CA5_5_6I2R11P a).Encloses (CA5_5_6I2R11Value a) :=
  contains_sound (CA5_5_6I2R11Raw_sound a) (CA5_5_6I2R11P_check a)
def CA5_5_6I2R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R11Certificates (CA5_5_6I2R11CertificateIndex a)).output
lemma CA5_5_6I2R11Terms_sound (a : PairSlot) :
    (CA5_5_6I2R11Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R11Certificates_valid
    (CA5_5_6I2R11CertificateIndex a) (CA5_5_6I2R11P_sound a)
def CA5_5_6I2R11Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R11Entropy_sound : CA5_5_6I2R11Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R11Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R11Value CA5_5_6I2R11Terms CA5_5_6I2R11Terms_sound) (by decide +kernel)
def CA5_5_6I2R11Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R11Mass_sound : CA5_5_6I2R11Mass.Encloses (∑ a, CA5_5_6I2R11Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R11P CA5_5_6I2R11Value CA5_5_6I2R11P_sound) (by decide +kernel)
def CA5_5_6I2R11MassTerm : Ball := .exact 0
lemma CA5_5_6I2R11MassTerm_sound : CA5_5_6I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R11Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R11Mass_sound)
def CA5_5_6I2R11H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R11H_sound : CA5_5_6I2R11H.Encloses (homogeneousEntropy CA5_5_6I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R11Value CA5_5_6I2R11MassTerm_sound CA5_5_6I2R11Entropy_sound) (by decide +kernel)
def CA5_5_6I2R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 12 a
def CA5_5_6I2R12Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 12 a
lemma CA5_5_6I2R12Raw_sound (a : PairSlot) :
    (CA5_5_6I2R12Raw a).Encloses (CA5_5_6I2R12Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 12 a
def CA5_5_6I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R12Certificates_valid :
    CA5_5_6I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R12Certificates (CA5_5_6I2R12CertificateIndex a)).input
lemma CA5_5_6I2R12P_check : ∀ a : PairSlot, contains (CA5_5_6I2R12Raw a) (CA5_5_6I2R12P a) = true := by
  decide +kernel
lemma CA5_5_6I2R12P_sound (a : PairSlot) :
    (CA5_5_6I2R12P a).Encloses (CA5_5_6I2R12Value a) :=
  contains_sound (CA5_5_6I2R12Raw_sound a) (CA5_5_6I2R12P_check a)
def CA5_5_6I2R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R12Certificates (CA5_5_6I2R12CertificateIndex a)).output
lemma CA5_5_6I2R12Terms_sound (a : PairSlot) :
    (CA5_5_6I2R12Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R12Certificates_valid
    (CA5_5_6I2R12CertificateIndex a) (CA5_5_6I2R12P_sound a)
def CA5_5_6I2R12Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R12Entropy_sound : CA5_5_6I2R12Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R12Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R12Value CA5_5_6I2R12Terms CA5_5_6I2R12Terms_sound) (by decide +kernel)
def CA5_5_6I2R12Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R12Mass_sound : CA5_5_6I2R12Mass.Encloses (∑ a, CA5_5_6I2R12Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R12P CA5_5_6I2R12Value CA5_5_6I2R12P_sound) (by decide +kernel)
def CA5_5_6I2R12MassTerm : Ball := .exact 0
lemma CA5_5_6I2R12MassTerm_sound : CA5_5_6I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R12Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R12Mass_sound)
def CA5_5_6I2R12H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R12H_sound : CA5_5_6I2R12H.Encloses (homogeneousEntropy CA5_5_6I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R12Value CA5_5_6I2R12MassTerm_sound CA5_5_6I2R12Entropy_sound) (by decide +kernel)
def CA5_5_6I2R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 13 a
def CA5_5_6I2R13Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 13 a
lemma CA5_5_6I2R13Raw_sound (a : PairSlot) :
    (CA5_5_6I2R13Raw a).Encloses (CA5_5_6I2R13Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 13 a
def CA5_5_6I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R13Certificates_valid :
    CA5_5_6I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R13Certificates (CA5_5_6I2R13CertificateIndex a)).input
lemma CA5_5_6I2R13P_check : ∀ a : PairSlot, contains (CA5_5_6I2R13Raw a) (CA5_5_6I2R13P a) = true := by
  decide +kernel
lemma CA5_5_6I2R13P_sound (a : PairSlot) :
    (CA5_5_6I2R13P a).Encloses (CA5_5_6I2R13Value a) :=
  contains_sound (CA5_5_6I2R13Raw_sound a) (CA5_5_6I2R13P_check a)
def CA5_5_6I2R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R13Certificates (CA5_5_6I2R13CertificateIndex a)).output
lemma CA5_5_6I2R13Terms_sound (a : PairSlot) :
    (CA5_5_6I2R13Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R13Certificates_valid
    (CA5_5_6I2R13CertificateIndex a) (CA5_5_6I2R13P_sound a)
def CA5_5_6I2R13Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R13Entropy_sound : CA5_5_6I2R13Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R13Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R13Value CA5_5_6I2R13Terms CA5_5_6I2R13Terms_sound) (by decide +kernel)
def CA5_5_6I2R13Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R13Mass_sound : CA5_5_6I2R13Mass.Encloses (∑ a, CA5_5_6I2R13Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R13P CA5_5_6I2R13Value CA5_5_6I2R13P_sound) (by decide +kernel)
def CA5_5_6I2R13MassTerm : Ball := .exact 0
lemma CA5_5_6I2R13MassTerm_sound : CA5_5_6I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R13Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R13Mass_sound)
def CA5_5_6I2R13H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R13H_sound : CA5_5_6I2R13H.Encloses (homogeneousEntropy CA5_5_6I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R13Value CA5_5_6I2R13MassTerm_sound CA5_5_6I2R13Entropy_sound) (by decide +kernel)
def CA5_5_6I2R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 14 a
def CA5_5_6I2R14Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 14 a
lemma CA5_5_6I2R14Raw_sound (a : PairSlot) :
    (CA5_5_6I2R14Raw a).Encloses (CA5_5_6I2R14Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 14 a
def CA5_5_6I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R14Certificates_valid :
    CA5_5_6I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R14Certificates (CA5_5_6I2R14CertificateIndex a)).input
lemma CA5_5_6I2R14P_check : ∀ a : PairSlot, contains (CA5_5_6I2R14Raw a) (CA5_5_6I2R14P a) = true := by
  decide +kernel
lemma CA5_5_6I2R14P_sound (a : PairSlot) :
    (CA5_5_6I2R14P a).Encloses (CA5_5_6I2R14Value a) :=
  contains_sound (CA5_5_6I2R14Raw_sound a) (CA5_5_6I2R14P_check a)
def CA5_5_6I2R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R14Certificates (CA5_5_6I2R14CertificateIndex a)).output
lemma CA5_5_6I2R14Terms_sound (a : PairSlot) :
    (CA5_5_6I2R14Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R14Certificates_valid
    (CA5_5_6I2R14CertificateIndex a) (CA5_5_6I2R14P_sound a)
def CA5_5_6I2R14Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R14Entropy_sound : CA5_5_6I2R14Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R14Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R14Value CA5_5_6I2R14Terms CA5_5_6I2R14Terms_sound) (by decide +kernel)
def CA5_5_6I2R14Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R14Mass_sound : CA5_5_6I2R14Mass.Encloses (∑ a, CA5_5_6I2R14Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R14P CA5_5_6I2R14Value CA5_5_6I2R14P_sound) (by decide +kernel)
def CA5_5_6I2R14MassTerm : Ball := .exact 0
lemma CA5_5_6I2R14MassTerm_sound : CA5_5_6I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R14Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R14Mass_sound)
def CA5_5_6I2R14H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R14H_sound : CA5_5_6I2R14H.Encloses (homogeneousEntropy CA5_5_6I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R14Value CA5_5_6I2R14MassTerm_sound CA5_5_6I2R14Entropy_sound) (by decide +kernel)
def CA5_5_6I2R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 15 a
def CA5_5_6I2R15Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 15 a
lemma CA5_5_6I2R15Raw_sound (a : PairSlot) :
    (CA5_5_6I2R15Raw a).Encloses (CA5_5_6I2R15Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 15 a
def CA5_5_6I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R15Certificates_valid :
    CA5_5_6I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R15Certificates (CA5_5_6I2R15CertificateIndex a)).input
lemma CA5_5_6I2R15P_check : ∀ a : PairSlot, contains (CA5_5_6I2R15Raw a) (CA5_5_6I2R15P a) = true := by
  decide +kernel
lemma CA5_5_6I2R15P_sound (a : PairSlot) :
    (CA5_5_6I2R15P a).Encloses (CA5_5_6I2R15Value a) :=
  contains_sound (CA5_5_6I2R15Raw_sound a) (CA5_5_6I2R15P_check a)
def CA5_5_6I2R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R15Certificates (CA5_5_6I2R15CertificateIndex a)).output
lemma CA5_5_6I2R15Terms_sound (a : PairSlot) :
    (CA5_5_6I2R15Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R15Certificates_valid
    (CA5_5_6I2R15CertificateIndex a) (CA5_5_6I2R15P_sound a)
def CA5_5_6I2R15Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R15Entropy_sound : CA5_5_6I2R15Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R15Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R15Value CA5_5_6I2R15Terms CA5_5_6I2R15Terms_sound) (by decide +kernel)
def CA5_5_6I2R15Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R15Mass_sound : CA5_5_6I2R15Mass.Encloses (∑ a, CA5_5_6I2R15Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R15P CA5_5_6I2R15Value CA5_5_6I2R15P_sound) (by decide +kernel)
def CA5_5_6I2R15MassTerm : Ball := .exact 0
lemma CA5_5_6I2R15MassTerm_sound : CA5_5_6I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R15Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R15Mass_sound)
def CA5_5_6I2R15H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R15H_sound : CA5_5_6I2R15H.Encloses (homogeneousEntropy CA5_5_6I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R15Value CA5_5_6I2R15MassTerm_sound CA5_5_6I2R15Entropy_sound) (by decide +kernel)
def CA5_5_6I2R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) 16 a
def CA5_5_6I2R16Raw (a : PairSlot) : Ball := residualBall (below (shape 5 5 6)) A5_5_6Law (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) 16 a
lemma CA5_5_6I2R16Raw_sound (a : PairSlot) :
    (CA5_5_6I2R16Raw a).Encloses (CA5_5_6I2R16Value a) := by
  exact residualBall_sound_on (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u => halfTable u ((Equiv.refl (Fin 3)) 2)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 5 5 6) (show (shape 5 5 6) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 2) a) 16 a
def CA5_5_6I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA5_5_6I2R16Certificates_valid :
    CA5_5_6I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I2R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA5_5_6I2R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R16Certificates (CA5_5_6I2R16CertificateIndex a)).input
lemma CA5_5_6I2R16P_check : ∀ a : PairSlot, contains (CA5_5_6I2R16Raw a) (CA5_5_6I2R16P a) = true := by
  decide +kernel
lemma CA5_5_6I2R16P_sound (a : PairSlot) :
    (CA5_5_6I2R16P a).Encloses (CA5_5_6I2R16Value a) :=
  contains_sound (CA5_5_6I2R16Raw_sound a) (CA5_5_6I2R16P_check a)
def CA5_5_6I2R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I2R16Certificates (CA5_5_6I2R16CertificateIndex a)).output
lemma CA5_5_6I2R16Terms_sound (a : PairSlot) :
    (CA5_5_6I2R16Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I2R16Certificates_valid
    (CA5_5_6I2R16CertificateIndex a) (CA5_5_6I2R16P_sound a)
def CA5_5_6I2R16Entropy : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R16Entropy_sound : CA5_5_6I2R16Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I2R16Value) := by
  exact contains_sound (entropyPair_enclosed CA5_5_6I2R16Value CA5_5_6I2R16Terms CA5_5_6I2R16Terms_sound) (by decide +kernel)
def CA5_5_6I2R16Mass : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R16Mass_sound : CA5_5_6I2R16Mass.Encloses (∑ a, CA5_5_6I2R16Value a) := by
  exact contains_sound (pairSumBall_sound CA5_5_6I2R16P CA5_5_6I2R16Value CA5_5_6I2R16P_sound) (by decide +kernel)
def CA5_5_6I2R16MassTerm : Ball := .exact 0
lemma CA5_5_6I2R16MassTerm_sound : CA5_5_6I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I2R16Value a))) :=
  entropyTerm_zero_ball (CA5_5_6I2R16Mass_sound)
def CA5_5_6I2R16H : Ball := ⟨0, 0⟩
lemma CA5_5_6I2R16H_sound : CA5_5_6I2R16H.Encloses (homogeneousEntropy CA5_5_6I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I2R16Value CA5_5_6I2R16MassTerm_sound CA5_5_6I2R16Entropy_sound) (by decide +kernel)
def CA5_5_6I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA5_5_6I2R0H
  | 1 => CA5_5_6I2R1H
  | 2 => CA5_5_6I2R2H
  | 3 => CA5_5_6I2R3H
  | 4 => CA5_5_6I2R4H
  | 5 => CA5_5_6I2R5H
  | 6 => CA5_5_6I2R6H
  | 7 => CA5_5_6I2R7H
  | 8 => CA5_5_6I2R8H
  | 9 => CA5_5_6I2R9H
  | 10 => CA5_5_6I2R10H
  | 11 => CA5_5_6I2R11H
  | 12 => CA5_5_6I2R12H
  | 13 => CA5_5_6I2R13H
  | 14 => CA5_5_6I2R14H
  | 15 => CA5_5_6I2R15H
  | 16 => CA5_5_6I2R16H
  | _ => (.exact 0)
lemma CA5_5_6I2ResidualEntropies_sound (k : Fin 17) :
    (CA5_5_6I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CA5_5_6I2R0H_sound
  · exact CA5_5_6I2R1H_sound
  · exact CA5_5_6I2R2H_sound
  · exact CA5_5_6I2R3H_sound
  · exact CA5_5_6I2R4H_sound
  · exact CA5_5_6I2R5H_sound
  · exact CA5_5_6I2R6H_sound
  · exact CA5_5_6I2R7H_sound
  · exact CA5_5_6I2R8H_sound
  · exact CA5_5_6I2R9H_sound
  · exact CA5_5_6I2R10H_sound
  · exact CA5_5_6I2R11H_sound
  · exact CA5_5_6I2R12H_sound
  · exact CA5_5_6I2R13H_sound
  · exact CA5_5_6I2R14H_sound
  · exact CA5_5_6I2R15H_sound
  · exact CA5_5_6I2R16H_sound
def CA5_5_6I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => Z0_2_6H2H
  | 0, 3, 5 => Z0_3_5H2H
  | 0, 4, 4 => Z0_4_4H2H
  | 0, 5, 3 => Z0_5_3H2H
  | 2, 0, 6 => Z2_0_6H2H
  | 3, 0, 5 => Z3_0_5H2H
  | 4, 0, 4 => Z4_0_4H2H
  | 5, 0, 3 => Z5_0_3H2H
  | _, _, _ => (.exact 0)
lemma CA5_5_6I2Singles_sound (u : Shape) (hu : u ∈ below (shape 5 5 6))
    (hd : designated (Equiv.refl (Fin 3)) 2 u) :
    (CA5_5_6I2Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) u)) := by
  rw [A5_5_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_2_6H2H_sound
  · exact Z0_3_5H2H_sound
  · exact Z0_4_4H2H_sound
  · exact Z0_5_3H2H_sound
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
  · exact Z5_0_3H2H_sound
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 5 1 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 5 2 1) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 2 (shape 5 3 0) by decide +kernel) hd |>.elim
def CA5_5_6I2Singleton : Ball := ⟨(67303983500677611484406205059 / 10000000000000000000000000000000), (8071347 / 1562500000000000000000000000000)⟩
lemma CA5_5_6I2Singleton_sound : CA5_5_6I2Singleton.Encloses
    (singletonEntropy (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2
    CA5_5_6I2Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ)) (fun u _ => A5_5_6Law_sound u) CA5_5_6I2Singles_sound) (by decide +kernel)
def CA5_5_6I2Group : Ball := ⟨(96051098143690551605291162488069 / 100000000000000000000000000000000), (81727436747 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I2Group_sound : CA5_5_6I2Group.Encloses
    (groupedEntropy (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (Equiv.refl (Fin 3)) 2 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA5_5_6I2Singleton_sound
    (finSumBall_sound 17 CA5_5_6I2ResidualEntropies _ CA5_5_6I2ResidualEntropies_sound)) (by decide +kernel)

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
def CA5_5_6I2H : Ball := ⟨(56863282770715546115407429474149 / 50000000000000000000000000000000), (500468822189 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I2_sound : CA5_5_6I2H.Encloses (stageACapacity (shape 5 5 6) 2) := by
  have hb := contains_sound (Ball.add_sound CA5_5_6I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA5_5_6I2Group_sound)))
    (show contains (.add CA5_5_6I2PairH (.neg (.mul (.exact 2) CA5_5_6I2Group))) CA5_5_6I2H = true by decide +kernel)
  unfold CA5_5_6I2PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
