import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA2_7_7I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_7_7I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA2_7_7I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA2_7_7I1R0Raw_sound (a : PairSlot) :
    (CA2_7_7I1R0Raw a).Encloses (CA2_7_7I1R0Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA2_7_7I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(518482090007836349659861879 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(394363156944662384672781891 / 6250000000000000000000000000000), (521523 / 25000000000000000000000000000000)⟩ ⟨(-1216977525881218296384070257089797 / 100000000000000000000000000000000), (201170517859 / 50000000000000000000000000000000)⟩ ⟨-18, 518482090007836349659861879, 381469726562500000000000000⟩]
lemma CA2_7_7I1R0Certificates_valid :
    CA2_7_7I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA2_7_7I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R0Certificates (CA2_7_7I1R0CertificateIndex a)).input
lemma CA2_7_7I1R0P_check : ∀ a : PairSlot, contains (CA2_7_7I1R0Raw a) (CA2_7_7I1R0P a) = true := by
  decide +kernel
lemma CA2_7_7I1R0P_sound (a : PairSlot) :
    (CA2_7_7I1R0P a).Encloses (CA2_7_7I1R0Value a) :=
  contains_sound (CA2_7_7I1R0Raw_sound a) (CA2_7_7I1R0P_check a)
def CA2_7_7I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R0Certificates (CA2_7_7I1R0CertificateIndex a)).output
lemma CA2_7_7I1R0Terms_sound (a : PairSlot) :
    (CA2_7_7I1R0Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R0Certificates_valid
    (CA2_7_7I1R0CertificateIndex a) (CA2_7_7I1R0P_sound a)
def CA2_7_7I1R0Entropy : Ball := ⟨(394363156944662384672781891 / 6250000000000000000000000000000), (521523 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I1R0Entropy_sound : CA2_7_7I1R0Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R0Value CA2_7_7I1R0Terms CA2_7_7I1R0Terms_sound) (by decide +kernel)
def CA2_7_7I1R0Mass : Ball := ⟨(518482090007836349659861879 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R0Mass_sound : CA2_7_7I1R0Mass.Encloses (∑ a, CA2_7_7I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R0P CA2_7_7I1R0Value CA2_7_7I1R0P_sound) (by decide +kernel)
def CA2_7_7I1R0MassTermLogWitness : LogWitness := ⟨-18, 518482090007836349659861879, 381469726562500000000000000⟩
def CA2_7_7I1R0MassTermLog : Ball := ⟨(-1216977525881218296384070257089797 / 100000000000000000000000000000000), (201170517859 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R0MassTermLog_sound : CA2_7_7I1R0MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R0Mass_sound) (w := CA2_7_7I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R0MassTerm : Ball := ⟨(394363156944662384672781891 / 6250000000000000000000000000000), (521523 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I1R0MassTerm_sound : CA2_7_7I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R0Mass_sound) CA2_7_7I1R0MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R0H : Ball := ⟨0, (521523 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I1R0H_sound : CA2_7_7I1R0H.Encloses (homogeneousEntropy CA2_7_7I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R0Value CA2_7_7I1R0MassTerm_sound CA2_7_7I1R0Entropy_sound) (by decide +kernel)
def CA2_7_7I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA2_7_7I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA2_7_7I1R1Raw_sound (a : PairSlot) :
    (CA2_7_7I1R1Raw a).Encloses (CA2_7_7I1R1Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA2_7_7I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(16422740291403525891109820993 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(481381006845902733106782874549 / 100000000000000000000000000000000), (166927251 / 100000000000000000000000000000000)⟩ ⟨(-366398206316610685122953063338753 / 50000000000000000000000000000000), (127054944381 / 50000000000000000000000000000000)⟩ ⟨-11, 16422740291403525891109820993, 12207031250000000000000000000⟩]
lemma CA2_7_7I1R1Certificates_valid :
    CA2_7_7I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA2_7_7I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R1Certificates (CA2_7_7I1R1CertificateIndex a)).input
lemma CA2_7_7I1R1P_check : ∀ a : PairSlot, contains (CA2_7_7I1R1Raw a) (CA2_7_7I1R1P a) = true := by
  decide +kernel
lemma CA2_7_7I1R1P_sound (a : PairSlot) :
    (CA2_7_7I1R1P a).Encloses (CA2_7_7I1R1Value a) :=
  contains_sound (CA2_7_7I1R1Raw_sound a) (CA2_7_7I1R1P_check a)
def CA2_7_7I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R1Certificates (CA2_7_7I1R1CertificateIndex a)).output
lemma CA2_7_7I1R1Terms_sound (a : PairSlot) :
    (CA2_7_7I1R1Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R1Certificates_valid
    (CA2_7_7I1R1CertificateIndex a) (CA2_7_7I1R1P_sound a)
def CA2_7_7I1R1Entropy : Ball := ⟨(481381006845902733106782874549 / 50000000000000000000000000000000), (166927251 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R1Entropy_sound : CA2_7_7I1R1Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R1Value CA2_7_7I1R1Terms CA2_7_7I1R1Terms_sound) (by decide +kernel)
def CA2_7_7I1R1Mass : Ball := ⟨(16422740291403525891109820993 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R1Mass_sound : CA2_7_7I1R1Mass.Encloses (∑ a, CA2_7_7I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R1P CA2_7_7I1R1Value CA2_7_7I1R1P_sound) (by decide +kernel)
def CA2_7_7I1R1MassTermLogWitness : LogWitness := ⟨-10, 16422740291403525891109820993, 12207031250000000000000000000⟩
def CA2_7_7I1R1MassTermLog : Ball := ⟨(-82935211822153354913022866703397 / 12500000000000000000000000000000), (232934065079 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R1MassTermLog_sound : CA2_7_7I1R1MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R1Mass_sound) (w := CA2_7_7I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R1MassTerm : Ball := ⟨(871695004651368917354137361287 / 100000000000000000000000000000000), (306033293 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R1MassTerm_sound : CA2_7_7I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R1Mass_sound) CA2_7_7I1R1MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R1H : Ball := ⟨(91067009040436548859428387811 / 100000000000000000000000000000000), (127977559 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I1R1H_sound : CA2_7_7I1R1H.Encloses (homogeneousEntropy CA2_7_7I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R1Value CA2_7_7I1R1MassTerm_sound CA2_7_7I1R1Entropy_sound) (by decide +kernel)
def CA2_7_7I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA2_7_7I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA2_7_7I1R2Raw_sound (a : PairSlot) :
    (CA2_7_7I1R2Raw a).Encloses (CA2_7_7I1R2Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA2_7_7I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(936943688749496935401112543 / 97656250000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(891615067682299212220383761227 / 20000000000000000000000000000000), (1625338259 / 100000000000000000000000000000000)⟩ ⟨(-46465857553062194688581618121661 / 10000000000000000000000000000000), (169406590297 / 100000000000000000000000000000000)⟩ ⟨-7, 936943688749496935401112543, 762939453125000000000000000⟩,
   .log ⟨(97581178763297969963962951187 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(676456231729529575982465463009 / 100000000000000000000000000000000), (247963429 / 100000000000000000000000000000000)⟩ ⟨(-693224083068728912677772212316411 / 100000000000000000000000000000000), (12705494261 / 5000000000000000000000000000000)⟩ ⟨-11, 97581178763297969963962951187, 48828125000000000000000000000⟩,
   .log ⟨(226227111864411376422478165517 / 6250000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(12012830951106762904887313794573 / 100000000000000000000000000000000), (4598923699 / 100000000000000000000000000000000)⟩ ⟨(-265503786263836968659047249629 / 80000000000000000000000000000), (63527471311 / 50000000000000000000000000000000)⟩ ⟨-5, 226227111864411376422478165517, 195312500000000000000000000000⟩]
lemma CA2_7_7I1R2Certificates_valid :
    CA2_7_7I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA2_7_7I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R2Certificates (CA2_7_7I1R2CertificateIndex a)).input
lemma CA2_7_7I1R2P_check : ∀ a : PairSlot, contains (CA2_7_7I1R2Raw a) (CA2_7_7I1R2P a) = true := by
  decide +kernel
lemma CA2_7_7I1R2P_sound (a : PairSlot) :
    (CA2_7_7I1R2P a).Encloses (CA2_7_7I1R2Value a) :=
  contains_sound (CA2_7_7I1R2Raw_sound a) (CA2_7_7I1R2P_check a)
def CA2_7_7I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R2Certificates (CA2_7_7I1R2CertificateIndex a)).output
lemma CA2_7_7I1R2Terms_sound (a : PairSlot) :
    (CA2_7_7I1R2Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R2Certificates_valid
    (CA2_7_7I1R2CertificateIndex a) (CA2_7_7I1R2P_sound a)
def CA2_7_7I1R2Entropy : Ball := ⟨(22281894091388814179056082332861 / 100000000000000000000000000000000), (333821083 / 4000000000000000000000000000000)⟩
lemma CA2_7_7I1R2Entropy_sound : CA2_7_7I1R2Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R2Value CA2_7_7I1R2Terms CA2_7_7I1R2Terms_sound) (by decide +kernel)
def CA2_7_7I1R2Mass : Ball := ⟨(573365682191614768638905503871 / 10000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R2Mass_sound : CA2_7_7I1R2Mass.Encloses (∑ a, CA2_7_7I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R2P CA2_7_7I1R2Value CA2_7_7I1R2P_sound) (by decide +kernel)
def CA2_7_7I1R2MassTermLogWitness : LogWitness := ⟨-5, 573365682191614768638905503871, 312500000000000000000000000000⟩
def CA2_7_7I1R2MassTermLog : Ball := ⟨(-71470416750031097905684090412837 / 25000000000000000000000000000000), (127054942743 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R2MassTermLog_sound : CA2_7_7I1R2MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R2Mass_sound) (w := CA2_7_7I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R2MassTerm : Ball := ⟨(3278294740512047307358775649571 / 20000000000000000000000000000000), (7284894499 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R2MassTerm_sound : CA2_7_7I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R2Mass_sound) CA2_7_7I1R2MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R2H : Ball := ⟨(2945210194414288821131102042503 / 50000000000000000000000000000000), (7815210787 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R2H_sound : CA2_7_7I1R2H.Encloses (homogeneousEntropy CA2_7_7I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R2Value CA2_7_7I1R2MassTerm_sound CA2_7_7I1R2Entropy_sound) (by decide +kernel)
def CA2_7_7I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA2_7_7I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA2_7_7I1R3Raw_sound (a : PairSlot) :
    (CA2_7_7I1R3Raw a).Encloses (CA2_7_7I1R3Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA2_7_7I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(319186405843124656703421426049 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(161316905522863411870927740587 / 5000000000000000000000000000000), (60831317 / 5000000000000000000000000000000)⟩ ⟨(-505400300795229536061048437334033 / 100000000000000000000000000000000), (19058241393 / 10000000000000000000000000000000)⟩ ⟨-8, 319186405843124656703421426049, 195312500000000000000000000000⟩,
   .log ⟨(4931876896034142675390643532267 / 25000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩ ⟨(32020826248307253689798850210269 / 100000000000000000000000000000000), (8354924511 / 50000000000000000000000000000000)⟩ ⟨(-162315620013022209206422899947421 / 100000000000000000000000000000000), (4235164749 / 5000000000000000000000000000000)⟩ ⟨-3, 4931876896034142675390643532267, 3125000000000000000000000000000⟩,
   .log ⟨(212667623876061015012098285571 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(866355461712993848957458311427 / 12500000000000000000000000000000), (504382161 / 20000000000000000000000000000000)⟩ ⟨(-40737534276392287801647223947449 / 10000000000000000000000000000000), (74115383037 / 50000000000000000000000000000000)⟩ ⟨-6, 212667623876061015012098285571, 195312500000000000000000000000⟩]
lemma CA2_7_7I1R3Certificates_valid :
    CA2_7_7I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA2_7_7I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R3Certificates (CA2_7_7I1R3CertificateIndex a)).input
lemma CA2_7_7I1R3P_check : ∀ a : PairSlot, contains (CA2_7_7I1R3Raw a) (CA2_7_7I1R3P a) = true := by
  decide +kernel
lemma CA2_7_7I1R3P_sound (a : PairSlot) :
    (CA2_7_7I1R3P a).Encloses (CA2_7_7I1R3Value a) :=
  contains_sound (CA2_7_7I1R3Raw_sound a) (CA2_7_7I1R3P_check a)
def CA2_7_7I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R3Certificates (CA2_7_7I1R3CertificateIndex a)).output
lemma CA2_7_7I1R3Terms_sound (a : PairSlot) :
    (CA2_7_7I1R3Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R3Certificates_valid
    (CA2_7_7I1R3CertificateIndex a) (CA2_7_7I1R3P_sound a)
def CA2_7_7I1R3Entropy : Ball := ⟨(1687120322098738908755082860537 / 2000000000000000000000000000000), (20448386167 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R3Entropy_sound : CA2_7_7I1R3Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R3Value CA2_7_7I1R3Terms CA2_7_7I1R3Terms_sound) (by decide +kernel)
def CA2_7_7I1R3Mass : Ball := ⟨(11033610693415654067533101632867 / 25000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R3Mass_sound : CA2_7_7I1R3Mass.Encloses (∑ a, CA2_7_7I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R3P CA2_7_7I1R3Value CA2_7_7I1R3P_sound) (by decide +kernel)
def CA2_7_7I1R3MassTermLogWitness : LogWitness := ⟨-2, 11033610693415654067533101632867, 6250000000000000000000000000000⟩
def CA2_7_7I1R3MassTermLog : Ball := ⟨(-81792969309321574946819002094641 / 100000000000000000000000000000000), (15881867829 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I1R3MassTermLog_sound : CA2_7_7I1R3MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R3Mass_sound) (w := CA2_7_7I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R3MassTerm : Ball := ⟨(18049435616350978685957054139607 / 50000000000000000000000000000000), (28037495571 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R3MassTerm_sound : CA2_7_7I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R3Mass_sound) CA2_7_7I1R3MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R3H : Ball := ⟨(12064286218058747016460008686909 / 25000000000000000000000000000000), (13786853581 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I1R3H_sound : CA2_7_7I1R3H.Encloses (homogeneousEntropy CA2_7_7I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R3Value CA2_7_7I1R3MassTerm_sound CA2_7_7I1R3Entropy_sound) (by decide +kernel)
def CA2_7_7I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA2_7_7I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA2_7_7I1R4Raw_sound (a : PairSlot) :
    (CA2_7_7I1R4Raw a).Encloses (CA2_7_7I1R4Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA2_7_7I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3994686615688407794575543003 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(312599217338392765931898463569 / 100000000000000000000000000000000), (109968023 / 100000000000000000000000000000000)⟩ ⟨(-782537523996791104538684222120479 / 100000000000000000000000000000000), (137642855191 / 50000000000000000000000000000000)⟩ ⟨-12, 3994686615688407794575543003, 2441406250000000000000000000⟩,
   .log ⟨(4248035449603416421730568330403 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(6709163582794615931166082232097 / 50000000000000000000000000000000), (337333691 / 6250000000000000000000000000000)⟩ ⟨(-157935677853652631212439156419493 / 50000000000000000000000000000000), (127054942521 / 100000000000000000000000000000000)⟩ ⟨-5, 4248035449603416421730568330403, 3125000000000000000000000000000⟩,
   .log ⟨(31141609959674067281134018926149 / 100000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩ ⟨(3633059069145374595738373947531 / 10000000000000000000000000000000), (19783477427 / 100000000000000000000000000000000)⟩ ⟨(-23332506404453077492658831608737 / 20000000000000000000000000000000), (63527471309 / 100000000000000000000000000000000)⟩ ⟨-2, 31141609959674067281134018926149, 25000000000000000000000000000000⟩,
   .log ⟨(21435807383318659594624099329 / 1000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩ ⟨(4118560827156602913436404968533 / 50000000000000000000000000000000), (3177446183 / 100000000000000000000000000000000)⟩ ⟨(-384269251305333710696431207285663 / 100000000000000000000000000000000), (74115383077 / 50000000000000000000000000000000)⟩ ⟨-6, 21435807383318659594624099329, 15625000000000000000000000000⟩,
   .log ⟨(129706705804216070720920218653 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(862244740368455921490701627033 / 100000000000000000000000000000000), (302131113 / 100000000000000000000000000000000)⟩ ⟨(-41547810453510731302108942954391 / 6250000000000000000000000000000), (116467031027 / 50000000000000000000000000000000)⟩ ⟨-10, 129706705804216070720920218653, 97656250000000000000000000000⟩]
lemma CA2_7_7I1R4Certificates_valid :
    CA2_7_7I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA2_7_7I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R4Certificates (CA2_7_7I1R4CertificateIndex a)).input
lemma CA2_7_7I1R4P_check : ∀ a : PairSlot, contains (CA2_7_7I1R4Raw a) (CA2_7_7I1R4P a) = true := by
  decide +kernel
lemma CA2_7_7I1R4P_sound (a : PairSlot) :
    (CA2_7_7I1R4P a).Encloses (CA2_7_7I1R4Value a) :=
  contains_sound (CA2_7_7I1R4Raw_sound a) (CA2_7_7I1R4P_check a)
def CA2_7_7I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R4Certificates (CA2_7_7I1R4CertificateIndex a)).output
lemma CA2_7_7I1R4Terms_sound (a : PairSlot) :
    (CA2_7_7I1R4Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R4Certificates_valid
    (CA2_7_7I1R4CertificateIndex a) (CA2_7_7I1R4P_sound a)
def CA2_7_7I1R4Entropy : Ball := ⟨(81128931506303862789148186832001 / 100000000000000000000000000000000), (4681889383 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I1R4Entropy_sound : CA2_7_7I1R4Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R4Value CA2_7_7I1R4Terms CA2_7_7I1R4Terms_sound) (by decide +kernel)
def CA2_7_7I1R4Mass : Ball := ⟨(11033610693415654067533101632867 / 25000000000000000000000000000000), (137 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R4Mass_sound : CA2_7_7I1R4Mass.Encloses (∑ a, CA2_7_7I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R4P CA2_7_7I1R4Value CA2_7_7I1R4P_sound) (by decide +kernel)
def CA2_7_7I1R4MassTermLogWitness : LogWitness := ⟨-2, 11033610693415654067533101632867, 6250000000000000000000000000000⟩
def CA2_7_7I1R4MassTermLog : Ball := ⟨(-81792969309321574946819002094641 / 100000000000000000000000000000000), (63527471359 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R4MassTermLog_sound : CA2_7_7I1R4MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R4Mass_sound) (w := CA2_7_7I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R4MassTerm : Ball := ⟨(18049435616350978685957054139607 / 50000000000000000000000000000000), (5607499121 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I1R4MassTerm_sound : CA2_7_7I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R4Mass_sound) CA2_7_7I1R4MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R4H : Ball := ⟨(45030060273601905417234078552787 / 100000000000000000000000000000000), (65492610669 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R4H_sound : CA2_7_7I1R4H.Encloses (homogeneousEntropy CA2_7_7I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R4Value CA2_7_7I1R4MassTerm_sound CA2_7_7I1R4Entropy_sound) (by decide +kernel)
def CA2_7_7I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA2_7_7I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA2_7_7I1R5Raw_sound (a : PairSlot) :
    (CA2_7_7I1R5Raw a).Encloses (CA2_7_7I1R5Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA2_7_7I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(100767844754924508667501994673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(347654413195527167073773901443 / 50000000000000000000000000000000), (234722641 / 100000000000000000000000000000000)⟩ ⟨(-345005308033580177149038696772543 / 50000000000000000000000000000000), (46586812301 / 20000000000000000000000000000000)⟩ ⟨-10, 100767844754924508667501994673, 97656250000000000000000000000⟩,
   .log ⟨(128328279892289891575263906127 / 5000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(9400307070204669460590086012587 / 100000000000000000000000000000000), (760887983 / 20000000000000000000000000000000)⟩ ⟨(-183130076201727585026414101691607 / 50000000000000000000000000000000), (37057691601 / 25000000000000000000000000000000)⟩ ⟨-6, 128328279892289891575263906127, 78125000000000000000000000000⟩,
   .log ⟨(99747484178675751510873701071 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1240287439410929187097892052713 / 100000000000000000000000000000000), (422447043 / 100000000000000000000000000000000)⟩ ⟨(-31085682251123901333661096905369 / 5000000000000000000000000000000), (26469779729 / 12500000000000000000000000000000)⟩ ⟨-9, 99747484178675751510873701071, 97656250000000000000000000000⟩]
lemma CA2_7_7I1R5Certificates_valid :
    CA2_7_7I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA2_7_7I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R5Certificates (CA2_7_7I1R5CertificateIndex a)).input
lemma CA2_7_7I1R5P_check : ∀ a : PairSlot, contains (CA2_7_7I1R5Raw a) (CA2_7_7I1R5P a) = true := by
  decide +kernel
lemma CA2_7_7I1R5P_sound (a : PairSlot) :
    (CA2_7_7I1R5P a).Encloses (CA2_7_7I1R5Value a) :=
  contains_sound (CA2_7_7I1R5Raw_sound a) (CA2_7_7I1R5P_check a)
def CA2_7_7I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R5Certificates (CA2_7_7I1R5CertificateIndex a)).output
lemma CA2_7_7I1R5Terms_sound (a : PairSlot) :
    (CA2_7_7I1R5Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R5Certificates_valid
    (CA2_7_7I1R5CertificateIndex a) (CA2_7_7I1R5P_sound a)
def CA2_7_7I1R5Entropy : Ball := ⟨(5667951668003326490917762934093 / 25000000000000000000000000000000), (4461609599 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R5Entropy_sound : CA2_7_7I1R5Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R5Value CA2_7_7I1R5Terms CA2_7_7I1R5Terms_sound) (by decide +kernel)
def CA2_7_7I1R5Mass : Ball := ⟨(573365682191614768638905503871 / 10000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R5Mass_sound : CA2_7_7I1R5Mass.Encloses (∑ a, CA2_7_7I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R5P CA2_7_7I1R5Value CA2_7_7I1R5P_sound) (by decide +kernel)
def CA2_7_7I1R5MassTermLogWitness : LogWitness := ⟨-5, 573365682191614768638905503871, 312500000000000000000000000000⟩
def CA2_7_7I1R5MassTermLog : Ball := ⟨(-71470416750031097905684090412837 / 25000000000000000000000000000000), (127054942761 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R5MassTermLog_sound : CA2_7_7I1R5MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R5Mass_sound) (w := CA2_7_7I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R5MassTerm : Ball := ⟨(3278294740512047307358775649571 / 20000000000000000000000000000000), (3642447251 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R5MassTerm_sound : CA2_7_7I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R5Mass_sound) CA2_7_7I1R5MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R5H : Ball := ⟨(6280332969453069426877173488517 / 100000000000000000000000000000000), (162081137 / 1000000000000000000000000000000)⟩
lemma CA2_7_7I1R5H_sound : CA2_7_7I1R5H.Encloses (homogeneousEntropy CA2_7_7I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R5Value CA2_7_7I1R5MassTerm_sound CA2_7_7I1R5Entropy_sound) (by decide +kernel)
def CA2_7_7I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA2_7_7I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA2_7_7I1R6Raw_sound (a : PairSlot) :
    (CA2_7_7I1R6Raw a).Encloses (CA2_7_7I1R6Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA2_7_7I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(9959407168548791733825735439 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(169733410514704021981757416199 / 100000000000000000000000000000000), (3690727 / 6250000000000000000000000000000)⟩ ⟨(-852126073581527594166230203002393 / 100000000000000000000000000000000), (148230768291 / 50000000000000000000000000000000)⟩ ⟨-13, 9959407168548791733825735439, 6103515625000000000000000000⟩,
   .log ⟨(55025814211550424684177823 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(3079795507774160501234131027 / 20000000000000000000000000000000), (5243489 / 100000000000000000000000000000000)⟩ ⟨(-559700124733035406423617292816217 / 50000000000000000000000000000000), (381164898987 / 100000000000000000000000000000000)⟩ ⟨-17, 55025814211550424684177823, 30517578125000000000000000⟩,
   .log ⟨(88319589956824610672646792579 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(621060135132702437816815171041 / 100000000000000000000000000000000), (8977153 / 4000000000000000000000000000000)⟩ ⟨(-703196352515121730921719718825911 / 100000000000000000000000000000000), (12705494323 / 5000000000000000000000000000000)⟩ ⟨-11, 88319589956824610672646792579, 48828125000000000000000000000⟩]
lemma CA2_7_7I1R6Certificates_valid :
    CA2_7_7I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA2_7_7I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R6Certificates (CA2_7_7I1R6CertificateIndex a)).input
lemma CA2_7_7I1R6P_check : ∀ a : PairSlot, contains (CA2_7_7I1R6Raw a) (CA2_7_7I1R6P a) = true := by
  decide +kernel
lemma CA2_7_7I1R6P_sound (a : PairSlot) :
    (CA2_7_7I1R6P a).Encloses (CA2_7_7I1R6Value a) :=
  contains_sound (CA2_7_7I1R6Raw_sound a) (CA2_7_7I1R6P_check a)
def CA2_7_7I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R6Certificates (CA2_7_7I1R6CertificateIndex a)).output
lemma CA2_7_7I1R6Terms_sound (a : PairSlot) :
    (CA2_7_7I1R6Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R6Certificates_valid
    (CA2_7_7I1R6CertificateIndex a) (CA2_7_7I1R6P_sound a)
def CA2_7_7I1R6Entropy : Ball := ⟨(991324911239852086792671313709 / 100000000000000000000000000000000), (353019067 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R6Entropy_sound : CA2_7_7I1R6Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R6Value CA2_7_7I1R6Terms CA2_7_7I1R6Terms_sound) (by decide +kernel)
def CA2_7_7I1R6Mass : Ball := ⟨(26181701868319459768431725097 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R6Mass_sound : CA2_7_7I1R6Mass.Encloses (∑ a, CA2_7_7I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R6P CA2_7_7I1R6Value CA2_7_7I1R6P_sound) (by decide +kernel)
def CA2_7_7I1R6MassTermLogWitness : LogWitness := ⟨-10, 26181701868319459768431725097, 19531250000000000000000000000⟩
def CA2_7_7I1R6MassTermLog : Ball := ⟨(-331921339386894290060685881598867 / 50000000000000000000000000000000), (29116758137 / 12500000000000000000000000000000)⟩
lemma CA2_7_7I1R6MassTermLog_sound : CA2_7_7I1R6MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R6Mass_sound) (w := CA2_7_7I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R6MassTerm : Ball := ⟨(43451327757804738615092393321 / 5000000000000000000000000000000), (304930553 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1R6MassTerm_sound : CA2_7_7I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R6Mass_sound) CA2_7_7I1R6MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R6H : Ball := ⟨(122298356083757314490823447289 / 100000000000000000000000000000000), (32897481 / 5000000000000000000000000000000)⟩
lemma CA2_7_7I1R6H_sound : CA2_7_7I1R6H.Encloses (homogeneousEntropy CA2_7_7I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R6Value CA2_7_7I1R6MassTerm_sound CA2_7_7I1R6Entropy_sound) (by decide +kernel)
def CA2_7_7I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA2_7_7I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA2_7_7I1R7Raw_sound (a : PairSlot) :
    (CA2_7_7I1R7Raw a).Encloses (CA2_7_7I1R7Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA2_7_7I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(61223223962159475536795967 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(395497734704434699516257969 / 12500000000000000000000000000000), (129647 / 12500000000000000000000000000000)⟩ ⟨(-1291985978879131993165599986787771 / 100000000000000000000000000000000), (423516882001 / 100000000000000000000000000000000)⟩ ⟨-19, 61223223962159475536795967, 47683715820312500000000000⟩]
lemma CA2_7_7I1R7Certificates_valid :
    CA2_7_7I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 5 => 1
  | 5, 4 => 1
  | _, _ => 0
def CA2_7_7I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R7Certificates (CA2_7_7I1R7CertificateIndex a)).input
lemma CA2_7_7I1R7P_check : ∀ a : PairSlot, contains (CA2_7_7I1R7Raw a) (CA2_7_7I1R7P a) = true := by
  decide +kernel
lemma CA2_7_7I1R7P_sound (a : PairSlot) :
    (CA2_7_7I1R7P a).Encloses (CA2_7_7I1R7Value a) :=
  contains_sound (CA2_7_7I1R7Raw_sound a) (CA2_7_7I1R7P_check a)
def CA2_7_7I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R7Certificates (CA2_7_7I1R7CertificateIndex a)).output
lemma CA2_7_7I1R7Terms_sound (a : PairSlot) :
    (CA2_7_7I1R7Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R7Certificates_valid
    (CA2_7_7I1R7CertificateIndex a) (CA2_7_7I1R7P_sound a)
def CA2_7_7I1R7Entropy : Ball := ⟨(395497734704434699516257969 / 6250000000000000000000000000000), (129647 / 6250000000000000000000000000000)⟩
lemma CA2_7_7I1R7Entropy_sound : CA2_7_7I1R7Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R7Value CA2_7_7I1R7Terms CA2_7_7I1R7Terms_sound) (by decide +kernel)
def CA2_7_7I1R7Mass : Ball := ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R7Mass_sound : CA2_7_7I1R7Mass.Encloses (∑ a, CA2_7_7I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R7P CA2_7_7I1R7Value CA2_7_7I1R7P_sound) (by decide +kernel)
def CA2_7_7I1R7MassTermLogWitness : LogWitness := ⟨-18, 61223223962159475536795967, 47683715820312500000000000⟩
def CA2_7_7I1R7MassTermLog : Ball := ⟨(-1222671260823137462223876793737441 / 100000000000000000000000000000000), (201170529159 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R7MassTermLog_sound : CA2_7_7I1R7MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I1R7Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I1R7Mass_sound) (w := CA2_7_7I1R7MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I1R7MassTerm : Ball := ⟨(1497117528669416949537789903 / 25000000000000000000000000000000), (985317 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R7MassTerm_sound : CA2_7_7I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R7Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I1R7Mass_sound) CA2_7_7I1R7MassTermLog_sound) (by decide +kernel)
def CA2_7_7I1R7H : Ball := ⟨(84873410148321848527241973 / 25000000000000000000000000000000), (2022493 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I1R7H_sound : CA2_7_7I1R7H.Encloses (homogeneousEntropy CA2_7_7I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R7Value CA2_7_7I1R7MassTerm_sound CA2_7_7I1R7Entropy_sound) (by decide +kernel)
def CA2_7_7I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA2_7_7I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA2_7_7I1R8Raw_sound (a : PairSlot) :
    (CA2_7_7I1R8Raw a).Encloses (CA2_7_7I1R8Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA2_7_7I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R8Certificates_valid :
    CA2_7_7I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R8Certificates (CA2_7_7I1R8CertificateIndex a)).input
lemma CA2_7_7I1R8P_check : ∀ a : PairSlot, contains (CA2_7_7I1R8Raw a) (CA2_7_7I1R8P a) = true := by
  decide +kernel
lemma CA2_7_7I1R8P_sound (a : PairSlot) :
    (CA2_7_7I1R8P a).Encloses (CA2_7_7I1R8Value a) :=
  contains_sound (CA2_7_7I1R8Raw_sound a) (CA2_7_7I1R8P_check a)
def CA2_7_7I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R8Certificates (CA2_7_7I1R8CertificateIndex a)).output
lemma CA2_7_7I1R8Terms_sound (a : PairSlot) :
    (CA2_7_7I1R8Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R8Certificates_valid
    (CA2_7_7I1R8CertificateIndex a) (CA2_7_7I1R8P_sound a)
def CA2_7_7I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R8Entropy_sound : CA2_7_7I1R8Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R8Value CA2_7_7I1R8Terms CA2_7_7I1R8Terms_sound) (by decide +kernel)
def CA2_7_7I1R8Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R8Mass_sound : CA2_7_7I1R8Mass.Encloses (∑ a, CA2_7_7I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R8P CA2_7_7I1R8Value CA2_7_7I1R8P_sound) (by decide +kernel)
def CA2_7_7I1R8MassTerm : Ball := .exact 0
lemma CA2_7_7I1R8MassTerm_sound : CA2_7_7I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R8Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R8Mass_sound)
def CA2_7_7I1R8H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R8H_sound : CA2_7_7I1R8H.Encloses (homogeneousEntropy CA2_7_7I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R8Value CA2_7_7I1R8MassTerm_sound CA2_7_7I1R8Entropy_sound) (by decide +kernel)
def CA2_7_7I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA2_7_7I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA2_7_7I1R9Raw_sound (a : PairSlot) :
    (CA2_7_7I1R9Raw a).Encloses (CA2_7_7I1R9Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA2_7_7I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R9Certificates_valid :
    CA2_7_7I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R9Certificates (CA2_7_7I1R9CertificateIndex a)).input
lemma CA2_7_7I1R9P_check : ∀ a : PairSlot, contains (CA2_7_7I1R9Raw a) (CA2_7_7I1R9P a) = true := by
  decide +kernel
lemma CA2_7_7I1R9P_sound (a : PairSlot) :
    (CA2_7_7I1R9P a).Encloses (CA2_7_7I1R9Value a) :=
  contains_sound (CA2_7_7I1R9Raw_sound a) (CA2_7_7I1R9P_check a)
def CA2_7_7I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R9Certificates (CA2_7_7I1R9CertificateIndex a)).output
lemma CA2_7_7I1R9Terms_sound (a : PairSlot) :
    (CA2_7_7I1R9Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R9Certificates_valid
    (CA2_7_7I1R9CertificateIndex a) (CA2_7_7I1R9P_sound a)
def CA2_7_7I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R9Entropy_sound : CA2_7_7I1R9Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R9Value CA2_7_7I1R9Terms CA2_7_7I1R9Terms_sound) (by decide +kernel)
def CA2_7_7I1R9Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R9Mass_sound : CA2_7_7I1R9Mass.Encloses (∑ a, CA2_7_7I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R9P CA2_7_7I1R9Value CA2_7_7I1R9P_sound) (by decide +kernel)
def CA2_7_7I1R9MassTerm : Ball := .exact 0
lemma CA2_7_7I1R9MassTerm_sound : CA2_7_7I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R9Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R9Mass_sound)
def CA2_7_7I1R9H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R9H_sound : CA2_7_7I1R9H.Encloses (homogeneousEntropy CA2_7_7I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R9Value CA2_7_7I1R9MassTerm_sound CA2_7_7I1R9Entropy_sound) (by decide +kernel)
def CA2_7_7I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA2_7_7I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA2_7_7I1R10Raw_sound (a : PairSlot) :
    (CA2_7_7I1R10Raw a).Encloses (CA2_7_7I1R10Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA2_7_7I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R10Certificates_valid :
    CA2_7_7I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R10Certificates (CA2_7_7I1R10CertificateIndex a)).input
lemma CA2_7_7I1R10P_check : ∀ a : PairSlot, contains (CA2_7_7I1R10Raw a) (CA2_7_7I1R10P a) = true := by
  decide +kernel
lemma CA2_7_7I1R10P_sound (a : PairSlot) :
    (CA2_7_7I1R10P a).Encloses (CA2_7_7I1R10Value a) :=
  contains_sound (CA2_7_7I1R10Raw_sound a) (CA2_7_7I1R10P_check a)
def CA2_7_7I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R10Certificates (CA2_7_7I1R10CertificateIndex a)).output
lemma CA2_7_7I1R10Terms_sound (a : PairSlot) :
    (CA2_7_7I1R10Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R10Certificates_valid
    (CA2_7_7I1R10CertificateIndex a) (CA2_7_7I1R10P_sound a)
def CA2_7_7I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R10Entropy_sound : CA2_7_7I1R10Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R10Value CA2_7_7I1R10Terms CA2_7_7I1R10Terms_sound) (by decide +kernel)
def CA2_7_7I1R10Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R10Mass_sound : CA2_7_7I1R10Mass.Encloses (∑ a, CA2_7_7I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R10P CA2_7_7I1R10Value CA2_7_7I1R10P_sound) (by decide +kernel)
def CA2_7_7I1R10MassTerm : Ball := .exact 0
lemma CA2_7_7I1R10MassTerm_sound : CA2_7_7I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R10Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R10Mass_sound)
def CA2_7_7I1R10H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R10H_sound : CA2_7_7I1R10H.Encloses (homogeneousEntropy CA2_7_7I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R10Value CA2_7_7I1R10MassTerm_sound CA2_7_7I1R10Entropy_sound) (by decide +kernel)
def CA2_7_7I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA2_7_7I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA2_7_7I1R11Raw_sound (a : PairSlot) :
    (CA2_7_7I1R11Raw a).Encloses (CA2_7_7I1R11Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA2_7_7I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R11Certificates_valid :
    CA2_7_7I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R11Certificates (CA2_7_7I1R11CertificateIndex a)).input
lemma CA2_7_7I1R11P_check : ∀ a : PairSlot, contains (CA2_7_7I1R11Raw a) (CA2_7_7I1R11P a) = true := by
  decide +kernel
lemma CA2_7_7I1R11P_sound (a : PairSlot) :
    (CA2_7_7I1R11P a).Encloses (CA2_7_7I1R11Value a) :=
  contains_sound (CA2_7_7I1R11Raw_sound a) (CA2_7_7I1R11P_check a)
def CA2_7_7I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R11Certificates (CA2_7_7I1R11CertificateIndex a)).output
lemma CA2_7_7I1R11Terms_sound (a : PairSlot) :
    (CA2_7_7I1R11Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R11Certificates_valid
    (CA2_7_7I1R11CertificateIndex a) (CA2_7_7I1R11P_sound a)
def CA2_7_7I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R11Entropy_sound : CA2_7_7I1R11Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R11Value CA2_7_7I1R11Terms CA2_7_7I1R11Terms_sound) (by decide +kernel)
def CA2_7_7I1R11Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R11Mass_sound : CA2_7_7I1R11Mass.Encloses (∑ a, CA2_7_7I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R11P CA2_7_7I1R11Value CA2_7_7I1R11P_sound) (by decide +kernel)
def CA2_7_7I1R11MassTerm : Ball := .exact 0
lemma CA2_7_7I1R11MassTerm_sound : CA2_7_7I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R11Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R11Mass_sound)
def CA2_7_7I1R11H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R11H_sound : CA2_7_7I1R11H.Encloses (homogeneousEntropy CA2_7_7I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R11Value CA2_7_7I1R11MassTerm_sound CA2_7_7I1R11Entropy_sound) (by decide +kernel)
def CA2_7_7I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA2_7_7I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA2_7_7I1R12Raw_sound (a : PairSlot) :
    (CA2_7_7I1R12Raw a).Encloses (CA2_7_7I1R12Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA2_7_7I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R12Certificates_valid :
    CA2_7_7I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R12Certificates (CA2_7_7I1R12CertificateIndex a)).input
lemma CA2_7_7I1R12P_check : ∀ a : PairSlot, contains (CA2_7_7I1R12Raw a) (CA2_7_7I1R12P a) = true := by
  decide +kernel
lemma CA2_7_7I1R12P_sound (a : PairSlot) :
    (CA2_7_7I1R12P a).Encloses (CA2_7_7I1R12Value a) :=
  contains_sound (CA2_7_7I1R12Raw_sound a) (CA2_7_7I1R12P_check a)
def CA2_7_7I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R12Certificates (CA2_7_7I1R12CertificateIndex a)).output
lemma CA2_7_7I1R12Terms_sound (a : PairSlot) :
    (CA2_7_7I1R12Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R12Certificates_valid
    (CA2_7_7I1R12CertificateIndex a) (CA2_7_7I1R12P_sound a)
def CA2_7_7I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R12Entropy_sound : CA2_7_7I1R12Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R12Value CA2_7_7I1R12Terms CA2_7_7I1R12Terms_sound) (by decide +kernel)
def CA2_7_7I1R12Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R12Mass_sound : CA2_7_7I1R12Mass.Encloses (∑ a, CA2_7_7I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R12P CA2_7_7I1R12Value CA2_7_7I1R12P_sound) (by decide +kernel)
def CA2_7_7I1R12MassTerm : Ball := .exact 0
lemma CA2_7_7I1R12MassTerm_sound : CA2_7_7I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R12Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R12Mass_sound)
def CA2_7_7I1R12H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R12H_sound : CA2_7_7I1R12H.Encloses (homogeneousEntropy CA2_7_7I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R12Value CA2_7_7I1R12MassTerm_sound CA2_7_7I1R12Entropy_sound) (by decide +kernel)
def CA2_7_7I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA2_7_7I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA2_7_7I1R13Raw_sound (a : PairSlot) :
    (CA2_7_7I1R13Raw a).Encloses (CA2_7_7I1R13Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA2_7_7I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R13Certificates_valid :
    CA2_7_7I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R13Certificates (CA2_7_7I1R13CertificateIndex a)).input
lemma CA2_7_7I1R13P_check : ∀ a : PairSlot, contains (CA2_7_7I1R13Raw a) (CA2_7_7I1R13P a) = true := by
  decide +kernel
lemma CA2_7_7I1R13P_sound (a : PairSlot) :
    (CA2_7_7I1R13P a).Encloses (CA2_7_7I1R13Value a) :=
  contains_sound (CA2_7_7I1R13Raw_sound a) (CA2_7_7I1R13P_check a)
def CA2_7_7I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R13Certificates (CA2_7_7I1R13CertificateIndex a)).output
lemma CA2_7_7I1R13Terms_sound (a : PairSlot) :
    (CA2_7_7I1R13Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R13Certificates_valid
    (CA2_7_7I1R13CertificateIndex a) (CA2_7_7I1R13P_sound a)
def CA2_7_7I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R13Entropy_sound : CA2_7_7I1R13Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R13Value CA2_7_7I1R13Terms CA2_7_7I1R13Terms_sound) (by decide +kernel)
def CA2_7_7I1R13Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R13Mass_sound : CA2_7_7I1R13Mass.Encloses (∑ a, CA2_7_7I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R13P CA2_7_7I1R13Value CA2_7_7I1R13P_sound) (by decide +kernel)
def CA2_7_7I1R13MassTerm : Ball := .exact 0
lemma CA2_7_7I1R13MassTerm_sound : CA2_7_7I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R13Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R13Mass_sound)
def CA2_7_7I1R13H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R13H_sound : CA2_7_7I1R13H.Encloses (homogeneousEntropy CA2_7_7I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R13Value CA2_7_7I1R13MassTerm_sound CA2_7_7I1R13Entropy_sound) (by decide +kernel)
def CA2_7_7I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA2_7_7I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA2_7_7I1R14Raw_sound (a : PairSlot) :
    (CA2_7_7I1R14Raw a).Encloses (CA2_7_7I1R14Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA2_7_7I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R14Certificates_valid :
    CA2_7_7I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R14Certificates (CA2_7_7I1R14CertificateIndex a)).input
lemma CA2_7_7I1R14P_check : ∀ a : PairSlot, contains (CA2_7_7I1R14Raw a) (CA2_7_7I1R14P a) = true := by
  decide +kernel
lemma CA2_7_7I1R14P_sound (a : PairSlot) :
    (CA2_7_7I1R14P a).Encloses (CA2_7_7I1R14Value a) :=
  contains_sound (CA2_7_7I1R14Raw_sound a) (CA2_7_7I1R14P_check a)
def CA2_7_7I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R14Certificates (CA2_7_7I1R14CertificateIndex a)).output
lemma CA2_7_7I1R14Terms_sound (a : PairSlot) :
    (CA2_7_7I1R14Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R14Certificates_valid
    (CA2_7_7I1R14CertificateIndex a) (CA2_7_7I1R14P_sound a)
def CA2_7_7I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R14Entropy_sound : CA2_7_7I1R14Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R14Value CA2_7_7I1R14Terms CA2_7_7I1R14Terms_sound) (by decide +kernel)
def CA2_7_7I1R14Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R14Mass_sound : CA2_7_7I1R14Mass.Encloses (∑ a, CA2_7_7I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R14P CA2_7_7I1R14Value CA2_7_7I1R14P_sound) (by decide +kernel)
def CA2_7_7I1R14MassTerm : Ball := .exact 0
lemma CA2_7_7I1R14MassTerm_sound : CA2_7_7I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R14Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R14Mass_sound)
def CA2_7_7I1R14H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R14H_sound : CA2_7_7I1R14H.Encloses (homogeneousEntropy CA2_7_7I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R14Value CA2_7_7I1R14MassTerm_sound CA2_7_7I1R14Entropy_sound) (by decide +kernel)
def CA2_7_7I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA2_7_7I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA2_7_7I1R15Raw_sound (a : PairSlot) :
    (CA2_7_7I1R15Raw a).Encloses (CA2_7_7I1R15Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA2_7_7I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R15Certificates_valid :
    CA2_7_7I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R15Certificates (CA2_7_7I1R15CertificateIndex a)).input
lemma CA2_7_7I1R15P_check : ∀ a : PairSlot, contains (CA2_7_7I1R15Raw a) (CA2_7_7I1R15P a) = true := by
  decide +kernel
lemma CA2_7_7I1R15P_sound (a : PairSlot) :
    (CA2_7_7I1R15P a).Encloses (CA2_7_7I1R15Value a) :=
  contains_sound (CA2_7_7I1R15Raw_sound a) (CA2_7_7I1R15P_check a)
def CA2_7_7I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R15Certificates (CA2_7_7I1R15CertificateIndex a)).output
lemma CA2_7_7I1R15Terms_sound (a : PairSlot) :
    (CA2_7_7I1R15Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R15Certificates_valid
    (CA2_7_7I1R15CertificateIndex a) (CA2_7_7I1R15P_sound a)
def CA2_7_7I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R15Entropy_sound : CA2_7_7I1R15Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R15Value CA2_7_7I1R15Terms CA2_7_7I1R15Terms_sound) (by decide +kernel)
def CA2_7_7I1R15Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R15Mass_sound : CA2_7_7I1R15Mass.Encloses (∑ a, CA2_7_7I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R15P CA2_7_7I1R15Value CA2_7_7I1R15P_sound) (by decide +kernel)
def CA2_7_7I1R15MassTerm : Ball := .exact 0
lemma CA2_7_7I1R15MassTerm_sound : CA2_7_7I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R15Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R15Mass_sound)
def CA2_7_7I1R15H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R15H_sound : CA2_7_7I1R15H.Encloses (homogeneousEntropy CA2_7_7I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R15Value CA2_7_7I1R15MassTerm_sound CA2_7_7I1R15Entropy_sound) (by decide +kernel)
def CA2_7_7I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA2_7_7I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 2 7 7)) A2_7_7Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA2_7_7I1R16Raw_sound (a : PairSlot) :
    (CA2_7_7I1R16Raw a).Encloses (CA2_7_7I1R16Value a) := by
  exact residualBall_sound_on (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 2 7 7) (show (shape 2 7 7) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA2_7_7I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA2_7_7I1R16Certificates_valid :
    CA2_7_7I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA2_7_7I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R16Certificates (CA2_7_7I1R16CertificateIndex a)).input
lemma CA2_7_7I1R16P_check : ∀ a : PairSlot, contains (CA2_7_7I1R16Raw a) (CA2_7_7I1R16P a) = true := by
  decide +kernel
lemma CA2_7_7I1R16P_sound (a : PairSlot) :
    (CA2_7_7I1R16P a).Encloses (CA2_7_7I1R16Value a) :=
  contains_sound (CA2_7_7I1R16Raw_sound a) (CA2_7_7I1R16P_check a)
def CA2_7_7I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I1R16Certificates (CA2_7_7I1R16CertificateIndex a)).output
lemma CA2_7_7I1R16Terms_sound (a : PairSlot) :
    (CA2_7_7I1R16Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I1R16Certificates_valid
    (CA2_7_7I1R16CertificateIndex a) (CA2_7_7I1R16P_sound a)
def CA2_7_7I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R16Entropy_sound : CA2_7_7I1R16Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA2_7_7I1R16Value CA2_7_7I1R16Terms CA2_7_7I1R16Terms_sound) (by decide +kernel)
def CA2_7_7I1R16Mass : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R16Mass_sound : CA2_7_7I1R16Mass.Encloses (∑ a, CA2_7_7I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA2_7_7I1R16P CA2_7_7I1R16Value CA2_7_7I1R16P_sound) (by decide +kernel)
def CA2_7_7I1R16MassTerm : Ball := .exact 0
lemma CA2_7_7I1R16MassTerm_sound : CA2_7_7I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I1R16Value a))) :=
  entropyTerm_zero_ball (CA2_7_7I1R16Mass_sound)
def CA2_7_7I1R16H : Ball := ⟨0, 0⟩
lemma CA2_7_7I1R16H_sound : CA2_7_7I1R16H.Encloses (homogeneousEntropy CA2_7_7I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I1R16Value CA2_7_7I1R16MassTerm_sound CA2_7_7I1R16Entropy_sound) (by decide +kernel)
def CA2_7_7I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA2_7_7I1R0H
  | 1 => CA2_7_7I1R1H
  | 2 => CA2_7_7I1R2H
  | 3 => CA2_7_7I1R3H
  | 4 => CA2_7_7I1R4H
  | 5 => CA2_7_7I1R5H
  | 6 => CA2_7_7I1R6H
  | 7 => CA2_7_7I1R7H
  | 8 => CA2_7_7I1R8H
  | 9 => CA2_7_7I1R9H
  | 10 => CA2_7_7I1R10H
  | 11 => CA2_7_7I1R11H
  | 12 => CA2_7_7I1R12H
  | 13 => CA2_7_7I1R13H
  | 14 => CA2_7_7I1R14H
  | 15 => CA2_7_7I1R15H
  | 16 => CA2_7_7I1R16H
  | _ => (.exact 0)
lemma CA2_7_7I1ResidualEntropies_sound (k : Fin 17) :
    (CA2_7_7I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA2_7_7I1R0H_sound
  · exact CA2_7_7I1R1H_sound
  · exact CA2_7_7I1R2H_sound
  · exact CA2_7_7I1R3H_sound
  · exact CA2_7_7I1R4H_sound
  · exact CA2_7_7I1R5H_sound
  · exact CA2_7_7I1R6H_sound
  · exact CA2_7_7I1R7H_sound
  · exact CA2_7_7I1R8H_sound
  · exact CA2_7_7I1R9H_sound
  · exact CA2_7_7I1R10H_sound
  · exact CA2_7_7I1R11H_sound
  · exact CA2_7_7I1R12H_sound
  · exact CA2_7_7I1R13H_sound
  · exact CA2_7_7I1R14H_sound
  · exact CA2_7_7I1R15H_sound
  · exact CA2_7_7I1R16H_sound
def CA2_7_7I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 7, 0 => Z1_7_0H1H
  | 2, 6, 0 => Z2_6_0H1H
  | _, _, _ => (.exact 0)
lemma CA2_7_7I1Singles_sound (u : Shape) (hu : u ∈ below (shape 2 7 7))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA2_7_7I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A2_7_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 0 6) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 1 5) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 2 4) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 3 3) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 4 2) by decide +kernel) hd |>.elim
  · exact (show ¬ designated (Equiv.refl (Fin 3)) 1 (shape 2 5 1) by decide +kernel) hd |>.elim
  · exact Z2_6_0H1H_sound
def CA2_7_7I1Singleton : Ball := ⟨(510743509163288709243151337 / 100000000000000000000000000000000), (19933 / 5000000000000000000000000000000)⟩
lemma CA2_7_7I1Singleton_sound : CA2_7_7I1Singleton.Encloses
    (singletonEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA2_7_7I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A2_7_7Law_sound u) CA2_7_7I1Singles_sound) (by decide +kernel)
def CA2_7_7I1Group : Ball := ⟨(4226886964255699639666683793131 / 4000000000000000000000000000000), (167571867093 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I1Group_sound : CA2_7_7I1Group.Encloses
    (groupedEntropy (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA2_7_7I1Singleton_sound
    (finSumBall_sound 17 CA2_7_7I1ResidualEntropies _ CA2_7_7I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA2_7_7I1H : Ball := ⟨(106734798192338952840863394793203 / 100000000000000000000000000000000), (100109470549 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I1_sound : CA2_7_7I1H.Encloses (stageACapacity (shape 2 7 7) 1) := by
  have hb := contains_sound (Ball.add_sound CA2_7_7I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA2_7_7I1Group_sound)))
    (show contains (.add CA2_7_7I1PairH (.neg (.mul (.exact 2) CA2_7_7I1Group))) CA2_7_7I1H = true by decide +kernel)
  simp only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false]
  change CA2_7_7I1H.Encloses (homogeneousEntropy CA2_7_7I1PairValue - _)
  simpa only [sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
