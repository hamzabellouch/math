import Mathlib
import OAI.LinearAlgebra.MatrixFields.CapacityA.CapA1_6_9I1Pair

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_6_9I1R0Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 0 a
def CA1_6_9I1R0Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 0 a
lemma CA1_6_9I1R0Raw_sound (a : PairSlot) :
    (CA1_6_9I1R0Raw a).Encloses (CA1_6_9I1R0Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 0 a
def CA1_6_9I1R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(8339999762212914871827795077 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩ ⟨(-54366969353445431436392639182027 / 6250000000000000000000000000000), (2316105809 / 781250000000000000000000000000)⟩ ⟨-13, 8339999762212914871827795077, 6103515625000000000000000000⟩]
lemma CA1_6_9I1R0Certificates_valid :
    CA1_6_9I1R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R0CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 0, 0 => 1
  | _, _ => 0
def CA1_6_9I1R0P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R0Certificates (CA1_6_9I1R0CertificateIndex a)).input
lemma CA1_6_9I1R0P_check : ∀ a : PairSlot, contains (CA1_6_9I1R0Raw a) (CA1_6_9I1R0P a) = true := by
  decide +kernel
lemma CA1_6_9I1R0P_sound (a : PairSlot) :
    (CA1_6_9I1R0P a).Encloses (CA1_6_9I1R0Value a) :=
  contains_sound (CA1_6_9I1R0Raw_sound a) (CA1_6_9I1R0P_check a)
def CA1_6_9I1R0Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R0Certificates (CA1_6_9I1R0CertificateIndex a)).output
lemma CA1_6_9I1R0Terms_sound (a : PairSlot) :
    (CA1_6_9I1R0Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R0Certificates_valid
    (CA1_6_9I1R0CertificateIndex a) (CA1_6_9I1R0P_sound a)
def CA1_6_9I1R0Entropy : Ball := ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R0Entropy_sound : CA1_6_9I1R0Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R0Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R0Value CA1_6_9I1R0Terms CA1_6_9I1R0Terms_sound) (by decide +kernel)
def CA1_6_9I1R0Mass : Ball := ⟨(8339999762212914871827795077 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R0Mass_sound : CA1_6_9I1R0Mass.Encloses (∑ a, CA1_6_9I1R0Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R0P CA1_6_9I1R0Value CA1_6_9I1R0P_sound) (by decide +kernel)
def CA1_6_9I1R0MassTermLogWitness : LogWitness := ⟨-13, 8339999762212914871827795077, 6103515625000000000000000000⟩
def CA1_6_9I1R0MassTermLog : Ball := ⟨(-54366969353445431436392639182027 / 6250000000000000000000000000000), (2316105809 / 781250000000000000000000000000)⟩
lemma CA1_6_9I1R0MassTermLog_sound : CA1_6_9I1R0MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R0Mass_sound) (w := CA1_6_9I1R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R0MassTerm : Ball := ⟨(1450945636735909530787380563 / 1000000000000000000000000000000), (24724901 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R0MassTerm_sound : CA1_6_9I1R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R0Mass_sound) CA1_6_9I1R0MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R0H : Ball := ⟨0, (24724901 / 25000000000000000000000000000000)⟩
lemma CA1_6_9I1R0H_sound : CA1_6_9I1R0H.Encloses (homogeneousEntropy CA1_6_9I1R0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R0Value CA1_6_9I1R0MassTerm_sound CA1_6_9I1R0Entropy_sound) (by decide +kernel)
def CA1_6_9I1R1Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 1 a
def CA1_6_9I1R1Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 1 a
lemma CA1_6_9I1R1Raw_sound (a : PairSlot) :
    (CA1_6_9I1R1Raw a).Encloses (CA1_6_9I1R1Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 1 a
def CA1_6_9I1R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(352950608149296318805341356721 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(3496646491070427809635638237251 / 100000000000000000000000000000000), (1345323603 / 100000000000000000000000000000000)⟩ ⟨(-247672507876184481726943786438277 / 50000000000000000000000000000000), (38116482771 / 20000000000000000000000000000000)⟩ ⟨-8, 352950608149296318805341356721, 195312500000000000000000000000⟩]
lemma CA1_6_9I1R1Certificates_valid :
    CA1_6_9I1R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R1CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 0 => 1
  | 0, 1 => 1
  | _, _ => 0
def CA1_6_9I1R1P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R1Certificates (CA1_6_9I1R1CertificateIndex a)).input
lemma CA1_6_9I1R1P_check : ∀ a : PairSlot, contains (CA1_6_9I1R1Raw a) (CA1_6_9I1R1P a) = true := by
  decide +kernel
lemma CA1_6_9I1R1P_sound (a : PairSlot) :
    (CA1_6_9I1R1P a).Encloses (CA1_6_9I1R1Value a) :=
  contains_sound (CA1_6_9I1R1Raw_sound a) (CA1_6_9I1R1P_check a)
def CA1_6_9I1R1Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R1Certificates (CA1_6_9I1R1CertificateIndex a)).output
lemma CA1_6_9I1R1Terms_sound (a : PairSlot) :
    (CA1_6_9I1R1Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R1Certificates_valid
    (CA1_6_9I1R1CertificateIndex a) (CA1_6_9I1R1P_sound a)
def CA1_6_9I1R1Entropy : Ball := ⟨(3496646491070427809635638237251 / 50000000000000000000000000000000), (1345323603 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R1Entropy_sound : CA1_6_9I1R1Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R1Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R1Value CA1_6_9I1R1Terms CA1_6_9I1R1Terms_sound) (by decide +kernel)
def CA1_6_9I1R1Mass : Ball := ⟨(352950608149296318805341356721 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I1R1Mass_sound : CA1_6_9I1R1Mass.Encloses (∑ a, CA1_6_9I1R1Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R1P CA1_6_9I1R1Value CA1_6_9I1R1P_sound) (by decide +kernel)
def CA1_6_9I1R1MassTermLogWitness : LogWitness := ⟨-7, 352950608149296318805341356721, 195312500000000000000000000000⟩
def CA1_6_9I1R1MassTermLog : Ball := ⟨(-26626893606023402032010273739139 / 6250000000000000000000000000000), (42351647543 / 25000000000000000000000000000000)⟩
lemma CA1_6_9I1R1MassTermLog_sound : CA1_6_9I1R1MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R1Mass_sound) (w := CA1_6_9I1R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R1MassTerm : Ball := ⟨(6014706106478444419857431517203 / 100000000000000000000000000000000), (478337281 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I1R1MassTerm_sound : CA1_6_9I1R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R1Mass_sound) CA1_6_9I1R1MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R1H : Ball := ⟨(978586875662411199413844957299 / 100000000000000000000000000000000), (5082333611 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I1R1H_sound : CA1_6_9I1R1H.Encloses (homogeneousEntropy CA1_6_9I1R1Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R1Value CA1_6_9I1R1MassTerm_sound CA1_6_9I1R1Entropy_sound) (by decide +kernel)
def CA1_6_9I1R2Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 2 a
def CA1_6_9I1R2Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 2 a
lemma CA1_6_9I1R2Raw_sound (a : PairSlot) :
    (CA1_6_9I1R2Raw a).Encloses (CA1_6_9I1R2Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 2 a
def CA1_6_9I1R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3750256193599697178331260570691 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(12313388784911392649224959762473 / 100000000000000000000000000000000), (952977181 / 20000000000000000000000000000000)⟩ ⟨(-328334603004610765255022211056333 / 100000000000000000000000000000000), (31763735631 / 25000000000000000000000000000000)⟩ ⟨-5, 3750256193599697178331260570691, 3125000000000000000000000000000⟩,
   .log ⟨(96463806186056584059676008661 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩ ⟨(428875244823396362642940222883 / 20000000000000000000000000000000), (817080241 / 100000000000000000000000000000000)⟩ ⟨(-69468290391118668442947267645409 / 12500000000000000000000000000000), (211758237607 / 100000000000000000000000000000000)⟩ ⟨-9, 96463806186056584059676008661, 48828125000000000000000000000⟩,
   .log ⟨(13846809169340604683773678740841 / 100000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩ ⟨(3422092395239441090087522368893 / 12500000000000000000000000000000), (1172870369 / 10000000000000000000000000000000)⟩ ⟨(-98855768239128658880322037043519 / 50000000000000000000000000000000), (84703294991 / 100000000000000000000000000000000)⟩ ⟨-3, 13846809169340604683773678740841, 12500000000000000000000000000000⟩]
lemma CA1_6_9I1R2Certificates_valid :
    CA1_6_9I1R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R2CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 0 => 1
  | 3, 0 => 2
  | 1, 1 => 3
  | 0, 2 => 1
  | 0, 3 => 2
  | _, _ => 0
def CA1_6_9I1R2P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R2Certificates (CA1_6_9I1R2CertificateIndex a)).input
lemma CA1_6_9I1R2P_check : ∀ a : PairSlot, contains (CA1_6_9I1R2Raw a) (CA1_6_9I1R2P a) = true := by
  decide +kernel
lemma CA1_6_9I1R2P_sound (a : PairSlot) :
    (CA1_6_9I1R2P a).Encloses (CA1_6_9I1R2Value a) :=
  contains_sound (CA1_6_9I1R2Raw_sound a) (CA1_6_9I1R2P_check a)
def CA1_6_9I1R2Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R2Certificates (CA1_6_9I1R2CertificateIndex a)).output
lemma CA1_6_9I1R2Terms_sound (a : PairSlot) :
    (CA1_6_9I1R2Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R2Certificates_valid
    (CA1_6_9I1R2CertificateIndex a) (CA1_6_9I1R2P_sound a)
def CA1_6_9I1R2Entropy : Ball := ⟨(1407306729499306941139487517623 / 2500000000000000000000000000000), (11446317991 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R2Entropy_sound : CA1_6_9I1R2Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R2Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R2Value CA1_6_9I1R2Terms CA1_6_9I1R2Terms_sound) (by decide +kernel)
def CA1_6_9I1R2Mass : Ball := ⟨(22119032006028451712913607951511 / 100000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R2Mass_sound : CA1_6_9I1R2Mass.Encloses (∑ a, CA1_6_9I1R2Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R2P CA1_6_9I1R2Value CA1_6_9I1R2P_sound) (by decide +kernel)
def CA1_6_9I1R2MassTermLogWitness : LogWitness := ⟨-3, 22119032006028451712913607951511, 12500000000000000000000000000000⟩
def CA1_6_9I1R2MassTermLog : Ball := ⟨(-4714786785377982092429811765109 / 3125000000000000000000000000000), (42351647533 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R2MassTermLog_sound : CA1_6_9I1R2MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R2Mass_sound) (w := CA1_6_9I1R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R2MassTerm : Ball := ⟨(1668584316918009319523460857527 / 5000000000000000000000000000000), (9367774529 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R2MassTerm_sound : CA1_6_9I1R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R2Mass_sound) CA1_6_9I1R2MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R2H : Ball := ⟨(1146029142080604562755514177719 / 5000000000000000000000000000000), (520352313 / 1250000000000000000000000000000)⟩
lemma CA1_6_9I1R2H_sound : CA1_6_9I1R2H.Encloses (homogeneousEntropy CA1_6_9I1R2Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R2Value CA1_6_9I1R2MassTerm_sound CA1_6_9I1R2Entropy_sound) (by decide +kernel)
def CA1_6_9I1R3Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 3 a
def CA1_6_9I1R3Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 3 a
lemma CA1_6_9I1R3Raw_sound (a : PairSlot) :
    (CA1_6_9I1R3Raw a).Encloses (CA1_6_9I1R3Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 3 a
def CA1_6_9I1R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(262997359306142918070847892299 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(2395636167101722520226825879023 / 50000000000000000000000000000000), (27845929 / 1562500000000000000000000000000)⟩ ⟨(-1821794844953613827296409995907 / 400000000000000000000000000000), (169406589939 / 100000000000000000000000000000000)⟩ ⟨-7, 262997359306142918070847892299, 195312500000000000000000000000⟩,
   .log ⟨(5788381024642755450801079594891 / 25000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩ ⟨(3387414264386620807997353345651 / 10000000000000000000000000000000), (1225737367 / 6250000000000000000000000000000)⟩ ⟨(-3657557970403826810673592756509 / 2500000000000000000000000000000), (8470329493 / 10000000000000000000000000000000)⟩ ⟨-3, 5788381024642755450801079594891, 3125000000000000000000000000000⟩,
   .log ⟨(561743006513585926658415270673 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩ ⟨(341143080310919619072648549763 / 4000000000000000000000000000000), (3330703861 / 100000000000000000000000000000000)⟩ ⟨(-379558664232641596305435459734451 / 100000000000000000000000000000000), (74115382979 / 50000000000000000000000000000000)⟩ ⟨-6, 561743006513585926658415270673, 390625000000000000000000000000⟩]
lemma CA1_6_9I1R3Certificates_valid :
    CA1_6_9I1R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R3CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 4, 0 => 1
  | 2, 1 => 2
  | 3, 1 => 3
  | 1, 2 => 2
  | 1, 3 => 3
  | 0, 4 => 1
  | _, _ => 0
def CA1_6_9I1R3P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R3Certificates (CA1_6_9I1R3CertificateIndex a)).input
lemma CA1_6_9I1R3P_check : ∀ a : PairSlot, contains (CA1_6_9I1R3Raw a) (CA1_6_9I1R3P a) = true := by
  decide +kernel
lemma CA1_6_9I1R3P_sound (a : PairSlot) :
    (CA1_6_9I1R3P a).Encloses (CA1_6_9I1R3Value a) :=
  contains_sound (CA1_6_9I1R3Raw_sound a) (CA1_6_9I1R3P_check a)
def CA1_6_9I1R3Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R3Certificates (CA1_6_9I1R3CertificateIndex a)).output
lemma CA1_6_9I1R3Terms_sound (a : PairSlot) :
    (CA1_6_9I1R3Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R3Certificates_valid
    (CA1_6_9I1R3CertificateIndex a) (CA1_6_9I1R3P_sound a)
def CA1_6_9I1R3Entropy : Ball := ⟨(47193991985842643597243398958631 / 50000000000000000000000000000000), (24724641189 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R3Entropy_sound : CA1_6_9I1R3Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R3Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R3Value CA1_6_9I1R3Terms CA1_6_9I1R3Terms_sound) (by decide +kernel)
def CA1_6_9I1R3Mass : Ball := ⟨(6613121390462484295530342757863 / 12500000000000000000000000000000), (11 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I1R3Mass_sound : CA1_6_9I1R3Mass.Encloses (∑ a, CA1_6_9I1R3Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R3P CA1_6_9I1R3Value CA1_6_9I1R3P_sound) (by decide +kernel)
def CA1_6_9I1R3MassTermLogWitness : LogWitness := ⟨-1, 6613121390462484295530342757863, 6250000000000000000000000000000⟩
def CA1_6_9I1R3MassTermLog : Ball := ⟨(-795841099307891183778313920487 / 1250000000000000000000000000000), (42351647573 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I1R3MassTermLog_sound : CA1_6_9I1R3MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R3Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R3Mass_sound) (w := CA1_6_9I1R3MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R3MassTerm : Ball := ⟨(33683160302350037717787471431689 / 100000000000000000000000000000000), (2240612699 / 10000000000000000000000000000000)⟩
lemma CA1_6_9I1R3MassTerm_sound : CA1_6_9I1R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R3Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R3Mass_sound) CA1_6_9I1R3MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R3H : Ball := ⟨(60704823669335249476699326485573 / 100000000000000000000000000000000), (8981926171 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I1R3H_sound : CA1_6_9I1R3H.Encloses (homogeneousEntropy CA1_6_9I1R3Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R3Value CA1_6_9I1R3MassTerm_sound CA1_6_9I1R3Entropy_sound) (by decide +kernel)
def CA1_6_9I1R4Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 4 a
def CA1_6_9I1R4Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 4 a
lemma CA1_6_9I1R4Raw_sound (a : PairSlot) :
    (CA1_6_9I1R4Raw a).Encloses (CA1_6_9I1R4Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 4 a
def CA1_6_9I1R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(35826987774826412940031031201 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(142129673252656233185977844649 / 50000000000000000000000000000000), (98626587 / 100000000000000000000000000000000)⟩ ⟨(-396711200355288234932394326306789 / 50000000000000000000000000000000), (275285710669 / 100000000000000000000000000000000)⟩ ⟨-12, 35826987774826412940031031201, 24414062500000000000000000000⟩,
   .log ⟨(163534707329622154185550545721 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩ ⟨(9532926071727824250208934309911 / 100000000000000000000000000000000), (969635009 / 25000000000000000000000000000000)⟩ ⟨(-72866229953507402120495250057111 / 20000000000000000000000000000000), (148230766201 / 100000000000000000000000000000000)⟩ ⟨-6, 163534707329622154185550545721, 97656250000000000000000000000⟩,
   .log ⟨(879221464663087013174741520473 / 6250000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(3448833987306901485794990391481 / 12500000000000000000000000000000), (2978918233 / 25000000000000000000000000000000)⟩ ⟨(-39225998521640691723875329727651 / 20000000000000000000000000000000), (84703295101 / 100000000000000000000000000000000)⟩ ⟨-3, 879221464663087013174741520473, 781250000000000000000000000000⟩,
   .log ⟨(1310487633486652602794470143421 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(2840331815290867417715528693877 / 50000000000000000000000000000000), (1110026219 / 50000000000000000000000000000000)⟩ ⟨(-27092317992100651631905078306153 / 6250000000000000000000000000000), (169406589921 / 100000000000000000000000000000000)⟩ ⟨-7, 1310487633486652602794470143421, 781250000000000000000000000000⟩,
   .log ⟨(31437173587048134177780952907 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(419915132460468872428984587311 / 50000000000000000000000000000000), (73227887 / 25000000000000000000000000000000)⟩ ⟨(-166966000974031016161403637963159 / 25000000000000000000000000000000), (58233515327 / 25000000000000000000000000000000)⟩ ⟨-10, 31437173587048134177780952907, 24414062500000000000000000000⟩]
lemma CA1_6_9I1R4Certificates_valid :
    CA1_6_9I1R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R4CertificateIndex (a : PairSlot) : ℕ :=
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
def CA1_6_9I1R4P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R4Certificates (CA1_6_9I1R4CertificateIndex a)).input
lemma CA1_6_9I1R4P_check : ∀ a : PairSlot, contains (CA1_6_9I1R4Raw a) (CA1_6_9I1R4P a) = true := by
  decide +kernel
lemma CA1_6_9I1R4P_sound (a : PairSlot) :
    (CA1_6_9I1R4P a).Encloses (CA1_6_9I1R4Value a) :=
  contains_sound (CA1_6_9I1R4Raw_sound a) (CA1_6_9I1R4P_check a)
def CA1_6_9I1R4Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R4Certificates (CA1_6_9I1R4CertificateIndex a)).output
lemma CA1_6_9I1R4Terms_sound (a : PairSlot) :
    (CA1_6_9I1R4Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R4Certificates_valid
    (CA1_6_9I1R4CertificateIndex a) (CA1_6_9I1R4P_sound a)
def CA1_6_9I1R4Entropy : Ball := ⟨(14856550065251473183810446770099 / 25000000000000000000000000000000), (12301511301 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R4Entropy_sound : CA1_6_9I1R4Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R4Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R4Value CA1_6_9I1R4Terms CA1_6_9I1R4Terms_sound) (by decide +kernel)
def CA1_6_9I1R4Mass : Ball := ⟨(2764879000753556464114200993939 / 12500000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I1R4Mass_sound : CA1_6_9I1R4Mass.Encloses (∑ a, CA1_6_9I1R4Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R4P CA1_6_9I1R4Value CA1_6_9I1R4P_sound) (by decide +kernel)
def CA1_6_9I1R4MassTermLogWitness : LogWitness := ⟨-3, 2764879000753556464114200993939, 1562500000000000000000000000000⟩
def CA1_6_9I1R4MassTermLog : Ball := ⟨(-150873177132095426957753976483483 / 100000000000000000000000000000000), (42351647567 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R4MassTermLog_sound : CA1_6_9I1R4MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R4Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R4Mass_sound) (w := CA1_6_9I1R4MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R4MassTerm : Ball := ⟨(1668584316918009319523460857527 / 5000000000000000000000000000000), (2341943637 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I1R4MassTerm_sound : CA1_6_9I1R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R4Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R4Mass_sound) CA1_6_9I1R4MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R4H : Ball := ⟨(203550890020669580818535702577 / 781250000000000000000000000000), (21669285849 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R4H_sound : CA1_6_9I1R4H.Encloses (homogeneousEntropy CA1_6_9I1R4Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R4Value CA1_6_9I1R4MassTerm_sound CA1_6_9I1R4Entropy_sound) (by decide +kernel)
def CA1_6_9I1R5Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 5 a
def CA1_6_9I1R5Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 5 a
lemma CA1_6_9I1R5Raw_sound (a : PairSlot) :
    (CA1_6_9I1R5Raw a).Encloses (CA1_6_9I1R5Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 5 a
def CA1_6_9I1R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18501565179107019817172619 / 62500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(4810446319640869613227379209 / 2000000000000000000000000000000), (81491473 / 100000000000000000000000000000000)⟩ ⟨(-812506650294289851993150014054797 / 100000000000000000000000000000000), (34410713907 / 12500000000000000000000000000000)⟩ ⟨-12, 18501565179107019817172619, 15258789062500000000000000⟩,
   .log ⟨(620735982479902521471775500981 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1577296221653711324887320429691 / 50000000000000000000000000000000), (591506823 / 50000000000000000000000000000000)⟩ ⟨(-254100981121193375479592091504871 / 50000000000000000000000000000000), (1488925109 / 781250000000000000000000000000)⟩ ⟨-8, 620735982479902521471775500981, 390625000000000000000000000000⟩,
   .log ⟨(55562729532118884431431022061 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(83293119056991338824175993333 / 20000000000000000000000000000000), (141190397 / 100000000000000000000000000000000)⟩ ⟨(-14990825641285761383223078064461 / 2000000000000000000000000000000), (50821977199 / 20000000000000000000000000000000)⟩ ⟨-11, 55562729532118884431431022061, 48828125000000000000000000000⟩]
lemma CA1_6_9I1R5Certificates_valid :
    CA1_6_9I1R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R5CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 1, 5 => 1
  | 2, 4 => 2
  | 3, 4 => 3
  | 4, 2 => 2
  | 4, 3 => 3
  | 5, 1 => 1
  | _, _ => 0
def CA1_6_9I1R5P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R5Certificates (CA1_6_9I1R5CertificateIndex a)).input
lemma CA1_6_9I1R5P_check : ∀ a : PairSlot, contains (CA1_6_9I1R5Raw a) (CA1_6_9I1R5P a) = true := by
  decide +kernel
lemma CA1_6_9I1R5P_sound (a : PairSlot) :
    (CA1_6_9I1R5P a).Encloses (CA1_6_9I1R5Value a) :=
  contains_sound (CA1_6_9I1R5Raw_sound a) (CA1_6_9I1R5P_check a)
def CA1_6_9I1R5Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R5Certificates (CA1_6_9I1R5CertificateIndex a)).output
lemma CA1_6_9I1R5Terms_sound (a : PairSlot) :
    (CA1_6_9I1R5Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R5Certificates_valid
    (CA1_6_9I1R5CertificateIndex a) (CA1_6_9I1R5P_sound a)
def CA1_6_9I1R5Entropy : Ball := ⟨(3811580354574422824556889786497 / 50000000000000000000000000000000), (351423879 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I1R5Entropy_sound : CA1_6_9I1R5Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R5Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R5Value CA1_6_9I1R5Terms CA1_6_9I1R5Terms_sound) (by decide +kernel)
def CA1_6_9I1R5Mass : Ball := ⟨(352950608149296318805341356721 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R5Mass_sound : CA1_6_9I1R5Mass.Encloses (∑ a, CA1_6_9I1R5Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R5P CA1_6_9I1R5Value CA1_6_9I1R5P_sound) (by decide +kernel)
def CA1_6_9I1R5MassTermLogWitness : LogWitness := ⟨-7, 352950608149296318805341356721, 195312500000000000000000000000⟩
def CA1_6_9I1R5MassTermLog : Ball := ⟨(-26626893606023402032010273739139 / 6250000000000000000000000000000), (33881318091 / 20000000000000000000000000000000)⟩
lemma CA1_6_9I1R5MassTermLog_sound : CA1_6_9I1R5MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R5Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R5Mass_sound) (w := CA1_6_9I1R5MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R5MassTerm : Ball := ⟨(6014706106478444419857431517203 / 100000000000000000000000000000000), (1195843213 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R5MassTerm_sound : CA1_6_9I1R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R5Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R5Mass_sound) CA1_6_9I1R5MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R5H : Ball := ⟨(1608454602670401229256348055791 / 100000000000000000000000000000000), (2601538729 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R5H_sound : CA1_6_9I1R5H.Encloses (homogeneousEntropy CA1_6_9I1R5Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R5Value CA1_6_9I1R5MassTerm_sound CA1_6_9I1R5Entropy_sound) (by decide +kernel)
def CA1_6_9I1R6Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 6 a
def CA1_6_9I1R6Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 6 a
lemma CA1_6_9I1R6Raw_sound (a : PairSlot) :
    (CA1_6_9I1R6Raw a).Encloses (CA1_6_9I1R6Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 6 a
def CA1_6_9I1R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(657080921971796282931564339 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(27719823945490765311282689673 / 100000000000000000000000000000000), (9461689 / 100000000000000000000000000000000)⟩ ⟨(-131832240037821096251951760685329 / 12500000000000000000000000000000), (179994520329 / 50000000000000000000000000000000)⟩ ⟨-16, 657080921971796282931564339, 381469726562500000000000000⟩,
   .log ⟨(94111745008810675585318067 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(1240679906901828064584075781 / 50000000000000000000000000000000), (83703 / 10000000000000000000000000000000)⟩ ⟨(-1318305071046845939950790763193751 / 100000000000000000000000000000000), (222346414313 / 50000000000000000000000000000000)⟩ ⟨-20, 94111745008810675585318067, 47683715820312500000000000⟩,
   .log ⟨(441876206744648671114472127 / 4000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(100645869110909624952901605809 / 100000000000000000000000000000000), (17544559 / 50000000000000000000000000000000)⟩ ⟨(-911077515147321236108554608474889 / 100000000000000000000000000000000), (317637373349 / 100000000000000000000000000000000)⟩ ⟨-14, 441876206744648671114472127, 244140625000000000000000000⟩]
lemma CA1_6_9I1R6Certificates_valid :
    CA1_6_9I1R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R6CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 2, 5 => 1
  | 3, 5 => 2
  | 4, 4 => 3
  | 5, 2 => 1
  | 5, 3 => 2
  | _, _ => 0
def CA1_6_9I1R6P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R6Certificates (CA1_6_9I1R6CertificateIndex a)).input
lemma CA1_6_9I1R6P_check : ∀ a : PairSlot, contains (CA1_6_9I1R6Raw a) (CA1_6_9I1R6P a) = true := by
  decide +kernel
lemma CA1_6_9I1R6P_sound (a : PairSlot) :
    (CA1_6_9I1R6P a).Encloses (CA1_6_9I1R6Value a) :=
  contains_sound (CA1_6_9I1R6Raw_sound a) (CA1_6_9I1R6P_check a)
def CA1_6_9I1R6Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R6Certificates (CA1_6_9I1R6CertificateIndex a)).output
lemma CA1_6_9I1R6Terms_sound (a : PairSlot) :
    (CA1_6_9I1R6Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R6Certificates_valid
    (CA1_6_9I1R6CertificateIndex a) (CA1_6_9I1R6P_sound a)
def CA1_6_9I1R6Entropy : Ball := ⟨(161048236629498467833803288279 / 100000000000000000000000000000000), (13921639 / 25000000000000000000000000000000)⟩
lemma CA1_6_9I1R6Entropy_sound : CA1_6_9I1R6Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R6Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R6Value CA1_6_9I1R6Terms CA1_6_9I1R6Terms_sound) (by decide +kernel)
def CA1_6_9I1R6Mass : Ball := ⟨(3335999904885165948731118031 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
lemma CA1_6_9I1R6Mass_sound : CA1_6_9I1R6Mass.Encloses (∑ a, CA1_6_9I1R6Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R6P CA1_6_9I1R6Value CA1_6_9I1R6P_sound) (by decide +kernel)
def CA1_6_9I1R6MassTermLogWitness : LogWitness := ⟨-13, 3335999904885165948731118031, 2441406250000000000000000000⟩
def CA1_6_9I1R6MassTermLog : Ball := ⟨(-869871509655126902982282226906437 / 100000000000000000000000000000000), (74115391883 / 25000000000000000000000000000000)⟩
lemma CA1_6_9I1R6MassTermLog_sound : CA1_6_9I1R6MassTermLog.Encloses (Real.log ((∑ a, CA1_6_9I1R6Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_6_9I1R6Mass_sound) (w := CA1_6_9I1R6MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_6_9I1R6MassTerm : Ball := ⟨(36273640918397738269684514077 / 25000000000000000000000000000000), (49449841 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I1R6MassTerm_sound : CA1_6_9I1R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R6Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_6_9I1R6Mass_sound) CA1_6_9I1R6MassTermLog_sound) (by decide +kernel)
def CA1_6_9I1R6H : Ball := ⟨(15953672955907514755065231971 / 100000000000000000000000000000000), (105136397 / 100000000000000000000000000000000)⟩
lemma CA1_6_9I1R6H_sound : CA1_6_9I1R6H.Encloses (homogeneousEntropy CA1_6_9I1R6Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R6Value CA1_6_9I1R6MassTerm_sound CA1_6_9I1R6Entropy_sound) (by decide +kernel)
def CA1_6_9I1R7Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 7 a
def CA1_6_9I1R7Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 7 a
lemma CA1_6_9I1R7Raw_sound (a : PairSlot) :
    (CA1_6_9I1R7Raw a).Encloses (CA1_6_9I1R7Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 7 a
def CA1_6_9I1R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R7Certificates_valid :
    CA1_6_9I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R7CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R7P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R7Certificates (CA1_6_9I1R7CertificateIndex a)).input
lemma CA1_6_9I1R7P_check : ∀ a : PairSlot, contains (CA1_6_9I1R7Raw a) (CA1_6_9I1R7P a) = true := by
  decide +kernel
lemma CA1_6_9I1R7P_sound (a : PairSlot) :
    (CA1_6_9I1R7P a).Encloses (CA1_6_9I1R7Value a) :=
  contains_sound (CA1_6_9I1R7Raw_sound a) (CA1_6_9I1R7P_check a)
def CA1_6_9I1R7Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R7Certificates (CA1_6_9I1R7CertificateIndex a)).output
lemma CA1_6_9I1R7Terms_sound (a : PairSlot) :
    (CA1_6_9I1R7Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R7Certificates_valid
    (CA1_6_9I1R7CertificateIndex a) (CA1_6_9I1R7P_sound a)
def CA1_6_9I1R7Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R7Entropy_sound : CA1_6_9I1R7Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R7Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R7Value CA1_6_9I1R7Terms CA1_6_9I1R7Terms_sound) (by decide +kernel)
def CA1_6_9I1R7Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R7Mass_sound : CA1_6_9I1R7Mass.Encloses (∑ a, CA1_6_9I1R7Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R7P CA1_6_9I1R7Value CA1_6_9I1R7P_sound) (by decide +kernel)
def CA1_6_9I1R7MassTerm : Ball := .exact 0
lemma CA1_6_9I1R7MassTerm_sound : CA1_6_9I1R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R7Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R7Mass_sound)
def CA1_6_9I1R7H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R7H_sound : CA1_6_9I1R7H.Encloses (homogeneousEntropy CA1_6_9I1R7Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R7Value CA1_6_9I1R7MassTerm_sound CA1_6_9I1R7Entropy_sound) (by decide +kernel)
def CA1_6_9I1R8Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 8 a
def CA1_6_9I1R8Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 8 a
lemma CA1_6_9I1R8Raw_sound (a : PairSlot) :
    (CA1_6_9I1R8Raw a).Encloses (CA1_6_9I1R8Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 8 a
def CA1_6_9I1R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R8Certificates_valid :
    CA1_6_9I1R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R8CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R8P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R8Certificates (CA1_6_9I1R8CertificateIndex a)).input
lemma CA1_6_9I1R8P_check : ∀ a : PairSlot, contains (CA1_6_9I1R8Raw a) (CA1_6_9I1R8P a) = true := by
  decide +kernel
lemma CA1_6_9I1R8P_sound (a : PairSlot) :
    (CA1_6_9I1R8P a).Encloses (CA1_6_9I1R8Value a) :=
  contains_sound (CA1_6_9I1R8Raw_sound a) (CA1_6_9I1R8P_check a)
def CA1_6_9I1R8Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R8Certificates (CA1_6_9I1R8CertificateIndex a)).output
lemma CA1_6_9I1R8Terms_sound (a : PairSlot) :
    (CA1_6_9I1R8Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R8Certificates_valid
    (CA1_6_9I1R8CertificateIndex a) (CA1_6_9I1R8P_sound a)
def CA1_6_9I1R8Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R8Entropy_sound : CA1_6_9I1R8Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R8Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R8Value CA1_6_9I1R8Terms CA1_6_9I1R8Terms_sound) (by decide +kernel)
def CA1_6_9I1R8Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R8Mass_sound : CA1_6_9I1R8Mass.Encloses (∑ a, CA1_6_9I1R8Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R8P CA1_6_9I1R8Value CA1_6_9I1R8P_sound) (by decide +kernel)
def CA1_6_9I1R8MassTerm : Ball := .exact 0
lemma CA1_6_9I1R8MassTerm_sound : CA1_6_9I1R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R8Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R8Mass_sound)
def CA1_6_9I1R8H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R8H_sound : CA1_6_9I1R8H.Encloses (homogeneousEntropy CA1_6_9I1R8Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R8Value CA1_6_9I1R8MassTerm_sound CA1_6_9I1R8Entropy_sound) (by decide +kernel)
def CA1_6_9I1R9Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 9 a
def CA1_6_9I1R9Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 9 a
lemma CA1_6_9I1R9Raw_sound (a : PairSlot) :
    (CA1_6_9I1R9Raw a).Encloses (CA1_6_9I1R9Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 9 a
def CA1_6_9I1R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R9Certificates_valid :
    CA1_6_9I1R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R9CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R9P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R9Certificates (CA1_6_9I1R9CertificateIndex a)).input
lemma CA1_6_9I1R9P_check : ∀ a : PairSlot, contains (CA1_6_9I1R9Raw a) (CA1_6_9I1R9P a) = true := by
  decide +kernel
lemma CA1_6_9I1R9P_sound (a : PairSlot) :
    (CA1_6_9I1R9P a).Encloses (CA1_6_9I1R9Value a) :=
  contains_sound (CA1_6_9I1R9Raw_sound a) (CA1_6_9I1R9P_check a)
def CA1_6_9I1R9Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R9Certificates (CA1_6_9I1R9CertificateIndex a)).output
lemma CA1_6_9I1R9Terms_sound (a : PairSlot) :
    (CA1_6_9I1R9Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R9Certificates_valid
    (CA1_6_9I1R9CertificateIndex a) (CA1_6_9I1R9P_sound a)
def CA1_6_9I1R9Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R9Entropy_sound : CA1_6_9I1R9Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R9Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R9Value CA1_6_9I1R9Terms CA1_6_9I1R9Terms_sound) (by decide +kernel)
def CA1_6_9I1R9Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R9Mass_sound : CA1_6_9I1R9Mass.Encloses (∑ a, CA1_6_9I1R9Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R9P CA1_6_9I1R9Value CA1_6_9I1R9P_sound) (by decide +kernel)
def CA1_6_9I1R9MassTerm : Ball := .exact 0
lemma CA1_6_9I1R9MassTerm_sound : CA1_6_9I1R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R9Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R9Mass_sound)
def CA1_6_9I1R9H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R9H_sound : CA1_6_9I1R9H.Encloses (homogeneousEntropy CA1_6_9I1R9Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R9Value CA1_6_9I1R9MassTerm_sound CA1_6_9I1R9Entropy_sound) (by decide +kernel)
def CA1_6_9I1R10Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 10 a
def CA1_6_9I1R10Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 10 a
lemma CA1_6_9I1R10Raw_sound (a : PairSlot) :
    (CA1_6_9I1R10Raw a).Encloses (CA1_6_9I1R10Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 10 a
def CA1_6_9I1R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R10Certificates_valid :
    CA1_6_9I1R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R10CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R10P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R10Certificates (CA1_6_9I1R10CertificateIndex a)).input
lemma CA1_6_9I1R10P_check : ∀ a : PairSlot, contains (CA1_6_9I1R10Raw a) (CA1_6_9I1R10P a) = true := by
  decide +kernel
lemma CA1_6_9I1R10P_sound (a : PairSlot) :
    (CA1_6_9I1R10P a).Encloses (CA1_6_9I1R10Value a) :=
  contains_sound (CA1_6_9I1R10Raw_sound a) (CA1_6_9I1R10P_check a)
def CA1_6_9I1R10Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R10Certificates (CA1_6_9I1R10CertificateIndex a)).output
lemma CA1_6_9I1R10Terms_sound (a : PairSlot) :
    (CA1_6_9I1R10Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R10Certificates_valid
    (CA1_6_9I1R10CertificateIndex a) (CA1_6_9I1R10P_sound a)
def CA1_6_9I1R10Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R10Entropy_sound : CA1_6_9I1R10Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R10Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R10Value CA1_6_9I1R10Terms CA1_6_9I1R10Terms_sound) (by decide +kernel)
def CA1_6_9I1R10Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R10Mass_sound : CA1_6_9I1R10Mass.Encloses (∑ a, CA1_6_9I1R10Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R10P CA1_6_9I1R10Value CA1_6_9I1R10P_sound) (by decide +kernel)
def CA1_6_9I1R10MassTerm : Ball := .exact 0
lemma CA1_6_9I1R10MassTerm_sound : CA1_6_9I1R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R10Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R10Mass_sound)
def CA1_6_9I1R10H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R10H_sound : CA1_6_9I1R10H.Encloses (homogeneousEntropy CA1_6_9I1R10Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R10Value CA1_6_9I1R10MassTerm_sound CA1_6_9I1R10Entropy_sound) (by decide +kernel)
def CA1_6_9I1R11Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 11 a
def CA1_6_9I1R11Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 11 a
lemma CA1_6_9I1R11Raw_sound (a : PairSlot) :
    (CA1_6_9I1R11Raw a).Encloses (CA1_6_9I1R11Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 11 a
def CA1_6_9I1R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R11Certificates_valid :
    CA1_6_9I1R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R11CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R11P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R11Certificates (CA1_6_9I1R11CertificateIndex a)).input
lemma CA1_6_9I1R11P_check : ∀ a : PairSlot, contains (CA1_6_9I1R11Raw a) (CA1_6_9I1R11P a) = true := by
  decide +kernel
lemma CA1_6_9I1R11P_sound (a : PairSlot) :
    (CA1_6_9I1R11P a).Encloses (CA1_6_9I1R11Value a) :=
  contains_sound (CA1_6_9I1R11Raw_sound a) (CA1_6_9I1R11P_check a)
def CA1_6_9I1R11Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R11Certificates (CA1_6_9I1R11CertificateIndex a)).output
lemma CA1_6_9I1R11Terms_sound (a : PairSlot) :
    (CA1_6_9I1R11Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R11Certificates_valid
    (CA1_6_9I1R11CertificateIndex a) (CA1_6_9I1R11P_sound a)
def CA1_6_9I1R11Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R11Entropy_sound : CA1_6_9I1R11Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R11Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R11Value CA1_6_9I1R11Terms CA1_6_9I1R11Terms_sound) (by decide +kernel)
def CA1_6_9I1R11Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R11Mass_sound : CA1_6_9I1R11Mass.Encloses (∑ a, CA1_6_9I1R11Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R11P CA1_6_9I1R11Value CA1_6_9I1R11P_sound) (by decide +kernel)
def CA1_6_9I1R11MassTerm : Ball := .exact 0
lemma CA1_6_9I1R11MassTerm_sound : CA1_6_9I1R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R11Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R11Mass_sound)
def CA1_6_9I1R11H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R11H_sound : CA1_6_9I1R11H.Encloses (homogeneousEntropy CA1_6_9I1R11Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R11Value CA1_6_9I1R11MassTerm_sound CA1_6_9I1R11Entropy_sound) (by decide +kernel)
def CA1_6_9I1R12Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 12 a
def CA1_6_9I1R12Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 12 a
lemma CA1_6_9I1R12Raw_sound (a : PairSlot) :
    (CA1_6_9I1R12Raw a).Encloses (CA1_6_9I1R12Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 12 a
def CA1_6_9I1R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R12Certificates_valid :
    CA1_6_9I1R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R12CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R12P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R12Certificates (CA1_6_9I1R12CertificateIndex a)).input
lemma CA1_6_9I1R12P_check : ∀ a : PairSlot, contains (CA1_6_9I1R12Raw a) (CA1_6_9I1R12P a) = true := by
  decide +kernel
lemma CA1_6_9I1R12P_sound (a : PairSlot) :
    (CA1_6_9I1R12P a).Encloses (CA1_6_9I1R12Value a) :=
  contains_sound (CA1_6_9I1R12Raw_sound a) (CA1_6_9I1R12P_check a)
def CA1_6_9I1R12Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R12Certificates (CA1_6_9I1R12CertificateIndex a)).output
lemma CA1_6_9I1R12Terms_sound (a : PairSlot) :
    (CA1_6_9I1R12Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R12Certificates_valid
    (CA1_6_9I1R12CertificateIndex a) (CA1_6_9I1R12P_sound a)
def CA1_6_9I1R12Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R12Entropy_sound : CA1_6_9I1R12Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R12Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R12Value CA1_6_9I1R12Terms CA1_6_9I1R12Terms_sound) (by decide +kernel)
def CA1_6_9I1R12Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R12Mass_sound : CA1_6_9I1R12Mass.Encloses (∑ a, CA1_6_9I1R12Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R12P CA1_6_9I1R12Value CA1_6_9I1R12P_sound) (by decide +kernel)
def CA1_6_9I1R12MassTerm : Ball := .exact 0
lemma CA1_6_9I1R12MassTerm_sound : CA1_6_9I1R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R12Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R12Mass_sound)
def CA1_6_9I1R12H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R12H_sound : CA1_6_9I1R12H.Encloses (homogeneousEntropy CA1_6_9I1R12Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R12Value CA1_6_9I1R12MassTerm_sound CA1_6_9I1R12Entropy_sound) (by decide +kernel)
def CA1_6_9I1R13Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 13 a
def CA1_6_9I1R13Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 13 a
lemma CA1_6_9I1R13Raw_sound (a : PairSlot) :
    (CA1_6_9I1R13Raw a).Encloses (CA1_6_9I1R13Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 13 a
def CA1_6_9I1R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R13Certificates_valid :
    CA1_6_9I1R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R13CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R13P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R13Certificates (CA1_6_9I1R13CertificateIndex a)).input
lemma CA1_6_9I1R13P_check : ∀ a : PairSlot, contains (CA1_6_9I1R13Raw a) (CA1_6_9I1R13P a) = true := by
  decide +kernel
lemma CA1_6_9I1R13P_sound (a : PairSlot) :
    (CA1_6_9I1R13P a).Encloses (CA1_6_9I1R13Value a) :=
  contains_sound (CA1_6_9I1R13Raw_sound a) (CA1_6_9I1R13P_check a)
def CA1_6_9I1R13Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R13Certificates (CA1_6_9I1R13CertificateIndex a)).output
lemma CA1_6_9I1R13Terms_sound (a : PairSlot) :
    (CA1_6_9I1R13Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R13Certificates_valid
    (CA1_6_9I1R13CertificateIndex a) (CA1_6_9I1R13P_sound a)
def CA1_6_9I1R13Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R13Entropy_sound : CA1_6_9I1R13Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R13Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R13Value CA1_6_9I1R13Terms CA1_6_9I1R13Terms_sound) (by decide +kernel)
def CA1_6_9I1R13Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R13Mass_sound : CA1_6_9I1R13Mass.Encloses (∑ a, CA1_6_9I1R13Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R13P CA1_6_9I1R13Value CA1_6_9I1R13P_sound) (by decide +kernel)
def CA1_6_9I1R13MassTerm : Ball := .exact 0
lemma CA1_6_9I1R13MassTerm_sound : CA1_6_9I1R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R13Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R13Mass_sound)
def CA1_6_9I1R13H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R13H_sound : CA1_6_9I1R13H.Encloses (homogeneousEntropy CA1_6_9I1R13Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R13Value CA1_6_9I1R13MassTerm_sound CA1_6_9I1R13Entropy_sound) (by decide +kernel)
def CA1_6_9I1R14Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 14 a
def CA1_6_9I1R14Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 14 a
lemma CA1_6_9I1R14Raw_sound (a : PairSlot) :
    (CA1_6_9I1R14Raw a).Encloses (CA1_6_9I1R14Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 14 a
def CA1_6_9I1R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R14Certificates_valid :
    CA1_6_9I1R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R14CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R14P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R14Certificates (CA1_6_9I1R14CertificateIndex a)).input
lemma CA1_6_9I1R14P_check : ∀ a : PairSlot, contains (CA1_6_9I1R14Raw a) (CA1_6_9I1R14P a) = true := by
  decide +kernel
lemma CA1_6_9I1R14P_sound (a : PairSlot) :
    (CA1_6_9I1R14P a).Encloses (CA1_6_9I1R14Value a) :=
  contains_sound (CA1_6_9I1R14Raw_sound a) (CA1_6_9I1R14P_check a)
def CA1_6_9I1R14Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R14Certificates (CA1_6_9I1R14CertificateIndex a)).output
lemma CA1_6_9I1R14Terms_sound (a : PairSlot) :
    (CA1_6_9I1R14Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R14Certificates_valid
    (CA1_6_9I1R14CertificateIndex a) (CA1_6_9I1R14P_sound a)
def CA1_6_9I1R14Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R14Entropy_sound : CA1_6_9I1R14Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R14Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R14Value CA1_6_9I1R14Terms CA1_6_9I1R14Terms_sound) (by decide +kernel)
def CA1_6_9I1R14Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R14Mass_sound : CA1_6_9I1R14Mass.Encloses (∑ a, CA1_6_9I1R14Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R14P CA1_6_9I1R14Value CA1_6_9I1R14P_sound) (by decide +kernel)
def CA1_6_9I1R14MassTerm : Ball := .exact 0
lemma CA1_6_9I1R14MassTerm_sound : CA1_6_9I1R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R14Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R14Mass_sound)
def CA1_6_9I1R14H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R14H_sound : CA1_6_9I1R14H.Encloses (homogeneousEntropy CA1_6_9I1R14Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R14Value CA1_6_9I1R14MassTerm_sound CA1_6_9I1R14Entropy_sound) (by decide +kernel)
def CA1_6_9I1R15Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 15 a
def CA1_6_9I1R15Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 15 a
lemma CA1_6_9I1R15Raw_sound (a : PairSlot) :
    (CA1_6_9I1R15Raw a).Encloses (CA1_6_9I1R15Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 15 a
def CA1_6_9I1R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R15Certificates_valid :
    CA1_6_9I1R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R15CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R15P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R15Certificates (CA1_6_9I1R15CertificateIndex a)).input
lemma CA1_6_9I1R15P_check : ∀ a : PairSlot, contains (CA1_6_9I1R15Raw a) (CA1_6_9I1R15P a) = true := by
  decide +kernel
lemma CA1_6_9I1R15P_sound (a : PairSlot) :
    (CA1_6_9I1R15P a).Encloses (CA1_6_9I1R15Value a) :=
  contains_sound (CA1_6_9I1R15Raw_sound a) (CA1_6_9I1R15P_check a)
def CA1_6_9I1R15Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R15Certificates (CA1_6_9I1R15CertificateIndex a)).output
lemma CA1_6_9I1R15Terms_sound (a : PairSlot) :
    (CA1_6_9I1R15Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R15Certificates_valid
    (CA1_6_9I1R15CertificateIndex a) (CA1_6_9I1R15P_sound a)
def CA1_6_9I1R15Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R15Entropy_sound : CA1_6_9I1R15Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R15Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R15Value CA1_6_9I1R15Terms CA1_6_9I1R15Terms_sound) (by decide +kernel)
def CA1_6_9I1R15Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R15Mass_sound : CA1_6_9I1R15Mass.Encloses (∑ a, CA1_6_9I1R15Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R15P CA1_6_9I1R15Value CA1_6_9I1R15P_sound) (by decide +kernel)
def CA1_6_9I1R15MassTerm : Ball := .exact 0
lemma CA1_6_9I1R15MassTerm_sound : CA1_6_9I1R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R15Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R15Mass_sound)
def CA1_6_9I1R15H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R15H_sound : CA1_6_9I1R15H.Encloses (homogeneousEntropy CA1_6_9I1R15Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R15Value CA1_6_9I1R15MassTerm_sound CA1_6_9I1R15Entropy_sound) (by decide +kernel)
def CA1_6_9I1R16Value (a : PairSlot) : ℝ := residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) 16 a
def CA1_6_9I1R16Raw (a : PairSlot) : Ball := residualBall (below (shape 1 6 9)) A1_6_9Law (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) 16 a
lemma CA1_6_9I1R16Raw_sound (a : PairSlot) :
    (CA1_6_9I1R16Raw a).Encloses (CA1_6_9I1R16Value a) := by
  exact residualBall_sound_on (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u => halfTable u ((Equiv.refl (Fin 3)) 1)) (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) (fun u hu a => halfTable_sound u (stageA_children_size (shape 1 6 9) (show (shape 1 6 9) ∈ positiveInitial by decide +kernel) u hu) ((Equiv.refl (Fin 3)) 1) a) 16 a
def CA1_6_9I1R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CA1_6_9I1R16Certificates_valid :
    CA1_6_9I1R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_6_9I1R16CertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | _, _ => 0
def CA1_6_9I1R16P (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R16Certificates (CA1_6_9I1R16CertificateIndex a)).input
lemma CA1_6_9I1R16P_check : ∀ a : PairSlot, contains (CA1_6_9I1R16Raw a) (CA1_6_9I1R16P a) = true := by
  decide +kernel
lemma CA1_6_9I1R16P_sound (a : PairSlot) :
    (CA1_6_9I1R16P a).Encloses (CA1_6_9I1R16Value a) :=
  contains_sound (CA1_6_9I1R16Raw_sound a) (CA1_6_9I1R16P_check a)
def CA1_6_9I1R16Terms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CA1_6_9I1R16Certificates (CA1_6_9I1R16CertificateIndex a)).output
lemma CA1_6_9I1R16Terms_sound (a : PairSlot) :
    (CA1_6_9I1R16Terms a).Encloses (Foundation.entropyTerm (CA1_6_9I1R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_6_9I1R16Certificates_valid
    (CA1_6_9I1R16CertificateIndex a) (CA1_6_9I1R16P_sound a)
def CA1_6_9I1R16Entropy : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R16Entropy_sound : CA1_6_9I1R16Entropy.Encloses (Foundation.finiteEntropy CA1_6_9I1R16Value) := by
  exact contains_sound (entropyPair_enclosed CA1_6_9I1R16Value CA1_6_9I1R16Terms CA1_6_9I1R16Terms_sound) (by decide +kernel)
def CA1_6_9I1R16Mass : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R16Mass_sound : CA1_6_9I1R16Mass.Encloses (∑ a, CA1_6_9I1R16Value a) := by
  exact contains_sound (pairSumBall_sound CA1_6_9I1R16P CA1_6_9I1R16Value CA1_6_9I1R16P_sound) (by decide +kernel)
def CA1_6_9I1R16MassTerm : Ball := .exact 0
lemma CA1_6_9I1R16MassTerm_sound : CA1_6_9I1R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_6_9I1R16Value a))) :=
  entropyTerm_zero_ball (CA1_6_9I1R16Mass_sound)
def CA1_6_9I1R16H : Ball := ⟨0, 0⟩
lemma CA1_6_9I1R16H_sound : CA1_6_9I1R16H.Encloses (homogeneousEntropy CA1_6_9I1R16Value) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1R16Value CA1_6_9I1R16MassTerm_sound CA1_6_9I1R16Entropy_sound) (by decide +kernel)
def CA1_6_9I1ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CA1_6_9I1R0H
  | 1 => CA1_6_9I1R1H
  | 2 => CA1_6_9I1R2H
  | 3 => CA1_6_9I1R3H
  | 4 => CA1_6_9I1R4H
  | 5 => CA1_6_9I1R5H
  | 6 => CA1_6_9I1R6H
  | 7 => CA1_6_9I1R7H
  | 8 => CA1_6_9I1R8H
  | 9 => CA1_6_9I1R9H
  | 10 => CA1_6_9I1R10H
  | 11 => CA1_6_9I1R11H
  | 12 => CA1_6_9I1R12H
  | 13 => CA1_6_9I1R13H
  | 14 => CA1_6_9I1R14H
  | 15 => CA1_6_9I1R15H
  | 16 => CA1_6_9I1R16H
  | _ => (.exact 0)
lemma CA1_6_9I1ResidualEntropies_sound (k : Fin 17) :
    (CA1_6_9I1ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) k)) := by
  fin_cases k
  · exact CA1_6_9I1R0H_sound
  · exact CA1_6_9I1R1H_sound
  · exact CA1_6_9I1R2H_sound
  · exact CA1_6_9I1R3H_sound
  · exact CA1_6_9I1R4H_sound
  · exact CA1_6_9I1R5H_sound
  · exact CA1_6_9I1R6H_sound
  · exact CA1_6_9I1R7H_sound
  · exact CA1_6_9I1R8H_sound
  · exact CA1_6_9I1R9H_sound
  · exact CA1_6_9I1R10H_sound
  · exact CA1_6_9I1R11H_sound
  · exact CA1_6_9I1R12H_sound
  · exact CA1_6_9I1R13H_sound
  · exact CA1_6_9I1R14H_sound
  · exact CA1_6_9I1R15H_sound
  · exact CA1_6_9I1R16H_sound
def CA1_6_9I1Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | _, _, _ => (.exact 0)
lemma CA1_6_9I1Singles_sound (u : Shape) (hu : u ∈ below (shape 1 6 9))
    (hd : designated (Equiv.refl (Fin 3)) 1 u) :
    (CA1_6_9I1Singles u).Encloses (homogeneousEntropy ((fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) u)) := by
  rw [A1_6_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def CA1_6_9I1Singleton : Ball := ⟨0, 0⟩
lemma CA1_6_9I1Singleton_sound : CA1_6_9I1Singleton.Encloses
    (singletonEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 1 6 9)) A1_6_9Law (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1
    CA1_6_9I1Singles (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ)) (fun u _ => A1_6_9Law_sound u) CA1_6_9I1Singles_sound) (by decide +kernel)
def CA1_6_9I1Group : Ball := ⟨(11228291558488176702000743821487 / 10000000000000000000000000000000), (20913951647 / 12500000000000000000000000000000)⟩
lemma CA1_6_9I1Group_sound : CA1_6_9I1Group.Encloses
    (groupedEntropy (below (shape 1 6 9)) (fun u => (stageALaw (shape 1 6 9) u : ℝ)) (Equiv.refl (Fin 3)) 1 (fun u a => (halfLaw u ((Equiv.refl (Fin 3)) 1) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CA1_6_9I1Singleton_sound
    (finSumBall_sound 17 CA1_6_9I1ResidualEntropies _ CA1_6_9I1ResidualEntropies_sound)) (by decide +kernel)

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
def CA1_6_9I1H : Ball := ⟨(56372479975836900762362253769597 / 50000000000000000000000000000000), (19637771163 / 4000000000000000000000000000000)⟩
lemma CA1_6_9I1_sound : CA1_6_9I1H.Encloses (stageACapacity (shape 1 6 9) 1) := by
  have hb := contains_sound (Ball.add_sound CA1_6_9I1PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CA1_6_9I1Group_sound)))
    (show contains (.add CA1_6_9I1PairH (.neg (.mul (.exact 2) CA1_6_9I1Group))) CA1_6_9I1H = true by decide +kernel)
  unfold CA1_6_9I1PairValue at hb
  simpa only [stageACapacity, nativeCapacity,
    show (1 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg] using hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
