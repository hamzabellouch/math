import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_2_12

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_2_12I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 2 12)) (fun u => (stageALaw (shape 2 2 12) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_2_12I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 2 12)) A2_2_12Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_2_12I0Raw_sound (a : Fin 17) :
    (CA2_2_12I0Raw a).Encloses (CA2_2_12I0Value a) := by
  exact marginalBall_sound (below (shape 2 2 12)) A2_2_12Law (fun u => (stageALaw (shape 2 2 12) u : ℝ)) (fun u _ => A2_2_12Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_2_12I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(13304581949811756576850221805683 / 50000000000000000000000000000000), (121 / 100000000000000000000000000000000)⟩ ⟨(17614129252825866852505103836653 / 50000000000000000000000000000000), (8452064587 / 50000000000000000000000000000000)⟩ ⟨(-26478290440497583697605424591511 / 20000000000000000000000000000000), (63527471503 / 100000000000000000000000000000000)⟩ ⟨-2, 13304581949811756576850221805683, 12500000000000000000000000000000⟩,
   .log ⟨(4678167220075297369259911277727 / 10000000000000000000000000000000), (141 / 100000000000000000000000000000000)⟩ ⟨(888475973950925703876602594341 / 2500000000000000000000000000000), (3714901689 / 12500000000000000000000000000000)⟩ ⟨(-37983933970475952861129556443821 / 50000000000000000000000000000000), (1270549427 / 2000000000000000000000000000000)⟩ ⟨-2, 4678167220075297369259911277727, 2500000000000000000000000000000⟩]
lemma CA2_2_12I0Certificates_valid :
    CA2_2_12I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_2_12I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_2_12I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I0Certificates (CA2_2_12I0CertificateIndex a)).input
lemma CA2_2_12I0P_check : ∀ a : Fin 17, contains (CA2_2_12I0Raw a) (CA2_2_12I0P a) = true := by
  decide +kernel
lemma CA2_2_12I0P_sound (a : Fin 17) :
    (CA2_2_12I0P a).Encloses (CA2_2_12I0Value a) :=
  contains_sound (CA2_2_12I0Raw_sound a) (CA2_2_12I0P_check a)
def CA2_2_12I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_2_12I0Certificates (CA2_2_12I0CertificateIndex a)).output
lemma CA2_2_12I0Terms_sound (a : Fin 17) :
    (CA2_2_12I0Terms a).Encloses (Foundation.entropyTerm (CA2_2_12I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_2_12I0Certificates_valid
    (CA2_2_12I0CertificateIndex a) (CA2_2_12I0P_sound a)
def CA2_2_12I0Entropy : Ball := ⟨(26498888992335123891271129780063 / 25000000000000000000000000000000), (3176373593 / 5000000000000000000000000000000)⟩
lemma CA2_2_12I0Entropy_sound : CA2_2_12I0Entropy.Encloses (Foundation.finiteEntropy CA2_2_12I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_2_12I0Value CA2_2_12I0Terms CA2_2_12I0Terms_sound) (by decide +kernel)
def CA2_2_12I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (383 / 100000000000000000000000000000000)⟩
lemma CA2_2_12I0Mass_sound : CA2_2_12I0Mass.Encloses (∑ a, CA2_2_12I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_2_12I0P CA2_2_12I0Value CA2_2_12I0P_sound) (by decide +kernel)
def CA2_2_12I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA2_2_12I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (4235164813 / 20000000000000000000000000000000)⟩
lemma CA2_2_12I0MassTermLog_sound : CA2_2_12I0MassTermLog.Encloses (Real.log ((∑ a, CA2_2_12I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_2_12I0Mass_sound) (w := CA2_2_12I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_2_12I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (10587912033 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I0MassTerm_sound : CA2_2_12I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_2_12I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_2_12I0Mass_sound) CA2_2_12I0MassTermLog_sound) (by decide +kernel)
def CA2_2_12I0H : Ball := ⟨(52997777984670247782542259560127 / 50000000000000000000000000000000), (42351647963 / 50000000000000000000000000000000)⟩
lemma CA2_2_12I0H_sound : CA2_2_12I0H.Encloses (homogeneousEntropy CA2_2_12I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_2_12I0Value CA2_2_12I0MassTerm_sound CA2_2_12I0Entropy_sound) (by decide +kernel)
lemma CA2_2_12I0_sound : CA2_2_12I0H.Encloses (stageACapacity (shape 2 2 12) 0) := by
  exact CA2_2_12I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
