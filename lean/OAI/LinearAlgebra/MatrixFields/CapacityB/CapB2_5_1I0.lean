import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB5_1_2

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_5_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 5 1)) (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) ((stageBPriority (shape 2 5 1)) 0) a
def CB2_5_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 5 1)) B2_5_1Law ((stageBPriority (shape 2 5 1)) 0) a
lemma CB2_5_1I0Raw_sound (a : Fin 17) :
    (CB2_5_1I0Raw a).Encloses (CB2_5_1I0Value a) := by
  exact marginalBall_sound (below (shape 2 5 1)) B2_5_1Law (fun u => (stageBLaw (shape 2 5 1) u : ℝ)) (fun u _ => B2_5_1Law_sound u) ((stageBPriority (shape 2 5 1)) 0) a
def CB2_5_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (9 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823759 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329491 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB2_5_1I0Certificates_valid :
    CB2_5_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_5_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0
def CB2_5_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I0Certificates (CB2_5_1I0CertificateIndex a)).input
lemma CB2_5_1I0P_check : ∀ a : Fin 17, contains (CB2_5_1I0Raw a) (CB2_5_1I0P a) = true := by
  decide +kernel
lemma CB2_5_1I0P_sound (a : Fin 17) :
    (CB2_5_1I0P a).Encloses (CB2_5_1I0Value a) :=
  contains_sound (CB2_5_1I0Raw_sound a) (CB2_5_1I0P_check a)
def CB2_5_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_5_1I0Certificates (CB2_5_1I0CertificateIndex a)).output
lemma CB2_5_1I0Terms_sound (a : Fin 17) :
    (CB2_5_1I0Terms a).Encloses (Foundation.entropyTerm (CB2_5_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_5_1I0Certificates_valid
    (CB2_5_1I0CertificateIndex a) (CB2_5_1I0P_sound a)
def CB2_5_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823759 / 50000000000000000000000000000000)⟩
lemma CB2_5_1I0Entropy_sound : CB2_5_1I0Entropy.Encloses (Foundation.finiteEntropy CB2_5_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_5_1I0Value CB2_5_1I0Terms CB2_5_1I0Terms_sound) (by decide +kernel)
def CB2_5_1I0Mass : Ball := ⟨1, (9 / 10000000000000000000000000000000)⟩
lemma CB2_5_1I0Mass_sound : CB2_5_1I0Mass.Encloses (∑ a, CB2_5_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_5_1I0P CB2_5_1I0Value CB2_5_1I0P_sound) (by decide +kernel)
def CB2_5_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_5_1I0MassTermLog : Ball := ⟨0, (5293955943 / 25000000000000000000000000000000)⟩
lemma CB2_5_1I0MassTermLog_sound : CB2_5_1I0MassTermLog.Encloses (Real.log ((∑ a, CB2_5_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_5_1I0Mass_sound) (w := CB2_5_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_5_1I0MassTerm : Ball := ⟨0, (21175823773 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I0MassTerm_sound : CB2_5_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_5_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_5_1I0Mass_sound) CB2_5_1I0MassTermLog_sound) (by decide +kernel)
def CB2_5_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471291 / 100000000000000000000000000000000)⟩
lemma CB2_5_1I0H_sound : CB2_5_1I0H.Encloses (homogeneousEntropy CB2_5_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_5_1I0Value CB2_5_1I0MassTerm_sound CB2_5_1I0Entropy_sound) (by decide +kernel)
lemma CB2_5_1I0_sound : CB2_5_1I0H.Encloses (stageBCapacity (shape 2 5 1) 0) := by
  exact CB2_5_1I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
