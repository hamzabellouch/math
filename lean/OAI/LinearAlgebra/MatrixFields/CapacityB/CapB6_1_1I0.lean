import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.NativeInterior

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB6_1_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 6 1 1)) (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) ((stageBPriority (shape 6 1 1)) 0) a
def CB6_1_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 6 1 1)) B6_1_1Law ((stageBPriority (shape 6 1 1)) 0) a
lemma CB6_1_1I0Raw_sound (a : Fin 17) :
    (CB6_1_1I0Raw a).Encloses (CB6_1_1I0Value a) := by
  exact marginalBall_sound (below (shape 6 1 1)) B6_1_1Law (fun u => (stageBLaw (shape 6 1 1) u : ℝ)) (fun u _ => B6_1_1Law_sound u) ((stageBPriority (shape 6 1 1)) 0) a
def CB6_1_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823793 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329499 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB6_1_1I0Certificates_valid :
    CB6_1_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB6_1_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0
def CB6_1_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I0Certificates (CB6_1_1I0CertificateIndex a)).input
lemma CB6_1_1I0P_check : ∀ a : Fin 17, contains (CB6_1_1I0Raw a) (CB6_1_1I0P a) = true := by
  decide +kernel
lemma CB6_1_1I0P_sound (a : Fin 17) :
    (CB6_1_1I0P a).Encloses (CB6_1_1I0Value a) :=
  contains_sound (CB6_1_1I0Raw_sound a) (CB6_1_1I0P_check a)
def CB6_1_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB6_1_1I0Certificates (CB6_1_1I0CertificateIndex a)).output
lemma CB6_1_1I0Terms_sound (a : Fin 17) :
    (CB6_1_1I0Terms a).Encloses (Foundation.entropyTerm (CB6_1_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB6_1_1I0Certificates_valid
    (CB6_1_1I0CertificateIndex a) (CB6_1_1I0P_sound a)
def CB6_1_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823793 / 50000000000000000000000000000000)⟩
lemma CB6_1_1I0Entropy_sound : CB6_1_1I0Entropy.Encloses (Foundation.finiteEntropy CB6_1_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB6_1_1I0Value CB6_1_1I0Terms CB6_1_1I0Terms_sound) (by decide +kernel)
def CB6_1_1I0Mass : Ball := ⟨1, (13 / 10000000000000000000000000000000)⟩
lemma CB6_1_1I0Mass_sound : CB6_1_1I0Mass.Encloses (∑ a, CB6_1_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB6_1_1I0P CB6_1_1I0Value CB6_1_1I0P_sound) (by decide +kernel)
def CB6_1_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB6_1_1I0MassTermLog : Ball := ⟨0, (5293955953 / 25000000000000000000000000000000)⟩
lemma CB6_1_1I0MassTermLog_sound : CB6_1_1I0MassTermLog.Encloses (Real.log ((∑ a, CB6_1_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB6_1_1I0Mass_sound) (w := CB6_1_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB6_1_1I0MassTerm : Ball := ⟨0, (21175823813 / 100000000000000000000000000000000)⟩
lemma CB6_1_1I0MassTerm_sound : CB6_1_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB6_1_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB6_1_1I0Mass_sound) CB6_1_1I0MassTermLog_sound) (by decide +kernel)
def CB6_1_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471399 / 100000000000000000000000000000000)⟩
lemma CB6_1_1I0H_sound : CB6_1_1I0H.Encloses (homogeneousEntropy CB6_1_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB6_1_1I0Value CB6_1_1I0MassTerm_sound CB6_1_1I0Entropy_sound) (by decide +kernel)
lemma CB6_1_1I0_sound : CB6_1_1I0H.Encloses (stageBCapacity (shape 6 1 1) 0) := by
  exact CB6_1_1I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
