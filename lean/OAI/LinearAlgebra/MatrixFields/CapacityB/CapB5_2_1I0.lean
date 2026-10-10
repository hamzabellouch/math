import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal5_2_1

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB5_2_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 2 1)) (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) ((stageBPriority (shape 5 2 1)) 0) a
def CB5_2_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 5 2 1)) B5_2_1Law ((stageBPriority (shape 5 2 1)) 0) a
lemma CB5_2_1I0Raw_sound (a : Fin 17) :
    (CB5_2_1I0Raw a).Encloses (CB5_2_1I0Value a) := by
  exact marginalBall_sound (below (shape 5 2 1)) B5_2_1Law (fun u => (stageBLaw (shape 5 2 1) u : ℝ)) (fun u _ => B5_2_1Law_sound u) ((stageBPriority (shape 5 2 1)) 0) a
def CB5_2_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823773 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647471 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB5_2_1I0Certificates_valid :
    CB5_2_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB5_2_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0
def CB5_2_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I0Certificates (CB5_2_1I0CertificateIndex a)).input
lemma CB5_2_1I0P_check : ∀ a : Fin 17, contains (CB5_2_1I0Raw a) (CB5_2_1I0P a) = true := by
  decide +kernel
lemma CB5_2_1I0P_sound (a : Fin 17) :
    (CB5_2_1I0P a).Encloses (CB5_2_1I0Value a) :=
  contains_sound (CB5_2_1I0Raw_sound a) (CB5_2_1I0P_check a)
def CB5_2_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_2_1I0Certificates (CB5_2_1I0CertificateIndex a)).output
lemma CB5_2_1I0Terms_sound (a : Fin 17) :
    (CB5_2_1I0Terms a).Encloses (Foundation.entropyTerm (CB5_2_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_2_1I0Certificates_valid
    (CB5_2_1I0CertificateIndex a) (CB5_2_1I0P_sound a)
def CB5_2_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823773 / 50000000000000000000000000000000)⟩
lemma CB5_2_1I0Entropy_sound : CB5_2_1I0Entropy.Encloses (Foundation.finiteEntropy CB5_2_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB5_2_1I0Value CB5_2_1I0Terms CB5_2_1I0Terms_sound) (by decide +kernel)
def CB5_2_1I0Mass : Ball := ⟨1, (53 / 50000000000000000000000000000000)⟩
lemma CB5_2_1I0Mass_sound : CB5_2_1I0Mass.Encloses (∑ a, CB5_2_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB5_2_1I0P CB5_2_1I0Value CB5_2_1I0P_sound) (by decide +kernel)
def CB5_2_1I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_2_1I0MassTermLog : Ball := ⟨0, (5293955947 / 25000000000000000000000000000000)⟩
lemma CB5_2_1I0MassTermLog_sound : CB5_2_1I0MassTermLog.Encloses (Real.log ((∑ a, CB5_2_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_2_1I0Mass_sound) (w := CB5_2_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB5_2_1I0MassTerm : Ball := ⟨0, (21175823789 / 100000000000000000000000000000000)⟩
lemma CB5_2_1I0MassTerm_sound : CB5_2_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_2_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB5_2_1I0Mass_sound) CB5_2_1I0MassTermLog_sound) (by decide +kernel)
def CB5_2_1I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494267 / 20000000000000000000000000000000)⟩
lemma CB5_2_1I0H_sound : CB5_2_1I0H.Encloses (homogeneousEntropy CB5_2_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB5_2_1I0Value CB5_2_1I0MassTerm_sound CB5_2_1I0Entropy_sound) (by decide +kernel)
lemma CB5_2_1I0_sound : CB5_2_1I0H.Encloses (stageBCapacity (shape 5 2 1) 0) := by
  exact CB5_2_1I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
