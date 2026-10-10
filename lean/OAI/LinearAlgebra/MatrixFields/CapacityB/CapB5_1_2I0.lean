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
def CB5_1_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 1 2)) (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) ((stageBPriority (shape 5 1 2)) 0) a
def CB5_1_2I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 5 1 2)) B5_1_2Law ((stageBPriority (shape 5 1 2)) 0) a
lemma CB5_1_2I0Raw_sound (a : Fin 17) :
    (CB5_1_2I0Raw a).Encloses (CB5_1_2I0Value a) := by
  exact marginalBall_sound (below (shape 5 1 2)) B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ)) (fun u _ => B5_1_2Law_sound u) ((stageBPriority (shape 5 1 2)) 0) a
def CB5_1_2I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823773 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647471 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB5_1_2I0Certificates_valid :
    CB5_1_2I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB5_1_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0
def CB5_1_2I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I0Certificates (CB5_1_2I0CertificateIndex a)).input
lemma CB5_1_2I0P_check : ∀ a : Fin 17, contains (CB5_1_2I0Raw a) (CB5_1_2I0P a) = true := by
  decide +kernel
lemma CB5_1_2I0P_sound (a : Fin 17) :
    (CB5_1_2I0P a).Encloses (CB5_1_2I0Value a) :=
  contains_sound (CB5_1_2I0Raw_sound a) (CB5_1_2I0P_check a)
def CB5_1_2I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB5_1_2I0Certificates (CB5_1_2I0CertificateIndex a)).output
lemma CB5_1_2I0Terms_sound (a : Fin 17) :
    (CB5_1_2I0Terms a).Encloses (Foundation.entropyTerm (CB5_1_2I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB5_1_2I0Certificates_valid
    (CB5_1_2I0CertificateIndex a) (CB5_1_2I0P_sound a)
def CB5_1_2I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823773 / 50000000000000000000000000000000)⟩
lemma CB5_1_2I0Entropy_sound : CB5_1_2I0Entropy.Encloses (Foundation.finiteEntropy CB5_1_2I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB5_1_2I0Value CB5_1_2I0Terms CB5_1_2I0Terms_sound) (by decide +kernel)
def CB5_1_2I0Mass : Ball := ⟨1, (53 / 50000000000000000000000000000000)⟩
lemma CB5_1_2I0Mass_sound : CB5_1_2I0Mass.Encloses (∑ a, CB5_1_2I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB5_1_2I0P CB5_1_2I0Value CB5_1_2I0P_sound) (by decide +kernel)
def CB5_1_2I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB5_1_2I0MassTermLog : Ball := ⟨0, (5293955947 / 25000000000000000000000000000000)⟩
lemma CB5_1_2I0MassTermLog_sound : CB5_1_2I0MassTermLog.Encloses (Real.log ((∑ a, CB5_1_2I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB5_1_2I0Mass_sound) (w := CB5_1_2I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB5_1_2I0MassTerm : Ball := ⟨0, (21175823789 / 100000000000000000000000000000000)⟩
lemma CB5_1_2I0MassTerm_sound : CB5_1_2I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB5_1_2I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB5_1_2I0Mass_sound) CB5_1_2I0MassTermLog_sound) (by decide +kernel)
def CB5_1_2I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494267 / 20000000000000000000000000000000)⟩
lemma CB5_1_2I0H_sound : CB5_1_2I0H.Encloses (homogeneousEntropy CB5_1_2I0Value) := by
  exact contains_sound (homogeneous_enclosed CB5_1_2I0Value CB5_1_2I0MassTerm_sound CB5_1_2I0Entropy_sound) (by decide +kernel)
lemma CB5_1_2I0_sound : CB5_1_2I0H.Encloses (stageBCapacity (shape 5 1 2) 0) := by
  exact CB5_1_2I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
