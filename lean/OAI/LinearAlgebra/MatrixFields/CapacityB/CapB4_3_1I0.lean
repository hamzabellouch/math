import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_3_1

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_3_1I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 3 1)) (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) ((stageBPriority (shape 4 3 1)) 0) a
def CB4_3_1I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 3 1)) B4_3_1Law ((stageBPriority (shape 4 3 1)) 0) a
lemma CB4_3_1I0Raw_sound (a : Fin 17) :
    (CB4_3_1I0Raw a).Encloses (CB4_3_1I0Value a) := by
  exact marginalBall_sound (below (shape 4 3 1)) B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ)) (fun u _ => B4_3_1Law_sound u) ((stageBPriority (shape 4 3 1)) 0) a
def CB4_3_1I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2646977967 / 12500000000000000000000000000000)⟩ ⟨(-8664339756999316367715399131291 / 12500000000000000000000000000000), (42351647427 / 100000000000000000000000000000000)⟩ ⟨-1, 50000000000000000000000000000001, 50000000000000000000000000000000⟩]
lemma CB4_3_1I0Certificates_valid :
    CB4_3_1I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_3_1I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 0 => 1
  | _ => 0
def CB4_3_1I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I0Certificates (CB4_3_1I0CertificateIndex a)).input
lemma CB4_3_1I0P_check : ∀ a : Fin 17, contains (CB4_3_1I0Raw a) (CB4_3_1I0P a) = true := by
  decide +kernel
lemma CB4_3_1I0P_sound (a : Fin 17) :
    (CB4_3_1I0P a).Encloses (CB4_3_1I0Value a) :=
  contains_sound (CB4_3_1I0Raw_sound a) (CB4_3_1I0P_check a)
def CB4_3_1I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_3_1I0Certificates (CB4_3_1I0CertificateIndex a)).output
lemma CB4_3_1I0Terms_sound (a : Fin 17) :
    (CB4_3_1I0Terms a).Encloses (Foundation.entropyTerm (CB4_3_1I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_3_1I0Certificates_valid
    (CB4_3_1I0CertificateIndex a) (CB4_3_1I0P_sound a)
def CB4_3_1I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2646977967 / 6250000000000000000000000000000)⟩
lemma CB4_3_1I0Entropy_sound : CB4_3_1I0Entropy.Encloses (Foundation.finiteEntropy CB4_3_1I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB4_3_1I0Value CB4_3_1I0Terms CB4_3_1I0Terms_sound) (by decide +kernel)
def CB4_3_1I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
lemma CB4_3_1I0Mass_sound : CB4_3_1I0Mass.Encloses (∑ a, CB4_3_1I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB4_3_1I0P CB4_3_1I0Value CB4_3_1I0P_sound) (by decide +kernel)
def CB4_3_1I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB4_3_1I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (165436123 / 781250000000000000000000000000)⟩
lemma CB4_3_1I0MassTermLog_sound : CB4_3_1I0MassTermLog.Encloses (Real.log ((∑ a, CB4_3_1I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_3_1I0Mass_sound) (w := CB4_3_1I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_3_1I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (4235164749 / 20000000000000000000000000000000)⟩
lemma CB4_3_1I0MassTerm_sound : CB4_3_1I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_3_1I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_3_1I0Mass_sound) CB4_3_1I0MassTermLog_sound) (by decide +kernel)
def CB4_3_1I0H : Ball := ⟨(17328679513998632735430798262583 / 25000000000000000000000000000000), (63527471217 / 100000000000000000000000000000000)⟩
lemma CB4_3_1I0H_sound : CB4_3_1I0H.Encloses (homogeneousEntropy CB4_3_1I0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_3_1I0Value CB4_3_1I0MassTerm_sound CB4_3_1I0Entropy_sound) (by decide +kernel)
lemma CB4_3_1I0_sound : CB4_3_1I0H.Encloses (stageBCapacity (shape 4 3 1) 0) := by
  exact CB4_3_1I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
