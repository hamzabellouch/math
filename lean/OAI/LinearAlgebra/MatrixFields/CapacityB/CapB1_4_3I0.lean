import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB2_3_3

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_4_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 4 3)) (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) ((stageBPriority (shape 1 4 3)) 0) a
def CB1_4_3I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 4 3)) B1_4_3Law ((stageBPriority (shape 1 4 3)) 0) a
lemma CB1_4_3I0Raw_sound (a : Fin 17) :
    (CB1_4_3I0Raw a).Encloses (CB1_4_3I0Value a) := by
  exact marginalBall_sound (below (shape 1 4 3)) B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ)) (fun u _ => B1_4_3Law_sound u) ((stageBPriority (shape 1 4 3)) 0) a
def CB1_4_3I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823729 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647419 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB1_4_3I0Certificates_valid :
    CB1_4_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_4_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CB1_4_3I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I0Certificates (CB1_4_3I0CertificateIndex a)).input
lemma CB1_4_3I0P_check : ∀ a : Fin 17, contains (CB1_4_3I0Raw a) (CB1_4_3I0P a) = true := by
  decide +kernel
lemma CB1_4_3I0P_sound (a : Fin 17) :
    (CB1_4_3I0P a).Encloses (CB1_4_3I0Value a) :=
  contains_sound (CB1_4_3I0Raw_sound a) (CB1_4_3I0P_check a)
def CB1_4_3I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB1_4_3I0Certificates (CB1_4_3I0CertificateIndex a)).output
lemma CB1_4_3I0Terms_sound (a : Fin 17) :
    (CB1_4_3I0Terms a).Encloses (Foundation.entropyTerm (CB1_4_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_4_3I0Certificates_valid
    (CB1_4_3I0CertificateIndex a) (CB1_4_3I0P_sound a)
def CB1_4_3I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823729 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I0Entropy_sound : CB1_4_3I0Entropy.Encloses (Foundation.finiteEntropy CB1_4_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_4_3I0Value CB1_4_3I0Terms CB1_4_3I0Terms_sound) (by decide +kernel)
def CB1_4_3I0Mass : Ball := ⟨1, (27 / 50000000000000000000000000000000)⟩
lemma CB1_4_3I0Mass_sound : CB1_4_3I0Mass.Encloses (∑ a, CB1_4_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_4_3I0P CB1_4_3I0Value CB1_4_3I0P_sound) (by decide +kernel)
def CB1_4_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_4_3I0MassTermLog : Ball := ⟨0, (2646977967 / 12500000000000000000000000000000)⟩
lemma CB1_4_3I0MassTermLog_sound : CB1_4_3I0MassTermLog.Encloses (Real.log ((∑ a, CB1_4_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_4_3I0Mass_sound) (w := CB1_4_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_4_3I0MassTerm : Ball := ⟨0, (21175823737 / 100000000000000000000000000000000)⟩
lemma CB1_4_3I0MassTerm_sound : CB1_4_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_4_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_4_3I0Mass_sound) CB1_4_3I0MassTermLog_sound) (by decide +kernel)
def CB1_4_3I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (12705494239 / 20000000000000000000000000000000)⟩
lemma CB1_4_3I0H_sound : CB1_4_3I0H.Encloses (homogeneousEntropy CB1_4_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_4_3I0Value CB1_4_3I0MassTerm_sound CB1_4_3I0Entropy_sound) (by decide +kernel)
lemma CB1_4_3I0_sound : CB1_4_3I0H.Encloses (stageBCapacity (shape 1 4 3) 0) := by
  exact CB1_4_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
