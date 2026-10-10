import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB1_2_5I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 2 5)) (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) ((stageBPriority (shape 1 2 5)) 0) a
def CB1_2_5I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 2 5)) B1_2_5Law ((stageBPriority (shape 1 2 5)) 0) a
lemma CB1_2_5I0Raw_sound (a : Fin 17) :
    (CB1_2_5I0Raw a).Encloses (CB1_2_5I0Value a) := by
  exact marginalBall_sound (below (shape 1 2 5)) B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ)) (fun u _ => B1_2_5Law_sound u) ((stageBPriority (shape 1 2 5)) 0) a
def CB1_2_5I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2646977971 / 12500000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329493 / 20000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CB1_2_5I0Certificates_valid :
    CB1_2_5I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB1_2_5I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CB1_2_5I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I0Certificates (CB1_2_5I0CertificateIndex a)).input
lemma CB1_2_5I0P_check : ∀ a : Fin 17, contains (CB1_2_5I0Raw a) (CB1_2_5I0P a) = true := by
  decide +kernel
lemma CB1_2_5I0P_sound (a : Fin 17) :
    (CB1_2_5I0P a).Encloses (CB1_2_5I0Value a) :=
  contains_sound (CB1_2_5I0Raw_sound a) (CB1_2_5I0P_check a)
def CB1_2_5I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB1_2_5I0Certificates (CB1_2_5I0CertificateIndex a)).output
lemma CB1_2_5I0Terms_sound (a : Fin 17) :
    (CB1_2_5I0Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I0Certificates_valid
    (CB1_2_5I0CertificateIndex a) (CB1_2_5I0P_sound a)
def CB1_2_5I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2646977971 / 6250000000000000000000000000000)⟩
lemma CB1_2_5I0Entropy_sound : CB1_2_5I0Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB1_2_5I0Value CB1_2_5I0Terms CB1_2_5I0Terms_sound) (by decide +kernel)
def CB1_2_5I0Mass : Ball := ⟨1, (1 / 1000000000000000000000000000000)⟩
lemma CB1_2_5I0Mass_sound : CB1_2_5I0Mass.Encloses (∑ a, CB1_2_5I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB1_2_5I0P CB1_2_5I0Value CB1_2_5I0P_sound) (by decide +kernel)
def CB1_2_5I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB1_2_5I0MassTermLog : Ball := ⟨0, (10587911891 / 50000000000000000000000000000000)⟩
lemma CB1_2_5I0MassTermLog_sound : CB1_2_5I0MassTermLog.Encloses (Real.log ((∑ a, CB1_2_5I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB1_2_5I0Mass_sound) (w := CB1_2_5I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB1_2_5I0MassTerm : Ball := ⟨0, (21175823783 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I0MassTerm_sound : CB1_2_5I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB1_2_5I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB1_2_5I0Mass_sound) CB1_2_5I0MassTermLog_sound) (by decide +kernel)
def CB1_2_5I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471319 / 100000000000000000000000000000000)⟩
lemma CB1_2_5I0H_sound : CB1_2_5I0H.Encloses (homogeneousEntropy CB1_2_5I0Value) := by
  exact contains_sound (homogeneous_enclosed CB1_2_5I0Value CB1_2_5I0MassTerm_sound CB1_2_5I0Entropy_sound) (by decide +kernel)
lemma CB1_2_5I0_sound : CB1_2_5I0H.Encloses (stageBCapacity (shape 1 2 5) 0) := by
  exact CB1_2_5I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
