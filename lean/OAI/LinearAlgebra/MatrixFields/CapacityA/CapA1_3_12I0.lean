import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_3_12

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_3_12I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 3 12)) (fun u => (stageALaw (shape 1 3 12) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_3_12I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 3 12)) A1_3_12Law ((Equiv.refl (Fin 3)) 0) a
lemma CA1_3_12I0Raw_sound (a : Fin 17) :
    (CA1_3_12I0Raw a).Encloses (CA1_3_12I0Value a) := by
  exact marginalBall_sound (below (shape 1 3 12)) A1_3_12Law (fun u => (stageALaw (shape 1 3 12) u : ℝ)) (fun u _ => A1_3_12Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA1_3_12I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (87 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (2117582383 / 10000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647539 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CA1_3_12I0Certificates_valid :
    CA1_3_12I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_3_12I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CA1_3_12I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I0Certificates (CA1_3_12I0CertificateIndex a)).input
lemma CA1_3_12I0P_check : ∀ a : Fin 17, contains (CA1_3_12I0Raw a) (CA1_3_12I0P a) = true := by
  decide +kernel
lemma CA1_3_12I0P_sound (a : Fin 17) :
    (CA1_3_12I0P a).Encloses (CA1_3_12I0Value a) :=
  contains_sound (CA1_3_12I0Raw_sound a) (CA1_3_12I0P_check a)
def CA1_3_12I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_3_12I0Certificates (CA1_3_12I0CertificateIndex a)).output
lemma CA1_3_12I0Terms_sound (a : Fin 17) :
    (CA1_3_12I0Terms a).Encloses (Foundation.entropyTerm (CA1_3_12I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_3_12I0Certificates_valid
    (CA1_3_12I0CertificateIndex a) (CA1_3_12I0P_sound a)
def CA1_3_12I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (2117582383 / 5000000000000000000000000000000)⟩
lemma CA1_3_12I0Entropy_sound : CA1_3_12I0Entropy.Encloses (Foundation.finiteEntropy CA1_3_12I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_3_12I0Value CA1_3_12I0Terms CA1_3_12I0Terms_sound) (by decide +kernel)
def CA1_3_12I0Mass : Ball := ⟨1, (87 / 50000000000000000000000000000000)⟩
lemma CA1_3_12I0Mass_sound : CA1_3_12I0Mass.Encloses (∑ a, CA1_3_12I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_3_12I0P CA1_3_12I0Value CA1_3_12I0P_sound) (by decide +kernel)
def CA1_3_12I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_3_12I0MassTermLog : Ball := ⟨0, (1323488991 / 6250000000000000000000000000000)⟩
lemma CA1_3_12I0MassTermLog_sound : CA1_3_12I0MassTermLog.Encloses (Real.log ((∑ a, CA1_3_12I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_3_12I0Mass_sound) (w := CA1_3_12I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_3_12I0MassTerm : Ball := ⟨0, (21175823857 / 100000000000000000000000000000000)⟩
lemma CA1_3_12I0MassTerm_sound : CA1_3_12I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_3_12I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_3_12I0Mass_sound) CA1_3_12I0MassTermLog_sound) (by decide +kernel)
def CA1_3_12I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471517 / 100000000000000000000000000000000)⟩
lemma CA1_3_12I0H_sound : CA1_3_12I0H.Encloses (homogeneousEntropy CA1_3_12I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_3_12I0Value CA1_3_12I0MassTerm_sound CA1_3_12I0Entropy_sound) (by decide +kernel)
lemma CA1_3_12I0_sound : CA1_3_12I0H.Encloses (stageACapacity (shape 1 3 12) 0) := by
  exact CA1_3_12I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
