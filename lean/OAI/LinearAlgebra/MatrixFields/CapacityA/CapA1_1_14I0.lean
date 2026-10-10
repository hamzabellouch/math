import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_1_14

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_1_14I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 1 14)) (fun u => (stageALaw (shape 1 1 14) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_1_14I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 1 14)) A1_1_14Law ((Equiv.refl (Fin 3)) 0) a
lemma CA1_1_14I0Raw_sound (a : Fin 17) :
    (CA1_1_14I0Raw a).Encloses (CA1_1_14I0Value a) := by
  exact marginalBall_sound (below (shape 1 1 14)) A1_1_14Law (fun u => (stageALaw (shape 1 1 14) u : ℝ)) (fun u _ => A1_1_14Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA1_1_14I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (47 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823763 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647459 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CA1_1_14I0Certificates_valid :
    CA1_1_14I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_1_14I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CA1_1_14I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I0Certificates (CA1_1_14I0CertificateIndex a)).input
lemma CA1_1_14I0P_check : ∀ a : Fin 17, contains (CA1_1_14I0Raw a) (CA1_1_14I0P a) = true := by
  decide +kernel
lemma CA1_1_14I0P_sound (a : Fin 17) :
    (CA1_1_14I0P a).Encloses (CA1_1_14I0Value a) :=
  contains_sound (CA1_1_14I0Raw_sound a) (CA1_1_14I0P_check a)
def CA1_1_14I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_1_14I0Certificates (CA1_1_14I0CertificateIndex a)).output
lemma CA1_1_14I0Terms_sound (a : Fin 17) :
    (CA1_1_14I0Terms a).Encloses (Foundation.entropyTerm (CA1_1_14I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_1_14I0Certificates_valid
    (CA1_1_14I0CertificateIndex a) (CA1_1_14I0P_sound a)
def CA1_1_14I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823763 / 50000000000000000000000000000000)⟩
lemma CA1_1_14I0Entropy_sound : CA1_1_14I0Entropy.Encloses (Foundation.finiteEntropy CA1_1_14I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_1_14I0Value CA1_1_14I0Terms CA1_1_14I0Terms_sound) (by decide +kernel)
def CA1_1_14I0Mass : Ball := ⟨1, (47 / 50000000000000000000000000000000)⟩
lemma CA1_1_14I0Mass_sound : CA1_1_14I0Mass.Encloses (∑ a, CA1_1_14I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_1_14I0P CA1_1_14I0Value CA1_1_14I0P_sound) (by decide +kernel)
def CA1_1_14I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_1_14I0MassTermLog : Ball := ⟨0, (661744493 / 3125000000000000000000000000000)⟩
lemma CA1_1_14I0MassTermLog_sound : CA1_1_14I0MassTermLog.Encloses (Real.log ((∑ a, CA1_1_14I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_1_14I0Mass_sound) (w := CA1_1_14I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_1_14I0MassTerm : Ball := ⟨0, (21175823777 / 100000000000000000000000000000000)⟩
lemma CA1_1_14I0MassTerm_sound : CA1_1_14I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_1_14I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_1_14I0Mass_sound) CA1_1_14I0MassTermLog_sound) (by decide +kernel)
def CA1_1_14I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471303 / 100000000000000000000000000000000)⟩
lemma CA1_1_14I0H_sound : CA1_1_14I0H.Encloses (homogeneousEntropy CA1_1_14I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_1_14I0Value CA1_1_14I0MassTerm_sound CA1_1_14I0Entropy_sound) (by decide +kernel)
lemma CA1_1_14I0_sound : CA1_1_14I0H.Encloses (stageACapacity (shape 1 1 14) 0) := by
  exact CA1_1_14I0H_sound

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
