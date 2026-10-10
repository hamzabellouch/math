import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_7_8

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_7_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 7 8)) (fun u => (stageALaw (shape 1 7 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_7_8I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 7 8)) A1_7_8Law ((Equiv.refl (Fin 3)) 0) a
lemma CA1_7_8I0Raw_sound (a : Fin 17) :
    (CA1_7_8I0Raw a).Encloses (CA1_7_8I0Value a) := by
  exact marginalBall_sound (below (shape 1 7 8)) A1_7_8Law (fun u => (stageALaw (shape 1 7 8) u : ℝ)) (fun u _ => A1_7_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA1_7_8I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (105879119 / 500000000000000000000000000000)⟩ ⟨(-8664339756999316367715399131291 / 12500000000000000000000000000000), (42351647503 / 100000000000000000000000000000000)⟩ ⟨-1, 50000000000000000000000000000001, 50000000000000000000000000000000⟩]
lemma CA1_7_8I0Certificates_valid :
    CA1_7_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_7_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CA1_7_8I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I0Certificates (CA1_7_8I0CertificateIndex a)).input
lemma CA1_7_8I0P_check : ∀ a : Fin 17, contains (CA1_7_8I0Raw a) (CA1_7_8I0P a) = true := by
  decide +kernel
lemma CA1_7_8I0P_sound (a : Fin 17) :
    (CA1_7_8I0P a).Encloses (CA1_7_8I0Value a) :=
  contains_sound (CA1_7_8I0Raw_sound a) (CA1_7_8I0P_check a)
def CA1_7_8I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_7_8I0Certificates (CA1_7_8I0CertificateIndex a)).output
lemma CA1_7_8I0Terms_sound (a : Fin 17) :
    (CA1_7_8I0Terms a).Encloses (Foundation.entropyTerm (CA1_7_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_7_8I0Certificates_valid
    (CA1_7_8I0CertificateIndex a) (CA1_7_8I0P_sound a)
def CA1_7_8I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (105879119 / 250000000000000000000000000000)⟩
lemma CA1_7_8I0Entropy_sound : CA1_7_8I0Entropy.Encloses (Foundation.finiteEntropy CA1_7_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_7_8I0Value CA1_7_8I0Terms CA1_7_8I0Terms_sound) (by decide +kernel)
def CA1_7_8I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (69 / 50000000000000000000000000000000)⟩
lemma CA1_7_8I0Mass_sound : CA1_7_8I0Mass.Encloses (∑ a, CA1_7_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_7_8I0P CA1_7_8I0Value CA1_7_8I0P_sound) (by decide +kernel)
def CA1_7_8I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA1_7_8I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (1058791191 / 5000000000000000000000000000000)⟩
lemma CA1_7_8I0MassTermLog_sound : CA1_7_8I0MassTermLog.Encloses (Real.log ((∑ a, CA1_7_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_7_8I0Mass_sound) (w := CA1_7_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_7_8I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823821 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I0MassTerm_sound : CA1_7_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I0Mass_sound) CA1_7_8I0MassTermLog_sound) (by decide +kernel)
def CA1_7_8I0H : Ball := ⟨(17328679513998632735430798262583 / 25000000000000000000000000000000), (63527471421 / 100000000000000000000000000000000)⟩
lemma CA1_7_8I0H_sound : CA1_7_8I0H.Encloses (homogeneousEntropy CA1_7_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_7_8I0Value CA1_7_8I0MassTerm_sound CA1_7_8I0Entropy_sound) (by decide +kernel)
lemma CA1_7_8I0_sound : CA1_7_8I0H.Encloses (stageACapacity (shape 1 7 8) 0) := by
  exact CA1_7_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
