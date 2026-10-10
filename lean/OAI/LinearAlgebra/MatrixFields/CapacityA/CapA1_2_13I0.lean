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
def CA1_2_13I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 2 13)) (fun u => (stageALaw (shape 1 2 13) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_2_13I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 2 13)) A1_2_13Law ((Equiv.refl (Fin 3)) 0) a
lemma CA1_2_13I0Raw_sound (a : Fin 17) :
    (CA1_2_13I0Raw a).Encloses (CA1_2_13I0Value a) := by
  exact marginalBall_sound (below (shape 1 2 13)) A1_2_13Law (fun u => (stageALaw (shape 1 2 13) u : ℝ)) (fun u _ => A1_2_13Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA1_2_13I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1 / 2), (77 / 100000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823813 / 100000000000000000000000000000000)⟩ ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (42351647519 / 100000000000000000000000000000000)⟩ ⟨-1, 1, 1⟩]
lemma CA1_2_13I0Certificates_valid :
    CA1_2_13I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_2_13I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CA1_2_13I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I0Certificates (CA1_2_13I0CertificateIndex a)).input
lemma CA1_2_13I0P_check : ∀ a : Fin 17, contains (CA1_2_13I0Raw a) (CA1_2_13I0P a) = true := by
  decide +kernel
lemma CA1_2_13I0P_sound (a : Fin 17) :
    (CA1_2_13I0P a).Encloses (CA1_2_13I0Value a) :=
  contains_sound (CA1_2_13I0Raw_sound a) (CA1_2_13I0P_check a)
def CA1_2_13I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_2_13I0Certificates (CA1_2_13I0CertificateIndex a)).output
lemma CA1_2_13I0Terms_sound (a : Fin 17) :
    (CA1_2_13I0Terms a).Encloses (Foundation.entropyTerm (CA1_2_13I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_2_13I0Certificates_valid
    (CA1_2_13I0CertificateIndex a) (CA1_2_13I0P_sound a)
def CA1_2_13I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823813 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I0Entropy_sound : CA1_2_13I0Entropy.Encloses (Foundation.finiteEntropy CA1_2_13I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_2_13I0Value CA1_2_13I0Terms CA1_2_13I0Terms_sound) (by decide +kernel)
def CA1_2_13I0Mass : Ball := ⟨1, (77 / 50000000000000000000000000000000)⟩
lemma CA1_2_13I0Mass_sound : CA1_2_13I0Mass.Encloses (∑ a, CA1_2_13I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_2_13I0P CA1_2_13I0Value CA1_2_13I0P_sound) (by decide +kernel)
def CA1_2_13I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA1_2_13I0MassTermLog : Ball := ⟨0, (5293955959 / 25000000000000000000000000000000)⟩
lemma CA1_2_13I0MassTermLog_sound : CA1_2_13I0MassTermLog.Encloses (Real.log ((∑ a, CA1_2_13I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_2_13I0Mass_sound) (w := CA1_2_13I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_2_13I0MassTerm : Ball := ⟨0, (21175823837 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I0MassTerm_sound : CA1_2_13I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_2_13I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_2_13I0Mass_sound) CA1_2_13I0MassTermLog_sound) (by decide +kernel)
def CA1_2_13I0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (63527471463 / 100000000000000000000000000000000)⟩
lemma CA1_2_13I0H_sound : CA1_2_13I0H.Encloses (homogeneousEntropy CA1_2_13I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_2_13I0Value CA1_2_13I0MassTerm_sound CA1_2_13I0Entropy_sound) (by decide +kernel)
lemma CA1_2_13I0_sound : CA1_2_13I0H.Encloses (stageACapacity (shape 1 2 13) 0) := by
  exact CA1_2_13I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
