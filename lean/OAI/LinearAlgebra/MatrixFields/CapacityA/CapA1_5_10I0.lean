import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA1_5_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 1 5 10)) (fun u => (stageALaw (shape 1 5 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA1_5_10I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 1 5 10)) A1_5_10Law ((Equiv.refl (Fin 3)) 0) a
lemma CA1_5_10I0Raw_sound (a : Fin 17) :
    (CA1_5_10I0Raw a).Encloses (CA1_5_10I0Value a) := by
  exact marginalBall_sound (below (shape 1 5 10)) A1_5_10Law (fun u => (stageALaw (shape 1 5 10) u : ℝ)) (fun u _ => A1_5_10Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA1_5_10I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(49999999999999999999999999999999 / 100000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩ ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (31763735667 / 100000000000000000000000000000000)⟩ ⟨(-69314718055994530941723193050331 / 100000000000000000000000000000000), (63527471217 / 100000000000000000000000000000000)⟩ ⟨-2, 49999999999999999999999999999999, 25000000000000000000000000000000⟩]
lemma CA1_5_10I0Certificates_valid :
    CA1_5_10I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA1_5_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 1
  | _ => 0
def CA1_5_10I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I0Certificates (CA1_5_10I0CertificateIndex a)).input
lemma CA1_5_10I0P_check : ∀ a : Fin 17, contains (CA1_5_10I0Raw a) (CA1_5_10I0P a) = true := by
  decide +kernel
lemma CA1_5_10I0P_sound (a : Fin 17) :
    (CA1_5_10I0P a).Encloses (CA1_5_10I0Value a) :=
  contains_sound (CA1_5_10I0Raw_sound a) (CA1_5_10I0P_check a)
def CA1_5_10I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA1_5_10I0Certificates (CA1_5_10I0CertificateIndex a)).output
lemma CA1_5_10I0Terms_sound (a : Fin 17) :
    (CA1_5_10I0Terms a).Encloses (Foundation.entropyTerm (CA1_5_10I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA1_5_10I0Certificates_valid
    (CA1_5_10I0CertificateIndex a) (CA1_5_10I0P_sound a)
def CA1_5_10I0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (31763735667 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I0Entropy_sound : CA1_5_10I0Entropy.Encloses (Foundation.finiteEntropy CA1_5_10I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA1_5_10I0Value CA1_5_10I0Terms CA1_5_10I0Terms_sound) (by decide +kernel)
def CA1_5_10I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (21 / 12500000000000000000000000000000)⟩
lemma CA1_5_10I0Mass_sound : CA1_5_10I0Mass.Encloses (∑ a, CA1_5_10I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA1_5_10I0P CA1_5_10I0Value CA1_5_10I0P_sound) (by decide +kernel)
def CA1_5_10I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA1_5_10I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823767 / 50000000000000000000000000000000)⟩
lemma CA1_5_10I0MassTermLog_sound : CA1_5_10I0MassTermLog.Encloses (Real.log ((∑ a, CA1_5_10I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA1_5_10I0Mass_sound) (w := CA1_5_10I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA1_5_10I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (8470329507 / 20000000000000000000000000000000)⟩
lemma CA1_5_10I0MassTerm_sound : CA1_5_10I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_5_10I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA1_5_10I0Mass_sound) CA1_5_10I0MassTermLog_sound) (by decide +kernel)
def CA1_5_10I0H : Ball := ⟨(69314718055994530941723193050329 / 100000000000000000000000000000000), (105879118869 / 100000000000000000000000000000000)⟩
lemma CA1_5_10I0H_sound : CA1_5_10I0H.Encloses (homogeneousEntropy CA1_5_10I0Value) := by
  exact contains_sound (homogeneous_enclosed CA1_5_10I0Value CA1_5_10I0MassTerm_sound CA1_5_10I0Entropy_sound) (by decide +kernel)
lemma CA1_5_10I0_sound : CA1_5_10I0H.Encloses (stageACapacity (shape 1 5 10) 0) := by
  exact CA1_5_10I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
