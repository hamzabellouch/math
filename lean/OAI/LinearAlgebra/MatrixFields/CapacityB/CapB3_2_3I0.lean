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
def CB3_2_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 2 3)) (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) ((stageBPriority (shape 3 2 3)) 0) a
def CB3_2_3I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 2 3)) B3_2_3Law ((stageBPriority (shape 3 2 3)) 0) a
lemma CB3_2_3I0Raw_sound (a : Fin 17) :
    (CB3_2_3I0Raw a).Encloses (CB3_2_3I0Value a) := by
  exact marginalBall_sound (below (shape 3 2 3)) B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ)) (fun u _ => B3_2_3Law_sound u) ((stageBPriority (shape 3 2 3)) 0) a
def CB3_2_3I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(660954401694675365284077503627 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(5718700990404566998542725209219 / 100000000000000000000000000000000), (2239400647 / 100000000000000000000000000000000)⟩ ⟨(-86521868615171017372683118901063 / 20000000000000000000000000000000), (84703294921 / 50000000000000000000000000000000)⟩ ⟨-7, 660954401694675365284077503627, 390625000000000000000000000000⟩,
   .log ⟨(24339045598305324634715922496373 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩ ⟨(8761339994149058187289105091327 / 25000000000000000000000000000000), (483186881 / 1562500000000000000000000000000)⟩ ⟨(-71994112988219155445620039600637 / 100000000000000000000000000000000), (31763735579 / 50000000000000000000000000000000)⟩ ⟨-2, 24339045598305324634715922496373, 12500000000000000000000000000000⟩]
lemma CB3_2_3I0Certificates_valid :
    CB3_2_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_2_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CB3_2_3I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I0Certificates (CB3_2_3I0CertificateIndex a)).input
lemma CB3_2_3I0P_check : ∀ a : Fin 17, contains (CB3_2_3I0Raw a) (CB3_2_3I0P a) = true := by
  decide +kernel
lemma CB3_2_3I0P_sound (a : Fin 17) :
    (CB3_2_3I0P a).Encloses (CB3_2_3I0Value a) :=
  contains_sound (CB3_2_3I0Raw_sound a) (CB3_2_3I0P_check a)
def CB3_2_3I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB3_2_3I0Certificates (CB3_2_3I0CertificateIndex a)).output
lemma CB3_2_3I0Terms_sound (a : Fin 17) :
    (CB3_2_3I0Terms a).Encloses (Foundation.entropyTerm (CB3_2_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_2_3I0Certificates_valid
    (CB3_2_3I0CertificateIndex a) (CB3_2_3I0P_sound a)
def CB3_2_3I0Entropy : Ball := ⟨(40764060967000799747699145574527 / 50000000000000000000000000000000), (33163361031 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I0Entropy_sound : CB3_2_3I0Entropy.Encloses (Foundation.finiteEntropy CB3_2_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB3_2_3I0Value CB3_2_3I0Terms CB3_2_3I0Terms_sound) (by decide +kernel)
def CB3_2_3I0Mass : Ball := ⟨1, (29 / 25000000000000000000000000000000)⟩
lemma CB3_2_3I0Mass_sound : CB3_2_3I0Mass.Encloses (∑ a, CB3_2_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB3_2_3I0P CB3_2_3I0Value CB3_2_3I0P_sound) (by decide +kernel)
def CB3_2_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_2_3I0MassTermLog : Ball := ⟨0, (10587911899 / 50000000000000000000000000000000)⟩
lemma CB3_2_3I0MassTermLog_sound : CB3_2_3I0MassTermLog.Encloses (Real.log ((∑ a, CB3_2_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_2_3I0Mass_sound) (w := CB3_2_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_2_3I0MassTerm : Ball := ⟨0, (21175823799 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I0MassTerm_sound : CB3_2_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_2_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_2_3I0Mass_sound) CB3_2_3I0MassTermLog_sound) (by decide +kernel)
def CB3_2_3I0H : Ball := ⟨(40764060967000799747699145574527 / 50000000000000000000000000000000), (87502545861 / 100000000000000000000000000000000)⟩
lemma CB3_2_3I0H_sound : CB3_2_3I0H.Encloses (homogeneousEntropy CB3_2_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_2_3I0Value CB3_2_3I0MassTerm_sound CB3_2_3I0Entropy_sound) (by decide +kernel)
lemma CB3_2_3I0_sound : CB3_2_3I0H.Encloses (stageBCapacity (shape 3 2 3) 0) := by
  exact CB3_2_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
