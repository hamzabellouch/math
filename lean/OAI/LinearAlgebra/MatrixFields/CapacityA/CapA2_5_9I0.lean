import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_5_9

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_5_9I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 5 9)) (fun u => (stageALaw (shape 2 5 9) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_5_9I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 5 9)) A2_5_9Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_5_9I0Raw_sound (a : Fin 17) :
    (CA2_5_9I0Raw a).Encloses (CA2_5_9I0Value a) := by
  exact marginalBall_sound (below (shape 2 5 9)) A2_5_9Law (fun u => (stageALaw (shape 2 5 9) u : ℝ)) (fun u _ => A2_5_9Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_5_9I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(12820241431770474661034931012817 / 50000000000000000000000000000000), (3 / 4000000000000000000000000000000)⟩ ⟨(34896638760094206029001325695197 / 100000000000000000000000000000000), (8144375253 / 50000000000000000000000000000000)⟩ ⟨(-27219954433631116156815148137033 / 20000000000000000000000000000000), (3176373567 / 5000000000000000000000000000000)⟩ ⟨-2, 12820241431770474661034931012817, 12500000000000000000000000000000⟩,
   .log ⟨(12179758568229525338965068987183 / 25000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩ ⟨(17516938145574499321587008667317 / 50000000000000000000000000000000), (61899941 / 200000000000000000000000000000)⟩ ⟨(-14382007695346950823450620237117 / 20000000000000000000000000000000), (7940933897 / 12500000000000000000000000000000)⟩ ⟨-2, 12179758568229525338965068987183, 6250000000000000000000000000000⟩]
lemma CA2_5_9I0Certificates_valid :
    CA2_5_9I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_5_9I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_5_9I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I0Certificates (CA2_5_9I0CertificateIndex a)).input
lemma CA2_5_9I0P_check : ∀ a : Fin 17, contains (CA2_5_9I0Raw a) (CA2_5_9I0P a) = true := by
  decide +kernel
lemma CA2_5_9I0P_sound (a : Fin 17) :
    (CA2_5_9I0P a).Encloses (CA2_5_9I0Value a) :=
  contains_sound (CA2_5_9I0Raw_sound a) (CA2_5_9I0P_check a)
def CA2_5_9I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_5_9I0Certificates (CA2_5_9I0CertificateIndex a)).output
lemma CA2_5_9I0Terms_sound (a : Fin 17) :
    (CA2_5_9I0Terms a).Encloses (Foundation.entropyTerm (CA2_5_9I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_5_9I0Certificates_valid
    (CA2_5_9I0CertificateIndex a) (CA2_5_9I0P_sound a)
def CA2_5_9I0Entropy : Ball := ⟨(26206788452834352675294167181257 / 25000000000000000000000000000000), (7940933939 / 12500000000000000000000000000000)⟩
lemma CA2_5_9I0Entropy_sound : CA2_5_9I0Entropy.Encloses (Foundation.finiteEntropy CA2_5_9I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_5_9I0Value CA2_5_9I0Terms CA2_5_9I0Terms_sound) (by decide +kernel)
def CA2_5_9I0Mass : Ball := ⟨1, (53 / 25000000000000000000000000000000)⟩
lemma CA2_5_9I0Mass_sound : CA2_5_9I0Mass.Encloses (∑ a, CA2_5_9I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_5_9I0P CA2_5_9I0Value CA2_5_9I0P_sound) (by decide +kernel)
def CA2_5_9I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_5_9I0MassTermLog : Ball := ⟨0, (10587911947 / 50000000000000000000000000000000)⟩
lemma CA2_5_9I0MassTermLog_sound : CA2_5_9I0MassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I0Mass_sound) (w := CA2_5_9I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_5_9I0MassTerm : Ball := ⟨0, (4235164779 / 20000000000000000000000000000000)⟩
lemma CA2_5_9I0MassTerm_sound : CA2_5_9I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I0Mass_sound) CA2_5_9I0MassTermLog_sound) (by decide +kernel)
def CA2_5_9I0H : Ball := ⟨(26206788452834352675294167181257 / 25000000000000000000000000000000), (84703295407 / 100000000000000000000000000000000)⟩
lemma CA2_5_9I0H_sound : CA2_5_9I0H.Encloses (homogeneousEntropy CA2_5_9I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I0Value CA2_5_9I0MassTerm_sound CA2_5_9I0Entropy_sound) (by decide +kernel)
lemma CA2_5_9I0_sound : CA2_5_9I0H.Encloses (stageACapacity (shape 2 5 9) 0) := by
  exact CA2_5_9I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
