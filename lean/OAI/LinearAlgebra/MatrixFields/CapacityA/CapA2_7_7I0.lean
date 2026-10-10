import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_7_7

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_7_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 7 7)) (fun u => (stageALaw (shape 2 7 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_7_7I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 7 7)) A2_7_7Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_7_7I0Raw_sound (a : Fin 17) :
    (CA2_7_7I0Raw a).Encloses (CA2_7_7I0Value a) := by
  exact marginalBall_sound (below (shape 2 7 7)) A2_7_7Law (fun u => (stageALaw (shape 2 7 7) u : ℝ)) (fun u _ => A2_7_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_7_7I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2478236922667912448826878641011 / 10000000000000000000000000000000), (9 / 12500000000000000000000000000000)⟩ ⟨(8643084865911444987514954227337 / 25000000000000000000000000000000), (20991483421 / 100000000000000000000000000000000)⟩ ⟨(-139503770391845325996477971161587 / 100000000000000000000000000000000), (84703295023 / 100000000000000000000000000000000)⟩ ⟨-3, 2478236922667912448826878641011, 1250000000000000000000000000000⟩,
   .log ⟨(25217630773320875511731213589889 / 50000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩ ⟨(34521908742701804978706762282031 / 100000000000000000000000000000000), (21360164223 / 100000000000000000000000000000000)⟩ ⟨(-17111990541962629104116060290069 / 25000000000000000000000000000000), (165436123 / 390625000000000000000000000000)⟩ ⟨-1, 25217630773320875511731213589889, 25000000000000000000000000000000⟩]
lemma CA2_7_7I0Certificates_valid :
    CA2_7_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_7_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_7_7I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I0Certificates (CA2_7_7I0CertificateIndex a)).input
lemma CA2_7_7I0P_check : ∀ a : Fin 17, contains (CA2_7_7I0Raw a) (CA2_7_7I0P a) = true := by
  decide +kernel
lemma CA2_7_7I0P_sound (a : Fin 17) :
    (CA2_7_7I0P a).Encloses (CA2_7_7I0Value a) :=
  contains_sound (CA2_7_7I0Raw_sound a) (CA2_7_7I0P_check a)
def CA2_7_7I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_7_7I0Certificates (CA2_7_7I0CertificateIndex a)).output
lemma CA2_7_7I0Terms_sound (a : Fin 17) :
    (CA2_7_7I0Terms a).Encloses (Foundation.entropyTerm (CA2_7_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_7_7I0Certificates_valid
    (CA2_7_7I0CertificateIndex a) (CA2_7_7I0P_sound a)
def CA2_7_7I0Entropy : Ball := ⟨(103666587669993364878826396100727 / 100000000000000000000000000000000), (12668626213 / 20000000000000000000000000000000)⟩
lemma CA2_7_7I0Entropy_sound : CA2_7_7I0Entropy.Encloses (Foundation.finiteEntropy CA2_7_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_7_7I0Value CA2_7_7I0Terms CA2_7_7I0Terms_sound) (by decide +kernel)
def CA2_7_7I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (103 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I0Mass_sound : CA2_7_7I0Mass.Encloses (∑ a, CA2_7_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_7_7I0P CA2_7_7I0Value CA2_7_7I0P_sound) (by decide +kernel)
def CA2_7_7I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA2_7_7I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
lemma CA2_7_7I0MassTermLog_sound : CA2_7_7I0MassTermLog.Encloses (Real.log ((∑ a, CA2_7_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_7_7I0Mass_sound) (w := CA2_7_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_7_7I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647573 / 100000000000000000000000000000000)⟩
lemma CA2_7_7I0MassTerm_sound : CA2_7_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_7_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_7_7I0Mass_sound) CA2_7_7I0MassTermLog_sound) (by decide +kernel)
def CA2_7_7I0H : Ball := ⟨(51833293834996682439413198050363 / 50000000000000000000000000000000), (52847389319 / 50000000000000000000000000000000)⟩
lemma CA2_7_7I0H_sound : CA2_7_7I0H.Encloses (homogeneousEntropy CA2_7_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_7_7I0Value CA2_7_7I0MassTerm_sound CA2_7_7I0Entropy_sound) (by decide +kernel)
lemma CA2_7_7I0_sound : CA2_7_7I0H.Encloses (stageACapacity (shape 2 7 7) 0) := by
  exact CA2_7_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
