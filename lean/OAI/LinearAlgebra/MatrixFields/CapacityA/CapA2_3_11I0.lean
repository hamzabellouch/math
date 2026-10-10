import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_3_11

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_3_11I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 3 11)) (fun u => (stageALaw (shape 2 3 11) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_3_11I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 3 11)) A2_3_11Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_3_11I0Raw_sound (a : Fin 17) :
    (CA2_3_11I0Raw a).Encloses (CA2_3_11I0Value a) := by
  exact marginalBall_sound (below (shape 2 3 11)) A2_3_11Law (fun u => (stageALaw (shape 2 3 11) u : ℝ)) (fun u _ => A2_3_11Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_3_11I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(26533248109664728192207347509433 / 100000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩ ⟨(17601779941022551087002795414573 / 50000000000000000000000000000000), (8427950849 / 50000000000000000000000000000000)⟩ ⟨(-66338579687916564099797439552099 / 50000000000000000000000000000000), (1270549427 / 2000000000000000000000000000000)⟩ ⟨-2, 26533248109664728192207347509433, 25000000000000000000000000000000⟩,
   .log ⟨(23466751890335271807792652490567 / 50000000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩ ⟨(17751152235485283878421062996329 / 50000000000000000000000000000000), (596313363 / 2000000000000000000000000000000)⟩ ⟨(-18910959981210752265746631219023 / 25000000000000000000000000000000), (31763735599 / 50000000000000000000000000000000)⟩ ⟨-2, 23466751890335271807792652490567, 12500000000000000000000000000000⟩]
lemma CA2_3_11I0Certificates_valid :
    CA2_3_11I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_3_11I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_3_11I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I0Certificates (CA2_3_11I0CertificateIndex a)).input
lemma CA2_3_11I0P_check : ∀ a : Fin 17, contains (CA2_3_11I0Raw a) (CA2_3_11I0P a) = true := by
  decide +kernel
lemma CA2_3_11I0P_sound (a : Fin 17) :
    (CA2_3_11I0P a).Encloses (CA2_3_11I0Value a) :=
  contains_sound (CA2_3_11I0Raw_sound a) (CA2_3_11I0P_check a)
def CA2_3_11I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_3_11I0Certificates (CA2_3_11I0CertificateIndex a)).output
lemma CA2_3_11I0Terms_sound (a : Fin 17) :
    (CA2_3_11I0Terms a).Encloses (Foundation.entropyTerm (CA2_3_11I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I0Certificates_valid
    (CA2_3_11I0CertificateIndex a) (CA2_3_11I0P_sound a)
def CA2_3_11I0Entropy : Ball := ⟨(2118188484701215442097066153019 / 2000000000000000000000000000000), (31763735773 / 50000000000000000000000000000000)⟩
lemma CA2_3_11I0Entropy_sound : CA2_3_11I0Entropy.Encloses (Foundation.finiteEntropy CA2_3_11I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_3_11I0Value CA2_3_11I0Terms CA2_3_11I0Terms_sound) (by decide +kernel)
def CA2_3_11I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
lemma CA2_3_11I0Mass_sound : CA2_3_11I0Mass.Encloses (∑ a, CA2_3_11I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_3_11I0P CA2_3_11I0Value CA2_3_11I0P_sound) (by decide +kernel)
def CA2_3_11I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_3_11I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
lemma CA2_3_11I0MassTermLog_sound : CA2_3_11I0MassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I0Mass_sound) (w := CA2_3_11I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_3_11I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I0MassTerm_sound : CA2_3_11I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I0Mass_sound) CA2_3_11I0MassTermLog_sound) (by decide +kernel)
def CA2_3_11I0H : Ball := ⟨(2118188484701215442097066153019 / 2000000000000000000000000000000), (84703295459 / 100000000000000000000000000000000)⟩
lemma CA2_3_11I0H_sound : CA2_3_11I0H.Encloses (homogeneousEntropy CA2_3_11I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I0Value CA2_3_11I0MassTerm_sound CA2_3_11I0Entropy_sound) (by decide +kernel)
lemma CA2_3_11I0_sound : CA2_3_11I0H.Encloses (stageACapacity (shape 2 3 11) 0) := by
  exact CA2_3_11I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
