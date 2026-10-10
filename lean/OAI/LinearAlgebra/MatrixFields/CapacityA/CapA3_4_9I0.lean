import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_4_9

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_4_9I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 4 9)) (fun u => (stageALaw (shape 3 4 9) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_4_9I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 4 9)) A3_4_9Law ((Equiv.refl (Fin 3)) 0) a
lemma CA3_4_9I0Raw_sound (a : Fin 17) :
    (CA3_4_9I0Raw a).Encloses (CA3_4_9I0Value a) := by
  exact marginalBall_sound (below (shape 3 4 9)) A3_4_9Law (fun u => (stageALaw (shape 3 4 9) u : ℝ)) (fun u _ => A3_4_9Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA3_4_9I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1299456700004793073277956283603 / 12500000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩ ⟨(23533497555094888247285717255271 / 100000000000000000000000000000000), (5503413263 / 50000000000000000000000000000000)⟩ ⟨(-113189119513409356234371341744503 / 50000000000000000000000000000000), (26469779707 / 25000000000000000000000000000000)⟩ ⟨-4, 1299456700004793073277956283603, 781250000000000000000000000000⟩,
   .log ⟨(4950543299995206926722043716397 / 12500000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩ ⟨(36682785892318360300699001332619 / 100000000000000000000000000000000), (25159639837 / 100000000000000000000000000000000)⟩ ⟨(-92623131617578913654954671725473 / 100000000000000000000000000000000), (15881867809 / 25000000000000000000000000000000)⟩ ⟨-2, 4950543299995206926722043716397, 3125000000000000000000000000000⟩]
lemma CA3_4_9I0Certificates_valid :
    CA3_4_9I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_4_9I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CA3_4_9I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I0Certificates (CA3_4_9I0CertificateIndex a)).input
lemma CA3_4_9I0P_check : ∀ a : Fin 17, contains (CA3_4_9I0Raw a) (CA3_4_9I0P a) = true := by
  decide +kernel
lemma CA3_4_9I0P_sound (a : Fin 17) :
    (CA3_4_9I0P a).Encloses (CA3_4_9I0Value a) :=
  contains_sound (CA3_4_9I0Raw_sound a) (CA3_4_9I0P_check a)
def CA3_4_9I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_4_9I0Certificates (CA3_4_9I0CertificateIndex a)).output
lemma CA3_4_9I0Terms_sound (a : Fin 17) :
    (CA3_4_9I0Terms a).Encloses (Foundation.entropyTerm (CA3_4_9I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_4_9I0Certificates_valid
    (CA3_4_9I0CertificateIndex a) (CA3_4_9I0P_sound a)
def CA3_4_9I0Entropy : Ball := ⟨(6021628344741324854798471858789 / 5000000000000000000000000000000), (36166466363 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I0Entropy_sound : CA3_4_9I0Entropy.Encloses (Foundation.finiteEntropy CA3_4_9I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_4_9I0Value CA3_4_9I0Terms CA3_4_9I0Terms_sound) (by decide +kernel)
def CA3_4_9I0Mass : Ball := ⟨1, (117 / 50000000000000000000000000000000)⟩
lemma CA3_4_9I0Mass_sound : CA3_4_9I0Mass.Encloses (∑ a, CA3_4_9I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_4_9I0P CA3_4_9I0Value CA3_4_9I0P_sound) (by decide +kernel)
def CA3_4_9I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_4_9I0MassTermLog : Ball := ⟨0, (5293955979 / 25000000000000000000000000000000)⟩
lemma CA3_4_9I0MassTermLog_sound : CA3_4_9I0MassTermLog.Encloses (Real.log ((∑ a, CA3_4_9I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_4_9I0Mass_sound) (w := CA3_4_9I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_4_9I0MassTerm : Ball := ⟨0, (21175823917 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I0MassTerm_sound : CA3_4_9I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_4_9I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_4_9I0Mass_sound) CA3_4_9I0MassTermLog_sound) (by decide +kernel)
def CA3_4_9I0H : Ball := ⟨(6021628344741324854798471858789 / 5000000000000000000000000000000), (93508756643 / 100000000000000000000000000000000)⟩
lemma CA3_4_9I0H_sound : CA3_4_9I0H.Encloses (homogeneousEntropy CA3_4_9I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_4_9I0Value CA3_4_9I0MassTerm_sound CA3_4_9I0Entropy_sound) (by decide +kernel)
lemma CA3_4_9I0_sound : CA3_4_9I0H.Encloses (stageACapacity (shape 3 4 9) 0) := by
  exact CA3_4_9I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
