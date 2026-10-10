import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_6_7

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_6_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 6 7)) (fun u => (stageALaw (shape 3 6 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_6_7I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 6 7)) A3_6_7Law ((Equiv.refl (Fin 3)) 0) a
lemma CA3_6_7I0Raw_sound (a : Fin 17) :
    (CA3_6_7I0Raw a).Encloses (CA3_6_7I0Value a) := by
  exact marginalBall_sound (below (shape 3 6 7)) A3_6_7Law (fun u => (stageALaw (shape 3 6 7) u : ℝ)) (fun u _ => A3_6_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA3_6_7I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1221182384919200440510029178837 / 12500000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩ ⟨(22722873647123665018424133843591 / 100000000000000000000000000000000), (10343817281 / 100000000000000000000000000000000)⟩ ⟨(-23259090869365844619034633399283 / 10000000000000000000000000000000), (13234889853 / 12500000000000000000000000000000)⟩ ⟨-4, 1221182384919200440510029178837, 781250000000000000000000000000⟩,
   .log ⟨(5028817615080799559489970821163 / 12500000000000000000000000000000), (3 / 4000000000000000000000000000000)⟩ ⟨(4578958471496020170345080397317 / 12500000000000000000000000000000), (1277872269 / 5000000000000000000000000000000)⟩ ⟨(-455271877206710810100848304047 / 500000000000000000000000000000), (12705494247 / 20000000000000000000000000000000)⟩ ⟨-2, 5028817615080799559489970821163, 3125000000000000000000000000000⟩]
lemma CA3_6_7I0Certificates_valid :
    CA3_6_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_6_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CA3_6_7I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I0Certificates (CA3_6_7I0CertificateIndex a)).input
lemma CA3_6_7I0P_check : ∀ a : Fin 17, contains (CA3_6_7I0Raw a) (CA3_6_7I0P a) = true := by
  decide +kernel
lemma CA3_6_7I0P_sound (a : Fin 17) :
    (CA3_6_7I0P a).Encloses (CA3_6_7I0Value a) :=
  contains_sound (CA3_6_7I0Raw_sound a) (CA3_6_7I0P_check a)
def CA3_6_7I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_6_7I0Certificates (CA3_6_7I0CertificateIndex a)).output
lemma CA3_6_7I0Terms_sound (a : Fin 17) :
    (CA3_6_7I0Terms a).Encloses (Foundation.entropyTerm (CA3_6_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_6_7I0Certificates_valid
    (CA3_6_7I0CertificateIndex a) (CA3_6_7I0P_sound a)
def CA3_6_7I0Entropy : Ball := ⟨(59354541419091826381184777022127 / 50000000000000000000000000000000), (35901262661 / 50000000000000000000000000000000)⟩
lemma CA3_6_7I0Entropy_sound : CA3_6_7I0Entropy.Encloses (Foundation.finiteEntropy CA3_6_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_6_7I0Value CA3_6_7I0Terms CA3_6_7I0Terms_sound) (by decide +kernel)
def CA3_6_7I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
lemma CA3_6_7I0Mass_sound : CA3_6_7I0Mass.Encloses (∑ a, CA3_6_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_6_7I0P CA3_6_7I0Value CA3_6_7I0P_sound) (by decide +kernel)
def CA3_6_7I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_6_7I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
lemma CA3_6_7I0MassTermLog_sound : CA3_6_7I0MassTermLog.Encloses (Real.log ((∑ a, CA3_6_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_6_7I0Mass_sound) (w := CA3_6_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_6_7I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
lemma CA3_6_7I0MassTerm_sound : CA3_6_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_6_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_6_7I0Mass_sound) CA3_6_7I0MassTermLog_sound) (by decide +kernel)
def CA3_6_7I0H : Ball := ⟨(59354541419091826381184777022127 / 50000000000000000000000000000000), (18595669847 / 20000000000000000000000000000000)⟩
lemma CA3_6_7I0H_sound : CA3_6_7I0H.Encloses (homogeneousEntropy CA3_6_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_6_7I0Value CA3_6_7I0MassTerm_sound CA3_6_7I0Entropy_sound) (by decide +kernel)
lemma CA3_6_7I0_sound : CA3_6_7I0H.Encloses (stageACapacity (shape 3 6 7) 0) := by
  exact CA3_6_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
