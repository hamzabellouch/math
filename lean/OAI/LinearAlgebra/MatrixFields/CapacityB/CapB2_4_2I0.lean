import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_4_2

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_4_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 4 2)) (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) ((stageBPriority (shape 2 4 2)) 0) a
def CB2_4_2I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 4 2)) B2_4_2Law ((stageBPriority (shape 2 4 2)) 0) a
lemma CB2_4_2I0Raw_sound (a : Fin 17) :
    (CB2_4_2I0Raw a).Encloses (CB2_4_2I0Value a) := by
  exact marginalBall_sound (below (shape 2 4 2)) B2_4_2Law (fun u => (stageBLaw (shape 2 4 2) u : ℝ)) (fun u _ => B2_4_2Law_sound u) ((stageBPriority (shape 2 4 2)) 0) a
def CB2_4_2I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18444910185167131143404389881443 / 100000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩ ⟨(15589469541528843690691167499179 / 50000000000000000000000000000000), (15623446821 / 100000000000000000000000000000000)⟩ ⟨(-169038172428353149777145115754231 / 100000000000000000000000000000000), (847032951 / 1000000000000000000000000000000)⟩ ⟨-3, 18444910185167131143404389881443, 12500000000000000000000000000000⟩,
   .log ⟨(31555089814832868856595610118557 / 50000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩ ⟨(29048864931223719890654738023041 / 100000000000000000000000000000000), (6682050217 / 25000000000000000000000000000000)⟩ ⟨(-46028810410117948265016649511163 / 100000000000000000000000000000000), (10587911879 / 25000000000000000000000000000000)⟩ ⟨-1, 31555089814832868856595610118557, 25000000000000000000000000000000⟩]
lemma CB2_4_2I0Certificates_valid :
    CB2_4_2I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_4_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CB2_4_2I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_4_2I0Certificates (CB2_4_2I0CertificateIndex a)).input
lemma CB2_4_2I0P_check : ∀ a : Fin 17, contains (CB2_4_2I0Raw a) (CB2_4_2I0P a) = true := by
  decide +kernel
lemma CB2_4_2I0P_sound (a : Fin 17) :
    (CB2_4_2I0P a).Encloses (CB2_4_2I0Value a) :=
  contains_sound (CB2_4_2I0Raw_sound a) (CB2_4_2I0P_check a)
def CB2_4_2I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_4_2I0Certificates (CB2_4_2I0CertificateIndex a)).output
lemma CB2_4_2I0Terms_sound (a : Fin 17) :
    (CB2_4_2I0Terms a).Encloses (Foundation.entropyTerm (CB2_4_2I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_4_2I0Certificates_valid
    (CB2_4_2I0CertificateIndex a) (CB2_4_2I0P_sound a)
def CB2_4_2I0Entropy : Ball := ⟨(91406743097339094653419408019757 / 100000000000000000000000000000000), (5797509451 / 10000000000000000000000000000000)⟩
lemma CB2_4_2I0Entropy_sound : CB2_4_2I0Entropy.Encloses (Foundation.finiteEntropy CB2_4_2I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_4_2I0Value CB2_4_2I0Terms CB2_4_2I0Terms_sound) (by decide +kernel)
def CB2_4_2I0Mass : Ball := ⟨1, (231 / 100000000000000000000000000000000)⟩
lemma CB2_4_2I0Mass_sound : CB2_4_2I0Mass.Encloses (∑ a, CB2_4_2I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_4_2I0P CB2_4_2I0Value CB2_4_2I0P_sound) (by decide +kernel)
def CB2_4_2I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_4_2I0MassTermLog : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
lemma CB2_4_2I0MassTermLog_sound : CB2_4_2I0MassTermLog.Encloses (Real.log ((∑ a, CB2_4_2I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_4_2I0Mass_sound) (w := CB2_4_2I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_4_2I0MassTerm : Ball := ⟨0, (10587911957 / 50000000000000000000000000000000)⟩
lemma CB2_4_2I0MassTerm_sound : CB2_4_2I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_4_2I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_4_2I0Mass_sound) CB2_4_2I0MassTermLog_sound) (by decide +kernel)
def CB2_4_2I0H : Ball := ⟨(91406743097339094653419408019757 / 100000000000000000000000000000000), (9893864803 / 12500000000000000000000000000000)⟩
lemma CB2_4_2I0H_sound : CB2_4_2I0H.Encloses (homogeneousEntropy CB2_4_2I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_4_2I0Value CB2_4_2I0MassTerm_sound CB2_4_2I0Entropy_sound) (by decide +kernel)
lemma CB2_4_2I0_sound : CB2_4_2I0H.Encloses (stageBCapacity (shape 2 4 2) 0) := by
  exact CB2_4_2I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
