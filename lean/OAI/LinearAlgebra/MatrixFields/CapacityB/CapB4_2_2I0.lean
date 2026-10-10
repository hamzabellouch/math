import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_2_2

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB4_2_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 2 2)) (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) ((stageBPriority (shape 4 2 2)) 0) a
def CB4_2_2I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 2 2)) B4_2_2Law ((stageBPriority (shape 4 2 2)) 0) a
lemma CB4_2_2I0Raw_sound (a : Fin 17) :
    (CB4_2_2I0Raw a).Encloses (CB4_2_2I0Value a) := by
  exact marginalBall_sound (below (shape 4 2 2)) B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ)) (fun u _ => B4_2_2Law_sound u) ((stageBPriority (shape 4 2 2)) 0) a
def CB4_2_2I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18443922190366941637623808000193 / 100000000000000000000000000000000), (69 / 100000000000000000000000000000000)⟩ ⟨(31178256963042688675819307809239 / 100000000000000000000000000000000), (15622609959 / 100000000000000000000000000000000)⟩ ⟨(-42260882258718742705346530515367 / 25000000000000000000000000000000), (42351647553 / 50000000000000000000000000000000)⟩ ⟨-3, 18443922190366941637623808000193, 12500000000000000000000000000000⟩,
   .log ⟨(63112155619266116724752383999613 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩ ⟨(726194960879906850566047157421 / 2500000000000000000000000000000), (2672903773 / 10000000000000000000000000000000)⟩ ⟨(-23012839721742060809676949114857 / 50000000000000000000000000000000), (42351647513 / 100000000000000000000000000000000)⟩ ⟨-1, 63112155619266116724752383999613, 50000000000000000000000000000000⟩]
lemma CB4_2_2I0Certificates_valid :
    CB4_2_2I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB4_2_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 2 => 1
  | 1 => 2
  | 0 => 1
  | _ => 0
def CB4_2_2I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I0Certificates (CB4_2_2I0CertificateIndex a)).input
lemma CB4_2_2I0P_check : ∀ a : Fin 17, contains (CB4_2_2I0Raw a) (CB4_2_2I0P a) = true := by
  decide +kernel
lemma CB4_2_2I0P_sound (a : Fin 17) :
    (CB4_2_2I0P a).Encloses (CB4_2_2I0Value a) :=
  contains_sound (CB4_2_2I0Raw_sound a) (CB4_2_2I0P_check a)
def CB4_2_2I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB4_2_2I0Certificates (CB4_2_2I0CertificateIndex a)).output
lemma CB4_2_2I0Terms_sound (a : Fin 17) :
    (CB4_2_2I0Terms a).Encloses (Foundation.entropyTerm (CB4_2_2I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_2_2I0Certificates_valid
    (CB4_2_2I0CertificateIndex a) (CB4_2_2I0P_sound a)
def CB4_2_2I0Entropy : Ball := ⟨(45702156180640825687140250957659 / 50000000000000000000000000000000), (3623391103 / 6250000000000000000000000000000)⟩
lemma CB4_2_2I0Entropy_sound : CB4_2_2I0Entropy.Encloses (Foundation.finiteEntropy CB4_2_2I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB4_2_2I0Value CB4_2_2I0Terms CB4_2_2I0Terms_sound) (by decide +kernel)
def CB4_2_2I0Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (231 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I0Mass_sound : CB4_2_2I0Mass.Encloses (∑ a, CB4_2_2I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB4_2_2I0P CB4_2_2I0Value CB4_2_2I0P_sound) (by decide +kernel)
def CB4_2_2I0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def CB4_2_2I0MassTermLog : Ball := ⟨0, (42351647597 / 100000000000000000000000000000000)⟩
lemma CB4_2_2I0MassTermLog_sound : CB4_2_2I0MassTermLog.Encloses (Real.log ((∑ a, CB4_2_2I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB4_2_2I0Mass_sound) (w := CB4_2_2I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB4_2_2I0MassTerm : Ball := ⟨0, (21175823799 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I0MassTerm_sound : CB4_2_2I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB4_2_2I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB4_2_2I0Mass_sound) CB4_2_2I0MassTermLog_sound) (by decide +kernel)
def CB4_2_2I0H : Ball := ⟨(45702156180640825687140250957659 / 50000000000000000000000000000000), (50162952623 / 50000000000000000000000000000000)⟩
lemma CB4_2_2I0H_sound : CB4_2_2I0H.Encloses (homogeneousEntropy CB4_2_2I0Value) := by
  exact contains_sound (homogeneous_enclosed CB4_2_2I0Value CB4_2_2I0MassTerm_sound CB4_2_2I0Entropy_sound) (by decide +kernel)
lemma CB4_2_2I0_sound : CB4_2_2I0H.Encloses (stageBCapacity (shape 4 2 2) 0) := by
  exact CB4_2_2I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
