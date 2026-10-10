import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_2_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_2_4I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 2 4)) (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) ((stageBPriority (shape 2 2 4)) 0) a
def CB2_2_4I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 2 4)) B2_2_4Law ((stageBPriority (shape 2 2 4)) 0) a
lemma CB2_2_4I0Raw_sound (a : Fin 17) :
    (CB2_2_4I0Raw a).Encloses (CB2_2_4I0Value a) := by
  exact marginalBall_sound (below (shape 2 2 4)) B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ)) (fun u _ => B2_2_4Law_sound u) ((stageBPriority (shape 2 2 4)) 0) a
def CB2_2_4I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(18432809600162602238233930394191 / 100000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩ ⟨(31170581090219803908545577364083 / 100000000000000000000000000000000), (15613197227 / 100000000000000000000000000000000)⟩ ⟨(-42275949470482293361630256775271 / 25000000000000000000000000000000), (847032951 / 1000000000000000000000000000000)⟩ ⟨-3, 18432809600162602238233930394191, 12500000000000000000000000000000⟩,
   .log ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩ ⟨(29035798632197530040660383517107 / 100000000000000000000000000000000), (6684612613 / 25000000000000000000000000000000)⟩ ⟨(-9198094054118637402943840466023 / 20000000000000000000000000000000), (8470329501 / 20000000000000000000000000000000)⟩ ⟨-1, 3156719039983739776176606960581, 2500000000000000000000000000000⟩]
lemma CB2_2_4I0Certificates_valid :
    CB2_2_4I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_2_4I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CB2_2_4I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I0Certificates (CB2_2_4I0CertificateIndex a)).input
lemma CB2_2_4I0P_check : ∀ a : Fin 17, contains (CB2_2_4I0Raw a) (CB2_2_4I0P a) = true := by
  decide +kernel
lemma CB2_2_4I0P_sound (a : Fin 17) :
    (CB2_2_4I0P a).Encloses (CB2_2_4I0Value a) :=
  contains_sound (CB2_2_4I0Raw_sound a) (CB2_2_4I0P_check a)
def CB2_2_4I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_2_4I0Certificates (CB2_2_4I0CertificateIndex a)).output
lemma CB2_2_4I0Terms_sound (a : Fin 17) :
    (CB2_2_4I0Terms a).Encloses (Foundation.entropyTerm (CB2_2_4I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_2_4I0Certificates_valid
    (CB2_2_4I0CertificateIndex a) (CB2_2_4I0P_sound a)
def CB2_2_4I0Entropy : Ball := ⟨(91376960812637137857751538245273 / 100000000000000000000000000000000), (28982422453 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I0Entropy_sound : CB2_2_4I0Entropy.Encloses (Foundation.finiteEntropy CB2_2_4I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_2_4I0Value CB2_2_4I0Terms CB2_2_4I0Terms_sound) (by decide +kernel)
def CB2_2_4I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (7 / 3125000000000000000000000000000)⟩
lemma CB2_2_4I0Mass_sound : CB2_2_4I0Mass.Encloses (∑ a, CB2_2_4I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_2_4I0P CB2_2_4I0Value CB2_2_4I0P_sound) (by decide +kernel)
def CB2_2_4I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB2_2_4I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911953 / 50000000000000000000000000000000)⟩
lemma CB2_2_4I0MassTermLog_sound : CB2_2_4I0MassTermLog.Encloses (Real.log ((∑ a, CB2_2_4I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_2_4I0Mass_sound) (w := CB2_2_4I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_2_4I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823907 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I0MassTerm_sound : CB2_2_4I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_2_4I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_2_4I0Mass_sound) CB2_2_4I0MassTermLog_sound) (by decide +kernel)
def CB2_2_4I0H : Ball := ⟨(3655078432505485514310061529811 / 4000000000000000000000000000000), (79140668813 / 100000000000000000000000000000000)⟩
lemma CB2_2_4I0H_sound : CB2_2_4I0H.Encloses (homogeneousEntropy CB2_2_4I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_2_4I0Value CB2_2_4I0MassTerm_sound CB2_2_4I0Entropy_sound) (by decide +kernel)
lemma CB2_2_4I0_sound : CB2_2_4I0H.Encloses (stageBCapacity (shape 2 2 4) 0) := by
  exact CB2_2_4I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
