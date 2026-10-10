import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB2_3_3

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB2_3_3I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 3 3)) (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) ((stageBPriority (shape 2 3 3)) 0) a
def CB2_3_3I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 3 3)) B2_3_3Law ((stageBPriority (shape 2 3 3)) 0) a
lemma CB2_3_3I0Raw_sound (a : Fin 17) :
    (CB2_3_3I0Raw a).Encloses (CB2_3_3I0Value a) := by
  exact marginalBall_sound (below (shape 2 3 3)) B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ)) (fun u _ => B2_3_3Law_sound u) ((stageBPriority (shape 2 3 3)) 0) a
def CB2_3_3I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(760593062115024579018426140229 / 1562500000000000000000000000000), (37 / 100000000000000000000000000000000)⟩ ⟨(17522698923159325737403422183301 / 50000000000000000000000000000000), (15461937227 / 50000000000000000000000000000000)⟩ ⟨(-35997195387638027415224768226347 / 50000000000000000000000000000000), (508219769 / 800000000000000000000000000000)⟩ ⟨-2, 760593062115024579018426140229, 390625000000000000000000000000⟩,
   .log ⟨(20656937884975420981573859771 / 1562500000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(1143830148399399966764789719769 / 20000000000000000000000000000000), (2239629721 / 100000000000000000000000000000000)⟩ ⟨(-432599114357115427902291684210243 / 100000000000000000000000000000000), (84703294921 / 50000000000000000000000000000000)⟩ ⟨-7, 20656937884975420981573859771, 12207031250000000000000000000⟩]
lemma CB2_3_3I0Certificates_valid :
    CB2_3_3I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB2_3_3I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 0 => 2
  | _ => 0
def CB2_3_3I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I0Certificates (CB2_3_3I0CertificateIndex a)).input
lemma CB2_3_3I0P_check : ∀ a : Fin 17, contains (CB2_3_3I0Raw a) (CB2_3_3I0P a) = true := by
  decide +kernel
lemma CB2_3_3I0P_sound (a : Fin 17) :
    (CB2_3_3I0P a).Encloses (CB2_3_3I0Value a) :=
  contains_sound (CB2_3_3I0Raw_sound a) (CB2_3_3I0P_check a)
def CB2_3_3I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB2_3_3I0Certificates (CB2_3_3I0CertificateIndex a)).output
lemma CB2_3_3I0Terms_sound (a : Fin 17) :
    (CB2_3_3I0Terms a).Encloses (Foundation.entropyTerm (CB2_3_3I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB2_3_3I0Certificates_valid
    (CB2_3_3I0CertificateIndex a) (CB2_3_3I0P_sound a)
def CB2_3_3I0Entropy : Ball := ⟨(40764548588315651308630792965447 / 50000000000000000000000000000000), (1326540167 / 2000000000000000000000000000000)⟩
lemma CB2_3_3I0Entropy_sound : CB2_3_3I0Entropy.Encloses (Foundation.finiteEntropy CB2_3_3I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB2_3_3I0Value CB2_3_3I0Terms CB2_3_3I0Terms_sound) (by decide +kernel)
def CB2_3_3I0Mass : Ball := ⟨1, (21 / 25000000000000000000000000000000)⟩
lemma CB2_3_3I0Mass_sound : CB2_3_3I0Mass.Encloses (∑ a, CB2_3_3I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB2_3_3I0P CB2_3_3I0Value CB2_3_3I0P_sound) (by decide +kernel)
def CB2_3_3I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB2_3_3I0MassTermLog : Ball := ⟨0, (10587911883 / 50000000000000000000000000000000)⟩
lemma CB2_3_3I0MassTermLog_sound : CB2_3_3I0MassTermLog.Encloses (Real.log ((∑ a, CB2_3_3I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB2_3_3I0Mass_sound) (w := CB2_3_3I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB2_3_3I0MassTerm : Ball := ⟨0, (21175823767 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I0MassTerm_sound : CB2_3_3I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB2_3_3I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB2_3_3I0Mass_sound) CB2_3_3I0MassTermLog_sound) (by decide +kernel)
def CB2_3_3I0H : Ball := ⟨(40764548588315651308630792965447 / 50000000000000000000000000000000), (87502832117 / 100000000000000000000000000000000)⟩
lemma CB2_3_3I0H_sound : CB2_3_3I0H.Encloses (homogeneousEntropy CB2_3_3I0Value) := by
  exact contains_sound (homogeneous_enclosed CB2_3_3I0Value CB2_3_3I0MassTerm_sound CB2_3_3I0Entropy_sound) (by decide +kernel)
lemma CB2_3_3I0_sound : CB2_3_3I0H.Encloses (stageBCapacity (shape 2 3 3) 0) := by
  exact CB2_3_3I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
