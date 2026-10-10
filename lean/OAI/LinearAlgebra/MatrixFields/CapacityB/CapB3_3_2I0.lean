import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_3_2

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_3_2I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 3 2)) (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) ((stageBPriority (shape 3 3 2)) 0) a
def CB3_3_2I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 3 2)) B3_3_2Law ((stageBPriority (shape 3 3 2)) 0) a
lemma CB3_3_2I0Raw_sound (a : Fin 17) :
    (CB3_3_2I0Raw a).Encloses (CB3_3_2I0Value a) := by
  exact marginalBall_sound (below (shape 3 3 2)) B3_3_2Law (fun u => (stageBLaw (shape 3 3 2) u : ℝ)) (fun u _ => B3_3_2Law_sound u) ((stageBPriority (shape 3 3 2)) 0) a
def CB3_3_2I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(330535454043745680088327227499 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩ ⟨(2859737996082385988803712780319 / 50000000000000000000000000000000), (2239795391 / 100000000000000000000000000000000)⟩ ⟨(-17303668705408561775845756218399 / 4000000000000000000000000000000), (169406589917 / 100000000000000000000000000000000)⟩ ⟨-7, 330535454043745680088327227499, 195312500000000000000000000000⟩,
   .log ⟨(9735571636765003455929338218001 / 20000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩ ⟨(35045425233336004962761276330757 / 100000000000000000000000000000000), (6184762471 / 20000000000000000000000000000000)⟩ ⟨(-71994591670389305922740185860467 / 100000000000000000000000000000000), (15881867789 / 25000000000000000000000000000000)⟩ ⟨-2, 9735571636765003455929338218001, 5000000000000000000000000000000⟩]
lemma CB3_3_2I0Certificates_valid :
    CB3_3_2I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_3_2I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CB3_3_2I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB3_3_2I0Certificates (CB3_3_2I0CertificateIndex a)).input
lemma CB3_3_2I0P_check : ∀ a : Fin 17, contains (CB3_3_2I0Raw a) (CB3_3_2I0P a) = true := by
  decide +kernel
lemma CB3_3_2I0P_sound (a : Fin 17) :
    (CB3_3_2I0P a).Encloses (CB3_3_2I0Value a) :=
  contains_sound (CB3_3_2I0Raw_sound a) (CB3_3_2I0P_check a)
def CB3_3_2I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CB3_3_2I0Certificates (CB3_3_2I0CertificateIndex a)).output
lemma CB3_3_2I0Terms_sound (a : Fin 17) :
    (CB3_3_2I0Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I0Certificates_valid
    (CB3_3_2I0CertificateIndex a) (CB3_3_2I0P_sound a)
def CB3_3_2I0Entropy : Ball := ⟨(8152980245100155388073740378279 / 10000000000000000000000000000000), (16581803873 / 25000000000000000000000000000000)⟩
lemma CB3_3_2I0Entropy_sound : CB3_3_2I0Entropy.Encloses (Foundation.finiteEntropy CB3_3_2I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CB3_3_2I0Value CB3_3_2I0Terms CB3_3_2I0Terms_sound) (by decide +kernel)
def CB3_3_2I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (29 / 25000000000000000000000000000000)⟩
lemma CB3_3_2I0Mass_sound : CB3_3_2I0Mass.Encloses (∑ a, CB3_3_2I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CB3_3_2I0P CB3_3_2I0Value CB3_3_2I0P_sound) (by decide +kernel)
def CB3_3_2I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CB3_3_2I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587911899 / 50000000000000000000000000000000)⟩
lemma CB3_3_2I0MassTermLog_sound : CB3_3_2I0MassTermLog.Encloses (Real.log ((∑ a, CB3_3_2I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_3_2I0Mass_sound) (w := CB3_3_2I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_3_2I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175823799 / 100000000000000000000000000000000)⟩
lemma CB3_3_2I0MassTerm_sound : CB3_3_2I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_3_2I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_3_2I0Mass_sound) CB3_3_2I0MassTermLog_sound) (by decide +kernel)
def CB3_3_2I0H : Ball := ⟨(10191225306375194235092175472849 / 12500000000000000000000000000000), (87503039291 / 100000000000000000000000000000000)⟩
lemma CB3_3_2I0H_sound : CB3_3_2I0H.Encloses (homogeneousEntropy CB3_3_2I0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_3_2I0Value CB3_3_2I0MassTerm_sound CB3_3_2I0Entropy_sound) (by decide +kernel)
lemma CB3_3_2I0_sound : CB3_3_2I0H.Encloses (stageBCapacity (shape 3 3 2) 0) := by
  exact CB3_3_2I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
