import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_4_10

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_4_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 4 10)) (fun u => (stageALaw (shape 2 4 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_4_10I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 4 10)) A2_4_10Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_4_10I0Raw_sound (a : Fin 17) :
    (CA2_4_10I0Raw a).Encloses (CA2_4_10I0Value a) := by
  exact marginalBall_sound (below (shape 2 4 10)) A2_4_10Law (fun u => (stageALaw (shape 2 4 10) u : ℝ)) (fun u _ => A2_4_10Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_4_10I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(26087705617267747066040049921581 / 100000000000000000000000000000000), (31 / 25000000000000000000000000000000)⟩ ⟨(1752710369667411269351514178767 / 5000000000000000000000000000000), (662914397 / 4000000000000000000000000000000)⟩ ⟨(-134370603178477487491496450973271 / 100000000000000000000000000000000), (15881867881 / 25000000000000000000000000000000)⟩ ⟨-2, 26087705617267747066040049921581, 25000000000000000000000000000000⟩,
   .log ⟨(23912294382732252933959950078419 / 50000000000000000000000000000000), (9 / 6250000000000000000000000000000)⟩ ⟨(35276864296661715112529795930633 / 100000000000000000000000000000000), (30381752033 / 100000000000000000000000000000000)⟩ ⟨(-14752605388689151031123206533413 / 20000000000000000000000000000000), (1270549427 / 2000000000000000000000000000000)⟩ ⟨-2, 23912294382732252933959950078419, 12500000000000000000000000000000⟩]
lemma CA2_4_10I0Certificates_valid :
    CA2_4_10I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_4_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_4_10I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I0Certificates (CA2_4_10I0CertificateIndex a)).input
lemma CA2_4_10I0P_check : ∀ a : Fin 17, contains (CA2_4_10I0Raw a) (CA2_4_10I0P a) = true := by
  decide +kernel
lemma CA2_4_10I0P_sound (a : Fin 17) :
    (CA2_4_10I0P a).Encloses (CA2_4_10I0Value a) :=
  contains_sound (CA2_4_10I0Raw_sound a) (CA2_4_10I0P_check a)
def CA2_4_10I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_4_10I0Certificates (CA2_4_10I0CertificateIndex a)).output
lemma CA2_4_10I0Terms_sound (a : Fin 17) :
    (CA2_4_10I0Terms a).Encloses (Foundation.entropyTerm (CA2_4_10I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_4_10I0Certificates_valid
    (CA2_4_10I0CertificateIndex a) (CA2_4_10I0P_sound a)
def CA2_4_10I0Entropy : Ball := ⟨(105385279083358165886590363081313 / 100000000000000000000000000000000), (63527471883 / 100000000000000000000000000000000)⟩
lemma CA2_4_10I0Entropy_sound : CA2_4_10I0Entropy.Encloses (Foundation.finiteEntropy CA2_4_10I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_4_10I0Value CA2_4_10I0Terms CA2_4_10I0Terms_sound) (by decide +kernel)
def CA2_4_10I0Mass : Ball := ⟨1, (49 / 12500000000000000000000000000000)⟩
lemma CA2_4_10I0Mass_sound : CA2_4_10I0Mass.Encloses (∑ a, CA2_4_10I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_4_10I0P CA2_4_10I0Value CA2_4_10I0P_sound) (by decide +kernel)
def CA2_4_10I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA2_4_10I0MassTermLog : Ball := ⟨0, (10587912037 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I0MassTermLog_sound : CA2_4_10I0MassTermLog.Encloses (Real.log ((∑ a, CA2_4_10I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_4_10I0Mass_sound) (w := CA2_4_10I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_4_10I0MassTerm : Ball := ⟨0, (847032963 / 4000000000000000000000000000000)⟩
lemma CA2_4_10I0MassTerm_sound : CA2_4_10I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_4_10I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_4_10I0Mass_sound) CA2_4_10I0MassTermLog_sound) (by decide +kernel)
def CA2_4_10I0H : Ball := ⟨(105385279083358165886590363081313 / 100000000000000000000000000000000), (42351647979 / 50000000000000000000000000000000)⟩
lemma CA2_4_10I0H_sound : CA2_4_10I0H.Encloses (homogeneousEntropy CA2_4_10I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_4_10I0Value CA2_4_10I0MassTerm_sound CA2_4_10I0Entropy_sound) (by decide +kernel)
lemma CA2_4_10I0_sound : CA2_4_10I0H.Encloses (stageACapacity (shape 2 4 10) 0) := by
  exact CA2_4_10I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
