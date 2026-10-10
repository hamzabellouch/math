import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_6_8

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA2_6_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 2 6 8)) (fun u => (stageALaw (shape 2 6 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA2_6_8I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 2 6 8)) A2_6_8Law ((Equiv.refl (Fin 3)) 0) a
lemma CA2_6_8I0Raw_sound (a : Fin 17) :
    (CA2_6_8I0Raw a).Encloses (CA2_6_8I0Value a) := by
  exact marginalBall_sound (below (shape 2 6 8)) A2_6_8Law (fun u => (stageALaw (shape 2 6 8) u : ℝ)) (fun u _ => A2_6_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA2_6_8I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5031635526765957794431946269157 / 20000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩ ⟨(4339745350595764104085212084849 / 12500000000000000000000000000000), (7991177147 / 50000000000000000000000000000000)⟩ ⟨(-68999359393347786611655126869357 / 50000000000000000000000000000000), (63527471517 / 100000000000000000000000000000000)⟩ ⟨-2, 5031635526765957794431946269157, 5000000000000000000000000000000⟩,
   .log ⟨(49683644732340422055680537308427 / 100000000000000000000000000000000), (137 / 100000000000000000000000000000000)⟩ ⟨(34753430609830510821655789687667 / 100000000000000000000000000000000), (31562763257 / 100000000000000000000000000000000)⟩ ⟨(-34974719343817148668740251262693 / 50000000000000000000000000000000), (15881867831 / 25000000000000000000000000000000)⟩ ⟨-2, 49683644732340422055680537308427, 25000000000000000000000000000000⟩]
lemma CA2_6_8I0Certificates_valid :
    CA2_6_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA2_6_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 1
  | _ => 0
def CA2_6_8I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I0Certificates (CA2_6_8I0CertificateIndex a)).input
lemma CA2_6_8I0P_check : ∀ a : Fin 17, contains (CA2_6_8I0Raw a) (CA2_6_8I0P a) = true := by
  decide +kernel
lemma CA2_6_8I0P_sound (a : Fin 17) :
    (CA2_6_8I0P a).Encloses (CA2_6_8I0Value a) :=
  contains_sound (CA2_6_8I0Raw_sound a) (CA2_6_8I0P_check a)
def CA2_6_8I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA2_6_8I0Certificates (CA2_6_8I0CertificateIndex a)).output
lemma CA2_6_8I0Terms_sound (a : Fin 17) :
    (CA2_6_8I0Terms a).Encloses (Foundation.entropyTerm (CA2_6_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_6_8I0Certificates_valid
    (CA2_6_8I0CertificateIndex a) (CA2_6_8I0P_sound a)
def CA2_6_8I0Entropy : Ball := ⟨(104189356219362736487019183045251 / 100000000000000000000000000000000), (12705494369 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I0Entropy_sound : CA2_6_8I0Entropy.Encloses (Foundation.finiteEntropy CA2_6_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA2_6_8I0Value CA2_6_8I0Terms CA2_6_8I0Terms_sound) (by decide +kernel)
def CA2_6_8I0Mass : Ball := ⟨(99999999999999999999999999999997 / 100000000000000000000000000000000), (373 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I0Mass_sound : CA2_6_8I0Mass.Encloses (∑ a, CA2_6_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA2_6_8I0P CA2_6_8I0Value CA2_6_8I0P_sound) (by decide +kernel)
def CA2_6_8I0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999997, 50000000000000000000000000000000⟩
def CA2_6_8I0MassTermLog : Ball := ⟨(-1 / 50000000000000000000000000000000), (42351647739 / 100000000000000000000000000000000)⟩
lemma CA2_6_8I0MassTermLog_sound : CA2_6_8I0MassTermLog.Encloses (Real.log ((∑ a, CA2_6_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_6_8I0Mass_sound) (w := CA2_6_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA2_6_8I0MassTerm : Ball := ⟨(1 / 50000000000000000000000000000000), (2117582387 / 5000000000000000000000000000000)⟩
lemma CA2_6_8I0MassTerm_sound : CA2_6_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_6_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA2_6_8I0Mass_sound) CA2_6_8I0MassTermLog_sound) (by decide +kernel)
def CA2_6_8I0H : Ball := ⟨(104189356219362736487019183045249 / 100000000000000000000000000000000), (21175823917 / 20000000000000000000000000000000)⟩
lemma CA2_6_8I0H_sound : CA2_6_8I0H.Encloses (homogeneousEntropy CA2_6_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA2_6_8I0Value CA2_6_8I0MassTerm_sound CA2_6_8I0Entropy_sound) (by decide +kernel)
lemma CA2_6_8I0_sound : CA2_6_8I0H.Encloses (stageACapacity (shape 2 6 8) 0) := by
  exact CA2_6_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
