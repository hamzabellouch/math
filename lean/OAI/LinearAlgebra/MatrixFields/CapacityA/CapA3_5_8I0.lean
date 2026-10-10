import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_5_8

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_5_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 5 8)) (fun u => (stageALaw (shape 3 5 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_5_8I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 5 8)) A3_5_8Law ((Equiv.refl (Fin 3)) 0) a
lemma CA3_5_8I0Raw_sound (a : Fin 17) :
    (CA3_5_8I0Raw a).Encloses (CA3_5_8I0Value a) := by
  exact marginalBall_sound (below (shape 3 5 8)) A3_5_8Law (fun u => (stageALaw (shape 3 5 8) u : ℝ)) (fun u _ => A3_5_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA3_5_8I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(10061494552782511104772956913071 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩ ⟨(23105764125084499096696734641399 / 100000000000000000000000000000000), (1331627733 / 12500000000000000000000000000000)⟩ ⟨(-114822723422806947883364156360731 / 50000000000000000000000000000000), (26469779703 / 25000000000000000000000000000000)⟩ ⟨-4, 10061494552782511104772956913071, 6250000000000000000000000000000⟩,
   .log ⟨(39938505447217488895227043086929 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩ ⟨(36656729644980840025676973240083 / 100000000000000000000000000000000), (25371922609 / 100000000000000000000000000000000)⟩ ⟨(-91782927865005299505533946601311 / 100000000000000000000000000000000), (63527471209 / 100000000000000000000000000000000)⟩ ⟨-2, 39938505447217488895227043086929, 25000000000000000000000000000000⟩]
lemma CA3_5_8I0Certificates_valid :
    CA3_5_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_5_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CA3_5_8I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I0Certificates (CA3_5_8I0CertificateIndex a)).input
lemma CA3_5_8I0P_check : ∀ a : Fin 17, contains (CA3_5_8I0Raw a) (CA3_5_8I0P a) = true := by
  decide +kernel
lemma CA3_5_8I0P_sound (a : Fin 17) :
    (CA3_5_8I0P a).Encloses (CA3_5_8I0Value a) :=
  contains_sound (CA3_5_8I0Raw_sound a) (CA3_5_8I0P_check a)
def CA3_5_8I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_5_8I0Certificates (CA3_5_8I0CertificateIndex a)).output
lemma CA3_5_8I0Terms_sound (a : Fin 17) :
    (CA3_5_8I0Terms a).Encloses (Foundation.entropyTerm (CA3_5_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_5_8I0Certificates_valid
    (CA3_5_8I0CertificateIndex a) (CA3_5_8I0P_sound a)
def CA3_5_8I0Entropy : Ball := ⟨(29881246885032669561186853940741 / 25000000000000000000000000000000), (36024944473 / 50000000000000000000000000000000)⟩
lemma CA3_5_8I0Entropy_sound : CA3_5_8I0Entropy.Encloses (Foundation.finiteEntropy CA3_5_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_5_8I0Value CA3_5_8I0Terms CA3_5_8I0Terms_sound) (by decide +kernel)
def CA3_5_8I0Mass : Ball := ⟨1, (13 / 6250000000000000000000000000000)⟩
lemma CA3_5_8I0Mass_sound : CA3_5_8I0Mass.Encloses (∑ a, CA3_5_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_5_8I0P CA3_5_8I0Value CA3_5_8I0P_sound) (by decide +kernel)
def CA3_5_8I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_5_8I0MassTermLog : Ball := ⟨0, (2117582389 / 10000000000000000000000000000000)⟩
lemma CA3_5_8I0MassTermLog_sound : CA3_5_8I0MassTermLog.Encloses (Real.log ((∑ a, CA3_5_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_5_8I0Mass_sound) (w := CA3_5_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_5_8I0MassTerm : Ball := ⟨0, (21175823891 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I0MassTerm_sound : CA3_5_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_5_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_5_8I0Mass_sound) CA3_5_8I0MassTermLog_sound) (by decide +kernel)
def CA3_5_8I0H : Ball := ⟨(29881246885032669561186853940741 / 25000000000000000000000000000000), (93225712837 / 100000000000000000000000000000000)⟩
lemma CA3_5_8I0H_sound : CA3_5_8I0H.Encloses (homogeneousEntropy CA3_5_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_5_8I0Value CA3_5_8I0MassTerm_sound CA3_5_8I0Entropy_sound) (by decide +kernel)
lemma CA3_5_8I0_sound : CA3_5_8I0H.Encloses (stageACapacity (shape 3 5 8) 0) := by
  exact CA3_5_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
