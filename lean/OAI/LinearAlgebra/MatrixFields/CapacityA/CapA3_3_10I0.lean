import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_3_10

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA3_3_10I0Value (a : Fin 17) : ℝ := marginal (below (shape 3 3 10)) (fun u => (stageALaw (shape 3 3 10) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA3_3_10I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 3 3 10)) A3_3_10Law ((Equiv.refl (Fin 3)) 0) a
lemma CA3_3_10I0Raw_sound (a : Fin 17) :
    (CA3_3_10I0Raw a).Encloses (CA3_3_10I0Value a) := by
  exact marginalBall_sound (below (shape 3 3 10)) A3_3_10Law (fun u => (stageALaw (shape 3 3 10) u : ℝ)) (fun u _ => A3_3_10Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA3_3_10I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(10497274588807341414561202190481 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩ ⟨(23661429292187606529377590229149 / 100000000000000000000000000000000), (11114421923 / 100000000000000000000000000000000)⟩ ⟨(-56351363137191031627685565486621 / 25000000000000000000000000000000), (21175823759 / 20000000000000000000000000000000)⟩ ⟨-4, 10497274588807341414561202190481, 6250000000000000000000000000000⟩,
   .log ⟨(39502725411192658585438797809519 / 100000000000000000000000000000000), (3 / 4000000000000000000000000000000)⟩ ⟨(18345075926178088449710102227777 / 50000000000000000000000000000000), (12547541297 / 50000000000000000000000000000000)⟩ ⟨(-290250162096730528682758688967 / 312500000000000000000000000000), (31763735619 / 50000000000000000000000000000000)⟩ ⟨-2, 39502725411192658585438797809519, 25000000000000000000000000000000⟩]
lemma CA3_3_10I0Certificates_valid :
    CA3_3_10I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA3_3_10I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 1
  | _ => 0
def CA3_3_10I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I0Certificates (CA3_3_10I0CertificateIndex a)).input
lemma CA3_3_10I0P_check : ∀ a : Fin 17, contains (CA3_3_10I0Raw a) (CA3_3_10I0P a) = true := by
  decide +kernel
lemma CA3_3_10I0P_sound (a : Fin 17) :
    (CA3_3_10I0P a).Encloses (CA3_3_10I0Value a) :=
  contains_sound (CA3_3_10I0Raw_sound a) (CA3_3_10I0P_check a)
def CA3_3_10I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA3_3_10I0Certificates (CA3_3_10I0CertificateIndex a)).output
lemma CA3_3_10I0Terms_sound (a : Fin 17) :
    (CA3_3_10I0Terms a).Encloses (Foundation.entropyTerm (CA3_3_10I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA3_3_10I0Certificates_valid
    (CA3_3_10I0CertificateIndex a) (CA3_3_10I0P_sound a)
def CA3_3_10I0Entropy : Ball := ⟨(60351581144543783428797794684703 / 50000000000000000000000000000000), (36209504517 / 50000000000000000000000000000000)⟩
lemma CA3_3_10I0Entropy_sound : CA3_3_10I0Entropy.Encloses (Foundation.finiteEntropy CA3_3_10I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA3_3_10I0Value CA3_3_10I0Terms CA3_3_10I0Terms_sound) (by decide +kernel)
def CA3_3_10I0Mass : Ball := ⟨1, (23 / 10000000000000000000000000000000)⟩
lemma CA3_3_10I0Mass_sound : CA3_3_10I0Mass.Encloses (∑ a, CA3_3_10I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA3_3_10I0P CA3_3_10I0Value CA3_3_10I0P_sound) (by decide +kernel)
def CA3_3_10I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA3_3_10I0MassTermLog : Ball := ⟨0, (2646977989 / 12500000000000000000000000000000)⟩
lemma CA3_3_10I0MassTermLog_sound : CA3_3_10I0MassTermLog.Encloses (Real.log ((∑ a, CA3_3_10I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA3_3_10I0Mass_sound) (w := CA3_3_10I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA3_3_10I0MassTerm : Ball := ⟨0, (21175823913 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I0MassTerm_sound : CA3_3_10I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA3_3_10I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA3_3_10I0Mass_sound) CA3_3_10I0MassTermLog_sound) (by decide +kernel)
def CA3_3_10I0H : Ball := ⟨(60351581144543783428797794684703 / 50000000000000000000000000000000), (93594832947 / 100000000000000000000000000000000)⟩
lemma CA3_3_10I0H_sound : CA3_3_10I0H.Encloses (homogeneousEntropy CA3_3_10I0Value) := by
  exact contains_sound (homogeneous_enclosed CA3_3_10I0Value CA3_3_10I0MassTerm_sound CA3_3_10I0Entropy_sound) (by decide +kernel)
lemma CA3_3_10I0_sound : CA3_3_10I0H.Encloses (stageACapacity (shape 3 3 10) 0) := by
  exact CA3_3_10I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
