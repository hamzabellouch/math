import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA4_5_7

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_5_7I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 5 7)) (fun u => (stageALaw (shape 4 5 7) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_5_7I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 5 7)) A4_5_7Law ((Equiv.refl (Fin 3)) 0) a
lemma CA4_5_7I0Raw_sound (a : Fin 17) :
    (CA4_5_7I0Raw a).Encloses (CA4_5_7I0Value a) := by
  exact marginalBall_sound (below (shape 4 5 7)) A4_5_7Law (fun u => (stageALaw (shape 4 5 7) u : ℝ)) (fun u _ => A4_5_7Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA4_5_7I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2588932326140645866727491993891 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩ ⟨(4729881788896945270895752580327 / 50000000000000000000000000000000), (239849643 / 6250000000000000000000000000000)⟩ ⟨(-584627939928931531044673636001 / 160000000000000000000000000000), (148230766399 / 100000000000000000000000000000000)⟩ ⟨-6, 2588932326140645866727491993891, 1562500000000000000000000000000⟩,
   .log ⟨(23161658632779186440713669476377 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩ ⟨(1355116307721707533931494734763 / 4000000000000000000000000000000), (2452336019 / 12500000000000000000000000000000)⟩ ⟨(-146267191957908803624313377112513 / 100000000000000000000000000000000), (42351647519 / 50000000000000000000000000000000)⟩ ⟨-3, 23161658632779186440713669476377, 12500000000000000000000000000000⟩,
   .log ⟨(6062352260270041923139709632433 / 12500000000000000000000000000000), (7 / 10000000000000000000000000000000)⟩ ⟨(35095236480304996425570291454063 / 100000000000000000000000000000000), (15405036369 / 50000000000000000000000000000000)⟩ ⟨(-72363075778158656714578664123817 / 100000000000000000000000000000000), (63527471193 / 100000000000000000000000000000000)⟩ ⟨-2, 6062352260270041923139709632433, 3125000000000000000000000000000⟩]
lemma CA4_5_7I0Certificates_valid :
    CA4_5_7I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_5_7I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0
def CA4_5_7I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I0Certificates (CA4_5_7I0CertificateIndex a)).input
lemma CA4_5_7I0P_check : ∀ a : Fin 17, contains (CA4_5_7I0Raw a) (CA4_5_7I0P a) = true := by
  decide +kernel
lemma CA4_5_7I0P_sound (a : Fin 17) :
    (CA4_5_7I0P a).Encloses (CA4_5_7I0Value a) :=
  contains_sound (CA4_5_7I0Raw_sound a) (CA4_5_7I0P_check a)
def CA4_5_7I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_5_7I0Certificates (CA4_5_7I0CertificateIndex a)).output
lemma CA4_5_7I0Terms_sound (a : Fin 17) :
    (CA4_5_7I0Terms a).Encloses (Foundation.entropyTerm (CA4_5_7I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_5_7I0Certificates_valid
    (CA4_5_7I0CertificateIndex a) (CA4_5_7I0P_sound a)
def CA4_5_7I0Entropy : Ball := ⟨(121770579021978154205728038513521 / 100000000000000000000000000000000), (38861318809 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I0Entropy_sound : CA4_5_7I0Entropy.Encloses (Foundation.finiteEntropy CA4_5_7I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_5_7I0Value CA4_5_7I0Terms CA4_5_7I0Terms_sound) (by decide +kernel)
def CA4_5_7I0Mass : Ball := ⟨1, (61 / 25000000000000000000000000000000)⟩
lemma CA4_5_7I0Mass_sound : CA4_5_7I0Mass.Encloses (∑ a, CA4_5_7I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_5_7I0P CA4_5_7I0Value CA4_5_7I0P_sound) (by decide +kernel)
def CA4_5_7I0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CA4_5_7I0MassTermLog : Ball := ⟨0, (10587911963 / 50000000000000000000000000000000)⟩
lemma CA4_5_7I0MassTermLog_sound : CA4_5_7I0MassTermLog.Encloses (Real.log ((∑ a, CA4_5_7I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_5_7I0Mass_sound) (w := CA4_5_7I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_5_7I0MassTerm : Ball := ⟨0, (21175823927 / 100000000000000000000000000000000)⟩
lemma CA4_5_7I0MassTerm_sound : CA4_5_7I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_5_7I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_5_7I0Mass_sound) CA4_5_7I0MassTermLog_sound) (by decide +kernel)
def CA4_5_7I0H : Ball := ⟨(121770579021978154205728038513521 / 100000000000000000000000000000000), (19779692309 / 20000000000000000000000000000000)⟩
lemma CA4_5_7I0H_sound : CA4_5_7I0H.Encloses (homogeneousEntropy CA4_5_7I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_5_7I0Value CA4_5_7I0MassTerm_sound CA4_5_7I0Entropy_sound) (by decide +kernel)
lemma CA4_5_7I0_sound : CA4_5_7I0H.Encloses (stageACapacity (shape 4 5 7) 0) := by
  exact CA4_5_7I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
