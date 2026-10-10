import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_1_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_4_8I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 4 8)) (fun u => (stageALaw (shape 4 4 8) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_4_8I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 4 8)) A4_4_8Law ((Equiv.refl (Fin 3)) 0) a
lemma CA4_4_8I0Raw_sound (a : Fin 17) :
    (CA4_4_8I0Raw a).Encloses (CA4_4_8I0Value a) := by
  exact marginalBall_sound (below (shape 4 4 8)) A4_4_8Law (fun u => (stageALaw (shape 4 4 8) u : ℝ)) (fun u _ => A4_4_8Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA4_4_8I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(2589321262873460994222456456713 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩ ⟨(4730397878676437863656173314291 / 50000000000000000000000000000000), (3838170821 / 100000000000000000000000000000000)⟩ ⟨(-365377440528715911135389273604699 / 100000000000000000000000000000000), (37057691619 / 25000000000000000000000000000000)⟩ ⟨-6, 2589321262873460994222456456713, 1562500000000000000000000000000⟩,
   .log ⟨(23158394703023787685168823300721 / 100000000000000000000000000000000), (99 / 100000000000000000000000000000000)⟩ ⟨(16938198667205440183393994905631 / 50000000000000000000000000000000), (3923184713 / 20000000000000000000000000000000)⟩ ⟨(-73140642451325965370550661695019 / 50000000000000000000000000000000), (84703295159 / 100000000000000000000000000000000)⟩ ⟨-3, 23158394703023787685168823300721, 12500000000000000000000000000000⟩,
   .log ⟨(4850456806820550264121744048513 / 10000000000000000000000000000000), (31 / 25000000000000000000000000000000)⟩ ⟨(4386705877521903671413106468791 / 12500000000000000000000000000000), (30813725651 / 100000000000000000000000000000000)⟩ ⟨(-72351220550665899606955299562419 / 100000000000000000000000000000000), (7940933913 / 12500000000000000000000000000000)⟩ ⟨-2, 4850456806820550264121744048513, 2500000000000000000000000000000⟩]
lemma CA4_4_8I0Certificates_valid :
    CA4_4_8I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_4_8I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0
def CA4_4_8I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I0Certificates (CA4_4_8I0CertificateIndex a)).input
lemma CA4_4_8I0P_check : ∀ a : Fin 17, contains (CA4_4_8I0Raw a) (CA4_4_8I0P a) = true := by
  decide +kernel
lemma CA4_4_8I0P_sound (a : Fin 17) :
    (CA4_4_8I0P a).Encloses (CA4_4_8I0Value a) :=
  contains_sound (CA4_4_8I0Raw_sound a) (CA4_4_8I0P_check a)
def CA4_4_8I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_4_8I0Certificates (CA4_4_8I0CertificateIndex a)).output
lemma CA4_4_8I0Terms_sound (a : Fin 17) :
    (CA4_4_8I0Terms a).Encloses (Foundation.entropyTerm (CA4_4_8I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_4_8I0Certificates_valid
    (CA4_4_8I0CertificateIndex a) (CA4_4_8I0P_sound a)
def CA4_4_8I0Entropy : Ball := ⟨(237828189850981917108409227793 / 195312500000000000000000000000), (77721914423 / 100000000000000000000000000000000)⟩
lemma CA4_4_8I0Entropy_sound : CA4_4_8I0Entropy.Encloses (Foundation.finiteEntropy CA4_4_8I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_4_8I0Value CA4_4_8I0Terms CA4_4_8I0Terms_sound) (by decide +kernel)
def CA4_4_8I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (179 / 50000000000000000000000000000000)⟩
lemma CA4_4_8I0Mass_sound : CA4_4_8I0Mass.Encloses (∑ a, CA4_4_8I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_4_8I0P CA4_4_8I0Value CA4_4_8I0P_sound) (by decide +kernel)
def CA4_4_8I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA4_4_8I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (10587911931 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I0MassTermLog_sound : CA4_4_8I0MassTermLog.Encloses (Real.log ((∑ a, CA4_4_8I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_4_8I0Mass_sound) (w := CA4_4_8I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_4_8I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (1694065909 / 4000000000000000000000000000000)⟩
lemma CA4_4_8I0MassTerm_sound : CA4_4_8I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_4_8I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_4_8I0Mass_sound) CA4_4_8I0MassTermLog_sound) (by decide +kernel)
def CA4_4_8I0H : Ball := ⟨(24353606640740548311901104926003 / 20000000000000000000000000000000), (30018390537 / 25000000000000000000000000000000)⟩
lemma CA4_4_8I0H_sound : CA4_4_8I0H.Encloses (homogeneousEntropy CA4_4_8I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_4_8I0Value CA4_4_8I0MassTerm_sound CA4_4_8I0Entropy_sound) (by decide +kernel)
lemma CA4_4_8I0_sound : CA4_4_8I0H.Encloses (stageACapacity (shape 4 4 8) 0) := by
  exact CA4_4_8I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
