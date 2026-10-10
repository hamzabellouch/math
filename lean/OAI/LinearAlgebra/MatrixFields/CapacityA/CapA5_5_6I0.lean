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
def CA5_5_6I0Value (a : Fin 17) : ℝ := marginal (below (shape 5 5 6)) (fun u => (stageALaw (shape 5 5 6) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA5_5_6I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 5 5 6)) A5_5_6Law ((Equiv.refl (Fin 3)) 0) a
lemma CA5_5_6I0Raw_sound (a : Fin 17) :
    (CA5_5_6I0Raw a).Encloses (CA5_5_6I0Value a) := by
  exact marginalBall_sound (below (shape 5 5 6)) A5_5_6Law (fun u => (stageALaw (shape 5 5 6) u : ℝ)) (fun u _ => A5_5_6Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA5_5_6I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(270590761901983101291232024027 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩ ⟨(199977325278267617159334197177 / 12500000000000000000000000000000), (286499131 / 50000000000000000000000000000000)⟩ ⟨(-591231788912900138456119133348293 / 100000000000000000000000000000000), (211758238677 / 100000000000000000000000000000000)⟩ ⟨-9, 270590761901983101291232024027, 195312500000000000000000000000⟩,
   .log ⟨(871492139876430027300788537499 / 10000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩ ⟨(4253114376545020880061123764263 / 20000000000000000000000000000000), (9227282079 / 100000000000000000000000000000000)⟩ ⟨(-244013352613144356441017926244217 / 100000000000000000000000000000000), (105879118851 / 100000000000000000000000000000000)⟩ ⟨-4, 871492139876430027300788537499, 625000000000000000000000000000⟩,
   .log ⟨(20507243919666858312850441300491 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩ ⟨(36553949822179816556948326600019 / 100000000000000000000000000000000), (26055467047 / 100000000000000000000000000000000)⟩ ⟨(-44562240988321991640392161064429 / 50000000000000000000000000000000), (63527471253 / 100000000000000000000000000000000)⟩ ⟨-2, 20507243919666858312850441300491, 12500000000000000000000000000000⟩]
lemma CA5_5_6I0Certificates_valid :
    CA5_5_6I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA5_5_6I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 3
  | 4 => 2
  | 5 => 1
  | _ => 0
def CA5_5_6I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I0Certificates (CA5_5_6I0CertificateIndex a)).input
lemma CA5_5_6I0P_check : ∀ a : Fin 17, contains (CA5_5_6I0Raw a) (CA5_5_6I0P a) = true := by
  decide +kernel
lemma CA5_5_6I0P_sound (a : Fin 17) :
    (CA5_5_6I0P a).Encloses (CA5_5_6I0Value a) :=
  contains_sound (CA5_5_6I0Raw_sound a) (CA5_5_6I0P_check a)
def CA5_5_6I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA5_5_6I0Certificates (CA5_5_6I0CertificateIndex a)).output
lemma CA5_5_6I0Terms_sound (a : Fin 17) :
    (CA5_5_6I0Terms a).Encloses (Foundation.entropyTerm (CA5_5_6I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA5_5_6I0Certificates_valid
    (CA5_5_6I0CertificateIndex a) (CA5_5_6I0P_sound a)
def CA5_5_6I0Entropy : Ball := ⟨(47535472245704849515622895199 / 40000000000000000000000000000), (8963936847 / 12500000000000000000000000000000)⟩
lemma CA5_5_6I0Entropy_sound : CA5_5_6I0Entropy.Encloses (Foundation.finiteEntropy CA5_5_6I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA5_5_6I0Value CA5_5_6I0Terms CA5_5_6I0Terms_sound) (by decide +kernel)
def CA5_5_6I0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (127 / 50000000000000000000000000000000)⟩
lemma CA5_5_6I0Mass_sound : CA5_5_6I0Mass.Encloses (∑ a, CA5_5_6I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA5_5_6I0P CA5_5_6I0Value CA5_5_6I0P_sound) (by decide +kernel)
def CA5_5_6I0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def CA5_5_6I0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (2117582381 / 5000000000000000000000000000000)⟩
lemma CA5_5_6I0MassTermLog_sound : CA5_5_6I0MassTermLog.Encloses (Real.log ((∑ a, CA5_5_6I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA5_5_6I0Mass_sound) (w := CA5_5_6I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA5_5_6I0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (42351647621 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I0MassTerm_sound : CA5_5_6I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA5_5_6I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA5_5_6I0Mass_sound) CA5_5_6I0MassTermLog_sound) (by decide +kernel)
def CA5_5_6I0H : Ball := ⟨(118838680614262123789057237997499 / 100000000000000000000000000000000), (114063142397 / 100000000000000000000000000000000)⟩
lemma CA5_5_6I0H_sound : CA5_5_6I0H.Encloses (homogeneousEntropy CA5_5_6I0Value) := by
  exact contains_sound (homogeneous_enclosed CA5_5_6I0Value CA5_5_6I0MassTerm_sound CA5_5_6I0Entropy_sound) (by decide +kernel)
lemma CA5_5_6I0_sound : CA5_5_6I0H.Encloses (stageACapacity (shape 5 5 6) 0) := by
  exact CA5_5_6I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
