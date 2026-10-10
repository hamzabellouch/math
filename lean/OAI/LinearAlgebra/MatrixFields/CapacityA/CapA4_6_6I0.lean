import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA4_6_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CA4_6_6I0Value (a : Fin 17) : ℝ := marginal (below (shape 4 6 6)) (fun u => (stageALaw (shape 4 6 6) u : ℝ)) ((Equiv.refl (Fin 3)) 0) a
def CA4_6_6I0Raw (a : Fin 17) : Ball := marginalBall (below (shape 4 6 6)) A4_6_6Law ((Equiv.refl (Fin 3)) 0) a
lemma CA4_6_6I0Raw_sound (a : Fin 17) :
    (CA4_6_6I0Raw a).Encloses (CA4_6_6I0Value a) := by
  exact marginalBall_sound (below (shape 4 6 6)) A4_6_6Law (fun u => (stageALaw (shape 4 6 6) u : ℝ)) (fun u _ => A4_6_6Law_sound u) ((Equiv.refl (Fin 3)) 0) a
def CA4_6_6I0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(1269317881239145350260745246849 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩ ⟨(9325788524935738087929366566497 / 100000000000000000000000000000000), (94075983 / 2500000000000000000000000000000)⟩ ⟨(-91838583765869091870909778712293 / 25000000000000000000000000000000), (148230766529 / 100000000000000000000000000000000)⟩ ⟨-6, 1269317881239145350260745246849, 781250000000000000000000000000⟩,
   .log ⟨(11588820373098244973492919766751 / 50000000000000000000000000000000), (7 / 6250000000000000000000000000000)⟩ ⟨(16942648327689404538018829373863 / 50000000000000000000000000000000), (1963222563 / 10000000000000000000000000000000)⟩ ⟨(-36549553324295391039878643229909 / 25000000000000000000000000000000), (16940659043 / 20000000000000000000000000000000)⟩ ⟨-3, 11588820373098244973492919766751, 6250000000000000000000000000000⟩,
   .log ⟨(24283723491325219352492669972801 / 50000000000000000000000000000000), (77 / 50000000000000000000000000000000)⟩ ⟨(35076221028848599746831186638677 / 100000000000000000000000000000000), (30853671087 / 100000000000000000000000000000000)⟩ ⟨(-72221669467984888230715756913543 / 100000000000000000000000000000000), (31763735683 / 50000000000000000000000000000000)⟩ ⟨-2, 24283723491325219352492669972801, 12500000000000000000000000000000⟩]
lemma CA4_6_6I0Certificates_valid :
    CA4_6_6I0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CA4_6_6I0CertificateIndex (a : Fin 17) : ℕ :=
  match a.val with
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ => 0
def CA4_6_6I0P (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I0Certificates (CA4_6_6I0CertificateIndex a)).input
lemma CA4_6_6I0P_check : ∀ a : Fin 17, contains (CA4_6_6I0Raw a) (CA4_6_6I0P a) = true := by
  decide +kernel
lemma CA4_6_6I0P_sound (a : Fin 17) :
    (CA4_6_6I0P a).Encloses (CA4_6_6I0Value a) :=
  contains_sound (CA4_6_6I0Raw_sound a) (CA4_6_6I0P_check a)
def CA4_6_6I0Terms (a : Fin 17) : Ball :=
  (CompactCertificate.entropyLookup CA4_6_6I0Certificates (CA4_6_6I0CertificateIndex a)).output
lemma CA4_6_6I0Terms_sound (a : Fin 17) :
    (CA4_6_6I0Terms a).Encloses (Foundation.entropyTerm (CA4_6_6I0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA4_6_6I0Certificates_valid
    (CA4_6_6I0CertificateIndex a) (CA4_6_6I0P_sound a)
def CA4_6_6I0Entropy : Ball := ⟨(121498391389477694074765237267123 / 100000000000000000000000000000000), (77644200987 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I0Entropy_sound : CA4_6_6I0Entropy.Encloses (Foundation.finiteEntropy CA4_6_6I0Value) := by
  exact contains_sound (entropyFin_enclosed 17 CA4_6_6I0Value CA4_6_6I0Terms CA4_6_6I0Terms_sound) (by decide +kernel)
def CA4_6_6I0Mass : Ball := ⟨(50000000000000000000000000000001 / 50000000000000000000000000000000), (13 / 3125000000000000000000000000000)⟩
lemma CA4_6_6I0Mass_sound : CA4_6_6I0Mass.Encloses (∑ a, CA4_6_6I0Value a) := by
  exact contains_sound (finSumBall_sound 17 CA4_6_6I0P CA4_6_6I0Value CA4_6_6I0P_sound) (by decide +kernel)
def CA4_6_6I0MassTermLogWitness : LogWitness := ⟨0, 50000000000000000000000000000001, 50000000000000000000000000000000⟩
def CA4_6_6I0MassTermLog : Ball := ⟨(1 / 50000000000000000000000000000000), (10587912049 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I0MassTermLog_sound : CA4_6_6I0MassTermLog.Encloses (Real.log ((∑ a, CA4_6_6I0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CA4_6_6I0Mass_sound) (w := CA4_6_6I0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CA4_6_6I0MassTerm : Ball := ⟨(-1 / 50000000000000000000000000000000), (21175824099 / 100000000000000000000000000000000)⟩
lemma CA4_6_6I0MassTerm_sound : CA4_6_6I0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA4_6_6I0Value a))) := by
  exact contains_sound (entropyTerm_ball (CA4_6_6I0Mass_sound) CA4_6_6I0MassTermLog_sound) (by decide +kernel)
def CA4_6_6I0H : Ball := ⟨(971987131115821552598121898137 / 800000000000000000000000000000), (49410012543 / 50000000000000000000000000000000)⟩
lemma CA4_6_6I0H_sound : CA4_6_6I0H.Encloses (homogeneousEntropy CA4_6_6I0Value) := by
  exact contains_sound (homogeneous_enclosed CA4_6_6I0Value CA4_6_6I0MassTerm_sound CA4_6_6I0Entropy_sound) (by decide +kernel)
lemma CA4_6_6I0_sound : CA4_6_6I0H.Encloses (stageACapacity (shape 4 6 6) 0) := by
  exact CA4_6_6I0H_sound

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
