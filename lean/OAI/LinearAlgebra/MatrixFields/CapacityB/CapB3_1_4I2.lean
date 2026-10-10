import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_1_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I2PairValue (a : PairSlot) : ℝ := pairLaw (below (shape 3 1 4)) (shape 3 1 4) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) a
def CB3_1_4I2PairRaw (a : PairSlot) : Ball := pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) a
lemma CB3_1_4I2PairRaw_sound (a : PairSlot) :
    (CB3_1_4I2PairRaw a).Encloses (CB3_1_4I2PairValue a) := by
  exact pairLawBall_sound_on (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) (fun u _ a => B3_1_4Little_sound (complement (shape 3 1 4) u) ((stageBPriority (shape 3 1 4)) 2) a) a
def CB3_1_4I2PairCertificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩ ⟨(-414510269489221060005265391870793 / 50000000000000000000000000000000), (275285711863 / 100000000000000000000000000000000)⟩ ⟨-12, 6274072805784506214853963141, 6103515625000000000000000000⟩,
   .log ⟨(3820996886917273539060027346381 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩ ⟨(3930295206317031159069190502873 / 20000000000000000000000000000000), (8091275691 / 100000000000000000000000000000000)⟩ ⟨(-128575582584677854984647202512921 / 50000000000000000000000000000000), (105879118611 / 100000000000000000000000000000000)⟩ ⟨-4, 3820996886917273539060027346381, 3125000000000000000000000000000⟩,
   .log ⟨(76473060096193834122862009176151 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩ ⟨(4102499213529906974063073891181 / 20000000000000000000000000000000), (253028131 / 781250000000000000000000000000)⟩ ⟨(-1341158313911284757935636752047 / 5000000000000000000000000000000), (1323488981 / 3125000000000000000000000000000)⟩ ⟨-1, 76473060096193834122862009176151, 50000000000000000000000000000000⟩,
   .log ⟨(408752583274976468404048388933 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩ ⟨(2613752313299241591256901234041 / 20000000000000000000000000000000), (5193403589 / 100000000000000000000000000000000)⟩ ⟨(-319723032984590996664872830008137 / 100000000000000000000000000000000), (63527471073 / 50000000000000000000000000000000)⟩ ⟨-5, 408752583274976468404048388933, 312500000000000000000000000000⟩,
   .log ⟨(17708108191266303098081954537 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(76489313075639343649791328593 / 50000000000000000000000000000000), (52497739 / 100000000000000000000000000000000)⟩ ⟨(-863890284037954129242199119797421 / 100000000000000000000000000000000), (37057692151 / 12500000000000000000000000000000)⟩ ⟨-13, 17708108191266303098081954537, 12207031250000000000000000000⟩]
lemma CB3_1_4I2PairCertificates_valid :
    CB3_1_4I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2PairCertificateIndex (a : PairSlot) : ℕ :=
  match a.1.val, a.2.val with
  | 5, 0 => 1
  | 4, 1 => 2
  | 2, 2 => 3
  | 2, 3 => 4
  | 3, 2 => 4
  | 3, 3 => 5
  | 1, 4 => 2
  | 0, 5 => 1
  | _, _ => 0
def CB3_1_4I2PairP (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2PairCertificates (CB3_1_4I2PairCertificateIndex a)).input
lemma CB3_1_4I2PairP_check : ∀ a : PairSlot, contains (CB3_1_4I2PairRaw a) (CB3_1_4I2PairP a) = true := by
  decide +kernel
lemma CB3_1_4I2PairP_sound (a : PairSlot) :
    (CB3_1_4I2PairP a).Encloses (CB3_1_4I2PairValue a) :=
  contains_sound (CB3_1_4I2PairRaw_sound a) (CB3_1_4I2PairP_check a)
def CB3_1_4I2PairTerms (a : PairSlot) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2PairCertificates (CB3_1_4I2PairCertificateIndex a)).output
lemma CB3_1_4I2PairTerms_sound (a : PairSlot) :
    (CB3_1_4I2PairTerms a).Encloses (Foundation.entropyTerm (CB3_1_4I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2PairCertificates_valid
    (CB3_1_4I2PairCertificateIndex a) (CB3_1_4I2PairP_sound a)
def CB3_1_4I2PairEntropy : Ball := ⟨(86522056707486857696995452485631 / 100000000000000000000000000000000), (59147630093 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2PairEntropy_sound : CB3_1_4I2PairEntropy.Encloses (Foundation.finiteEntropy CB3_1_4I2PairValue) := by
  exact contains_sound (entropyPair_enclosed CB3_1_4I2PairValue CB3_1_4I2PairTerms CB3_1_4I2PairTerms_sound) (by decide +kernel)
def CB3_1_4I2PairMass : Ball := ⟨1, (57 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2PairMass_sound : CB3_1_4I2PairMass.Encloses (∑ a, CB3_1_4I2PairValue a) := by
  exact contains_sound (pairSumBall_sound CB3_1_4I2PairP CB3_1_4I2PairValue CB3_1_4I2PairP_sound) (by decide +kernel)
def CB3_1_4I2PairMassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def CB3_1_4I2PairMassTermLog : Ball := ⟨0, (21175823739 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2PairMassTermLog_sound : CB3_1_4I2PairMassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2PairMass_sound) (w := CB3_1_4I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2PairMassTerm : Ball := ⟨0, (1058791187 / 5000000000000000000000000000000)⟩
lemma CB3_1_4I2PairMassTerm_sound : CB3_1_4I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2PairMass_sound) CB3_1_4I2PairMassTermLog_sound) (by decide +kernel)
def CB3_1_4I2PairH : Ball := ⟨(86522056707486857696995452485631 / 100000000000000000000000000000000), (80323453833 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2PairH_sound : CB3_1_4I2PairH.Encloses (homogeneousEntropy CB3_1_4I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2PairValue CB3_1_4I2PairMassTerm_sound CB3_1_4I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I2R0Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 0 a
def CB3_1_4I2R0Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 0 a
lemma CB3_1_4I2R0Raw_sound (a : Fin 6) :
    (CB3_1_4I2R0Raw a).Encloses (CB3_1_4I2R0Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 0 a
def CB3_1_4I2R0Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩ ⟨(-414510269489221060005265391870793 / 50000000000000000000000000000000), (275285711863 / 100000000000000000000000000000000)⟩ ⟨-12, 6274072805784506214853963141, 6103515625000000000000000000⟩]
lemma CB3_1_4I2R0Certificates_valid :
    CB3_1_4I2R0Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R0CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 0 => 1
  | _ => 0
def CB3_1_4I2R0P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R0Certificates (CB3_1_4I2R0CertificateIndex a)).input
lemma CB3_1_4I2R0P_check : ∀ a : Fin 6, contains (CB3_1_4I2R0Raw a) (CB3_1_4I2R0P a) = true := by
  decide +kernel
lemma CB3_1_4I2R0P_sound (a : Fin 6) :
    (CB3_1_4I2R0P a).Encloses (CB3_1_4I2R0Value a) :=
  contains_sound (CB3_1_4I2R0Raw_sound a) (CB3_1_4I2R0P_check a)
def CB3_1_4I2R0Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R0Certificates (CB3_1_4I2R0CertificateIndex a)).output
lemma CB3_1_4I2R0Terms_sound (a : Fin 6) :
    (CB3_1_4I2R0Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R0Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R0Certificates_valid
    (CB3_1_4I2R0CertificateIndex a) (CB3_1_4I2R0P_sound a)
def CB3_1_4I2R0Entropy : Ball := ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R0Entropy_sound : CB3_1_4I2R0Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R0Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R0Value CB3_1_4I2R0Terms CB3_1_4I2R0Terms_sound) (by decide +kernel)
def CB3_1_4I2R0Mass : Ball := ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R0Mass_sound : CB3_1_4I2R0Mass.Encloses (∑ a, CB3_1_4I2R0Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R0P CB3_1_4I2R0Value CB3_1_4I2R0P_sound) (by decide +kernel)
def CB3_1_4I2R0MassTermLogWitness : LogWitness := ⟨-12, 6274072805784506214853963141, 6103515625000000000000000000⟩
def CB3_1_4I2R0MassTermLog : Ball := ⟨(-414510269489221060005265391870793 / 50000000000000000000000000000000), (275285711863 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R0MassTermLog_sound : CB3_1_4I2R0MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2R0Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2R0Mass_sound) (w := CB3_1_4I2R0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2R0MassTerm : Ball := ⟨(2080534087616583180597915017 / 1000000000000000000000000000000), (69086513 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R0MassTerm_sound : CB3_1_4I2R0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R0Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2R0Mass_sound) CB3_1_4I2R0MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2R0H : Ball := ⟨0, (69086513 / 50000000000000000000000000000000)⟩
lemma CB3_1_4I2R0H_sound : CB3_1_4I2R0H.Encloses (homogeneousEntropy CB3_1_4I2R0Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R0Value CB3_1_4I2R0MassTerm_sound CB3_1_4I2R0Entropy_sound) (by decide +kernel)
def CB3_1_4I2R1Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 1 a
def CB3_1_4I2R1Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 1 a
lemma CB3_1_4I2R1Raw_sound (a : Fin 6) :
    (CB3_1_4I2R1Raw a).Encloses (CB3_1_4I2R1Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 1 a
def CB3_1_4I2R1Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩ ⟨(4371852957778900787421083283603 / 25000000000000000000000000000000), (3356321177 / 50000000000000000000000000000000)⟩ ⟨(-275830538978442120010530936506341 / 100000000000000000000000000000000), (26469779643 / 25000000000000000000000000000000)⟩ ⟨-4, 3169955708291305924669541513661, 3125000000000000000000000000000⟩]
lemma CB3_1_4I2R1Certificates_valid :
    CB3_1_4I2R1Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R1CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 1 => 1
  | _ => 0
def CB3_1_4I2R1P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R1Certificates (CB3_1_4I2R1CertificateIndex a)).input
lemma CB3_1_4I2R1P_check : ∀ a : Fin 6, contains (CB3_1_4I2R1Raw a) (CB3_1_4I2R1P a) = true := by
  decide +kernel
lemma CB3_1_4I2R1P_sound (a : Fin 6) :
    (CB3_1_4I2R1P a).Encloses (CB3_1_4I2R1Value a) :=
  contains_sound (CB3_1_4I2R1Raw_sound a) (CB3_1_4I2R1P_check a)
def CB3_1_4I2R1Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R1Certificates (CB3_1_4I2R1CertificateIndex a)).output
lemma CB3_1_4I2R1Terms_sound (a : Fin 6) :
    (CB3_1_4I2R1Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R1Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R1Certificates_valid
    (CB3_1_4I2R1CertificateIndex a) (CB3_1_4I2R1P_sound a)
def CB3_1_4I2R1Entropy : Ball := ⟨(4371852957778900787421083283603 / 25000000000000000000000000000000), (3356321177 / 50000000000000000000000000000000)⟩
lemma CB3_1_4I2R1Entropy_sound : CB3_1_4I2R1Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R1Value CB3_1_4I2R1Terms CB3_1_4I2R1Terms_sound) (by decide +kernel)
def CB3_1_4I2R1Mass : Ball := ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
lemma CB3_1_4I2R1Mass_sound : CB3_1_4I2R1Mass.Encloses (∑ a, CB3_1_4I2R1Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R1P CB3_1_4I2R1Value CB3_1_4I2R1P_sound) (by decide +kernel)
def CB3_1_4I2R1MassTermLogWitness : LogWitness := ⟨-4, 3169955708291305924669541513661, 3125000000000000000000000000000⟩
def CB3_1_4I2R1MassTermLog : Ball := ⟨(-275830538978442120010530936506341 / 100000000000000000000000000000000), (26469779643 / 25000000000000000000000000000000)⟩
lemma CB3_1_4I2R1MassTermLog_sound : CB3_1_4I2R1MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2R1Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2R1Mass_sound) (w := CB3_1_4I2R1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2R1MassTerm : Ball := ⟨(4371852957778900787421083283603 / 25000000000000000000000000000000), (3356321177 / 50000000000000000000000000000000)⟩
lemma CB3_1_4I2R1MassTerm_sound : CB3_1_4I2R1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2R1Mass_sound) CB3_1_4I2R1MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2R1H : Ball := ⟨0, (3356321177 / 25000000000000000000000000000000)⟩
lemma CB3_1_4I2R1H_sound : CB3_1_4I2R1H.Encloses (homogeneousEntropy CB3_1_4I2R1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R1Value CB3_1_4I2R1MassTerm_sound CB3_1_4I2R1Entropy_sound) (by decide +kernel)
def CB3_1_4I2R2Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 2 a
def CB3_1_4I2R2Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 2 a
lemma CB3_1_4I2R2Raw_sound (a : Fin 6) :
    (CB3_1_4I2R2Raw a).Encloses (CB3_1_4I2R2Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 2 a
def CB3_1_4I2R2Certificates : List CompactCertificate.EntropyDatum :=
  [.zero,
   .log ⟨(5279935150339487151005350643271 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩ ⟨(36402611261242721942916282948503 / 100000000000000000000000000000000), (5366734843 / 20000000000000000000000000000000)⟩ ⟨(-21545370719954605796349959838063 / 25000000000000000000000000000000), (63527471077 / 100000000000000000000000000000000)⟩ ⟨-2, 5279935150339487151005350643271, 3125000000000000000000000000000⟩,
   .log ⟨(46714366113208844488862154253 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩ ⟨(651733287129766991087305557601 / 100000000000000000000000000000000), (59352913 / 25000000000000000000000000000000)⟩ ⟨(-174393163537298972606767996914933 / 25000000000000000000000000000000), (127054942633 / 50000000000000000000000000000000)⟩ ⟨-11, 46714366113208844488862154253, 24414062500000000000000000000⟩]
lemma CB3_1_4I2R2Certificates_valid :
    CB3_1_4I2R2Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R2CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | 2 => 1
  | 3 => 2
  | _ => 0
def CB3_1_4I2R2P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R2Certificates (CB3_1_4I2R2CertificateIndex a)).input
lemma CB3_1_4I2R2P_check : ∀ a : Fin 6, contains (CB3_1_4I2R2Raw a) (CB3_1_4I2R2P a) = true := by
  decide +kernel
lemma CB3_1_4I2R2P_sound (a : Fin 6) :
    (CB3_1_4I2R2P a).Encloses (CB3_1_4I2R2Value a) :=
  contains_sound (CB3_1_4I2R2Raw_sound a) (CB3_1_4I2R2P_check a)
def CB3_1_4I2R2Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R2Certificates (CB3_1_4I2R2CertificateIndex a)).output
lemma CB3_1_4I2R2Terms_sound (a : Fin 6) :
    (CB3_1_4I2R2Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R2Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R2Certificates_valid
    (CB3_1_4I2R2CertificateIndex a) (CB3_1_4I2R2P_sound a)
def CB3_1_4I2R2Entropy : Ball := ⟨(4631793068546561116750448563263 / 12500000000000000000000000000000), (27071085867 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R2Entropy_sound : CB3_1_4I2R2Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R2Value CB3_1_4I2R2Terms CB3_1_4I2R2Terms_sound) (by decide +kernel)
def CB3_1_4I2R2Mass : Ball := ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R2Mass_sound : CB3_1_4I2R2Mass.Encloses (∑ a, CB3_1_4I2R2Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R2P CB3_1_4I2R2Value CB3_1_4I2R2P_sound) (by decide +kernel)
def CB3_1_4I2R2MassTermLogWitness : LogWitness := ⟨-2, 21166454967471157448510264727337, 12500000000000000000000000000000⟩
def CB3_1_4I2R2MassTermLog : Ball := ⟨(-85960538978442120010530974697353 / 100000000000000000000000000000000), (63527471079 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2R2MassTermLog_sound : CB3_1_4I2R2MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2R2Value a))) := by
  exact checkLog_sound logTwoBall_sound (CB3_1_4I2R2Mass_sound) (w := CB3_1_4I2R2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2R2MassTerm : Ball := ⟨(71073432705732197860803257381 / 195312500000000000000000000000), (3361628391 / 12500000000000000000000000000000)⟩
lemma CB3_1_4I2R2MassTerm_sound : CB3_1_4I2R2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2R2Mass_sound) CB3_1_4I2R2MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2R2H : Ball := ⟨(83093375379700453659040090879 / 12500000000000000000000000000000), (10792822599 / 20000000000000000000000000000000)⟩
lemma CB3_1_4I2R2H_sound : CB3_1_4I2R2H.Encloses (homogeneousEntropy CB3_1_4I2R2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R2Value CB3_1_4I2R2MassTerm_sound CB3_1_4I2R2Entropy_sound) (by decide +kernel)
def CB3_1_4I2R3Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 3 a
def CB3_1_4I2R3Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 3 a
lemma CB3_1_4I2R3Raw_sound (a : Fin 6) :
    (CB3_1_4I2R3Raw a).Encloses (CB3_1_4I2R3Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 3 a
def CB3_1_4I2R3Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R3Certificates_valid :
    CB3_1_4I2R3Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R3CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R3P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R3Certificates (CB3_1_4I2R3CertificateIndex a)).input
lemma CB3_1_4I2R3P_check : ∀ a : Fin 6, contains (CB3_1_4I2R3Raw a) (CB3_1_4I2R3P a) = true := by
  decide +kernel
lemma CB3_1_4I2R3P_sound (a : Fin 6) :
    (CB3_1_4I2R3P a).Encloses (CB3_1_4I2R3Value a) :=
  contains_sound (CB3_1_4I2R3Raw_sound a) (CB3_1_4I2R3P_check a)
def CB3_1_4I2R3Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R3Certificates (CB3_1_4I2R3CertificateIndex a)).output
lemma CB3_1_4I2R3Terms_sound (a : Fin 6) :
    (CB3_1_4I2R3Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R3Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R3Certificates_valid
    (CB3_1_4I2R3CertificateIndex a) (CB3_1_4I2R3P_sound a)
def CB3_1_4I2R3Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R3Entropy_sound : CB3_1_4I2R3Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R3Value CB3_1_4I2R3Terms CB3_1_4I2R3Terms_sound) (by decide +kernel)
def CB3_1_4I2R3Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R3Mass_sound : CB3_1_4I2R3Mass.Encloses (∑ a, CB3_1_4I2R3Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R3P CB3_1_4I2R3Value CB3_1_4I2R3P_sound) (by decide +kernel)
def CB3_1_4I2R3MassTerm : Ball := .exact 0
lemma CB3_1_4I2R3MassTerm_sound : CB3_1_4I2R3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R3Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R3Mass_sound)
def CB3_1_4I2R3H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R3H_sound : CB3_1_4I2R3H.Encloses (homogeneousEntropy CB3_1_4I2R3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R3Value CB3_1_4I2R3MassTerm_sound CB3_1_4I2R3Entropy_sound) (by decide +kernel)
def CB3_1_4I2R4Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 4 a
def CB3_1_4I2R4Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 4 a
lemma CB3_1_4I2R4Raw_sound (a : Fin 6) :
    (CB3_1_4I2R4Raw a).Encloses (CB3_1_4I2R4Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 4 a
def CB3_1_4I2R4Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R4Certificates_valid :
    CB3_1_4I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R4CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R4P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R4Certificates (CB3_1_4I2R4CertificateIndex a)).input
lemma CB3_1_4I2R4P_check : ∀ a : Fin 6, contains (CB3_1_4I2R4Raw a) (CB3_1_4I2R4P a) = true := by
  decide +kernel
lemma CB3_1_4I2R4P_sound (a : Fin 6) :
    (CB3_1_4I2R4P a).Encloses (CB3_1_4I2R4Value a) :=
  contains_sound (CB3_1_4I2R4Raw_sound a) (CB3_1_4I2R4P_check a)
def CB3_1_4I2R4Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R4Certificates (CB3_1_4I2R4CertificateIndex a)).output
lemma CB3_1_4I2R4Terms_sound (a : Fin 6) :
    (CB3_1_4I2R4Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R4Certificates_valid
    (CB3_1_4I2R4CertificateIndex a) (CB3_1_4I2R4P_sound a)
def CB3_1_4I2R4Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R4Entropy_sound : CB3_1_4I2R4Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R4Value CB3_1_4I2R4Terms CB3_1_4I2R4Terms_sound) (by decide +kernel)
def CB3_1_4I2R4Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R4Mass_sound : CB3_1_4I2R4Mass.Encloses (∑ a, CB3_1_4I2R4Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R4P CB3_1_4I2R4Value CB3_1_4I2R4P_sound) (by decide +kernel)
def CB3_1_4I2R4MassTerm : Ball := .exact 0
lemma CB3_1_4I2R4MassTerm_sound : CB3_1_4I2R4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R4Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R4Mass_sound)
def CB3_1_4I2R4H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R4H_sound : CB3_1_4I2R4H.Encloses (homogeneousEntropy CB3_1_4I2R4Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R4Value CB3_1_4I2R4MassTerm_sound CB3_1_4I2R4Entropy_sound) (by decide +kernel)
def CB3_1_4I2R5Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 5 a
def CB3_1_4I2R5Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 5 a
lemma CB3_1_4I2R5Raw_sound (a : Fin 6) :
    (CB3_1_4I2R5Raw a).Encloses (CB3_1_4I2R5Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 5 a
def CB3_1_4I2R5Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R5Certificates_valid :
    CB3_1_4I2R5Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R5CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R5P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R5Certificates (CB3_1_4I2R5CertificateIndex a)).input
lemma CB3_1_4I2R5P_check : ∀ a : Fin 6, contains (CB3_1_4I2R5Raw a) (CB3_1_4I2R5P a) = true := by
  decide +kernel
lemma CB3_1_4I2R5P_sound (a : Fin 6) :
    (CB3_1_4I2R5P a).Encloses (CB3_1_4I2R5Value a) :=
  contains_sound (CB3_1_4I2R5Raw_sound a) (CB3_1_4I2R5P_check a)
def CB3_1_4I2R5Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R5Certificates (CB3_1_4I2R5CertificateIndex a)).output
lemma CB3_1_4I2R5Terms_sound (a : Fin 6) :
    (CB3_1_4I2R5Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R5Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R5Certificates_valid
    (CB3_1_4I2R5CertificateIndex a) (CB3_1_4I2R5P_sound a)
def CB3_1_4I2R5Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R5Entropy_sound : CB3_1_4I2R5Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R5Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R5Value CB3_1_4I2R5Terms CB3_1_4I2R5Terms_sound) (by decide +kernel)
def CB3_1_4I2R5Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R5Mass_sound : CB3_1_4I2R5Mass.Encloses (∑ a, CB3_1_4I2R5Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R5P CB3_1_4I2R5Value CB3_1_4I2R5P_sound) (by decide +kernel)
def CB3_1_4I2R5MassTerm : Ball := .exact 0
lemma CB3_1_4I2R5MassTerm_sound : CB3_1_4I2R5MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R5Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R5Mass_sound)
def CB3_1_4I2R5H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R5H_sound : CB3_1_4I2R5H.Encloses (homogeneousEntropy CB3_1_4I2R5Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R5Value CB3_1_4I2R5MassTerm_sound CB3_1_4I2R5Entropy_sound) (by decide +kernel)
def CB3_1_4I2R6Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 6 a
def CB3_1_4I2R6Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 6 a
lemma CB3_1_4I2R6Raw_sound (a : Fin 6) :
    (CB3_1_4I2R6Raw a).Encloses (CB3_1_4I2R6Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 6 a
def CB3_1_4I2R6Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R6Certificates_valid :
    CB3_1_4I2R6Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R6CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R6P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R6Certificates (CB3_1_4I2R6CertificateIndex a)).input
lemma CB3_1_4I2R6P_check : ∀ a : Fin 6, contains (CB3_1_4I2R6Raw a) (CB3_1_4I2R6P a) = true := by
  decide +kernel
lemma CB3_1_4I2R6P_sound (a : Fin 6) :
    (CB3_1_4I2R6P a).Encloses (CB3_1_4I2R6Value a) :=
  contains_sound (CB3_1_4I2R6Raw_sound a) (CB3_1_4I2R6P_check a)
def CB3_1_4I2R6Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R6Certificates (CB3_1_4I2R6CertificateIndex a)).output
lemma CB3_1_4I2R6Terms_sound (a : Fin 6) :
    (CB3_1_4I2R6Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R6Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R6Certificates_valid
    (CB3_1_4I2R6CertificateIndex a) (CB3_1_4I2R6P_sound a)
def CB3_1_4I2R6Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R6Entropy_sound : CB3_1_4I2R6Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R6Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R6Value CB3_1_4I2R6Terms CB3_1_4I2R6Terms_sound) (by decide +kernel)
def CB3_1_4I2R6Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R6Mass_sound : CB3_1_4I2R6Mass.Encloses (∑ a, CB3_1_4I2R6Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R6P CB3_1_4I2R6Value CB3_1_4I2R6P_sound) (by decide +kernel)
def CB3_1_4I2R6MassTerm : Ball := .exact 0
lemma CB3_1_4I2R6MassTerm_sound : CB3_1_4I2R6MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R6Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R6Mass_sound)
def CB3_1_4I2R6H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R6H_sound : CB3_1_4I2R6H.Encloses (homogeneousEntropy CB3_1_4I2R6Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R6Value CB3_1_4I2R6MassTerm_sound CB3_1_4I2R6Entropy_sound) (by decide +kernel)
def CB3_1_4I2R7Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 7 a
def CB3_1_4I2R7Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 7 a
lemma CB3_1_4I2R7Raw_sound (a : Fin 6) :
    (CB3_1_4I2R7Raw a).Encloses (CB3_1_4I2R7Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 7 a
def CB3_1_4I2R7Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R7Certificates_valid :
    CB3_1_4I2R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R7CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R7P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R7Certificates (CB3_1_4I2R7CertificateIndex a)).input
lemma CB3_1_4I2R7P_check : ∀ a : Fin 6, contains (CB3_1_4I2R7Raw a) (CB3_1_4I2R7P a) = true := by
  decide +kernel
lemma CB3_1_4I2R7P_sound (a : Fin 6) :
    (CB3_1_4I2R7P a).Encloses (CB3_1_4I2R7Value a) :=
  contains_sound (CB3_1_4I2R7Raw_sound a) (CB3_1_4I2R7P_check a)
def CB3_1_4I2R7Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R7Certificates (CB3_1_4I2R7CertificateIndex a)).output
lemma CB3_1_4I2R7Terms_sound (a : Fin 6) :
    (CB3_1_4I2R7Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R7Certificates_valid
    (CB3_1_4I2R7CertificateIndex a) (CB3_1_4I2R7P_sound a)
def CB3_1_4I2R7Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R7Entropy_sound : CB3_1_4I2R7Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R7Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R7Value CB3_1_4I2R7Terms CB3_1_4I2R7Terms_sound) (by decide +kernel)
def CB3_1_4I2R7Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R7Mass_sound : CB3_1_4I2R7Mass.Encloses (∑ a, CB3_1_4I2R7Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R7P CB3_1_4I2R7Value CB3_1_4I2R7P_sound) (by decide +kernel)
def CB3_1_4I2R7MassTerm : Ball := .exact 0
lemma CB3_1_4I2R7MassTerm_sound : CB3_1_4I2R7MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R7Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R7Mass_sound)
def CB3_1_4I2R7H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R7H_sound : CB3_1_4I2R7H.Encloses (homogeneousEntropy CB3_1_4I2R7Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R7Value CB3_1_4I2R7MassTerm_sound CB3_1_4I2R7Entropy_sound) (by decide +kernel)
def CB3_1_4I2R8Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 8 a
def CB3_1_4I2R8Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 8 a
lemma CB3_1_4I2R8Raw_sound (a : Fin 6) :
    (CB3_1_4I2R8Raw a).Encloses (CB3_1_4I2R8Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 8 a
def CB3_1_4I2R8Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R8Certificates_valid :
    CB3_1_4I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R8CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R8P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R8Certificates (CB3_1_4I2R8CertificateIndex a)).input
lemma CB3_1_4I2R8P_check : ∀ a : Fin 6, contains (CB3_1_4I2R8Raw a) (CB3_1_4I2R8P a) = true := by
  decide +kernel
lemma CB3_1_4I2R8P_sound (a : Fin 6) :
    (CB3_1_4I2R8P a).Encloses (CB3_1_4I2R8Value a) :=
  contains_sound (CB3_1_4I2R8Raw_sound a) (CB3_1_4I2R8P_check a)
def CB3_1_4I2R8Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R8Certificates (CB3_1_4I2R8CertificateIndex a)).output
lemma CB3_1_4I2R8Terms_sound (a : Fin 6) :
    (CB3_1_4I2R8Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R8Certificates_valid
    (CB3_1_4I2R8CertificateIndex a) (CB3_1_4I2R8P_sound a)
def CB3_1_4I2R8Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R8Entropy_sound : CB3_1_4I2R8Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R8Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R8Value CB3_1_4I2R8Terms CB3_1_4I2R8Terms_sound) (by decide +kernel)
def CB3_1_4I2R8Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R8Mass_sound : CB3_1_4I2R8Mass.Encloses (∑ a, CB3_1_4I2R8Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R8P CB3_1_4I2R8Value CB3_1_4I2R8P_sound) (by decide +kernel)
def CB3_1_4I2R8MassTerm : Ball := .exact 0
lemma CB3_1_4I2R8MassTerm_sound : CB3_1_4I2R8MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R8Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R8Mass_sound)
def CB3_1_4I2R8H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R8H_sound : CB3_1_4I2R8H.Encloses (homogeneousEntropy CB3_1_4I2R8Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R8Value CB3_1_4I2R8MassTerm_sound CB3_1_4I2R8Entropy_sound) (by decide +kernel)
def CB3_1_4I2R9Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 9 a
def CB3_1_4I2R9Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 9 a
lemma CB3_1_4I2R9Raw_sound (a : Fin 6) :
    (CB3_1_4I2R9Raw a).Encloses (CB3_1_4I2R9Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 9 a
def CB3_1_4I2R9Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R9Certificates_valid :
    CB3_1_4I2R9Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R9CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R9P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R9Certificates (CB3_1_4I2R9CertificateIndex a)).input
lemma CB3_1_4I2R9P_check : ∀ a : Fin 6, contains (CB3_1_4I2R9Raw a) (CB3_1_4I2R9P a) = true := by
  decide +kernel
lemma CB3_1_4I2R9P_sound (a : Fin 6) :
    (CB3_1_4I2R9P a).Encloses (CB3_1_4I2R9Value a) :=
  contains_sound (CB3_1_4I2R9Raw_sound a) (CB3_1_4I2R9P_check a)
def CB3_1_4I2R9Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R9Certificates (CB3_1_4I2R9CertificateIndex a)).output
lemma CB3_1_4I2R9Terms_sound (a : Fin 6) :
    (CB3_1_4I2R9Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R9Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R9Certificates_valid
    (CB3_1_4I2R9CertificateIndex a) (CB3_1_4I2R9P_sound a)
def CB3_1_4I2R9Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R9Entropy_sound : CB3_1_4I2R9Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R9Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R9Value CB3_1_4I2R9Terms CB3_1_4I2R9Terms_sound) (by decide +kernel)
def CB3_1_4I2R9Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R9Mass_sound : CB3_1_4I2R9Mass.Encloses (∑ a, CB3_1_4I2R9Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R9P CB3_1_4I2R9Value CB3_1_4I2R9P_sound) (by decide +kernel)
def CB3_1_4I2R9MassTerm : Ball := .exact 0
lemma CB3_1_4I2R9MassTerm_sound : CB3_1_4I2R9MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R9Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R9Mass_sound)
def CB3_1_4I2R9H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R9H_sound : CB3_1_4I2R9H.Encloses (homogeneousEntropy CB3_1_4I2R9Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R9Value CB3_1_4I2R9MassTerm_sound CB3_1_4I2R9Entropy_sound) (by decide +kernel)
def CB3_1_4I2R10Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 10 a
def CB3_1_4I2R10Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 10 a
lemma CB3_1_4I2R10Raw_sound (a : Fin 6) :
    (CB3_1_4I2R10Raw a).Encloses (CB3_1_4I2R10Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 10 a
def CB3_1_4I2R10Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R10Certificates_valid :
    CB3_1_4I2R10Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R10CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R10P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R10Certificates (CB3_1_4I2R10CertificateIndex a)).input
lemma CB3_1_4I2R10P_check : ∀ a : Fin 6, contains (CB3_1_4I2R10Raw a) (CB3_1_4I2R10P a) = true := by
  decide +kernel
lemma CB3_1_4I2R10P_sound (a : Fin 6) :
    (CB3_1_4I2R10P a).Encloses (CB3_1_4I2R10Value a) :=
  contains_sound (CB3_1_4I2R10Raw_sound a) (CB3_1_4I2R10P_check a)
def CB3_1_4I2R10Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R10Certificates (CB3_1_4I2R10CertificateIndex a)).output
lemma CB3_1_4I2R10Terms_sound (a : Fin 6) :
    (CB3_1_4I2R10Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R10Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R10Certificates_valid
    (CB3_1_4I2R10CertificateIndex a) (CB3_1_4I2R10P_sound a)
def CB3_1_4I2R10Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R10Entropy_sound : CB3_1_4I2R10Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R10Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R10Value CB3_1_4I2R10Terms CB3_1_4I2R10Terms_sound) (by decide +kernel)
def CB3_1_4I2R10Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R10Mass_sound : CB3_1_4I2R10Mass.Encloses (∑ a, CB3_1_4I2R10Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R10P CB3_1_4I2R10Value CB3_1_4I2R10P_sound) (by decide +kernel)
def CB3_1_4I2R10MassTerm : Ball := .exact 0
lemma CB3_1_4I2R10MassTerm_sound : CB3_1_4I2R10MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R10Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R10Mass_sound)
def CB3_1_4I2R10H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R10H_sound : CB3_1_4I2R10H.Encloses (homogeneousEntropy CB3_1_4I2R10Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R10Value CB3_1_4I2R10MassTerm_sound CB3_1_4I2R10Entropy_sound) (by decide +kernel)
def CB3_1_4I2R11Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 11 a
def CB3_1_4I2R11Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 11 a
lemma CB3_1_4I2R11Raw_sound (a : Fin 6) :
    (CB3_1_4I2R11Raw a).Encloses (CB3_1_4I2R11Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 11 a
def CB3_1_4I2R11Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R11Certificates_valid :
    CB3_1_4I2R11Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R11CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R11P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R11Certificates (CB3_1_4I2R11CertificateIndex a)).input
lemma CB3_1_4I2R11P_check : ∀ a : Fin 6, contains (CB3_1_4I2R11Raw a) (CB3_1_4I2R11P a) = true := by
  decide +kernel
lemma CB3_1_4I2R11P_sound (a : Fin 6) :
    (CB3_1_4I2R11P a).Encloses (CB3_1_4I2R11Value a) :=
  contains_sound (CB3_1_4I2R11Raw_sound a) (CB3_1_4I2R11P_check a)
def CB3_1_4I2R11Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R11Certificates (CB3_1_4I2R11CertificateIndex a)).output
lemma CB3_1_4I2R11Terms_sound (a : Fin 6) :
    (CB3_1_4I2R11Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R11Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R11Certificates_valid
    (CB3_1_4I2R11CertificateIndex a) (CB3_1_4I2R11P_sound a)
def CB3_1_4I2R11Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R11Entropy_sound : CB3_1_4I2R11Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R11Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R11Value CB3_1_4I2R11Terms CB3_1_4I2R11Terms_sound) (by decide +kernel)
def CB3_1_4I2R11Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R11Mass_sound : CB3_1_4I2R11Mass.Encloses (∑ a, CB3_1_4I2R11Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R11P CB3_1_4I2R11Value CB3_1_4I2R11P_sound) (by decide +kernel)
def CB3_1_4I2R11MassTerm : Ball := .exact 0
lemma CB3_1_4I2R11MassTerm_sound : CB3_1_4I2R11MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R11Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R11Mass_sound)
def CB3_1_4I2R11H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R11H_sound : CB3_1_4I2R11H.Encloses (homogeneousEntropy CB3_1_4I2R11Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R11Value CB3_1_4I2R11MassTerm_sound CB3_1_4I2R11Entropy_sound) (by decide +kernel)
def CB3_1_4I2R12Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 12 a
def CB3_1_4I2R12Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 12 a
lemma CB3_1_4I2R12Raw_sound (a : Fin 6) :
    (CB3_1_4I2R12Raw a).Encloses (CB3_1_4I2R12Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 12 a
def CB3_1_4I2R12Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R12Certificates_valid :
    CB3_1_4I2R12Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R12CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R12P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R12Certificates (CB3_1_4I2R12CertificateIndex a)).input
lemma CB3_1_4I2R12P_check : ∀ a : Fin 6, contains (CB3_1_4I2R12Raw a) (CB3_1_4I2R12P a) = true := by
  decide +kernel
lemma CB3_1_4I2R12P_sound (a : Fin 6) :
    (CB3_1_4I2R12P a).Encloses (CB3_1_4I2R12Value a) :=
  contains_sound (CB3_1_4I2R12Raw_sound a) (CB3_1_4I2R12P_check a)
def CB3_1_4I2R12Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R12Certificates (CB3_1_4I2R12CertificateIndex a)).output
lemma CB3_1_4I2R12Terms_sound (a : Fin 6) :
    (CB3_1_4I2R12Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R12Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R12Certificates_valid
    (CB3_1_4I2R12CertificateIndex a) (CB3_1_4I2R12P_sound a)
def CB3_1_4I2R12Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R12Entropy_sound : CB3_1_4I2R12Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R12Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R12Value CB3_1_4I2R12Terms CB3_1_4I2R12Terms_sound) (by decide +kernel)
def CB3_1_4I2R12Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R12Mass_sound : CB3_1_4I2R12Mass.Encloses (∑ a, CB3_1_4I2R12Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R12P CB3_1_4I2R12Value CB3_1_4I2R12P_sound) (by decide +kernel)
def CB3_1_4I2R12MassTerm : Ball := .exact 0
lemma CB3_1_4I2R12MassTerm_sound : CB3_1_4I2R12MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R12Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R12Mass_sound)
def CB3_1_4I2R12H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R12H_sound : CB3_1_4I2R12H.Encloses (homogeneousEntropy CB3_1_4I2R12Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R12Value CB3_1_4I2R12MassTerm_sound CB3_1_4I2R12Entropy_sound) (by decide +kernel)
def CB3_1_4I2R13Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 13 a
def CB3_1_4I2R13Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 13 a
lemma CB3_1_4I2R13Raw_sound (a : Fin 6) :
    (CB3_1_4I2R13Raw a).Encloses (CB3_1_4I2R13Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 13 a
def CB3_1_4I2R13Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R13Certificates_valid :
    CB3_1_4I2R13Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R13CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R13P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R13Certificates (CB3_1_4I2R13CertificateIndex a)).input
lemma CB3_1_4I2R13P_check : ∀ a : Fin 6, contains (CB3_1_4I2R13Raw a) (CB3_1_4I2R13P a) = true := by
  decide +kernel
lemma CB3_1_4I2R13P_sound (a : Fin 6) :
    (CB3_1_4I2R13P a).Encloses (CB3_1_4I2R13Value a) :=
  contains_sound (CB3_1_4I2R13Raw_sound a) (CB3_1_4I2R13P_check a)
def CB3_1_4I2R13Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R13Certificates (CB3_1_4I2R13CertificateIndex a)).output
lemma CB3_1_4I2R13Terms_sound (a : Fin 6) :
    (CB3_1_4I2R13Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R13Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R13Certificates_valid
    (CB3_1_4I2R13CertificateIndex a) (CB3_1_4I2R13P_sound a)
def CB3_1_4I2R13Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R13Entropy_sound : CB3_1_4I2R13Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R13Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R13Value CB3_1_4I2R13Terms CB3_1_4I2R13Terms_sound) (by decide +kernel)
def CB3_1_4I2R13Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R13Mass_sound : CB3_1_4I2R13Mass.Encloses (∑ a, CB3_1_4I2R13Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R13P CB3_1_4I2R13Value CB3_1_4I2R13P_sound) (by decide +kernel)
def CB3_1_4I2R13MassTerm : Ball := .exact 0
lemma CB3_1_4I2R13MassTerm_sound : CB3_1_4I2R13MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R13Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R13Mass_sound)
def CB3_1_4I2R13H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R13H_sound : CB3_1_4I2R13H.Encloses (homogeneousEntropy CB3_1_4I2R13Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R13Value CB3_1_4I2R13MassTerm_sound CB3_1_4I2R13Entropy_sound) (by decide +kernel)
def CB3_1_4I2R14Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 14 a
def CB3_1_4I2R14Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 14 a
lemma CB3_1_4I2R14Raw_sound (a : Fin 6) :
    (CB3_1_4I2R14Raw a).Encloses (CB3_1_4I2R14Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 14 a
def CB3_1_4I2R14Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R14Certificates_valid :
    CB3_1_4I2R14Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R14CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R14P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R14Certificates (CB3_1_4I2R14CertificateIndex a)).input
lemma CB3_1_4I2R14P_check : ∀ a : Fin 6, contains (CB3_1_4I2R14Raw a) (CB3_1_4I2R14P a) = true := by
  decide +kernel
lemma CB3_1_4I2R14P_sound (a : Fin 6) :
    (CB3_1_4I2R14P a).Encloses (CB3_1_4I2R14Value a) :=
  contains_sound (CB3_1_4I2R14Raw_sound a) (CB3_1_4I2R14P_check a)
def CB3_1_4I2R14Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R14Certificates (CB3_1_4I2R14CertificateIndex a)).output
lemma CB3_1_4I2R14Terms_sound (a : Fin 6) :
    (CB3_1_4I2R14Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R14Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R14Certificates_valid
    (CB3_1_4I2R14CertificateIndex a) (CB3_1_4I2R14P_sound a)
def CB3_1_4I2R14Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R14Entropy_sound : CB3_1_4I2R14Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R14Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R14Value CB3_1_4I2R14Terms CB3_1_4I2R14Terms_sound) (by decide +kernel)
def CB3_1_4I2R14Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R14Mass_sound : CB3_1_4I2R14Mass.Encloses (∑ a, CB3_1_4I2R14Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R14P CB3_1_4I2R14Value CB3_1_4I2R14P_sound) (by decide +kernel)
def CB3_1_4I2R14MassTerm : Ball := .exact 0
lemma CB3_1_4I2R14MassTerm_sound : CB3_1_4I2R14MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R14Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R14Mass_sound)
def CB3_1_4I2R14H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R14H_sound : CB3_1_4I2R14H.Encloses (homogeneousEntropy CB3_1_4I2R14Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R14Value CB3_1_4I2R14MassTerm_sound CB3_1_4I2R14Entropy_sound) (by decide +kernel)
def CB3_1_4I2R15Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 15 a
def CB3_1_4I2R15Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 15 a
lemma CB3_1_4I2R15Raw_sound (a : Fin 6) :
    (CB3_1_4I2R15Raw a).Encloses (CB3_1_4I2R15Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 15 a
def CB3_1_4I2R15Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R15Certificates_valid :
    CB3_1_4I2R15Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R15CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R15P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R15Certificates (CB3_1_4I2R15CertificateIndex a)).input
lemma CB3_1_4I2R15P_check : ∀ a : Fin 6, contains (CB3_1_4I2R15Raw a) (CB3_1_4I2R15P a) = true := by
  decide +kernel
lemma CB3_1_4I2R15P_sound (a : Fin 6) :
    (CB3_1_4I2R15P a).Encloses (CB3_1_4I2R15Value a) :=
  contains_sound (CB3_1_4I2R15Raw_sound a) (CB3_1_4I2R15P_check a)
def CB3_1_4I2R15Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R15Certificates (CB3_1_4I2R15CertificateIndex a)).output
lemma CB3_1_4I2R15Terms_sound (a : Fin 6) :
    (CB3_1_4I2R15Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R15Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R15Certificates_valid
    (CB3_1_4I2R15CertificateIndex a) (CB3_1_4I2R15P_sound a)
def CB3_1_4I2R15Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R15Entropy_sound : CB3_1_4I2R15Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R15Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R15Value CB3_1_4I2R15Terms CB3_1_4I2R15Terms_sound) (by decide +kernel)
def CB3_1_4I2R15Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R15Mass_sound : CB3_1_4I2R15Mass.Encloses (∑ a, CB3_1_4I2R15Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R15P CB3_1_4I2R15Value CB3_1_4I2R15P_sound) (by decide +kernel)
def CB3_1_4I2R15MassTerm : Ball := .exact 0
lemma CB3_1_4I2R15MassTerm_sound : CB3_1_4I2R15MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R15Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R15Mass_sound)
def CB3_1_4I2R15H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R15H_sound : CB3_1_4I2R15H.Encloses (homogeneousEntropy CB3_1_4I2R15Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R15Value CB3_1_4I2R15MassTerm_sound CB3_1_4I2R15Entropy_sound) (by decide +kernel)
def CB3_1_4I2R16Value (a : Fin 6) : ℝ := residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) 16 a
def CB3_1_4I2R16Raw (a : Fin 6) : Ball := residualBall (below (shape 3 1 4)) B3_1_4Law (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) 16 a
lemma CB3_1_4I2R16Raw_sound (a : Fin 6) :
    (CB3_1_4I2R16Raw a).Encloses (CB3_1_4I2R16Value a) := by
  exact residualBall_sound_on (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u => B3_1_4Little u ((stageBPriority (shape 3 1 4)) 2)) (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) (fun u _ a => B3_1_4Little_sound u ((stageBPriority (shape 3 1 4)) 2) a) 16 a
def CB3_1_4I2R16Certificates : List CompactCertificate.EntropyDatum :=
  [.zero]
lemma CB3_1_4I2R16Certificates_valid :
    CB3_1_4I2R16Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
def CB3_1_4I2R16CertificateIndex (a : Fin 6) : ℕ :=
  match a.val with
  | _ => 0
def CB3_1_4I2R16P (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R16Certificates (CB3_1_4I2R16CertificateIndex a)).input
lemma CB3_1_4I2R16P_check : ∀ a : Fin 6, contains (CB3_1_4I2R16Raw a) (CB3_1_4I2R16P a) = true := by
  decide +kernel
lemma CB3_1_4I2R16P_sound (a : Fin 6) :
    (CB3_1_4I2R16P a).Encloses (CB3_1_4I2R16Value a) :=
  contains_sound (CB3_1_4I2R16Raw_sound a) (CB3_1_4I2R16P_check a)
def CB3_1_4I2R16Terms (a : Fin 6) : Ball :=
  (CompactCertificate.entropyLookup CB3_1_4I2R16Certificates (CB3_1_4I2R16CertificateIndex a)).output
lemma CB3_1_4I2R16Terms_sound (a : Fin 6) :
    (CB3_1_4I2R16Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2R16Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_1_4I2R16Certificates_valid
    (CB3_1_4I2R16CertificateIndex a) (CB3_1_4I2R16P_sound a)
def CB3_1_4I2R16Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R16Entropy_sound : CB3_1_4I2R16Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2R16Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2R16Value CB3_1_4I2R16Terms CB3_1_4I2R16Terms_sound) (by decide +kernel)
def CB3_1_4I2R16Mass : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R16Mass_sound : CB3_1_4I2R16Mass.Encloses (∑ a, CB3_1_4I2R16Value a) := by
  exact contains_sound (finSumBall_sound 6 CB3_1_4I2R16P CB3_1_4I2R16Value CB3_1_4I2R16P_sound) (by decide +kernel)
def CB3_1_4I2R16MassTerm : Ball := .exact 0
lemma CB3_1_4I2R16MassTerm_sound : CB3_1_4I2R16MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2R16Value a))) :=
  entropyTerm_zero_ball (CB3_1_4I2R16Mass_sound)
def CB3_1_4I2R16H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2R16H_sound : CB3_1_4I2R16H.Encloses (homogeneousEntropy CB3_1_4I2R16Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2R16Value CB3_1_4I2R16MassTerm_sound CB3_1_4I2R16Entropy_sound) (by decide +kernel)
def CB3_1_4I2ResidualEntropies (a : Fin 17) : Ball :=
  match a.val with
  | 0 => CB3_1_4I2R0H
  | 1 => CB3_1_4I2R1H
  | 2 => CB3_1_4I2R2H
  | 3 => CB3_1_4I2R3H
  | 4 => CB3_1_4I2R4H
  | 5 => CB3_1_4I2R5H
  | 6 => CB3_1_4I2R6H
  | 7 => CB3_1_4I2R7H
  | 8 => CB3_1_4I2R8H
  | 9 => CB3_1_4I2R9H
  | 10 => CB3_1_4I2R10H
  | 11 => CB3_1_4I2R11H
  | 12 => CB3_1_4I2R12H
  | 13 => CB3_1_4I2R13H
  | 14 => CB3_1_4I2R14H
  | 15 => CB3_1_4I2R15H
  | 16 => CB3_1_4I2R16H
  | _ => (.exact 0)
lemma CB3_1_4I2ResidualEntropies_sound (k : Fin 17) :
    (CB3_1_4I2ResidualEntropies k).Encloses (homogeneousEntropy
      (residualLaw (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) k)) := by
  fin_cases k
  · exact CB3_1_4I2R0H_sound
  · exact CB3_1_4I2R1H_sound
  · exact CB3_1_4I2R2H_sound
  · exact CB3_1_4I2R3H_sound
  · exact CB3_1_4I2R4H_sound
  · exact CB3_1_4I2R5H_sound
  · exact CB3_1_4I2R6H_sound
  · exact CB3_1_4I2R7H_sound
  · exact CB3_1_4I2R8H_sound
  · exact CB3_1_4I2R9H_sound
  · exact CB3_1_4I2R10H_sound
  · exact CB3_1_4I2R11H_sound
  · exact CB3_1_4I2R12H_sound
  · exact CB3_1_4I2R13H_sound
  · exact CB3_1_4I2R14H_sound
  · exact CB3_1_4I2R15H_sound
  · exact CB3_1_4I2R16H_sound
def CB3_1_4I2S0_0_4Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S0_0_4E_5Log : Ball := .exact 0
lemma CB3_1_4I2S0_0_4E_5Log_sound : CB3_1_4I2S0_0_4E_5Log.Encloses (Real.log (CB3_1_4I2S0_0_4Value (5 : Fin 6))) := by
  exact log_exact_one_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6))
def CB3_1_4I2S0_0_4E_5 : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_0_4E_5_sound : CB3_1_4I2S0_0_4E_5.Encloses (Foundation.entropyTerm (CB3_1_4I2S0_0_4Value (5 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6)) CB3_1_4I2S0_0_4E_5Log_sound) (by decide +kernel)
def CB3_1_4I2S0_0_4Terms (a : Fin 6) : Ball :=
  match a.val with
  | 5 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_1_4I2S0_0_4Terms_sound (a : Fin 6) :
    (CB3_1_4I2S0_0_4Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2S0_0_4Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6)))
  · exact CB3_1_4I2S0_0_4E_5_sound
def CB3_1_4I2S0_0_4Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_0_4Entropy_sound : CB3_1_4I2S0_0_4Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S0_0_4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S0_0_4Value CB3_1_4I2S0_0_4Terms CB3_1_4I2S0_0_4Terms_sound) (by decide +kernel)
def CB3_1_4I2S0_0_4Mass : Ball := ⟨1, 0⟩
lemma CB3_1_4I2S0_0_4Mass_sound : CB3_1_4I2S0_0_4Mass.Encloses (∑ a, CB3_1_4I2S0_0_4Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_1_4Little (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2)) CB3_1_4I2S0_0_4Value (B3_1_4Little_sound (shape 0 0 4) ((stageBPriority (shape 3 1 4)) 2))) (by decide +kernel)
def CB3_1_4I2S0_0_4MassTermLog : Ball := .exact 0
lemma CB3_1_4I2S0_0_4MassTermLog_sound : CB3_1_4I2S0_0_4MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2S0_0_4Value a))) := by
  exact log_exact_one_ball (CB3_1_4I2S0_0_4Mass_sound)
def CB3_1_4I2S0_0_4MassTerm : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_0_4MassTerm_sound : CB3_1_4I2S0_0_4MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2S0_0_4Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2S0_0_4Mass_sound) CB3_1_4I2S0_0_4MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2S0_0_4H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_0_4H_sound : CB3_1_4I2S0_0_4H.Encloses (homogeneousEntropy CB3_1_4I2S0_0_4Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2S0_0_4Value CB3_1_4I2S0_0_4MassTerm_sound CB3_1_4I2S0_0_4Entropy_sound) (by decide +kernel)
def CB3_1_4I2S0_1_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S0_1_3E_4Log : Ball := .exact 0
lemma CB3_1_4I2S0_1_3E_4Log_sound : CB3_1_4I2S0_1_3E_4Log.Encloses (Real.log (CB3_1_4I2S0_1_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6))
def CB3_1_4I2S0_1_3E_4 : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_1_3E_4_sound : CB3_1_4I2S0_1_3E_4.Encloses (Foundation.entropyTerm (CB3_1_4I2S0_1_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6)) CB3_1_4I2S0_1_3E_4Log_sound) (by decide +kernel)
def CB3_1_4I2S0_1_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_1_4I2S0_1_3Terms_sound (a : Fin 6) :
    (CB3_1_4I2S0_1_3Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2S0_1_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)))
  · exact CB3_1_4I2S0_1_3E_4_sound
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6)))
def CB3_1_4I2S0_1_3Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_1_3Entropy_sound : CB3_1_4I2S0_1_3Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S0_1_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S0_1_3Value CB3_1_4I2S0_1_3Terms CB3_1_4I2S0_1_3Terms_sound) (by decide +kernel)
def CB3_1_4I2S0_1_3Mass : Ball := ⟨1, 0⟩
lemma CB3_1_4I2S0_1_3Mass_sound : CB3_1_4I2S0_1_3Mass.Encloses (∑ a, CB3_1_4I2S0_1_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_1_4Little (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2)) CB3_1_4I2S0_1_3Value (B3_1_4Little_sound (shape 0 1 3) ((stageBPriority (shape 3 1 4)) 2))) (by decide +kernel)
def CB3_1_4I2S0_1_3MassTermLog : Ball := .exact 0
lemma CB3_1_4I2S0_1_3MassTermLog_sound : CB3_1_4I2S0_1_3MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2S0_1_3Value a))) := by
  exact log_exact_one_ball (CB3_1_4I2S0_1_3Mass_sound)
def CB3_1_4I2S0_1_3MassTerm : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_1_3MassTerm_sound : CB3_1_4I2S0_1_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2S0_1_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2S0_1_3Mass_sound) CB3_1_4I2S0_1_3MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2S0_1_3H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S0_1_3H_sound : CB3_1_4I2S0_1_3H.Encloses (homogeneousEntropy CB3_1_4I2S0_1_3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2S0_1_3Value CB3_1_4I2S0_1_3MassTerm_sound CB3_1_4I2S0_1_3Entropy_sound) (by decide +kernel)
def CB3_1_4I2S1_0_3Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S1_0_3E_4Log : Ball := .exact 0
lemma CB3_1_4I2S1_0_3E_4Log_sound : CB3_1_4I2S1_0_3E_4Log.Encloses (Real.log (CB3_1_4I2S1_0_3Value (4 : Fin 6))) := by
  exact log_exact_one_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6))
def CB3_1_4I2S1_0_3E_4 : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S1_0_3E_4_sound : CB3_1_4I2S1_0_3E_4.Encloses (Foundation.entropyTerm (CB3_1_4I2S1_0_3Value (4 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6)) CB3_1_4I2S1_0_3E_4Log_sound) (by decide +kernel)
def CB3_1_4I2S1_0_3Terms (a : Fin 6) : Ball :=
  match a.val with
  | 4 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_1_4I2S1_0_3Terms_sound (a : Fin 6) :
    (CB3_1_4I2S1_0_3Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2S1_0_3Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)))
  · exact CB3_1_4I2S1_0_3E_4_sound
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6)))
def CB3_1_4I2S1_0_3Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S1_0_3Entropy_sound : CB3_1_4I2S1_0_3Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S1_0_3Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S1_0_3Value CB3_1_4I2S1_0_3Terms CB3_1_4I2S1_0_3Terms_sound) (by decide +kernel)
def CB3_1_4I2S1_0_3Mass : Ball := ⟨1, 0⟩
lemma CB3_1_4I2S1_0_3Mass_sound : CB3_1_4I2S1_0_3Mass.Encloses (∑ a, CB3_1_4I2S1_0_3Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_1_4Little (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2)) CB3_1_4I2S1_0_3Value (B3_1_4Little_sound (shape 1 0 3) ((stageBPriority (shape 3 1 4)) 2))) (by decide +kernel)
def CB3_1_4I2S1_0_3MassTermLog : Ball := .exact 0
lemma CB3_1_4I2S1_0_3MassTermLog_sound : CB3_1_4I2S1_0_3MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2S1_0_3Value a))) := by
  exact log_exact_one_ball (CB3_1_4I2S1_0_3Mass_sound)
def CB3_1_4I2S1_0_3MassTerm : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S1_0_3MassTerm_sound : CB3_1_4I2S1_0_3MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2S1_0_3Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2S1_0_3Mass_sound) CB3_1_4I2S1_0_3MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2S1_0_3H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S1_0_3H_sound : CB3_1_4I2S1_0_3H.Encloses (homogeneousEntropy CB3_1_4I2S1_0_3Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2S1_0_3Value CB3_1_4I2S1_0_3MassTerm_sound CB3_1_4I2S1_0_3Entropy_sound) (by decide +kernel)
def CB3_1_4I2S2_0_2Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S2_0_2E_2LogWitness : LogWitness := ⟨-1, 56577, 31250⟩
def CB3_1_4I2S2_0_2E_2Log : Ball := ⟨(-9956401454401802915036069658881 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2E_2Log_sound : CB3_1_4I2S2_0_2E_2Log.Encloses (Real.log (CB3_1_4I2S2_0_2Value (2 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)) (w := CB3_1_4I2S2_0_2E_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2S2_0_2E_2 : Ball := ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2E_2_sound : CB3_1_4I2S2_0_2E_2.Encloses (Foundation.entropyTerm (CB3_1_4I2S2_0_2Value (2 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)) CB3_1_4I2S2_0_2E_2Log_sound) (by decide +kernel)
def CB3_1_4I2S2_0_2E_3LogWitness : LogWitness := ⟨-4, 23692, 15625⟩
def CB3_1_4I2S2_0_2E_3Log : Ball := ⟨(-235632347944752769756850307028051 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2E_3Log_sound : CB3_1_4I2S2_0_2E_3Log.Encloses (Real.log (CB3_1_4I2S2_0_2Value (3 : Fin 6))) := by
  exact checkLog_sound logTwoBall_sound ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)) (w := CB3_1_4I2S2_0_2E_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def CB3_1_4I2S2_0_2E_3 : Ball := ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2E_3_sound : CB3_1_4I2S2_0_2E_3.Encloses (Foundation.entropyTerm (CB3_1_4I2S2_0_2Value (3 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)) CB3_1_4I2S2_0_2E_3Log_sound) (by decide +kernel)
def CB3_1_4I2S2_0_2Terms (a : Fin 6) : Ball :=
  match a.val with
  | 2 => ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
  | 3 => ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
  | _ => (.exact 0)
lemma CB3_1_4I2S2_0_2Terms_sound (a : Fin 6) :
    (CB3_1_4I2S2_0_2Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2S2_0_2Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (0 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6)))
  · exact CB3_1_4I2S2_0_2E_2_sound
  · exact CB3_1_4I2S2_0_2E_3_sound
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6)))
def CB3_1_4I2S2_0_2Entropy : Ball := ⟨(15671629775699691670350560652941 / 50000000000000000000000000000000), (6046502343 / 12500000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2Entropy_sound : CB3_1_4I2S2_0_2Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S2_0_2Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S2_0_2Value CB3_1_4I2S2_0_2Terms CB3_1_4I2S2_0_2Terms_sound) (by decide +kernel)
def CB3_1_4I2S2_0_2Mass : Ball := ⟨1, 0⟩
lemma CB3_1_4I2S2_0_2Mass_sound : CB3_1_4I2S2_0_2Mass.Encloses (∑ a, CB3_1_4I2S2_0_2Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_1_4Little (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2)) CB3_1_4I2S2_0_2Value (B3_1_4Little_sound (shape 2 0 2) ((stageBPriority (shape 3 1 4)) 2))) (by decide +kernel)
def CB3_1_4I2S2_0_2MassTermLog : Ball := .exact 0
lemma CB3_1_4I2S2_0_2MassTermLog_sound : CB3_1_4I2S2_0_2MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2S2_0_2Value a))) := by
  exact log_exact_one_ball (CB3_1_4I2S2_0_2Mass_sound)
def CB3_1_4I2S2_0_2MassTerm : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S2_0_2MassTerm_sound : CB3_1_4I2S2_0_2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2S2_0_2Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2S2_0_2Mass_sound) CB3_1_4I2S2_0_2MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2S2_0_2H : Ball := ⟨(15671629775699691670350560652941 / 50000000000000000000000000000000), (6046502343 / 12500000000000000000000000000000)⟩
lemma CB3_1_4I2S2_0_2H_sound : CB3_1_4I2S2_0_2H.Encloses (homogeneousEntropy CB3_1_4I2S2_0_2Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2S2_0_2Value CB3_1_4I2S2_0_2MassTerm_sound CB3_1_4I2S2_0_2Entropy_sound) (by decide +kernel)
def CB3_1_4I2S3_0_1Value (a : Fin 6) : ℝ := (littleLaw (shape 3 1 4) (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2) a : ℝ)
def CB3_1_4I2S3_0_1E_1Log : Ball := .exact 0
lemma CB3_1_4I2S3_0_1E_1Log_sound : CB3_1_4I2S3_0_1E_1Log.Encloses (Real.log (CB3_1_4I2S3_0_1Value (1 : Fin 6))) := by
  exact log_exact_one_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6))
def CB3_1_4I2S3_0_1E_1 : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S3_0_1E_1_sound : CB3_1_4I2S3_0_1E_1.Encloses (Foundation.entropyTerm (CB3_1_4I2S3_0_1Value (1 : Fin 6))) := by
  exact contains_sound (entropyTerm_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (1 : Fin 6)) CB3_1_4I2S3_0_1E_1Log_sound) (by decide +kernel)
def CB3_1_4I2S3_0_1Terms (a : Fin 6) : Ball :=
  match a.val with
  | 1 => ⟨0, 0⟩
  | _ => (.exact 0)
lemma CB3_1_4I2S3_0_1Terms_sound (a : Fin 6) :
    (CB3_1_4I2S3_0_1Terms a).Encloses (Foundation.entropyTerm (CB3_1_4I2S3_0_1Value a)) := by
  fin_cases a
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (0 : Fin 6)))
  · exact CB3_1_4I2S3_0_1E_1_sound
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (2 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (3 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (4 : Fin 6)))
  · exact (entropyTerm_zero_ball ((B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) (5 : Fin 6)))
def CB3_1_4I2S3_0_1Entropy : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S3_0_1Entropy_sound : CB3_1_4I2S3_0_1Entropy.Encloses (Foundation.finiteEntropy CB3_1_4I2S3_0_1Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB3_1_4I2S3_0_1Value CB3_1_4I2S3_0_1Terms CB3_1_4I2S3_0_1Terms_sound) (by decide +kernel)
def CB3_1_4I2S3_0_1Mass : Ball := ⟨1, 0⟩
lemma CB3_1_4I2S3_0_1Mass_sound : CB3_1_4I2S3_0_1Mass.Encloses (∑ a, CB3_1_4I2S3_0_1Value a) := by
  exact contains_sound (finSumBall_sound 6 (B3_1_4Little (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2)) CB3_1_4I2S3_0_1Value (B3_1_4Little_sound (shape 3 0 1) ((stageBPriority (shape 3 1 4)) 2))) (by decide +kernel)
def CB3_1_4I2S3_0_1MassTermLog : Ball := .exact 0
lemma CB3_1_4I2S3_0_1MassTermLog_sound : CB3_1_4I2S3_0_1MassTermLog.Encloses (Real.log ((∑ a, CB3_1_4I2S3_0_1Value a))) := by
  exact log_exact_one_ball (CB3_1_4I2S3_0_1Mass_sound)
def CB3_1_4I2S3_0_1MassTerm : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S3_0_1MassTerm_sound : CB3_1_4I2S3_0_1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, CB3_1_4I2S3_0_1Value a))) := by
  exact contains_sound (entropyTerm_ball (CB3_1_4I2S3_0_1Mass_sound) CB3_1_4I2S3_0_1MassTermLog_sound) (by decide +kernel)
def CB3_1_4I2S3_0_1H : Ball := ⟨0, 0⟩
lemma CB3_1_4I2S3_0_1H_sound : CB3_1_4I2S3_0_1H.Encloses (homogeneousEntropy CB3_1_4I2S3_0_1Value) := by
  exact contains_sound (homogeneous_enclosed CB3_1_4I2S3_0_1Value CB3_1_4I2S3_0_1MassTerm_sound CB3_1_4I2S3_0_1Entropy_sound) (by decide +kernel)
def CB3_1_4I2Singles (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => CB3_1_4I2S0_0_4H
  | 0, 1, 3 => CB3_1_4I2S0_1_3H
  | 1, 0, 3 => CB3_1_4I2S1_0_3H
  | 2, 0, 2 => CB3_1_4I2S2_0_2H
  | 3, 0, 1 => CB3_1_4I2S3_0_1H
  | _, _, _ => (.exact 0)
lemma CB3_1_4I2Singles_sound (u : Shape) (hu : u ∈ below (shape 3 1 4))
    (hd : designated (stageBPriority (shape 3 1 4)) 2 u) :
    (CB3_1_4I2Singles u).Encloses (homogeneousEntropy ((fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) u)) := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact CB3_1_4I2S0_0_4H_sound
  · exact CB3_1_4I2S0_1_3H_sound
  · exact CB3_1_4I2S1_0_3H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 1 4)) 2 (shape 1 1 2) by decide +kernel) hd |>.elim
  · exact CB3_1_4I2S2_0_2H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 1 4)) 2 (shape 2 1 1) by decide +kernel) hd |>.elim
  · exact CB3_1_4I2S3_0_1H_sound
  · exact (show ¬ designated (stageBPriority (shape 3 1 4)) 2 (shape 3 1 0) by decide +kernel) hd |>.elim
def CB3_1_4I2Singleton : Ball := ⟨(3317128459142276397553763101999 / 25000000000000000000000000000000), (20477283133 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2Singleton_sound : CB3_1_4I2Singleton.Encloses
    (singletonEntropy (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ))) := by
  exact contains_sound (singletonBall_sound (below (shape 3 1 4)) B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2
    CB3_1_4I2Singles (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ)) (fun u _ => B3_1_4Law_sound u) CB3_1_4I2Singles_sound) (by decide +kernel)
def CB3_1_4I2Group : Ball := ⟨(3483315209901677304871843283757 / 25000000000000000000000000000000), (44002426931 / 50000000000000000000000000000000)⟩
lemma CB3_1_4I2Group_sound : CB3_1_4I2Group.Encloses
    (groupedEntropy (below (shape 3 1 4)) (fun u => (stageBLaw (shape 3 1 4) u : ℝ)) (stageBPriority (shape 3 1 4)) 2 (fun u a => (littleLaw (shape 3 1 4) u ((stageBPriority (shape 3 1 4)) 2) a : ℝ))) := by
  exact contains_sound (Ball.add_sound CB3_1_4I2Singleton_sound
    (finSumBall_sound 17 CB3_1_4I2ResidualEntropies _ CB3_1_4I2ResidualEntropies_sound)) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def CB3_1_4I2H : Ball := ⟨(2346221401130937570320828248623 / 4000000000000000000000000000000), (256333161557 / 100000000000000000000000000000000)⟩
lemma CB3_1_4I2_sound : CB3_1_4I2H.Encloses (stageBCapacity (shape 3 1 4) 2) := by
  have hb := contains_sound (Ball.add_sound CB3_1_4I2PairH_sound
    (Ball.neg_sound (Ball.mul_sound
      (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) CB3_1_4I2Group_sound)))
    (show contains (.add CB3_1_4I2PairH (.neg (.mul (.exact 2) CB3_1_4I2Group))) CB3_1_4I2H = true by decide +kernel)
  simp only [stageBCapacity, nativeCapacity,
    show (2 : Fin 3) ≠ 0 by decide, ite_false, sub_eq_add_neg]
  exact hb

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
