import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Zero0_1_7

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z0_1_7Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 1 7) a.1 a.2 : ℝ)
def Z0_1_7E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7E_4_5Log_sound : Z0_1_7E_4_5Log.Encloses (Real.log (Z0_1_7Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_1_7Probs_sound ((4,5) : PairSlot)) (w := Z0_1_7E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7E_4_5_sound : Z0_1_7E_4_5.Encloses (Foundation.entropyTerm (Z0_1_7Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7Probs_sound ((4,5) : PairSlot)) Z0_1_7E_4_5Log_sound) (by decide +kernel)
def Z0_1_7E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7E_5_4Log_sound : Z0_1_7E_5_4Log.Encloses (Real.log (Z0_1_7Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_1_7Probs_sound ((5,4) : PairSlot)) (w := Z0_1_7E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7E_5_4_sound : Z0_1_7E_5_4.Encloses (Foundation.entropyTerm (Z0_1_7Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7Probs_sound ((5,4) : PairSlot)) Z0_1_7E_5_4Log_sound) (by decide +kernel)
def Z0_1_7Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_1_7Terms_sound (a : PairSlot) :
    (Z0_1_7Terms a).Encloses (Foundation.entropyTerm (Z0_1_7Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((4,4) : PairSlot))) Z0_1_7E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,3) : PairSlot))) Z0_1_7E_5_4_sound (entropyTerm_zero_ball (Z0_1_7Probs_sound ((5,5) : PairSlot)))
def Z0_1_7Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z0_1_7Entropy_sound : Z0_1_7Entropy.Encloses (Foundation.finiteEntropy Z0_1_7Value) := by
  exact contains_sound (entropyPair_enclosed Z0_1_7Value Z0_1_7Terms Z0_1_7Terms_sound) (by decide +kernel)
def Z0_1_7Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma Z0_1_7Labels_sound : Z0_1_7Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 1 7) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_1_7Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_1_7Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z0_1_7Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma Z0_1_7Four_sound : Z0_1_7Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 1 7)) := by
  exact contains_sound (Ball.add_sound Z0_1_7Entropy_sound Z0_1_7Labels_sound) (by decide +kernel)
def Z0_1_7H0Value (a : PairSlot) : ℝ := (halfLaw (shape 0 1 7) 0 a : ℝ)
def Z0_1_7H0E_0_0Log : Ball := .exact 0
lemma Z0_1_7H0E_0_0Log_sound : Z0_1_7H0E_0_0Log.Encloses (Real.log (Z0_1_7H0Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z0_1_7Half_sound 0) ((0,0) : PairSlot))
def Z0_1_7H0E_0_0 : Ball := ⟨0, 0⟩
lemma Z0_1_7H0E_0_0_sound : Z0_1_7H0E_0_0.Encloses (Foundation.entropyTerm (Z0_1_7H0Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_1_7Half_sound 0) ((0,0) : PairSlot)) Z0_1_7H0E_0_0Log_sound) (by decide +kernel)
def Z0_1_7H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_1_7H0Terms_sound (a : PairSlot) :
    (Z0_1_7H0Terms a).Encloses (Foundation.entropyTerm (Z0_1_7H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z0_1_7H0E_0_0_sound (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 0) ((5,5) : PairSlot)))
def Z0_1_7H0Entropy : Ball := ⟨0, 0⟩
lemma Z0_1_7H0Entropy_sound : Z0_1_7H0Entropy.Encloses (Foundation.finiteEntropy Z0_1_7H0Value) := by
  exact contains_sound (entropyPair_enclosed Z0_1_7H0Value Z0_1_7H0Terms Z0_1_7H0Terms_sound) (by decide +kernel)
def Z0_1_7H0Mass : Ball := ⟨1, 0⟩
lemma Z0_1_7H0Mass_sound : Z0_1_7H0Mass.Encloses (∑ a, Z0_1_7H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_1_7Half 0) Z0_1_7H0Value (Z0_1_7Half_sound 0)) (by decide +kernel)
def Z0_1_7H0MassTermLog : Ball := .exact 0
lemma Z0_1_7H0MassTermLog_sound : Z0_1_7H0MassTermLog.Encloses (Real.log ((∑ a, Z0_1_7H0Value a))) := by
  exact log_exact_one_ball (Z0_1_7H0Mass_sound)
def Z0_1_7H0MassTerm : Ball := ⟨0, 0⟩
lemma Z0_1_7H0MassTerm_sound : Z0_1_7H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_1_7H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7H0Mass_sound) Z0_1_7H0MassTermLog_sound) (by decide +kernel)
def Z0_1_7H0H : Ball := ⟨0, 0⟩
lemma Z0_1_7H0H_sound : Z0_1_7H0H.Encloses (homogeneousEntropy Z0_1_7H0Value) := by
  exact contains_sound (homogeneous_enclosed Z0_1_7H0Value Z0_1_7H0MassTerm_sound Z0_1_7H0Entropy_sound) (by decide +kernel)
def Z0_1_7H1Value (a : PairSlot) : ℝ := (halfLaw (shape 0 1 7) 1 a : ℝ)
def Z0_1_7H1E_1_0LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H1E_1_0Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7H1E_1_0Log_sound : Z0_1_7H1E_1_0Log.Encloses (Real.log (Z0_1_7H1Value ((1,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_1_7Half_sound 1) ((1,0) : PairSlot)) (w := Z0_1_7H1E_1_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7H1E_1_0 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7H1E_1_0_sound : Z0_1_7H1E_1_0.Encloses (Foundation.entropyTerm (Z0_1_7H1Value ((1,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_1_7Half_sound 1) ((1,0) : PairSlot)) Z0_1_7H1E_1_0Log_sound) (by decide +kernel)
def Z0_1_7H1E_0_1LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H1E_0_1Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7H1E_0_1Log_sound : Z0_1_7H1E_0_1Log.Encloses (Real.log (Z0_1_7H1Value ((0,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_1_7Half_sound 1) ((0,1) : PairSlot)) (w := Z0_1_7H1E_0_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7H1E_0_1 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7H1E_0_1_sound : Z0_1_7H1E_0_1.Encloses (Foundation.entropyTerm (Z0_1_7H1Value ((0,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_1_7Half_sound 1) ((0,1) : PairSlot)) Z0_1_7H1E_0_1Log_sound) (by decide +kernel)
def Z0_1_7H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 0 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 0, 1 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_1_7H1Terms_sound (a : PairSlot) :
    (Z0_1_7H1Terms a).Encloses (Foundation.entropyTerm (Z0_1_7H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((0,0) : PairSlot))) Z0_1_7H1E_0_1_sound (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 Z0_1_7H1E_1_0_sound (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 1) ((5,5) : PairSlot)))
def Z0_1_7H1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z0_1_7H1Entropy_sound : Z0_1_7H1Entropy.Encloses (Foundation.finiteEntropy Z0_1_7H1Value) := by
  exact contains_sound (entropyPair_enclosed Z0_1_7H1Value Z0_1_7H1Terms Z0_1_7H1Terms_sound) (by decide +kernel)
def Z0_1_7H1Mass : Ball := ⟨1, 0⟩
lemma Z0_1_7H1Mass_sound : Z0_1_7H1Mass.Encloses (∑ a, Z0_1_7H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_1_7Half 1) Z0_1_7H1Value (Z0_1_7Half_sound 1)) (by decide +kernel)
def Z0_1_7H1MassTermLog : Ball := .exact 0
lemma Z0_1_7H1MassTermLog_sound : Z0_1_7H1MassTermLog.Encloses (Real.log ((∑ a, Z0_1_7H1Value a))) := by
  exact log_exact_one_ball (Z0_1_7H1Mass_sound)
def Z0_1_7H1MassTerm : Ball := ⟨0, 0⟩
lemma Z0_1_7H1MassTerm_sound : Z0_1_7H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_1_7H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7H1Mass_sound) Z0_1_7H1MassTermLog_sound) (by decide +kernel)
def Z0_1_7H1H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z0_1_7H1H_sound : Z0_1_7H1H.Encloses (homogeneousEntropy Z0_1_7H1Value) := by
  exact contains_sound (homogeneous_enclosed Z0_1_7H1Value Z0_1_7H1MassTerm_sound Z0_1_7H1Entropy_sound) (by decide +kernel)
def Z0_1_7H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 1 7) 2 a : ℝ)
def Z0_1_7H2E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H2E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7H2E_4_5Log_sound : Z0_1_7H2E_4_5Log.Encloses (Real.log (Z0_1_7H2Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_1_7Half_sound 2) ((4,5) : PairSlot)) (w := Z0_1_7H2E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7H2E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7H2E_4_5_sound : Z0_1_7H2E_4_5.Encloses (Foundation.entropyTerm (Z0_1_7H2Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_1_7Half_sound 2) ((4,5) : PairSlot)) Z0_1_7H2E_4_5Log_sound) (by decide +kernel)
def Z0_1_7H2E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z0_1_7H2E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z0_1_7H2E_5_4Log_sound : Z0_1_7H2E_5_4Log.Encloses (Real.log (Z0_1_7H2Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_1_7Half_sound 2) ((5,4) : PairSlot)) (w := Z0_1_7H2E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_1_7H2E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z0_1_7H2E_5_4_sound : Z0_1_7H2E_5_4.Encloses (Foundation.entropyTerm (Z0_1_7H2Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_1_7Half_sound 2) ((5,4) : PairSlot)) Z0_1_7H2E_5_4Log_sound) (by decide +kernel)
def Z0_1_7H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_1_7H2Terms_sound (a : PairSlot) :
    (Z0_1_7H2Terms a).Encloses (Foundation.entropyTerm (Z0_1_7H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((4,4) : PairSlot))) Z0_1_7H2E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((5,3) : PairSlot))) Z0_1_7H2E_5_4_sound (entropyTerm_zero_ball ((Z0_1_7Half_sound 2) ((5,5) : PairSlot)))
def Z0_1_7H2Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z0_1_7H2Entropy_sound : Z0_1_7H2Entropy.Encloses (Foundation.finiteEntropy Z0_1_7H2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_1_7H2Value Z0_1_7H2Terms Z0_1_7H2Terms_sound) (by decide +kernel)
def Z0_1_7H2Mass : Ball := ⟨1, 0⟩
lemma Z0_1_7H2Mass_sound : Z0_1_7H2Mass.Encloses (∑ a, Z0_1_7H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_1_7Half 2) Z0_1_7H2Value (Z0_1_7Half_sound 2)) (by decide +kernel)
def Z0_1_7H2MassTermLog : Ball := .exact 0
lemma Z0_1_7H2MassTermLog_sound : Z0_1_7H2MassTermLog.Encloses (Real.log ((∑ a, Z0_1_7H2Value a))) := by
  exact log_exact_one_ball (Z0_1_7H2Mass_sound)
def Z0_1_7H2MassTerm : Ball := ⟨0, 0⟩
lemma Z0_1_7H2MassTerm_sound : Z0_1_7H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_1_7H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_1_7H2Mass_sound) Z0_1_7H2MassTermLog_sound) (by decide +kernel)
def Z0_1_7H2H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z0_1_7H2H_sound : Z0_1_7H2H.Encloses (homogeneousEntropy Z0_1_7H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_1_7H2Value Z0_1_7H2MassTerm_sound Z0_1_7H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
