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
def Z0_8_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w195
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w195
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z0_8_0Raw_sound_0 (j : Fin 6) :
    (Z0_8_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound_1 (j : Fin 6) :
    (Z0_8_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound_2 (j : Fin 6) :
    (Z0_8_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound_3 (j : Fin 6) :
    (Z0_8_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound_4 (j : Fin 6) :
    (Z0_8_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound_5 (j : Fin 6) :
    (Z0_8_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_8_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_8_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 8 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 8 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_8_0Raw_sound (ij : PairSlot) :
    (Z0_8_0Raw ij).Encloses (weight (orderedPairInteger (shape 0 8 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_8_0Raw_sound_0 j) (Z0_8_0Raw_sound_1 j) (Z0_8_0Raw_sound_2 j) (Z0_8_0Raw_sound_3 j) (Z0_8_0Raw_sound_4 j) (Z0_8_0Raw_sound_5 j)
def Z0_8_0Den : Ball := ⟨1, 0⟩
lemma Z0_8_0Den_sound : Z0_8_0Den.Encloses
    (((orderedPairs (shape 0 8 0)).map (fun ij => weight (orderedPairInteger (shape 0 8 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 8 0)) Z0_8_0Raw
    (fun ij => weight (orderedPairInteger (shape 0 8 0) ij.1 ij.2))
    (fun ij _ => Z0_8_0Raw_sound ij)) (by decide +kernel)
lemma Z0_8_0Den_pos : 0 < Z0_8_0Den.lower := by decide +kernel
def Z0_8_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 5, 5 => ⟨1, 0⟩
  | _, _ => (.exact 0)
lemma Z0_8_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 8 0) →
    contains (.mul (Z0_8_0Raw (i,j)) (.inv Z0_8_0Den)) (Z0_8_0Probs (i,j)) = true := by
  decide +kernel
lemma Z0_8_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 8 0) → Z0_8_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_8_0Probs_sound (ij : PairSlot) :
    (Z0_8_0Probs ij).Encloses (zeroPairLaw (shape 0 8 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 8 0)
  · have hb := contains_sound (Ball.mul_sound (Z0_8_0Raw_sound ij)
      (Ball.inv_sound Z0_8_0Den_sound Z0_8_0Den_pos)) (Z0_8_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_8_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z0_8_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 8 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 8 0) then Z0_8_0Probs ij
  else Z0_8_0Probs (kappa ij.1, kappa ij.2)
lemma Z0_8_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_8_0Half w ij).Encloses (halfLaw (shape 0 8 0) w ij : ℝ) := by
  have hp : positive (shape 0 8 0) = false := by decide +kernel
  simp only [Z0_8_0Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_8_0Probs_sound _
  · exact Z0_8_0Probs_sound _

def Z0_8_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 8 0) a.1 a.2 : ℝ)
def Z0_8_0E_5_5Log : Ball := .exact 0
lemma Z0_8_0E_5_5Log_sound : Z0_8_0E_5_5Log.Encloses (Real.log (Z0_8_0Value ((5,5) : PairSlot))) := by
  exact log_exact_one_ball (Z0_8_0Probs_sound ((5,5) : PairSlot))
def Z0_8_0E_5_5 : Ball := ⟨0, 0⟩
lemma Z0_8_0E_5_5_sound : Z0_8_0E_5_5.Encloses (Foundation.entropyTerm (Z0_8_0Value ((5,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_8_0Probs_sound ((5,5) : PairSlot)) Z0_8_0E_5_5Log_sound) (by decide +kernel)
def Z0_8_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_8_0Terms_sound (a : PairSlot) :
    (Z0_8_0Terms a).Encloses (Foundation.entropyTerm (Z0_8_0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_8_0Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z0_8_0Probs_sound ((5,4) : PairSlot))) Z0_8_0E_5_5_sound
def Z0_8_0Entropy : Ball := ⟨0, 0⟩
lemma Z0_8_0Entropy_sound : Z0_8_0Entropy.Encloses (Foundation.finiteEntropy Z0_8_0Value) := by
  exact contains_sound (entropyPair_enclosed Z0_8_0Value Z0_8_0Terms Z0_8_0Terms_sound) (by decide +kernel)
def Z0_8_0Labels : Ball := ⟨0, 0⟩
lemma Z0_8_0Labels_sound : Z0_8_0Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 8 0) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_8_0Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_8_0Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z0_8_0Four : Ball := ⟨0, 0⟩
lemma Z0_8_0Four_sound : Z0_8_0Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 8 0)) := by
  exact contains_sound (Ball.add_sound Z0_8_0Entropy_sound Z0_8_0Labels_sound) (by decide +kernel)
def Z0_8_0H0Value (a : PairSlot) : ℝ := (halfLaw (shape 0 8 0) 0 a : ℝ)
def Z0_8_0H0E_0_0Log : Ball := .exact 0
lemma Z0_8_0H0E_0_0Log_sound : Z0_8_0H0E_0_0Log.Encloses (Real.log (Z0_8_0H0Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z0_8_0Half_sound 0) ((0,0) : PairSlot))
def Z0_8_0H0E_0_0 : Ball := ⟨0, 0⟩
lemma Z0_8_0H0E_0_0_sound : Z0_8_0H0E_0_0.Encloses (Foundation.entropyTerm (Z0_8_0H0Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_8_0Half_sound 0) ((0,0) : PairSlot)) Z0_8_0H0E_0_0Log_sound) (by decide +kernel)
def Z0_8_0H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_8_0H0Terms_sound (a : PairSlot) :
    (Z0_8_0H0Terms a).Encloses (Foundation.entropyTerm (Z0_8_0H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z0_8_0H0E_0_0_sound (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 0) ((5,5) : PairSlot)))
def Z0_8_0H0Entropy : Ball := ⟨0, 0⟩
lemma Z0_8_0H0Entropy_sound : Z0_8_0H0Entropy.Encloses (Foundation.finiteEntropy Z0_8_0H0Value) := by
  exact contains_sound (entropyPair_enclosed Z0_8_0H0Value Z0_8_0H0Terms Z0_8_0H0Terms_sound) (by decide +kernel)
def Z0_8_0H0Mass : Ball := ⟨1, 0⟩
lemma Z0_8_0H0Mass_sound : Z0_8_0H0Mass.Encloses (∑ a, Z0_8_0H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_8_0Half 0) Z0_8_0H0Value (Z0_8_0Half_sound 0)) (by decide +kernel)
def Z0_8_0H0MassTermLog : Ball := .exact 0
lemma Z0_8_0H0MassTermLog_sound : Z0_8_0H0MassTermLog.Encloses (Real.log ((∑ a, Z0_8_0H0Value a))) := by
  exact log_exact_one_ball (Z0_8_0H0Mass_sound)
def Z0_8_0H0MassTerm : Ball := ⟨0, 0⟩
lemma Z0_8_0H0MassTerm_sound : Z0_8_0H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_8_0H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_8_0H0Mass_sound) Z0_8_0H0MassTermLog_sound) (by decide +kernel)
def Z0_8_0H0H : Ball := ⟨0, 0⟩
lemma Z0_8_0H0H_sound : Z0_8_0H0H.Encloses (homogeneousEntropy Z0_8_0H0Value) := by
  exact contains_sound (homogeneous_enclosed Z0_8_0H0Value Z0_8_0H0MassTerm_sound Z0_8_0H0Entropy_sound) (by decide +kernel)
def Z0_8_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 0 8 0) 1 a : ℝ)
def Z0_8_0H1E_5_5Log : Ball := .exact 0
lemma Z0_8_0H1E_5_5Log_sound : Z0_8_0H1E_5_5Log.Encloses (Real.log (Z0_8_0H1Value ((5,5) : PairSlot))) := by
  exact log_exact_one_ball ((Z0_8_0Half_sound 1) ((5,5) : PairSlot))
def Z0_8_0H1E_5_5 : Ball := ⟨0, 0⟩
lemma Z0_8_0H1E_5_5_sound : Z0_8_0H1E_5_5.Encloses (Foundation.entropyTerm (Z0_8_0H1Value ((5,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_8_0Half_sound 1) ((5,5) : PairSlot)) Z0_8_0H1E_5_5Log_sound) (by decide +kernel)
def Z0_8_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 5 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_8_0H1Terms_sound (a : PairSlot) :
    (Z0_8_0H1Terms a).Encloses (Foundation.entropyTerm (Z0_8_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 1) ((5,4) : PairSlot))) Z0_8_0H1E_5_5_sound
def Z0_8_0H1Entropy : Ball := ⟨0, 0⟩
lemma Z0_8_0H1Entropy_sound : Z0_8_0H1Entropy.Encloses (Foundation.finiteEntropy Z0_8_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z0_8_0H1Value Z0_8_0H1Terms Z0_8_0H1Terms_sound) (by decide +kernel)
def Z0_8_0H1Mass : Ball := ⟨1, 0⟩
lemma Z0_8_0H1Mass_sound : Z0_8_0H1Mass.Encloses (∑ a, Z0_8_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_8_0Half 1) Z0_8_0H1Value (Z0_8_0Half_sound 1)) (by decide +kernel)
def Z0_8_0H1MassTermLog : Ball := .exact 0
lemma Z0_8_0H1MassTermLog_sound : Z0_8_0H1MassTermLog.Encloses (Real.log ((∑ a, Z0_8_0H1Value a))) := by
  exact log_exact_one_ball (Z0_8_0H1Mass_sound)
def Z0_8_0H1MassTerm : Ball := ⟨0, 0⟩
lemma Z0_8_0H1MassTerm_sound : Z0_8_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_8_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_8_0H1Mass_sound) Z0_8_0H1MassTermLog_sound) (by decide +kernel)
def Z0_8_0H1H : Ball := ⟨0, 0⟩
lemma Z0_8_0H1H_sound : Z0_8_0H1H.Encloses (homogeneousEntropy Z0_8_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z0_8_0H1Value Z0_8_0H1MassTerm_sound Z0_8_0H1Entropy_sound) (by decide +kernel)
def Z0_8_0H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 8 0) 2 a : ℝ)
def Z0_8_0H2E_0_0Log : Ball := .exact 0
lemma Z0_8_0H2E_0_0Log_sound : Z0_8_0H2E_0_0Log.Encloses (Real.log (Z0_8_0H2Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z0_8_0Half_sound 2) ((0,0) : PairSlot))
def Z0_8_0H2E_0_0 : Ball := ⟨0, 0⟩
lemma Z0_8_0H2E_0_0_sound : Z0_8_0H2E_0_0.Encloses (Foundation.entropyTerm (Z0_8_0H2Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_8_0Half_sound 2) ((0,0) : PairSlot)) Z0_8_0H2E_0_0Log_sound) (by decide +kernel)
def Z0_8_0H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_8_0H2Terms_sound (a : PairSlot) :
    (Z0_8_0H2Terms a).Encloses (Foundation.entropyTerm (Z0_8_0H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z0_8_0H2E_0_0_sound (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_8_0Half_sound 2) ((5,5) : PairSlot)))
def Z0_8_0H2Entropy : Ball := ⟨0, 0⟩
lemma Z0_8_0H2Entropy_sound : Z0_8_0H2Entropy.Encloses (Foundation.finiteEntropy Z0_8_0H2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_8_0H2Value Z0_8_0H2Terms Z0_8_0H2Terms_sound) (by decide +kernel)
def Z0_8_0H2Mass : Ball := ⟨1, 0⟩
lemma Z0_8_0H2Mass_sound : Z0_8_0H2Mass.Encloses (∑ a, Z0_8_0H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_8_0Half 2) Z0_8_0H2Value (Z0_8_0Half_sound 2)) (by decide +kernel)
def Z0_8_0H2MassTermLog : Ball := .exact 0
lemma Z0_8_0H2MassTermLog_sound : Z0_8_0H2MassTermLog.Encloses (Real.log ((∑ a, Z0_8_0H2Value a))) := by
  exact log_exact_one_ball (Z0_8_0H2Mass_sound)
def Z0_8_0H2MassTerm : Ball := ⟨0, 0⟩
lemma Z0_8_0H2MassTerm_sound : Z0_8_0H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_8_0H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_8_0H2Mass_sound) Z0_8_0H2MassTermLog_sound) (by decide +kernel)
def Z0_8_0H2H : Ball := ⟨0, 0⟩
lemma Z0_8_0H2H_sound : Z0_8_0H2H.Encloses (homogeneousEntropy Z0_8_0H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_8_0H2Value Z0_8_0H2MassTerm_sound Z0_8_0H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
