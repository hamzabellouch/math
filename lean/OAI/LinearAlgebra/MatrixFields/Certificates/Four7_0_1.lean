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
def Z7_0_1Raw (ij : PairSlot) : Ball :=
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
lemma Z7_0_1Raw_sound_0 (j : Fin 6) :
    (Z7_0_1Raw (0,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (0,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (0,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 0 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_1 (j : Fin 6) :
    (Z7_0_1Raw (1,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (1,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (1,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 1 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_2 (j : Fin 6) :
    (Z7_0_1Raw (2,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (2,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (2,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 2 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_3 (j : Fin 6) :
    (Z7_0_1Raw (3,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (3,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (3,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 3 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_4 (j : Fin 6) :
    (Z7_0_1Raw (4,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (4,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (4,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 4 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound_5 (j : Fin 6) :
    (Z7_0_1Raw (5,j)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 j) : ℝ) := by
  fin_cases j
  · change (Z7_0_1Raw (5,0)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 0) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,1)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 1) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,2)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 2) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,3)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 3) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,4)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 4) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z7_0_1Raw (5,5)).Encloses (weight (orderedPairInteger (shape 7 0 1) 5 5) : ℝ)
    have he : orderedPairInteger (shape 7 0 1) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z7_0_1Raw_sound (ij : PairSlot) :
    (Z7_0_1Raw ij).Encloses (weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z7_0_1Raw_sound_0 j) (Z7_0_1Raw_sound_1 j) (Z7_0_1Raw_sound_2 j) (Z7_0_1Raw_sound_3 j) (Z7_0_1Raw_sound_4 j) (Z7_0_1Raw_sound_5 j)
def Z7_0_1Den : Ball := ⟨2, 0⟩
lemma Z7_0_1Den_sound : Z7_0_1Den.Encloses
    (((orderedPairs (shape 7 0 1)).map (fun ij => weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 7 0 1)) Z7_0_1Raw
    (fun ij => weight (orderedPairInteger (shape 7 0 1) ij.1 ij.2))
    (fun ij _ => Z7_0_1Raw_sound ij)) (by decide +kernel)
lemma Z7_0_1Den_pos : 0 < Z7_0_1Den.lower := by decide +kernel
def Z7_0_1Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 4, 5 => ⟨(1 / 2), 0⟩
  | 5, 4 => ⟨(1 / 2), 0⟩
  | _, _ => (.exact 0)
lemma Z7_0_1Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 7 0 1) →
    contains (.mul (Z7_0_1Raw (i,j)) (.inv Z7_0_1Den)) (Z7_0_1Probs (i,j)) = true := by
  decide +kernel
lemma Z7_0_1Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 7 0 1) → Z7_0_1Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z7_0_1Probs_sound (ij : PairSlot) :
    (Z7_0_1Probs ij).Encloses (zeroPairLaw (shape 7 0 1) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 7 0 1)
  · have hb := contains_sound (Ball.mul_sound (Z7_0_1Raw_sound ij)
      (Ball.inv_sound Z7_0_1Den_sound Z7_0_1Den_pos)) (Z7_0_1Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z7_0_1Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z7_0_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 7 0 1) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 7 0 1) then Z7_0_1Probs ij
  else Z7_0_1Probs (kappa ij.1, kappa ij.2)
lemma Z7_0_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z7_0_1Half w ij).Encloses (halfLaw (shape 7 0 1) w ij : ℝ) := by
  have hp : positive (shape 7 0 1) = false := by decide +kernel
  simp only [Z7_0_1Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z7_0_1Probs_sound _
  · exact Z7_0_1Probs_sound _

def Z7_0_1Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 7 0 1) a.1 a.2 : ℝ)
def Z7_0_1E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1E_4_5Log_sound : Z7_0_1E_4_5Log.Encloses (Real.log (Z7_0_1Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z7_0_1Probs_sound ((4,5) : PairSlot)) (w := Z7_0_1E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1E_4_5_sound : Z7_0_1E_4_5.Encloses (Foundation.entropyTerm (Z7_0_1Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z7_0_1Probs_sound ((4,5) : PairSlot)) Z7_0_1E_4_5Log_sound) (by decide +kernel)
def Z7_0_1E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1E_5_4Log_sound : Z7_0_1E_5_4Log.Encloses (Real.log (Z7_0_1Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z7_0_1Probs_sound ((5,4) : PairSlot)) (w := Z7_0_1E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1E_5_4_sound : Z7_0_1E_5_4.Encloses (Foundation.entropyTerm (Z7_0_1Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z7_0_1Probs_sound ((5,4) : PairSlot)) Z7_0_1E_5_4Log_sound) (by decide +kernel)
def Z7_0_1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z7_0_1Terms_sound (a : PairSlot) :
    (Z7_0_1Terms a).Encloses (Foundation.entropyTerm (Z7_0_1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((4,4) : PairSlot))) Z7_0_1E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z7_0_1Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z7_0_1Probs_sound ((5,3) : PairSlot))) Z7_0_1E_5_4_sound (entropyTerm_zero_ball (Z7_0_1Probs_sound ((5,5) : PairSlot)))
def Z7_0_1Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z7_0_1Entropy_sound : Z7_0_1Entropy.Encloses (Foundation.finiteEntropy Z7_0_1Value) := by
  exact contains_sound (entropyPair_enclosed Z7_0_1Value Z7_0_1Terms Z7_0_1Terms_sound) (by decide +kernel)
def Z7_0_1Labels : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma Z7_0_1Labels_sound : Z7_0_1Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 7 0 1) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z7_0_1Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z7_0_1Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z7_0_1Four : Ball := ⟨(18723326709712443708970142577019 / 6250000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma Z7_0_1Four_sound : Z7_0_1Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 7 0 1)) := by
  exact contains_sound (Ball.add_sound Z7_0_1Entropy_sound Z7_0_1Labels_sound) (by decide +kernel)
def Z7_0_1H0Value (a : PairSlot) : ℝ := (halfLaw (shape 7 0 1) 0 a : ℝ)
def Z7_0_1H0E_4_5LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1H0E_4_5Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1H0E_4_5Log_sound : Z7_0_1H0E_4_5Log.Encloses (Real.log (Z7_0_1H0Value ((4,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z7_0_1Half_sound 0) ((4,5) : PairSlot)) (w := Z7_0_1H0E_4_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1H0E_4_5 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1H0E_4_5_sound : Z7_0_1H0E_4_5.Encloses (Foundation.entropyTerm (Z7_0_1H0Value ((4,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z7_0_1Half_sound 0) ((4,5) : PairSlot)) Z7_0_1H0E_4_5Log_sound) (by decide +kernel)
def Z7_0_1H0E_5_4LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1H0E_5_4Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1H0E_5_4Log_sound : Z7_0_1H0E_5_4Log.Encloses (Real.log (Z7_0_1H0Value ((5,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z7_0_1Half_sound 0) ((5,4) : PairSlot)) (w := Z7_0_1H0E_5_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1H0E_5_4 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1H0E_5_4_sound : Z7_0_1H0E_5_4.Encloses (Foundation.entropyTerm (Z7_0_1H0Value ((5,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z7_0_1Half_sound 0) ((5,4) : PairSlot)) Z7_0_1H0E_5_4Log_sound) (by decide +kernel)
def Z7_0_1H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 5 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 5, 4 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z7_0_1H0Terms_sound (a : PairSlot) :
    (Z7_0_1H0Terms a).Encloses (Foundation.entropyTerm (Z7_0_1H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((4,4) : PairSlot))) Z7_0_1H0E_4_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((5,3) : PairSlot))) Z7_0_1H0E_5_4_sound (entropyTerm_zero_ball ((Z7_0_1Half_sound 0) ((5,5) : PairSlot)))
def Z7_0_1H0Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z7_0_1H0Entropy_sound : Z7_0_1H0Entropy.Encloses (Foundation.finiteEntropy Z7_0_1H0Value) := by
  exact contains_sound (entropyPair_enclosed Z7_0_1H0Value Z7_0_1H0Terms Z7_0_1H0Terms_sound) (by decide +kernel)
def Z7_0_1H0Mass : Ball := ⟨1, 0⟩
lemma Z7_0_1H0Mass_sound : Z7_0_1H0Mass.Encloses (∑ a, Z7_0_1H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z7_0_1Half 0) Z7_0_1H0Value (Z7_0_1Half_sound 0)) (by decide +kernel)
def Z7_0_1H0MassTermLog : Ball := .exact 0
lemma Z7_0_1H0MassTermLog_sound : Z7_0_1H0MassTermLog.Encloses (Real.log ((∑ a, Z7_0_1H0Value a))) := by
  exact log_exact_one_ball (Z7_0_1H0Mass_sound)
def Z7_0_1H0MassTerm : Ball := ⟨0, 0⟩
lemma Z7_0_1H0MassTerm_sound : Z7_0_1H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z7_0_1H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z7_0_1H0Mass_sound) Z7_0_1H0MassTermLog_sound) (by decide +kernel)
def Z7_0_1H0H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z7_0_1H0H_sound : Z7_0_1H0H.Encloses (homogeneousEntropy Z7_0_1H0Value) := by
  exact contains_sound (homogeneous_enclosed Z7_0_1H0Value Z7_0_1H0MassTerm_sound Z7_0_1H0Entropy_sound) (by decide +kernel)
def Z7_0_1H1Value (a : PairSlot) : ℝ := (halfLaw (shape 7 0 1) 1 a : ℝ)
def Z7_0_1H1E_0_0Log : Ball := .exact 0
lemma Z7_0_1H1E_0_0Log_sound : Z7_0_1H1E_0_0Log.Encloses (Real.log (Z7_0_1H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z7_0_1Half_sound 1) ((0,0) : PairSlot))
def Z7_0_1H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z7_0_1H1E_0_0_sound : Z7_0_1H1E_0_0.Encloses (Foundation.entropyTerm (Z7_0_1H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z7_0_1Half_sound 1) ((0,0) : PairSlot)) Z7_0_1H1E_0_0Log_sound) (by decide +kernel)
def Z7_0_1H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z7_0_1H1Terms_sound (a : PairSlot) :
    (Z7_0_1H1Terms a).Encloses (Foundation.entropyTerm (Z7_0_1H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z7_0_1H1E_0_0_sound (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 1) ((5,5) : PairSlot)))
def Z7_0_1H1Entropy : Ball := ⟨0, 0⟩
lemma Z7_0_1H1Entropy_sound : Z7_0_1H1Entropy.Encloses (Foundation.finiteEntropy Z7_0_1H1Value) := by
  exact contains_sound (entropyPair_enclosed Z7_0_1H1Value Z7_0_1H1Terms Z7_0_1H1Terms_sound) (by decide +kernel)
def Z7_0_1H1Mass : Ball := ⟨1, 0⟩
lemma Z7_0_1H1Mass_sound : Z7_0_1H1Mass.Encloses (∑ a, Z7_0_1H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z7_0_1Half 1) Z7_0_1H1Value (Z7_0_1Half_sound 1)) (by decide +kernel)
def Z7_0_1H1MassTermLog : Ball := .exact 0
lemma Z7_0_1H1MassTermLog_sound : Z7_0_1H1MassTermLog.Encloses (Real.log ((∑ a, Z7_0_1H1Value a))) := by
  exact log_exact_one_ball (Z7_0_1H1Mass_sound)
def Z7_0_1H1MassTerm : Ball := ⟨0, 0⟩
lemma Z7_0_1H1MassTerm_sound : Z7_0_1H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z7_0_1H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z7_0_1H1Mass_sound) Z7_0_1H1MassTermLog_sound) (by decide +kernel)
def Z7_0_1H1H : Ball := ⟨0, 0⟩
lemma Z7_0_1H1H_sound : Z7_0_1H1H.Encloses (homogeneousEntropy Z7_0_1H1Value) := by
  exact contains_sound (homogeneous_enclosed Z7_0_1H1Value Z7_0_1H1MassTerm_sound Z7_0_1H1Entropy_sound) (by decide +kernel)
def Z7_0_1H2Value (a : PairSlot) : ℝ := (halfLaw (shape 7 0 1) 2 a : ℝ)
def Z7_0_1H2E_1_0LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1H2E_1_0Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1H2E_1_0Log_sound : Z7_0_1H2E_1_0Log.Encloses (Real.log (Z7_0_1H2Value ((1,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z7_0_1Half_sound 2) ((1,0) : PairSlot)) (w := Z7_0_1H2E_1_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1H2E_1_0 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1H2E_1_0_sound : Z7_0_1H2E_1_0.Encloses (Foundation.entropyTerm (Z7_0_1H2Value ((1,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z7_0_1Half_sound 2) ((1,0) : PairSlot)) Z7_0_1H2E_1_0Log_sound) (by decide +kernel)
def Z7_0_1H2E_0_1LogWitness : LogWitness := ⟨-1, 1, 1⟩
def Z7_0_1H2E_0_1Log : Ball := ⟨(-6931471805599453094172319305033 / 10000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma Z7_0_1H2E_0_1Log_sound : Z7_0_1H2E_0_1Log.Encloses (Real.log (Z7_0_1H2Value ((0,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z7_0_1Half_sound 2) ((0,1) : PairSlot)) (w := Z7_0_1H2E_0_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z7_0_1H2E_0_1 : Ball := ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
lemma Z7_0_1H2E_0_1_sound : Z7_0_1H2E_0_1.Encloses (Foundation.entropyTerm (Z7_0_1H2Value ((0,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z7_0_1Half_sound 2) ((0,1) : PairSlot)) Z7_0_1H2E_0_1Log_sound) (by decide +kernel)
def Z7_0_1H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 0 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | 0, 1 => ⟨(6931471805599453094172319305033 / 20000000000000000000000000000000), (21175823683 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z7_0_1H2Terms_sound (a : PairSlot) :
    (Z7_0_1H2Terms a).Encloses (Foundation.entropyTerm (Z7_0_1H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((0,0) : PairSlot))) Z7_0_1H2E_0_1_sound (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 Z7_0_1H2E_1_0_sound (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z7_0_1Half_sound 2) ((5,5) : PairSlot)))
def Z7_0_1H2Entropy : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z7_0_1H2Entropy_sound : Z7_0_1H2Entropy.Encloses (Foundation.finiteEntropy Z7_0_1H2Value) := by
  exact contains_sound (entropyPair_enclosed Z7_0_1H2Value Z7_0_1H2Terms Z7_0_1H2Terms_sound) (by decide +kernel)
def Z7_0_1H2Mass : Ball := ⟨1, 0⟩
lemma Z7_0_1H2Mass_sound : Z7_0_1H2Mass.Encloses (∑ a, Z7_0_1H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z7_0_1Half 2) Z7_0_1H2Value (Z7_0_1Half_sound 2)) (by decide +kernel)
def Z7_0_1H2MassTermLog : Ball := .exact 0
lemma Z7_0_1H2MassTermLog_sound : Z7_0_1H2MassTermLog.Encloses (Real.log ((∑ a, Z7_0_1H2Value a))) := by
  exact log_exact_one_ball (Z7_0_1H2Mass_sound)
def Z7_0_1H2MassTerm : Ball := ⟨0, 0⟩
lemma Z7_0_1H2MassTerm_sound : Z7_0_1H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z7_0_1H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z7_0_1H2Mass_sound) Z7_0_1H2MassTermLog_sound) (by decide +kernel)
def Z7_0_1H2H : Ball := ⟨(6931471805599453094172319305033 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma Z7_0_1H2H_sound : Z7_0_1H2H.Encloses (homogeneousEntropy Z7_0_1H2Value) := by
  exact contains_sound (homogeneous_enclosed Z7_0_1H2Value Z7_0_1H2MassTerm_sound Z7_0_1H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
