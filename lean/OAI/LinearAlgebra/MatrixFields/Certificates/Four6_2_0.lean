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
def Z6_2_0Raw (ij : PairSlot) : Ball :=
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
  | 2, 5 => w194
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w196
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w194
  | 5, 3 => w196
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z6_2_0Raw_sound_0 (j : Fin 6) :
    (Z6_2_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_2_0Raw_sound_1 (j : Fin 6) :
    (Z6_2_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_2_0Raw_sound_2 (j : Fin 6) :
    (Z6_2_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 2 5 = (-52) := by decide +kernel
    rw [he]
    exact w194_sound
lemma Z6_2_0Raw_sound_3 (j : Fin 6) :
    (Z6_2_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 3 5 = (17) := by decide +kernel
    rw [he]
    exact w196_sound
lemma Z6_2_0Raw_sound_4 (j : Fin 6) :
    (Z6_2_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_2_0Raw_sound_5 (j : Fin 6) :
    (Z6_2_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z6_2_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 2 = (-52) := by decide +kernel
    rw [he]
    exact w194_sound
  · change (Z6_2_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 3 = (17) := by decide +kernel
    rw [he]
    exact w196_sound
  · change (Z6_2_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_2_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 6 2 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 6 2 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_2_0Raw_sound (ij : PairSlot) :
    (Z6_2_0Raw ij).Encloses (weight (orderedPairInteger (shape 6 2 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z6_2_0Raw_sound_0 j) (Z6_2_0Raw_sound_1 j) (Z6_2_0Raw_sound_2 j) (Z6_2_0Raw_sound_3 j) (Z6_2_0Raw_sound_4 j) (Z6_2_0Raw_sound_5 j)
def Z6_2_0Den : Ball := ⟨(249651494241494819962441097012029 / 50000000000000000000000000000000), (127 / 25000000000000000000000000000000)⟩
lemma Z6_2_0Den_sound : Z6_2_0Den.Encloses
    (((orderedPairs (shape 6 2 0)).map (fun ij => weight (orderedPairInteger (shape 6 2 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 6 2 0)) Z6_2_0Raw
    (fun ij => weight (orderedPairInteger (shape 6 2 0) ij.1 ij.2))
    (fun ij _ => Z6_2_0Raw_sound ij)) (by decide +kernel)
lemma Z6_2_0Den_pos : 0 < Z6_2_0Den.lower := by decide +kernel
def Z6_2_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(19924044508891583790197036118597 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(4012399160127629130320676344027 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 4, 4 => ⟨(10013959690470270558199582161267 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(19924044508891583790197036118597 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(4012399160127629130320676344027 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_2_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 6 2 0) →
    contains (.mul (Z6_2_0Raw (i,j)) (.inv Z6_2_0Den)) (Z6_2_0Probs (i,j)) = true := by
  decide +kernel
lemma Z6_2_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 6 2 0) → Z6_2_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z6_2_0Probs_sound (ij : PairSlot) :
    (Z6_2_0Probs ij).Encloses (zeroPairLaw (shape 6 2 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 6 2 0)
  · have hb := contains_sound (Ball.mul_sound (Z6_2_0Raw_sound ij)
      (Ball.inv_sound Z6_2_0Den_sound Z6_2_0Den_pos)) (Z6_2_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z6_2_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z6_2_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 6 2 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 6 2 0) then Z6_2_0Probs ij
  else Z6_2_0Probs (kappa ij.1, kappa ij.2)
lemma Z6_2_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z6_2_0Half w ij).Encloses (halfLaw (shape 6 2 0) w ij : ℝ) := by
  have hp : positive (shape 6 2 0) = false := by decide +kernel
  simp only [Z6_2_0Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z6_2_0Probs_sound _
  · exact Z6_2_0Probs_sound _

def Z6_2_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 6 2 0) a.1 a.2 : ℝ)
def Z6_2_0E_2_5LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0E_2_5Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0E_2_5Log_sound : Z6_2_0E_2_5Log.Encloses (Real.log (Z6_2_0Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0Probs_sound ((2,5) : PairSlot)) (w := Z6_2_0E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0E_2_5 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0E_2_5_sound : Z6_2_0E_2_5.Encloses (Foundation.entropyTerm (Z6_2_0Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0Probs_sound ((2,5) : PairSlot)) Z6_2_0E_2_5Log_sound) (by decide +kernel)
def Z6_2_0E_3_5LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0E_3_5Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0E_3_5Log_sound : Z6_2_0E_3_5Log.Encloses (Real.log (Z6_2_0Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0Probs_sound ((3,5) : PairSlot)) (w := Z6_2_0E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0E_3_5 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0E_3_5_sound : Z6_2_0E_3_5.Encloses (Foundation.entropyTerm (Z6_2_0Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0Probs_sound ((3,5) : PairSlot)) Z6_2_0E_3_5Log_sound) (by decide +kernel)
def Z6_2_0E_4_4LogWitness : LogWitness := ⟨-3, 10013959690470270558199582161267, 6250000000000000000000000000000⟩
def Z6_2_0E_4_4Log : Ball := ⟨(-160804291684602305029666172383561 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_2_0E_4_4Log_sound : Z6_2_0E_4_4Log.Encloses (Real.log (Z6_2_0Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0Probs_sound ((4,4) : PairSlot)) (w := Z6_2_0E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0E_4_4 : Ball := ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
lemma Z6_2_0E_4_4_sound : Z6_2_0E_4_4.Encloses (Foundation.entropyTerm (Z6_2_0Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0Probs_sound ((4,4) : PairSlot)) Z6_2_0E_4_4Log_sound) (by decide +kernel)
def Z6_2_0E_5_2LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0E_5_2Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0E_5_2Log_sound : Z6_2_0E_5_2Log.Encloses (Real.log (Z6_2_0Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0Probs_sound ((5,2) : PairSlot)) (w := Z6_2_0E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0E_5_2 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0E_5_2_sound : Z6_2_0E_5_2.Encloses (Foundation.entropyTerm (Z6_2_0Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0Probs_sound ((5,2) : PairSlot)) Z6_2_0E_5_2Log_sound) (by decide +kernel)
def Z6_2_0E_5_3LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0E_5_3Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0E_5_3Log_sound : Z6_2_0E_5_3Log.Encloses (Real.log (Z6_2_0Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0Probs_sound ((5,3) : PairSlot)) (w := Z6_2_0E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0E_5_3 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0E_5_3_sound : Z6_2_0E_5_3.Encloses (Foundation.entropyTerm (Z6_2_0Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0Probs_sound ((5,3) : PairSlot)) Z6_2_0E_5_3Log_sound) (by decide +kernel)
def Z6_2_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 3, 5 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 5, 3 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_2_0Terms_sound (a : PairSlot) :
    (Z6_2_0Terms a).Encloses (Foundation.entropyTerm (Z6_2_0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((2,4) : PairSlot))) Z6_2_0E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((3,4) : PairSlot))) Z6_2_0E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((4,3) : PairSlot))) Z6_2_0E_4_4_sound (entropyTerm_zero_ball (Z6_2_0Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_2_0Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((5,1) : PairSlot))) Z6_2_0E_5_2_sound Z6_2_0E_5_3_sound (entropyTerm_zero_ball (Z6_2_0Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z6_2_0Probs_sound ((5,5) : PairSlot)))
def Z6_2_0Entropy : Ball := ⟨(40235822740443151951467192515337 / 25000000000000000000000000000000), (84703295281 / 100000000000000000000000000000000)⟩
lemma Z6_2_0Entropy_sound : Z6_2_0Entropy.Encloses (Foundation.finiteEntropy Z6_2_0Value) := by
  exact contains_sound (entropyPair_enclosed Z6_2_0Value Z6_2_0Terms Z6_2_0Terms_sound) (by decide +kernel)
def Z6_2_0Labels : Ball := ⟨(12415492963912716150755123942433 / 5000000000000000000000000000000), (44435757761 / 50000000000000000000000000000000)⟩
lemma Z6_2_0Labels_sound : Z6_2_0Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 6 2 0) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z6_2_0Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z6_2_0Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z6_2_0Four : Ball := ⟨(51156643780003366352621406113751 / 12500000000000000000000000000000), (173574810803 / 100000000000000000000000000000000)⟩
lemma Z6_2_0Four_sound : Z6_2_0Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 6 2 0)) := by
  exact contains_sound (Ball.add_sound Z6_2_0Entropy_sound Z6_2_0Labels_sound) (by decide +kernel)
def Z6_2_0H0Value (a : PairSlot) : ℝ := (halfLaw (shape 6 2 0) 0 a : ℝ)
def Z6_2_0H0E_2_5LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0H0E_2_5Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0E_2_5Log_sound : Z6_2_0H0E_2_5Log.Encloses (Real.log (Z6_2_0H0Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 0) ((2,5) : PairSlot)) (w := Z6_2_0H0E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0E_2_5 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H0E_2_5_sound : Z6_2_0H0E_2_5.Encloses (Foundation.entropyTerm (Z6_2_0H0Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 0) ((2,5) : PairSlot)) Z6_2_0H0E_2_5Log_sound) (by decide +kernel)
def Z6_2_0H0E_3_5LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0H0E_3_5Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H0E_3_5Log_sound : Z6_2_0H0E_3_5Log.Encloses (Real.log (Z6_2_0H0Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 0) ((3,5) : PairSlot)) (w := Z6_2_0H0E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0E_3_5 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H0E_3_5_sound : Z6_2_0H0E_3_5.Encloses (Foundation.entropyTerm (Z6_2_0H0Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 0) ((3,5) : PairSlot)) Z6_2_0H0E_3_5Log_sound) (by decide +kernel)
def Z6_2_0H0E_4_4LogWitness : LogWitness := ⟨-3, 10013959690470270558199582161267, 6250000000000000000000000000000⟩
def Z6_2_0H0E_4_4Log : Ball := ⟨(-160804291684602305029666172383561 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H0E_4_4Log_sound : Z6_2_0H0E_4_4Log.Encloses (Real.log (Z6_2_0H0Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 0) ((4,4) : PairSlot)) (w := Z6_2_0H0E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0E_4_4 : Ball := ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0E_4_4_sound : Z6_2_0H0E_4_4.Encloses (Foundation.entropyTerm (Z6_2_0H0Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 0) ((4,4) : PairSlot)) Z6_2_0H0E_4_4Log_sound) (by decide +kernel)
def Z6_2_0H0E_5_2LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0H0E_5_2Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0E_5_2Log_sound : Z6_2_0H0E_5_2Log.Encloses (Real.log (Z6_2_0H0Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 0) ((5,2) : PairSlot)) (w := Z6_2_0H0E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0E_5_2 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H0E_5_2_sound : Z6_2_0H0E_5_2.Encloses (Foundation.entropyTerm (Z6_2_0H0Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 0) ((5,2) : PairSlot)) Z6_2_0H0E_5_2Log_sound) (by decide +kernel)
def Z6_2_0H0E_5_3LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0H0E_5_3Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H0E_5_3Log_sound : Z6_2_0H0E_5_3Log.Encloses (Real.log (Z6_2_0H0Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 0) ((5,3) : PairSlot)) (w := Z6_2_0H0E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0E_5_3 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H0E_5_3_sound : Z6_2_0H0E_5_3.Encloses (Foundation.entropyTerm (Z6_2_0H0Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 0) ((5,3) : PairSlot)) Z6_2_0H0E_5_3Log_sound) (by decide +kernel)
def Z6_2_0H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 3, 5 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 5, 3 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_2_0H0Terms_sound (a : PairSlot) :
    (Z6_2_0H0Terms a).Encloses (Foundation.entropyTerm (Z6_2_0H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((2,4) : PairSlot))) Z6_2_0H0E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((3,4) : PairSlot))) Z6_2_0H0E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((4,3) : PairSlot))) Z6_2_0H0E_4_4_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((5,1) : PairSlot))) Z6_2_0H0E_5_2_sound Z6_2_0H0E_5_3_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 0) ((5,5) : PairSlot)))
def Z6_2_0H0Entropy : Ball := ⟨(40235822740443151951467192515337 / 25000000000000000000000000000000), (84703295281 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0Entropy_sound : Z6_2_0H0Entropy.Encloses (Foundation.finiteEntropy Z6_2_0H0Value) := by
  exact contains_sound (entropyPair_enclosed Z6_2_0H0Value Z6_2_0H0Terms Z6_2_0H0Terms_sound) (by decide +kernel)
def Z6_2_0H0Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0Mass_sound : Z6_2_0H0Mass.Encloses (∑ a, Z6_2_0H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_2_0Half 0) Z6_2_0H0Value (Z6_2_0Half_sound 0)) (by decide +kernel)
def Z6_2_0H0MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def Z6_2_0H0MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (1694065903 / 4000000000000000000000000000000)⟩
lemma Z6_2_0H0MassTermLog_sound : Z6_2_0H0MassTermLog.Encloses (Real.log ((∑ a, Z6_2_0H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0H0Mass_sound) (w := Z6_2_0H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H0MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (5293955947 / 12500000000000000000000000000000)⟩
lemma Z6_2_0H0MassTerm_sound : Z6_2_0H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_2_0H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0H0Mass_sound) Z6_2_0H0MassTermLog_sound) (by decide +kernel)
def Z6_2_0H0H : Ball := ⟨(160943290961772607805868770061347 / 100000000000000000000000000000000), (127054942857 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H0H_sound : Z6_2_0H0H.Encloses (homogeneousEntropy Z6_2_0H0Value) := by
  exact contains_sound (homogeneous_enclosed Z6_2_0H0Value Z6_2_0H0MassTerm_sound Z6_2_0H0Entropy_sound) (by decide +kernel)
def Z6_2_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 6 2 0) 1 a : ℝ)
def Z6_2_0H1E_2_0LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0H1E_2_0Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1E_2_0Log_sound : Z6_2_0H1E_2_0Log.Encloses (Real.log (Z6_2_0H1Value ((2,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 1) ((2,0) : PairSlot)) (w := Z6_2_0H1E_2_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1E_2_0 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H1E_2_0_sound : Z6_2_0H1E_2_0.Encloses (Foundation.entropyTerm (Z6_2_0H1Value ((2,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 1) ((2,0) : PairSlot)) Z6_2_0H1E_2_0Log_sound) (by decide +kernel)
def Z6_2_0H1E_3_0LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0H1E_3_0Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H1E_3_0Log_sound : Z6_2_0H1E_3_0Log.Encloses (Real.log (Z6_2_0H1Value ((3,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 1) ((3,0) : PairSlot)) (w := Z6_2_0H1E_3_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1E_3_0 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H1E_3_0_sound : Z6_2_0H1E_3_0.Encloses (Foundation.entropyTerm (Z6_2_0H1Value ((3,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 1) ((3,0) : PairSlot)) Z6_2_0H1E_3_0Log_sound) (by decide +kernel)
def Z6_2_0H1E_1_1LogWitness : LogWitness := ⟨-3, 10013959690470270558199582161267, 6250000000000000000000000000000⟩
def Z6_2_0H1E_1_1Log : Ball := ⟨(-160804291684602305029666172383561 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H1E_1_1Log_sound : Z6_2_0H1E_1_1Log.Encloses (Real.log (Z6_2_0H1Value ((1,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 1) ((1,1) : PairSlot)) (w := Z6_2_0H1E_1_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1E_1_1 : Ball := ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1E_1_1_sound : Z6_2_0H1E_1_1.Encloses (Foundation.entropyTerm (Z6_2_0H1Value ((1,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 1) ((1,1) : PairSlot)) Z6_2_0H1E_1_1Log_sound) (by decide +kernel)
def Z6_2_0H1E_0_2LogWitness : LogWitness := ⟨-3, 19924044508891583790197036118597, 12500000000000000000000000000000⟩
def Z6_2_0H1E_0_2Log : Ball := ⟨(-3226485833692046100593323447671 / 2000000000000000000000000000000), (84703294967 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1E_0_2Log_sound : Z6_2_0H1E_0_2Log.Encloses (Real.log (Z6_2_0H1Value ((0,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 1) ((0,2) : PairSlot)) (w := Z6_2_0H1E_0_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1E_0_2 : Ball := ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H1E_0_2_sound : Z6_2_0H1E_0_2.Encloses (Foundation.entropyTerm (Z6_2_0H1Value ((0,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 1) ((0,2) : PairSlot)) Z6_2_0H1E_0_2Log_sound) (by decide +kernel)
def Z6_2_0H1E_0_3LogWitness : LogWitness := ⟨-3, 4012399160127629130320676344027, 2500000000000000000000000000000⟩
def Z6_2_0H1E_0_3Log : Ball := ⟨(-160634291684602305029666172383581 / 100000000000000000000000000000000), (42351647483 / 50000000000000000000000000000000)⟩
lemma Z6_2_0H1E_0_3Log_sound : Z6_2_0H1E_0_3Log.Encloses (Real.log (Z6_2_0H1Value ((0,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_2_0Half_sound 1) ((0,3) : PairSlot)) (w := Z6_2_0H1E_0_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1E_0_3 : Ball := ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
lemma Z6_2_0H1E_0_3_sound : Z6_2_0H1E_0_3.Encloses (Foundation.entropyTerm (Z6_2_0H1Value ((0,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 1) ((0,3) : PairSlot)) Z6_2_0H1E_0_3Log_sound) (by decide +kernel)
def Z6_2_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 0 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 3, 0 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | 1, 1 => ⟨(8051438474921156001297838292377 / 25000000000000000000000000000000), (16964307637 / 100000000000000000000000000000000)⟩
  | 0, 2 => ⟨(32142323678894247471214709989819 / 100000000000000000000000000000000), (8438161133 / 50000000000000000000000000000000)⟩
  | 0, 3 => ⟨(32226444852149744429123998456101 / 100000000000000000000000000000000), (4248292889 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_2_0H1Terms_sound (a : PairSlot) :
    (Z6_2_0H1Terms a).Encloses (Foundation.entropyTerm (Z6_2_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((0,1) : PairSlot))) Z6_2_0H1E_0_2_sound Z6_2_0H1E_0_3_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((1,0) : PairSlot))) Z6_2_0H1E_1_1_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 Z6_2_0H1E_2_0_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 Z6_2_0H1E_3_0_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 1) ((5,5) : PairSlot)))
def Z6_2_0H1Entropy : Ball := ⟨(40235822740443151951467192515337 / 25000000000000000000000000000000), (84703295281 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1Entropy_sound : Z6_2_0H1Entropy.Encloses (Foundation.finiteEntropy Z6_2_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z6_2_0H1Value Z6_2_0H1Terms Z6_2_0H1Terms_sound) (by decide +kernel)
def Z6_2_0H1Mass : Ball := ⟨(49999999999999999999999999999999 / 50000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1Mass_sound : Z6_2_0H1Mass.Encloses (∑ a, Z6_2_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_2_0Half 1) Z6_2_0H1Value (Z6_2_0Half_sound 1)) (by decide +kernel)
def Z6_2_0H1MassTermLogWitness : LogWitness := ⟨-1, 49999999999999999999999999999999, 25000000000000000000000000000000⟩
def Z6_2_0H1MassTermLog : Ball := ⟨(-1 / 100000000000000000000000000000000), (1694065903 / 4000000000000000000000000000000)⟩
lemma Z6_2_0H1MassTermLog_sound : Z6_2_0H1MassTermLog.Encloses (Real.log ((∑ a, Z6_2_0H1Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z6_2_0H1Mass_sound) (w := Z6_2_0H1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_2_0H1MassTerm : Ball := ⟨(1 / 100000000000000000000000000000000), (5293955947 / 12500000000000000000000000000000)⟩
lemma Z6_2_0H1MassTerm_sound : Z6_2_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_2_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0H1Mass_sound) Z6_2_0H1MassTermLog_sound) (by decide +kernel)
def Z6_2_0H1H : Ball := ⟨(160943290961772607805868770061347 / 100000000000000000000000000000000), (127054942857 / 100000000000000000000000000000000)⟩
lemma Z6_2_0H1H_sound : Z6_2_0H1H.Encloses (homogeneousEntropy Z6_2_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z6_2_0H1Value Z6_2_0H1MassTerm_sound Z6_2_0H1Entropy_sound) (by decide +kernel)
def Z6_2_0H2Value (a : PairSlot) : ℝ := (halfLaw (shape 6 2 0) 2 a : ℝ)
def Z6_2_0H2E_0_0Log : Ball := .exact 0
lemma Z6_2_0H2E_0_0Log_sound : Z6_2_0H2E_0_0Log.Encloses (Real.log (Z6_2_0H2Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z6_2_0Half_sound 2) ((0,0) : PairSlot))
def Z6_2_0H2E_0_0 : Ball := ⟨0, 0⟩
lemma Z6_2_0H2E_0_0_sound : Z6_2_0H2E_0_0.Encloses (Foundation.entropyTerm (Z6_2_0H2Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_2_0Half_sound 2) ((0,0) : PairSlot)) Z6_2_0H2E_0_0Log_sound) (by decide +kernel)
def Z6_2_0H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z6_2_0H2Terms_sound (a : PairSlot) :
    (Z6_2_0H2Terms a).Encloses (Foundation.entropyTerm (Z6_2_0H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z6_2_0H2E_0_0_sound (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_2_0Half_sound 2) ((5,5) : PairSlot)))
def Z6_2_0H2Entropy : Ball := ⟨0, 0⟩
lemma Z6_2_0H2Entropy_sound : Z6_2_0H2Entropy.Encloses (Foundation.finiteEntropy Z6_2_0H2Value) := by
  exact contains_sound (entropyPair_enclosed Z6_2_0H2Value Z6_2_0H2Terms Z6_2_0H2Terms_sound) (by decide +kernel)
def Z6_2_0H2Mass : Ball := ⟨1, 0⟩
lemma Z6_2_0H2Mass_sound : Z6_2_0H2Mass.Encloses (∑ a, Z6_2_0H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_2_0Half 2) Z6_2_0H2Value (Z6_2_0Half_sound 2)) (by decide +kernel)
def Z6_2_0H2MassTermLog : Ball := .exact 0
lemma Z6_2_0H2MassTermLog_sound : Z6_2_0H2MassTermLog.Encloses (Real.log ((∑ a, Z6_2_0H2Value a))) := by
  exact log_exact_one_ball (Z6_2_0H2Mass_sound)
def Z6_2_0H2MassTerm : Ball := ⟨0, 0⟩
lemma Z6_2_0H2MassTerm_sound : Z6_2_0H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_2_0H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_2_0H2Mass_sound) Z6_2_0H2MassTermLog_sound) (by decide +kernel)
def Z6_2_0H2H : Ball := ⟨0, 0⟩
lemma Z6_2_0H2H_sound : Z6_2_0H2H.Encloses (homogeneousEntropy Z6_2_0H2Value) := by
  exact contains_sound (homogeneous_enclosed Z6_2_0H2Value Z6_2_0H2MassTerm_sound Z6_2_0H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
