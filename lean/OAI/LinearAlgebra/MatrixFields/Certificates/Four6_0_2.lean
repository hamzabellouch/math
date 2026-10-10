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
def Z6_0_2Raw (ij : PairSlot) : Ball :=
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
  | 2, 5 => w192
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w197
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w192
  | 5, 3 => w197
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z6_0_2Raw_sound_0 (j : Fin 6) :
    (Z6_0_2Raw (0,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (0,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (0,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (0,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (0,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (0,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (0,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 0 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_0_2Raw_sound_1 (j : Fin 6) :
    (Z6_0_2Raw (1,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (1,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (1,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (1,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (1,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (1,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (1,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 1 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_0_2Raw_sound_2 (j : Fin 6) :
    (Z6_0_2Raw (2,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (2,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (2,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (2,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (2,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (2,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (2,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 2 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 2 5 = (-166) := by decide +kernel
    rw [he]
    exact w192_sound
lemma Z6_0_2Raw_sound_3 (j : Fin 6) :
    (Z6_0_2Raw (3,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (3,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (3,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (3,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (3,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (3,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (3,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 3 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 3 5 = (94) := by decide +kernel
    rw [he]
    exact w197_sound
lemma Z6_0_2Raw_sound_4 (j : Fin 6) :
    (Z6_0_2Raw (4,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (4,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (4,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (4,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (4,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (4,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (4,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 4 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_0_2Raw_sound_5 (j : Fin 6) :
    (Z6_0_2Raw (5,j)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 j) : ℝ) := by
  fin_cases j
  · change (Z6_0_2Raw (5,0)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 0) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (5,1)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 1) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (5,2)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 2) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 2 = (-166) := by decide +kernel
    rw [he]
    exact w192_sound
  · change (Z6_0_2Raw (5,3)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 3) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 3 = (94) := by decide +kernel
    rw [he]
    exact w197_sound
  · change (Z6_0_2Raw (5,4)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 4) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z6_0_2Raw (5,5)).Encloses (weight (orderedPairInteger (shape 6 0 2) 5 5) : ℝ)
    have he : orderedPairInteger (shape 6 0 2) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z6_0_2Raw_sound (ij : PairSlot) :
    (Z6_0_2Raw ij).Encloses (weight (orderedPairInteger (shape 6 0 2) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z6_0_2Raw_sound_0 j) (Z6_0_2Raw_sound_1 j) (Z6_0_2Raw_sound_2 j) (Z6_0_2Raw_sound_3 j) (Z6_0_2Raw_sound_4 j) (Z6_0_2Raw_sound_5 j)
def Z6_0_2Den : Ball := ⟨(249298133952733756367028847637691 / 50000000000000000000000000000000), (253 / 50000000000000000000000000000000)⟩
lemma Z6_0_2Den_sound : Z6_0_2Den.Encloses
    (((orderedPairs (shape 6 0 2)).map (fun ij => weight (orderedPairInteger (shape 6 0 2) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 6 0 2)) Z6_0_2Raw
    (fun ij => weight (orderedPairInteger (shape 6 0 2) ij.1 ij.2))
    (fun ij _ => Z6_0_2Raw_sound ij)) (by decide +kernel)
lemma Z6_0_2Den_pos : 0 < Z6_0_2Den.lower := by decide +kernel
def Z6_0_2Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(19726120793130810407094355236181 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 3, 5 => ⟨(20245725524523564193484784547927 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 4, 4 => ⟨(20056307364691250798841720431783 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 5, 2 => ⟨(19726120793130810407094355236181 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 5, 3 => ⟨(20245725524523564193484784547927 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_0_2Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 6 0 2) →
    contains (.mul (Z6_0_2Raw (i,j)) (.inv Z6_0_2Den)) (Z6_0_2Probs (i,j)) = true := by
  decide +kernel
lemma Z6_0_2Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 6 0 2) → Z6_0_2Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z6_0_2Probs_sound (ij : PairSlot) :
    (Z6_0_2Probs ij).Encloses (zeroPairLaw (shape 6 0 2) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 6 0 2)
  · have hb := contains_sound (Ball.mul_sound (Z6_0_2Raw_sound ij)
      (Ball.inv_sound Z6_0_2Den_sound Z6_0_2Den_pos)) (Z6_0_2Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z6_0_2Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z6_0_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 6 0 2) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 6 0 2) then Z6_0_2Probs ij
  else Z6_0_2Probs (kappa ij.1, kappa ij.2)
lemma Z6_0_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z6_0_2Half w ij).Encloses (halfLaw (shape 6 0 2) w ij : ℝ) := by
  have hp : positive (shape 6 0 2) = false := by decide +kernel
  simp only [Z6_0_2Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z6_0_2Probs_sound _
  · exact Z6_0_2Probs_sound _

def Z6_0_2Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 6 0 2) a.1 a.2 : ℝ)
def Z6_0_2E_2_5LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2E_2_5Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2E_2_5Log_sound : Z6_0_2E_2_5Log.Encloses (Real.log (Z6_0_2Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2Probs_sound ((2,5) : PairSlot)) (w := Z6_0_2E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2E_2_5 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2E_2_5_sound : Z6_0_2E_2_5.Encloses (Foundation.entropyTerm (Z6_0_2Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2Probs_sound ((2,5) : PairSlot)) Z6_0_2E_2_5Log_sound) (by decide +kernel)
def Z6_0_2E_3_5LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2E_3_5Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2E_3_5Log_sound : Z6_0_2E_3_5Log.Encloses (Real.log (Z6_0_2Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2Probs_sound ((3,5) : PairSlot)) (w := Z6_0_2E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2E_3_5 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2E_3_5_sound : Z6_0_2E_3_5.Encloses (Foundation.entropyTerm (Z6_0_2Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2Probs_sound ((3,5) : PairSlot)) Z6_0_2E_3_5Log_sound) (by decide +kernel)
def Z6_0_2E_4_4LogWitness : LogWitness := ⟨-3, 20056307364691250798841720431783, 12500000000000000000000000000000⟩
def Z6_0_2E_4_4Log : Ball := ⟨(-160662649992587437116070072559717 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_0_2E_4_4Log_sound : Z6_0_2E_4_4Log.Encloses (Real.log (Z6_0_2Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2Probs_sound ((4,4) : PairSlot)) (w := Z6_0_2E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2E_4_4 : Ball := ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
lemma Z6_0_2E_4_4_sound : Z6_0_2E_4_4.Encloses (Foundation.entropyTerm (Z6_0_2Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2Probs_sound ((4,4) : PairSlot)) Z6_0_2E_4_4Log_sound) (by decide +kernel)
def Z6_0_2E_5_2LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2E_5_2Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2E_5_2Log_sound : Z6_0_2E_5_2Log.Encloses (Real.log (Z6_0_2Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2Probs_sound ((5,2) : PairSlot)) (w := Z6_0_2E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2E_5_2 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2E_5_2_sound : Z6_0_2E_5_2.Encloses (Foundation.entropyTerm (Z6_0_2Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2Probs_sound ((5,2) : PairSlot)) Z6_0_2E_5_2Log_sound) (by decide +kernel)
def Z6_0_2E_5_3LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2E_5_3Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2E_5_3Log_sound : Z6_0_2E_5_3Log.Encloses (Real.log (Z6_0_2Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2Probs_sound ((5,3) : PairSlot)) (w := Z6_0_2E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2E_5_3 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2E_5_3_sound : Z6_0_2E_5_3.Encloses (Foundation.entropyTerm (Z6_0_2Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2Probs_sound ((5,3) : PairSlot)) Z6_0_2E_5_3Log_sound) (by decide +kernel)
def Z6_0_2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
  | 5, 2 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_0_2Terms_sound (a : PairSlot) :
    (Z6_0_2Terms a).Encloses (Foundation.entropyTerm (Z6_0_2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((2,4) : PairSlot))) Z6_0_2E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((3,4) : PairSlot))) Z6_0_2E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((4,3) : PairSlot))) Z6_0_2E_4_4_sound (entropyTerm_zero_ball (Z6_0_2Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z6_0_2Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((5,1) : PairSlot))) Z6_0_2E_5_2_sound Z6_0_2E_5_3_sound (entropyTerm_zero_ball (Z6_0_2Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z6_0_2Probs_sound ((5,5) : PairSlot)))
def Z6_0_2Entropy : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (84703295277 / 100000000000000000000000000000000)⟩
lemma Z6_0_2Entropy_sound : Z6_0_2Entropy.Encloses (Foundation.finiteEntropy Z6_0_2Value) := by
  exact contains_sound (entropyPair_enclosed Z6_0_2Value Z6_0_2Terms Z6_0_2Terms_sound) (by decide +kernel)
def Z6_0_2Labels : Ball := ⟨(49484222105438999677313478916931 / 20000000000000000000000000000000), (443250503 / 500000000000000000000000000000)⟩
lemma Z6_0_2Labels_sound : Z6_0_2Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 6 0 2) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z6_0_2Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z6_0_2Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z6_0_2Four : Ball := ⟨(102089512022563333850328871447177 / 25000000000000000000000000000000), (173353395877 / 100000000000000000000000000000000)⟩
lemma Z6_0_2Four_sound : Z6_0_2Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 6 0 2)) := by
  exact contains_sound (Ball.add_sound Z6_0_2Entropy_sound Z6_0_2Labels_sound) (by decide +kernel)
def Z6_0_2H0Value (a : PairSlot) : ℝ := (halfLaw (shape 6 0 2) 0 a : ℝ)
def Z6_0_2H0E_2_5LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2H0E_2_5Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H0E_2_5Log_sound : Z6_0_2H0E_2_5Log.Encloses (Real.log (Z6_0_2H0Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 0) ((2,5) : PairSlot)) (w := Z6_0_2H0E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0E_2_5 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H0E_2_5_sound : Z6_0_2H0E_2_5.Encloses (Foundation.entropyTerm (Z6_0_2H0Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 0) ((2,5) : PairSlot)) Z6_0_2H0E_2_5Log_sound) (by decide +kernel)
def Z6_0_2H0E_3_5LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2H0E_3_5Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H0E_3_5Log_sound : Z6_0_2H0E_3_5Log.Encloses (Real.log (Z6_0_2H0Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 0) ((3,5) : PairSlot)) (w := Z6_0_2H0E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0E_3_5 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H0E_3_5_sound : Z6_0_2H0E_3_5.Encloses (Foundation.entropyTerm (Z6_0_2H0Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 0) ((3,5) : PairSlot)) Z6_0_2H0E_3_5Log_sound) (by decide +kernel)
def Z6_0_2H0E_4_4LogWitness : LogWitness := ⟨-3, 20056307364691250798841720431783, 12500000000000000000000000000000⟩
def Z6_0_2H0E_4_4Log : Ball := ⟨(-160662649992587437116070072559717 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H0E_4_4Log_sound : Z6_0_2H0E_4_4Log.Encloses (Real.log (Z6_0_2H0Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 0) ((4,4) : PairSlot)) (w := Z6_0_2H0E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0E_4_4 : Ball := ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H0E_4_4_sound : Z6_0_2H0E_4_4.Encloses (Foundation.entropyTerm (Z6_0_2H0Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 0) ((4,4) : PairSlot)) Z6_0_2H0E_4_4Log_sound) (by decide +kernel)
def Z6_0_2H0E_5_2LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2H0E_5_2Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H0E_5_2Log_sound : Z6_0_2H0E_5_2Log.Encloses (Real.log (Z6_0_2H0Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 0) ((5,2) : PairSlot)) (w := Z6_0_2H0E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0E_5_2 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H0E_5_2_sound : Z6_0_2H0E_5_2.Encloses (Foundation.entropyTerm (Z6_0_2H0Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 0) ((5,2) : PairSlot)) Z6_0_2H0E_5_2Log_sound) (by decide +kernel)
def Z6_0_2H0E_5_3LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2H0E_5_3Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H0E_5_3Log_sound : Z6_0_2H0E_5_3Log.Encloses (Real.log (Z6_0_2H0Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 0) ((5,3) : PairSlot)) (w := Z6_0_2H0E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0E_5_3 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H0E_5_3_sound : Z6_0_2H0E_5_3.Encloses (Foundation.entropyTerm (Z6_0_2H0Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 0) ((5,3) : PairSlot)) Z6_0_2H0E_5_3Log_sound) (by decide +kernel)
def Z6_0_2H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
  | 5, 2 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_0_2H0Terms_sound (a : PairSlot) :
    (Z6_0_2H0Terms a).Encloses (Foundation.entropyTerm (Z6_0_2H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((2,4) : PairSlot))) Z6_0_2H0E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((3,4) : PairSlot))) Z6_0_2H0E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((4,3) : PairSlot))) Z6_0_2H0E_4_4_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((5,1) : PairSlot))) Z6_0_2H0E_5_2_sound Z6_0_2H0E_5_3_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 0) ((5,5) : PairSlot)))
def Z6_0_2H0Entropy : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (84703295277 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H0Entropy_sound : Z6_0_2H0Entropy.Encloses (Foundation.finiteEntropy Z6_0_2H0Value) := by
  exact contains_sound (entropyPair_enclosed Z6_0_2H0Value Z6_0_2H0Terms Z6_0_2H0Terms_sound) (by decide +kernel)
def Z6_0_2H0Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (207 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H0Mass_sound : Z6_0_2H0Mass.Encloses (∑ a, Z6_0_2H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_0_2Half 0) Z6_0_2H0Value (Z6_0_2Half_sound 0)) (by decide +kernel)
def Z6_0_2H0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z6_0_2H0MassTermLog : Ball := ⟨0, (42351647573 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H0MassTermLog_sound : Z6_0_2H0MassTermLog.Encloses (Real.log ((∑ a, Z6_0_2H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2H0Mass_sound) (w := Z6_0_2H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H0MassTerm : Ball := ⟨0, (21175823787 / 50000000000000000000000000000000)⟩
lemma Z6_0_2H0MassTerm_sound : Z6_0_2H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_0_2H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2H0Mass_sound) Z6_0_2H0MassTermLog_sound) (by decide +kernel)
def Z6_0_2H0H : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (127054942851 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H0H_sound : Z6_0_2H0H.Encloses (homogeneousEntropy Z6_0_2H0Value) := by
  exact contains_sound (homogeneous_enclosed Z6_0_2H0Value Z6_0_2H0MassTerm_sound Z6_0_2H0Entropy_sound) (by decide +kernel)
def Z6_0_2H1Value (a : PairSlot) : ℝ := (halfLaw (shape 6 0 2) 1 a : ℝ)
def Z6_0_2H1E_0_0Log : Ball := .exact 0
lemma Z6_0_2H1E_0_0Log_sound : Z6_0_2H1E_0_0Log.Encloses (Real.log (Z6_0_2H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z6_0_2Half_sound 1) ((0,0) : PairSlot))
def Z6_0_2H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z6_0_2H1E_0_0_sound : Z6_0_2H1E_0_0.Encloses (Foundation.entropyTerm (Z6_0_2H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 1) ((0,0) : PairSlot)) Z6_0_2H1E_0_0Log_sound) (by decide +kernel)
def Z6_0_2H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z6_0_2H1Terms_sound (a : PairSlot) :
    (Z6_0_2H1Terms a).Encloses (Foundation.entropyTerm (Z6_0_2H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z6_0_2H1E_0_0_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 1) ((5,5) : PairSlot)))
def Z6_0_2H1Entropy : Ball := ⟨0, 0⟩
lemma Z6_0_2H1Entropy_sound : Z6_0_2H1Entropy.Encloses (Foundation.finiteEntropy Z6_0_2H1Value) := by
  exact contains_sound (entropyPair_enclosed Z6_0_2H1Value Z6_0_2H1Terms Z6_0_2H1Terms_sound) (by decide +kernel)
def Z6_0_2H1Mass : Ball := ⟨1, 0⟩
lemma Z6_0_2H1Mass_sound : Z6_0_2H1Mass.Encloses (∑ a, Z6_0_2H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_0_2Half 1) Z6_0_2H1Value (Z6_0_2Half_sound 1)) (by decide +kernel)
def Z6_0_2H1MassTermLog : Ball := .exact 0
lemma Z6_0_2H1MassTermLog_sound : Z6_0_2H1MassTermLog.Encloses (Real.log ((∑ a, Z6_0_2H1Value a))) := by
  exact log_exact_one_ball (Z6_0_2H1Mass_sound)
def Z6_0_2H1MassTerm : Ball := ⟨0, 0⟩
lemma Z6_0_2H1MassTerm_sound : Z6_0_2H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_0_2H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2H1Mass_sound) Z6_0_2H1MassTermLog_sound) (by decide +kernel)
def Z6_0_2H1H : Ball := ⟨0, 0⟩
lemma Z6_0_2H1H_sound : Z6_0_2H1H.Encloses (homogeneousEntropy Z6_0_2H1Value) := by
  exact contains_sound (homogeneous_enclosed Z6_0_2H1Value Z6_0_2H1MassTerm_sound Z6_0_2H1Entropy_sound) (by decide +kernel)
def Z6_0_2H2Value (a : PairSlot) : ℝ := (halfLaw (shape 6 0 2) 2 a : ℝ)
def Z6_0_2H2E_2_0LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2H2E_2_0Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H2E_2_0Log_sound : Z6_0_2H2E_2_0Log.Encloses (Real.log (Z6_0_2H2Value ((2,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 2) ((2,0) : PairSlot)) (w := Z6_0_2H2E_2_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2E_2_0 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H2E_2_0_sound : Z6_0_2H2E_2_0.Encloses (Foundation.entropyTerm (Z6_0_2H2Value ((2,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 2) ((2,0) : PairSlot)) Z6_0_2H2E_2_0Log_sound) (by decide +kernel)
def Z6_0_2H2E_3_0LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2H2E_3_0Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H2E_3_0Log_sound : Z6_0_2H2E_3_0Log.Encloses (Real.log (Z6_0_2H2Value ((3,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 2) ((3,0) : PairSlot)) (w := Z6_0_2H2E_3_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2E_3_0 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H2E_3_0_sound : Z6_0_2H2E_3_0.Encloses (Foundation.entropyTerm (Z6_0_2H2Value ((3,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 2) ((3,0) : PairSlot)) Z6_0_2H2E_3_0Log_sound) (by decide +kernel)
def Z6_0_2H2E_1_1LogWitness : LogWitness := ⟨-3, 20056307364691250798841720431783, 12500000000000000000000000000000⟩
def Z6_0_2H2E_1_1Log : Ball := ⟨(-160662649992587437116070072559717 / 100000000000000000000000000000000), (21175823709 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H2E_1_1Log_sound : Z6_0_2H2E_1_1Log.Encloses (Real.log (Z6_0_2H2Value ((1,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 2) ((1,1) : PairSlot)) (w := Z6_0_2H2E_1_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2E_1_1 : Ball := ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H2E_1_1_sound : Z6_0_2H2E_1_1.Encloses (Foundation.entropyTerm (Z6_0_2H2Value ((1,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 2) ((1,1) : PairSlot)) Z6_0_2H2E_1_1Log_sound) (by decide +kernel)
def Z6_0_2H2E_0_2LogWitness : LogWitness := ⟨-3, 19726120793130810407094355236181, 12500000000000000000000000000000⟩
def Z6_0_2H2E_0_2Log : Ball := ⟨(-6492905999703497484642802902389 / 4000000000000000000000000000000), (16940658993 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H2E_0_2Log_sound : Z6_0_2H2E_0_2Log.Encloses (Real.log (Z6_0_2H2Value ((0,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 2) ((0,2) : PairSlot)) (w := Z6_0_2H2E_0_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2E_0_2 : Ball := ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H2E_0_2_sound : Z6_0_2H2E_0_2.Encloses (Foundation.entropyTerm (Z6_0_2H2Value ((0,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 2) ((0,2) : PairSlot)) Z6_0_2H2E_0_2Log_sound) (by decide +kernel)
def Z6_0_2H2E_0_3LogWitness : LogWitness := ⟨-3, 20245725524523564193484784547927, 12500000000000000000000000000000⟩
def Z6_0_2H2E_0_3Log : Ball := ⟨(-79861324996293718558035036279851 / 50000000000000000000000000000000), (21175823741 / 25000000000000000000000000000000)⟩
lemma Z6_0_2H2E_0_3Log_sound : Z6_0_2H2E_0_3Log.Encloses (Real.log (Z6_0_2H2Value ((0,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z6_0_2Half_sound 2) ((0,3) : PairSlot)) (w := Z6_0_2H2E_0_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2E_0_3 : Ball := ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
lemma Z6_0_2H2E_0_3_sound : Z6_0_2H2E_0_3.Encloses (Foundation.entropyTerm (Z6_0_2H2Value ((0,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z6_0_2Half_sound 2) ((0,3) : PairSlot)) Z6_0_2H2E_0_3Log_sound) (by decide +kernel)
def Z6_0_2H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 0 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 3, 0 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | 1, 1 => ⟨(32222994902771441455963269141339 / 100000000000000000000000000000000), (3397670639 / 20000000000000000000000000000000)⟩
  | 0, 2 => ⟨(4002495251518592288865068392969 / 12500000000000000000000000000000), (4177168589 / 25000000000000000000000000000000)⟩
  | 0, 3 => ⟨(6467401863598941893694372777521 / 20000000000000000000000000000000), (3429759337 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z6_0_2H2Terms_sound (a : PairSlot) :
    (Z6_0_2H2Terms a).Encloses (Foundation.entropyTerm (Z6_0_2H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((0,1) : PairSlot))) Z6_0_2H2E_0_2_sound Z6_0_2H2E_0_3_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((1,0) : PairSlot))) Z6_0_2H2E_1_1_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 Z6_0_2H2E_2_0_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 Z6_0_2H2E_3_0_sound (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z6_0_2Half_sound 2) ((5,5) : PairSlot)))
def Z6_0_2H2Entropy : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (84703295277 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H2Entropy_sound : Z6_0_2H2Entropy.Encloses (Foundation.finiteEntropy Z6_0_2H2Value) := by
  exact contains_sound (entropyPair_enclosed Z6_0_2H2Value Z6_0_2H2Terms Z6_0_2H2Terms_sound) (by decide +kernel)
def Z6_0_2H2Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (207 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H2Mass_sound : Z6_0_2H2Mass.Encloses (∑ a, Z6_0_2H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z6_0_2Half 2) Z6_0_2H2Value (Z6_0_2Half_sound 2)) (by decide +kernel)
def Z6_0_2H2MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z6_0_2H2MassTermLog : Ball := ⟨0, (42351647573 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H2MassTermLog_sound : Z6_0_2H2MassTermLog.Encloses (Real.log ((∑ a, Z6_0_2H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z6_0_2H2Mass_sound) (w := Z6_0_2H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z6_0_2H2MassTerm : Ball := ⟨0, (21175823787 / 50000000000000000000000000000000)⟩
lemma Z6_0_2H2MassTerm_sound : Z6_0_2H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z6_0_2H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z6_0_2H2Mass_sound) Z6_0_2H2MassTermLog_sound) (by decide +kernel)
def Z6_0_2H2H : Ball := ⟨(160936937563058337014748091204053 / 100000000000000000000000000000000), (127054942851 / 100000000000000000000000000000000)⟩
lemma Z6_0_2H2H_sound : Z6_0_2H2H.Encloses (homogeneousEntropy Z6_0_2H2Value) := by
  exact contains_sound (homogeneous_enclosed Z6_0_2H2Value Z6_0_2H2MassTerm_sound Z6_0_2H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
