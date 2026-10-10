import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_3_12

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z2_0_6Raw (ij : PairSlot) : Ball :=
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
  | 2, 5 => w136
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w54
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w195
  | 5, 2 => w136
  | 5, 3 => w54
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z2_0_6Raw_sound_0 (j : Fin 6) :
    (Z2_0_6Raw (0,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (0,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (0,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 0 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_1 (j : Fin 6) :
    (Z2_0_6Raw (1,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (1,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (1,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 1 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_2 (j : Fin 6) :
    (Z2_0_6Raw (2,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (2,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (2,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 2 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 2 5 = (-9623) := by decide +kernel
    rw [he]
    exact w136_sound
lemma Z2_0_6Raw_sound_3 (j : Fin 6) :
    (Z2_0_6Raw (3,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (3,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (3,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 3 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 3 5 = (-34674) := by decide +kernel
    rw [he]
    exact w54_sound
lemma Z2_0_6Raw_sound_4 (j : Fin 6) :
    (Z2_0_6Raw (4,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (4,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (4,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 4 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound_5 (j : Fin 6) :
    (Z2_0_6Raw (5,j)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 j) : ℝ) := by
  fin_cases j
  · change (Z2_0_6Raw (5,0)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 0) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,1)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 1) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,2)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 2) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 2 = (-9623) := by decide +kernel
    rw [he]
    exact w136_sound
  · change (Z2_0_6Raw (5,3)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 3) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 3 = (-34674) := by decide +kernel
    rw [he]
    exact w54_sound
  · change (Z2_0_6Raw (5,4)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 4) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z2_0_6Raw (5,5)).Encloses (weight (orderedPairInteger (shape 2 0 6) 5 5) : ℝ)
    have he : orderedPairInteger (shape 2 0 6) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z2_0_6Raw_sound (ij : PairSlot) :
    (Z2_0_6Raw ij).Encloses (weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z2_0_6Raw_sound_0 j) (Z2_0_6Raw_sound_1 j) (Z2_0_6Raw_sound_2 j) (Z2_0_6Raw_sound_3 j) (Z2_0_6Raw_sound_4 j) (Z2_0_6Raw_sound_5 j)
def Z2_0_6Den : Ball := ⟨(730569027616488524394965632979 / 400000000000000000000000000000), (3 / 3125000000000000000000000000000)⟩
lemma Z2_0_6Den_sound : Z2_0_6Den.Encloses
    (((orderedPairs (shape 2 0 6)).map (fun ij => weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 2 0 6)) Z2_0_6Raw
    (fun ij => weight (orderedPairInteger (shape 2 0 6) ij.1 ij.2))
    (fun ij _ => Z2_0_6Raw_sound ij)) (by decide +kernel)
lemma Z2_0_6Den_pos : 0 < Z2_0_6Den.lower := by decide +kernel
def Z2_0_6Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 2, 5 => ⟨(10457964405071752630514678883453 / 50000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1708150169428319858018410671529 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 4 => ⟨(5475184204085634976190446312313 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 5, 2 => ⟨(10457964405071752630514678883453 / 50000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1708150169428319858018410671529 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z2_0_6Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 2 0 6) →
    contains (.mul (Z2_0_6Raw (i,j)) (.inv Z2_0_6Den)) (Z2_0_6Probs (i,j)) = true := by
  decide +kernel
lemma Z2_0_6Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 2 0 6) → Z2_0_6Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z2_0_6Probs_sound (ij : PairSlot) :
    (Z2_0_6Probs ij).Encloses (zeroPairLaw (shape 2 0 6) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 2 0 6)
  · have hb := contains_sound (Ball.mul_sound (Z2_0_6Raw_sound ij)
      (Ball.inv_sound Z2_0_6Den_sound Z2_0_6Den_pos)) (Z2_0_6Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z2_0_6Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z2_0_6Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 2 0 6) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 2 0 6) then Z2_0_6Probs ij
  else Z2_0_6Probs (kappa ij.1, kappa ij.2)
lemma Z2_0_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z2_0_6Half w ij).Encloses (halfLaw (shape 2 0 6) w ij : ℝ) := by
  have hp : positive (shape 2 0 6) = false := by decide +kernel
  simp only [Z2_0_6Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z2_0_6Probs_sound _
  · exact Z2_0_6Probs_sound _

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
def Z2_0_6Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 2 0 6) a.1 a.2 : ℝ)
def Z2_0_6E_2_5LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6E_2_5Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6E_2_5Log_sound : Z2_0_6E_2_5Log.Encloses (Real.log (Z2_0_6Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((2,5) : PairSlot)) (w := Z2_0_6E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6E_2_5 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6E_2_5_sound : Z2_0_6E_2_5.Encloses (Foundation.entropyTerm (Z2_0_6Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((2,5) : PairSlot)) Z2_0_6E_2_5Log_sound) (by decide +kernel)
def Z2_0_6E_3_5LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6E_3_5Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6E_3_5Log_sound : Z2_0_6E_3_5Log.Encloses (Real.log (Z2_0_6Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((3,5) : PairSlot)) (w := Z2_0_6E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6E_3_5 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6E_3_5_sound : Z2_0_6E_3_5.Encloses (Foundation.entropyTerm (Z2_0_6Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((3,5) : PairSlot)) Z2_0_6E_3_5Log_sound) (by decide +kernel)
def Z2_0_6E_4_4LogWitness : LogWitness := ⟨-1, 5475184204085634976190446312313, 5000000000000000000000000000000⟩
def Z2_0_6E_4_4Log : Ball := ⟨(-6023591732755962787186797906847 / 10000000000000000000000000000000), (2117582371 / 5000000000000000000000000000000)⟩
lemma Z2_0_6E_4_4Log_sound : Z2_0_6E_4_4Log.Encloses (Real.log (Z2_0_6Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((4,4) : PairSlot)) (w := Z2_0_6E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6E_4_4 : Ball := ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
lemma Z2_0_6E_4_4_sound : Z2_0_6E_4_4.Encloses (Foundation.entropyTerm (Z2_0_6Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((4,4) : PairSlot)) Z2_0_6E_4_4Log_sound) (by decide +kernel)
def Z2_0_6E_5_2LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6E_5_2Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6E_5_2Log_sound : Z2_0_6E_5_2Log.Encloses (Real.log (Z2_0_6Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((5,2) : PairSlot)) (w := Z2_0_6E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6E_5_2 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6E_5_2_sound : Z2_0_6E_5_2.Encloses (Foundation.entropyTerm (Z2_0_6Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((5,2) : PairSlot)) Z2_0_6E_5_2Log_sound) (by decide +kernel)
def Z2_0_6E_5_3LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6E_5_3Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6E_5_3Log_sound : Z2_0_6E_5_3Log.Encloses (Real.log (Z2_0_6Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6Probs_sound ((5,3) : PairSlot)) (w := Z2_0_6E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6E_5_3 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6E_5_3_sound : Z2_0_6E_5_3.Encloses (Foundation.entropyTerm (Z2_0_6Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6Probs_sound ((5,3) : PairSlot)) Z2_0_6E_5_3Log_sound) (by decide +kernel)
def Z2_0_6Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z2_0_6Terms_sound (a : PairSlot) :
    (Z2_0_6Terms a).Encloses (Foundation.entropyTerm (Z2_0_6Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((2,4) : PairSlot))) Z2_0_6E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,3) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((3,4) : PairSlot))) Z2_0_6E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,1) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,3) : PairSlot))) Z2_0_6E_4_4_sound (entropyTerm_zero_ball (Z2_0_6Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,0) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,1) : PairSlot))) Z2_0_6E_5_2_sound Z2_0_6E_5_3_sound (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z2_0_6Probs_sound ((5,5) : PairSlot)))
def Z2_0_6Entropy : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (1273705543 / 2000000000000000000000000000000)⟩
lemma Z2_0_6Entropy_sound : Z2_0_6Entropy.Encloses (Foundation.finiteEntropy Z2_0_6Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6Value Z2_0_6Terms Z2_0_6Terms_sound) (by decide +kernel)
def Z2_0_6Labels : Ball := ⟨(389161104745575982126957038149479 / 100000000000000000000000000000000), (126897136649 / 100000000000000000000000000000000)⟩
lemma Z2_0_6Labels_sound : Z2_0_6Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 2 0 6) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z2_0_6Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z2_0_6Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z2_0_6Four : Ball := ⟨(250748749228044656387794087131641 / 50000000000000000000000000000000), (190582413799 / 100000000000000000000000000000000)⟩
lemma Z2_0_6Four_sound : Z2_0_6Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 2 0 6)) := by
  exact contains_sound (Ball.add_sound Z2_0_6Entropy_sound Z2_0_6Labels_sound) (by decide +kernel)
def Z2_0_6H0Value (a : PairSlot) : ℝ := (halfLaw (shape 2 0 6) 0 a : ℝ)
def Z2_0_6H0E_2_0LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H0E_2_0Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6H0E_2_0Log_sound : Z2_0_6H0E_2_0Log.Encloses (Real.log (Z2_0_6H0Value ((2,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 0) ((2,0) : PairSlot)) (w := Z2_0_6H0E_2_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0E_2_0 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H0E_2_0_sound : Z2_0_6H0E_2_0.Encloses (Foundation.entropyTerm (Z2_0_6H0Value ((2,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 0) ((2,0) : PairSlot)) Z2_0_6H0E_2_0Log_sound) (by decide +kernel)
def Z2_0_6H0E_3_0LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H0E_3_0Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H0E_3_0Log_sound : Z2_0_6H0E_3_0Log.Encloses (Real.log (Z2_0_6H0Value ((3,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 0) ((3,0) : PairSlot)) (w := Z2_0_6H0E_3_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0E_3_0 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H0E_3_0_sound : Z2_0_6H0E_3_0.Encloses (Foundation.entropyTerm (Z2_0_6H0Value ((3,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 0) ((3,0) : PairSlot)) Z2_0_6H0E_3_0Log_sound) (by decide +kernel)
def Z2_0_6H0E_1_1LogWitness : LogWitness := ⟨-1, 5475184204085634976190446312313, 5000000000000000000000000000000⟩
def Z2_0_6H0E_1_1Log : Ball := ⟨(-6023591732755962787186797906847 / 10000000000000000000000000000000), (2117582371 / 5000000000000000000000000000000)⟩
lemma Z2_0_6H0E_1_1Log_sound : Z2_0_6H0E_1_1Log.Encloses (Real.log (Z2_0_6H0Value ((1,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 0) ((1,1) : PairSlot)) (w := Z2_0_6H0E_1_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0E_1_1 : Ball := ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
lemma Z2_0_6H0E_1_1_sound : Z2_0_6H0E_1_1.Encloses (Foundation.entropyTerm (Z2_0_6H0Value ((1,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 0) ((1,1) : PairSlot)) Z2_0_6H0E_1_1Log_sound) (by decide +kernel)
def Z2_0_6H0E_0_2LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H0E_0_2Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6H0E_0_2Log_sound : Z2_0_6H0E_0_2Log.Encloses (Real.log (Z2_0_6H0Value ((0,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 0) ((0,2) : PairSlot)) (w := Z2_0_6H0E_0_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0E_0_2 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H0E_0_2_sound : Z2_0_6H0E_0_2.Encloses (Foundation.entropyTerm (Z2_0_6H0Value ((0,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 0) ((0,2) : PairSlot)) Z2_0_6H0E_0_2Log_sound) (by decide +kernel)
def Z2_0_6H0E_0_3LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H0E_0_3Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H0E_0_3Log_sound : Z2_0_6H0E_0_3Log.Encloses (Real.log (Z2_0_6H0Value ((0,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 0) ((0,3) : PairSlot)) (w := Z2_0_6H0E_0_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0E_0_3 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H0E_0_3_sound : Z2_0_6H0E_0_3.Encloses (Foundation.entropyTerm (Z2_0_6H0Value ((0,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 0) ((0,3) : PairSlot)) Z2_0_6H0E_0_3Log_sound) (by decide +kernel)
def Z2_0_6H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 0 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 3, 0 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | 1, 1 => ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
  | 0, 2 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 0, 3 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z2_0_6H0Terms_sound (a : PairSlot) :
    (Z2_0_6H0Terms a).Encloses (Foundation.entropyTerm (Z2_0_6H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((0,1) : PairSlot))) Z2_0_6H0E_0_2_sound Z2_0_6H0E_0_3_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((1,0) : PairSlot))) Z2_0_6H0E_1_1_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 Z2_0_6H0E_2_0_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 Z2_0_6H0E_3_0_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 0) ((5,5) : PairSlot)))
def Z2_0_6H0Entropy : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (1273705543 / 2000000000000000000000000000000)⟩
lemma Z2_0_6H0Entropy_sound : Z2_0_6H0Entropy.Encloses (Foundation.finiteEntropy Z2_0_6H0Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6H0Value Z2_0_6H0Terms Z2_0_6H0Terms_sound) (by decide +kernel)
def Z2_0_6H0Mass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
lemma Z2_0_6H0Mass_sound : Z2_0_6H0Mass.Encloses (∑ a, Z2_0_6H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z2_0_6Half 0) Z2_0_6H0Value (Z2_0_6Half_sound 0)) (by decide +kernel)
def Z2_0_6H0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z2_0_6H0MassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
lemma Z2_0_6H0MassTermLog_sound : Z2_0_6H0MassTermLog.Encloses (Real.log ((∑ a, Z2_0_6H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6H0Mass_sound) (w := Z2_0_6H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H0MassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H0MassTerm_sound : Z2_0_6H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z2_0_6H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6H0Mass_sound) Z2_0_6H0MassTermLog_sound) (by decide +kernel)
def Z2_0_6H0H : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (84861100943 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H0H_sound : Z2_0_6H0H.Encloses (homogeneousEntropy Z2_0_6H0Value) := by
  exact contains_sound (homogeneous_enclosed Z2_0_6H0Value Z2_0_6H0MassTerm_sound Z2_0_6H0Entropy_sound) (by decide +kernel)
def Z2_0_6H1Value (a : PairSlot) : ℝ := (halfLaw (shape 2 0 6) 1 a : ℝ)
def Z2_0_6H1E_0_0Log : Ball := .exact 0
lemma Z2_0_6H1E_0_0Log_sound : Z2_0_6H1E_0_0Log.Encloses (Real.log (Z2_0_6H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z2_0_6Half_sound 1) ((0,0) : PairSlot))
def Z2_0_6H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z2_0_6H1E_0_0_sound : Z2_0_6H1E_0_0.Encloses (Foundation.entropyTerm (Z2_0_6H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 1) ((0,0) : PairSlot)) Z2_0_6H1E_0_0Log_sound) (by decide +kernel)
def Z2_0_6H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z2_0_6H1Terms_sound (a : PairSlot) :
    (Z2_0_6H1Terms a).Encloses (Foundation.entropyTerm (Z2_0_6H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z2_0_6H1E_0_0_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 1) ((5,5) : PairSlot)))
def Z2_0_6H1Entropy : Ball := ⟨0, 0⟩
lemma Z2_0_6H1Entropy_sound : Z2_0_6H1Entropy.Encloses (Foundation.finiteEntropy Z2_0_6H1Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6H1Value Z2_0_6H1Terms Z2_0_6H1Terms_sound) (by decide +kernel)
def Z2_0_6H1Mass : Ball := ⟨1, 0⟩
lemma Z2_0_6H1Mass_sound : Z2_0_6H1Mass.Encloses (∑ a, Z2_0_6H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z2_0_6Half 1) Z2_0_6H1Value (Z2_0_6Half_sound 1)) (by decide +kernel)
def Z2_0_6H1MassTermLog : Ball := .exact 0
lemma Z2_0_6H1MassTermLog_sound : Z2_0_6H1MassTermLog.Encloses (Real.log ((∑ a, Z2_0_6H1Value a))) := by
  exact log_exact_one_ball (Z2_0_6H1Mass_sound)
def Z2_0_6H1MassTerm : Ball := ⟨0, 0⟩
lemma Z2_0_6H1MassTerm_sound : Z2_0_6H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z2_0_6H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6H1Mass_sound) Z2_0_6H1MassTermLog_sound) (by decide +kernel)
def Z2_0_6H1H : Ball := ⟨0, 0⟩
lemma Z2_0_6H1H_sound : Z2_0_6H1H.Encloses (homogeneousEntropy Z2_0_6H1Value) := by
  exact contains_sound (homogeneous_enclosed Z2_0_6H1Value Z2_0_6H1MassTerm_sound Z2_0_6H1Entropy_sound) (by decide +kernel)
def Z2_0_6H2Value (a : PairSlot) : ℝ := (halfLaw (shape 2 0 6) 2 a : ℝ)
def Z2_0_6H2E_2_5LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H2E_2_5Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6H2E_2_5Log_sound : Z2_0_6H2E_2_5Log.Encloses (Real.log (Z2_0_6H2Value ((2,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((2,5) : PairSlot)) (w := Z2_0_6H2E_2_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2E_2_5 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H2E_2_5_sound : Z2_0_6H2E_2_5.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((2,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((2,5) : PairSlot)) Z2_0_6H2E_2_5Log_sound) (by decide +kernel)
def Z2_0_6H2E_3_5LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H2E_3_5Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H2E_3_5Log_sound : Z2_0_6H2E_3_5Log.Encloses (Real.log (Z2_0_6H2Value ((3,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((3,5) : PairSlot)) (w := Z2_0_6H2E_3_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2E_3_5 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H2E_3_5_sound : Z2_0_6H2E_3_5.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((3,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((3,5) : PairSlot)) Z2_0_6H2E_3_5Log_sound) (by decide +kernel)
def Z2_0_6H2E_4_4LogWitness : LogWitness := ⟨-1, 5475184204085634976190446312313, 5000000000000000000000000000000⟩
def Z2_0_6H2E_4_4Log : Ball := ⟨(-6023591732755962787186797906847 / 10000000000000000000000000000000), (2117582371 / 5000000000000000000000000000000)⟩
lemma Z2_0_6H2E_4_4Log_sound : Z2_0_6H2E_4_4Log.Encloses (Real.log (Z2_0_6H2Value ((4,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((4,4) : PairSlot)) (w := Z2_0_6H2E_4_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2E_4_4 : Ball := ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
lemma Z2_0_6H2E_4_4_sound : Z2_0_6H2E_4_4.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((4,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((4,4) : PairSlot)) Z2_0_6H2E_4_4Log_sound) (by decide +kernel)
def Z2_0_6H2E_5_2LogWitness : LogWitness := ⟨-3, 10457964405071752630514678883453, 6250000000000000000000000000000⟩
def Z2_0_6H2E_5_2Log : Ball := ⟨(-78232958663779813935933970438769 / 50000000000000000000000000000000), (10587911863 / 12500000000000000000000000000000)⟩
lemma Z2_0_6H2E_5_2Log_sound : Z2_0_6H2E_5_2Log.Encloses (Real.log (Z2_0_6H2Value ((5,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((5,2) : PairSlot)) (w := Z2_0_6H2E_5_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2E_5_2 : Ball := ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H2E_5_2_sound : Z2_0_6H2E_5_2.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((5,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((5,2) : PairSlot)) Z2_0_6H2E_5_2Log_sound) (by decide +kernel)
def Z2_0_6H2E_5_3LogWitness : LogWitness := ⟨-6, 1708150169428319858018410671529, 1562500000000000000000000000000⟩
def Z2_0_6H2E_5_3Log : Ball := ⟨(-203487958663779813935933941795503 / 50000000000000000000000000000000), (74115383007 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H2E_5_3Log_sound : Z2_0_6H2E_5_3Log.Encloses (Real.log (Z2_0_6H2Value ((5,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z2_0_6Half_sound 2) ((5,3) : PairSlot)) (w := Z2_0_6H2E_5_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2E_5_3 : Ball := ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
lemma Z2_0_6H2E_5_3_sound : Z2_0_6H2E_5_3.Encloses (Foundation.entropyTerm (Z2_0_6H2Value ((5,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z2_0_6Half_sound 2) ((5,3) : PairSlot)) Z2_0_6H2E_5_3Log_sound) (by decide +kernel)
def Z2_0_6H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 2, 5 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 3, 5 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | 4, 4 => ⟨(32980274307046266973832495616429 / 100000000000000000000000000000000), (5797076779 / 25000000000000000000000000000000)⟩
  | 5, 2 => ⟨(32726299880370363099063710099363 / 100000000000000000000000000000000), (17716480919 / 100000000000000000000000000000000)⟩
  | 5, 3 => ⟨(1737939955340792184583902537331 / 25000000000000000000000000000000), (1266002049 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z2_0_6H2Terms_sound (a : PairSlot) :
    (Z2_0_6H2Terms a).Encloses (Foundation.entropyTerm (Z2_0_6H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((2,4) : PairSlot))) Z2_0_6H2E_2_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((3,4) : PairSlot))) Z2_0_6H2E_3_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,3) : PairSlot))) Z2_0_6H2E_4_4_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,1) : PairSlot))) Z2_0_6H2E_5_2_sound Z2_0_6H2E_5_3_sound (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z2_0_6Half_sound 2) ((5,5) : PairSlot)))
def Z2_0_6H2Entropy : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (1273705543 / 2000000000000000000000000000000)⟩
lemma Z2_0_6H2Entropy_sound : Z2_0_6H2Entropy.Encloses (Foundation.finiteEntropy Z2_0_6H2Value) := by
  exact contains_sound (entropyPair_enclosed Z2_0_6H2Value Z2_0_6H2Terms Z2_0_6H2Terms_sound) (by decide +kernel)
def Z2_0_6H2Mass : Ball := ⟨1, (11 / 10000000000000000000000000000000)⟩
lemma Z2_0_6H2Mass_sound : Z2_0_6H2Mass.Encloses (∑ a, Z2_0_6H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z2_0_6Half 2) Z2_0_6H2Value (Z2_0_6Half_sound 2)) (by decide +kernel)
def Z2_0_6H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z2_0_6H2MassTermLog : Ball := ⟨0, (1323488987 / 6250000000000000000000000000000)⟩
lemma Z2_0_6H2MassTermLog_sound : Z2_0_6H2MassTermLog.Encloses (Real.log ((∑ a, Z2_0_6H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z2_0_6H2Mass_sound) (w := Z2_0_6H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z2_0_6H2MassTerm : Ball := ⟨0, (21175823793 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H2MassTerm_sound : Z2_0_6H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z2_0_6H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z2_0_6H2Mass_sound) Z2_0_6H2MassTermLog_sound) (by decide +kernel)
def Z2_0_6H2H : Ball := ⟨(112336393710513330648631136113803 / 100000000000000000000000000000000), (84861100943 / 100000000000000000000000000000000)⟩
lemma Z2_0_6H2H_sound : Z2_0_6H2H.Encloses (homogeneousEntropy Z2_0_6H2Value) := by
  exact contains_sound (homogeneous_enclosed Z2_0_6H2Value Z2_0_6H2MassTerm_sound Z2_0_6H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
