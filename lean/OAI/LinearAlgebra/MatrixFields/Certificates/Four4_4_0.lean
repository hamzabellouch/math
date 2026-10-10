import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_4_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z4_4_0Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w123
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w212
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w221
  | 2, 3 => w204
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w204
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w212
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w123
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z4_4_0Raw_sound_0 (j : Fin 6) :
    (Z4_4_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 0 5 = (-12216) := by decide +kernel
    rw [he]
    exact w123_sound
lemma Z4_4_0Raw_sound_1 (j : Fin 6) :
    (Z4_4_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 4 = (28778) := by decide +kernel
    rw [he]
    exact w212_sound
  · change (Z4_4_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_2 (j : Fin 6) :
    (Z4_4_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 2 = (44147) := by decide +kernel
    rw [he]
    exact w221_sound
  · change (Z4_4_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 3 = (22176) := by decide +kernel
    rw [he]
    exact w204_sound
  · change (Z4_4_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_3 (j : Fin 6) :
    (Z4_4_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 2 = (22176) := by decide +kernel
    rw [he]
    exact w204_sound
  · change (Z4_4_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_4 (j : Fin 6) :
    (Z4_4_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 1 = (28778) := by decide +kernel
    rw [he]
    exact w212_sound
  · change (Z4_4_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound_5 (j : Fin 6) :
    (Z4_4_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z4_4_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 0 = (-12216) := by decide +kernel
    rw [he]
    exact w123_sound
  · change (Z4_4_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_4_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 4 4 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 4 4 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_4_0Raw_sound (ij : PairSlot) :
    (Z4_4_0Raw ij).Encloses (weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z4_4_0Raw_sound_0 j) (Z4_4_0Raw_sound_1 j) (Z4_4_0Raw_sound_2 j) (Z4_4_0Raw_sound_3 j) (Z4_4_0Raw_sound_4 j) (Z4_4_0Raw_sound_5 j)
def Z4_4_0Den : Ball := ⟨(1381673256774017391432963646374551 / 10000000000000000000000000000000), (7051 / 50000000000000000000000000000000)⟩
lemma Z4_4_0Den_sound : Z4_4_0Den.Encloses
    (((orderedPairs (shape 4 4 0)).map (fun ij => weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 4 4 0)) Z4_4_0Raw
    (fun ij => weight (orderedPairInteger (shape 4 4 0) ij.1 ij.2))
    (fun ij _ => Z4_4_0Raw_sound ij)) (by decide +kernel)
lemma Z4_4_0Den_pos : 0 < Z4_4_0Den.lower := by decide +kernel
def Z4_4_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 5 => ⟨(13333388289568308767749416709 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4 => ⟨(12864926472604064794547580018297 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 2 => ⟨(59823869115870383240874620994737 / 100000000000000000000000000000000), (123 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(1661981174399030590448466000577 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 2 => ⟨(1661981174399030590448466000577 / 25000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 3, 3 => ⟨(180940029615764141468627407341 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1 => ⟨(12864926472604064794547580018297 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 5, 0 => ⟨(13333388289568308767749416709 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_4_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 4 4 0) →
    contains (.mul (Z4_4_0Raw (i,j)) (.inv Z4_4_0Den)) (Z4_4_0Probs (i,j)) = true := by
  decide +kernel
lemma Z4_4_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 4 4 0) → Z4_4_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z4_4_0Probs_sound (ij : PairSlot) :
    (Z4_4_0Probs ij).Encloses (zeroPairLaw (shape 4 4 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 4 4 0)
  · have hb := contains_sound (Ball.mul_sound (Z4_4_0Raw_sound ij)
      (Ball.inv_sound Z4_4_0Den_sound Z4_4_0Den_pos)) (Z4_4_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z4_4_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z4_4_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 4 4 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 4 4 0) then Z4_4_0Probs ij
  else Z4_4_0Probs (kappa ij.1, kappa ij.2)
lemma Z4_4_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z4_4_0Half w ij).Encloses (halfLaw (shape 4 4 0) w ij : ℝ) := by
  have hp : positive (shape 4 4 0) = false := by decide +kernel
  simp only [Z4_4_0Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z4_4_0Probs_sound _
  · exact Z4_4_0Probs_sound _

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
def Z4_4_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 4 4 0) a.1 a.2 : ℝ)
def Z4_4_0E_0_5LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0E_0_5Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0E_0_5Log_sound : Z4_4_0E_0_5Log.Encloses (Real.log (Z4_4_0Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((0,5) : PairSlot)) (w := Z4_4_0E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_0_5 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0E_0_5_sound : Z4_4_0E_0_5.Encloses (Foundation.entropyTerm (Z4_4_0Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((0,5) : PairSlot)) Z4_4_0E_0_5Log_sound) (by decide +kernel)
def Z4_4_0E_1_4LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0E_1_4Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0E_1_4Log_sound : Z4_4_0E_1_4Log.Encloses (Real.log (Z4_4_0Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((1,4) : PairSlot)) (w := Z4_4_0E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_1_4 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0E_1_4_sound : Z4_4_0E_1_4.Encloses (Foundation.entropyTerm (Z4_4_0Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((1,4) : PairSlot)) Z4_4_0E_1_4Log_sound) (by decide +kernel)
def Z4_4_0E_2_2LogWitness : LogWitness := ⟨-1, 59823869115870383240874620994737, 50000000000000000000000000000000⟩
def Z4_4_0E_2_2Log : Ball := ⟨(-51376545557549166812453081310857 / 100000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
lemma Z4_4_0E_2_2Log_sound : Z4_4_0E_2_2Log.Encloses (Real.log (Z4_4_0Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((2,2) : PairSlot)) (w := Z4_4_0E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_2_2 : Ball := ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
lemma Z4_4_0E_2_2_sound : Z4_4_0E_2_2.Encloses (Foundation.entropyTerm (Z4_4_0Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((2,2) : PairSlot)) Z4_4_0E_2_2Log_sound) (by decide +kernel)
def Z4_4_0E_2_3LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0E_2_3Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0E_2_3Log_sound : Z4_4_0E_2_3Log.Encloses (Real.log (Z4_4_0Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((2,3) : PairSlot)) (w := Z4_4_0E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_2_3 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0E_2_3_sound : Z4_4_0E_2_3.Encloses (Foundation.entropyTerm (Z4_4_0Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((2,3) : PairSlot)) Z4_4_0E_2_3Log_sound) (by decide +kernel)
def Z4_4_0E_3_2LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0E_3_2Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0E_3_2Log_sound : Z4_4_0E_3_2Log.Encloses (Real.log (Z4_4_0Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((3,2) : PairSlot)) (w := Z4_4_0E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_3_2 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0E_3_2_sound : Z4_4_0E_3_2.Encloses (Foundation.entropyTerm (Z4_4_0Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((3,2) : PairSlot)) Z4_4_0E_3_2Log_sound) (by decide +kernel)
def Z4_4_0E_3_3LogWitness : LogWitness := ⟨-8, 180940029615764141468627407341, 97656250000000000000000000000⟩
def Z4_4_0E_3_3Log : Ball := ⟨(-15401454548673411462889154616633 / 3125000000000000000000000000000), (190582413423 / 100000000000000000000000000000000)⟩
lemma Z4_4_0E_3_3Log_sound : Z4_4_0E_3_3Log.Encloses (Real.log (Z4_4_0Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((3,3) : PairSlot)) (w := Z4_4_0E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_3_3 : Ball := ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
lemma Z4_4_0E_3_3_sound : Z4_4_0E_3_3.Encloses (Foundation.entropyTerm (Z4_4_0Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((3,3) : PairSlot)) Z4_4_0E_3_3Log_sound) (by decide +kernel)
def Z4_4_0E_4_1LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0E_4_1Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0E_4_1Log_sound : Z4_4_0E_4_1Log.Encloses (Real.log (Z4_4_0Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((4,1) : PairSlot)) (w := Z4_4_0E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_4_1 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0E_4_1_sound : Z4_4_0E_4_1.Encloses (Foundation.entropyTerm (Z4_4_0Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((4,1) : PairSlot)) Z4_4_0E_4_1Log_sound) (by decide +kernel)
def Z4_4_0E_5_0LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0E_5_0Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0E_5_0Log_sound : Z4_4_0E_5_0Log.Encloses (Real.log (Z4_4_0Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0Probs_sound ((5,0) : PairSlot)) (w := Z4_4_0E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0E_5_0 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0E_5_0_sound : Z4_4_0E_5_0.Encloses (Foundation.entropyTerm (Z4_4_0Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0Probs_sound ((5,0) : PairSlot)) Z4_4_0E_5_0Log_sound) (by decide +kernel)
def Z4_4_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | 1, 4 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
  | 4, 1 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_4_0Terms_sound (a : PairSlot) :
    (Z4_4_0Terms a).Encloses (Foundation.entropyTerm (Z4_4_0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((0,4) : PairSlot))) Z4_4_0E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,3) : PairSlot))) Z4_4_0E_1_4_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,1) : PairSlot))) Z4_4_0E_2_2_sound Z4_4_0E_2_3_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,1) : PairSlot))) Z4_4_0E_3_2_sound Z4_4_0E_3_3_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,0) : PairSlot))) Z4_4_0E_4_1_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_4_0E_5_0_sound (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z4_4_0Probs_sound ((5,5) : PairSlot)))
def Z4_4_0Entropy : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (63490820907 / 100000000000000000000000000000000)⟩
lemma Z4_4_0Entropy_sound : Z4_4_0Entropy.Encloses (Foundation.finiteEntropy Z4_4_0Value) := by
  exact contains_sound (entropyPair_enclosed Z4_4_0Value Z4_4_0Terms Z4_4_0Terms_sound) (by decide +kernel)
def Z4_4_0Labels : Ball := ⟨(278319288524584121929550231720779 / 50000000000000000000000000000000), (182174349901 / 100000000000000000000000000000000)⟩
lemma Z4_4_0Labels_sound : Z4_4_0Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 4 4 0) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z4_4_0Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z4_4_0Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z4_4_0Four : Ball := ⟨(341185829672345662609619992603639 / 50000000000000000000000000000000), (30708146351 / 12500000000000000000000000000000)⟩
lemma Z4_4_0Four_sound : Z4_4_0Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 4 4 0)) := by
  exact contains_sound (Ball.add_sound Z4_4_0Entropy_sound Z4_4_0Labels_sound) (by decide +kernel)
def Z4_4_0H0Value (a : PairSlot) : ℝ := (halfLaw (shape 4 4 0) 0 a : ℝ)
def Z4_4_0H0E_0_5LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H0E_0_5Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0H0E_0_5Log_sound : Z4_4_0H0E_0_5Log.Encloses (Real.log (Z4_4_0H0Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((0,5) : PairSlot)) (w := Z4_4_0H0E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_0_5 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H0E_0_5_sound : Z4_4_0H0E_0_5.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((0,5) : PairSlot)) Z4_4_0H0E_0_5Log_sound) (by decide +kernel)
def Z4_4_0H0E_1_4LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H0E_1_4Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0E_1_4Log_sound : Z4_4_0H0E_1_4Log.Encloses (Real.log (Z4_4_0H0Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((1,4) : PairSlot)) (w := Z4_4_0H0E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_1_4 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0H0E_1_4_sound : Z4_4_0H0E_1_4.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((1,4) : PairSlot)) Z4_4_0H0E_1_4Log_sound) (by decide +kernel)
def Z4_4_0H0E_2_2LogWitness : LogWitness := ⟨-1, 59823869115870383240874620994737, 50000000000000000000000000000000⟩
def Z4_4_0H0E_2_2Log : Ball := ⟨(-51376545557549166812453081310857 / 100000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0E_2_2Log_sound : Z4_4_0H0E_2_2Log.Encloses (Real.log (Z4_4_0H0Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((2,2) : PairSlot)) (w := Z4_4_0H0E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_2_2 : Ball := ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H0E_2_2_sound : Z4_4_0H0E_2_2.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((2,2) : PairSlot)) Z4_4_0H0E_2_2Log_sound) (by decide +kernel)
def Z4_4_0H0E_2_3LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H0E_2_3Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0H0E_2_3Log_sound : Z4_4_0H0E_2_3Log.Encloses (Real.log (Z4_4_0H0Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((2,3) : PairSlot)) (w := Z4_4_0H0E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_2_3 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0H0E_2_3_sound : Z4_4_0H0E_2_3.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((2,3) : PairSlot)) Z4_4_0H0E_2_3Log_sound) (by decide +kernel)
def Z4_4_0H0E_3_2LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H0E_3_2Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0H0E_3_2Log_sound : Z4_4_0H0E_3_2Log.Encloses (Real.log (Z4_4_0H0Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((3,2) : PairSlot)) (w := Z4_4_0H0E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_3_2 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0H0E_3_2_sound : Z4_4_0H0E_3_2.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((3,2) : PairSlot)) Z4_4_0H0E_3_2Log_sound) (by decide +kernel)
def Z4_4_0H0E_3_3LogWitness : LogWitness := ⟨-8, 180940029615764141468627407341, 97656250000000000000000000000⟩
def Z4_4_0H0E_3_3Log : Ball := ⟨(-15401454548673411462889154616633 / 3125000000000000000000000000000), (190582413423 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0E_3_3Log_sound : Z4_4_0H0E_3_3Log.Encloses (Real.log (Z4_4_0H0Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((3,3) : PairSlot)) (w := Z4_4_0H0E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_3_3 : Ball := ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
lemma Z4_4_0H0E_3_3_sound : Z4_4_0H0E_3_3.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((3,3) : PairSlot)) Z4_4_0H0E_3_3Log_sound) (by decide +kernel)
def Z4_4_0H0E_4_1LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H0E_4_1Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0E_4_1Log_sound : Z4_4_0H0E_4_1Log.Encloses (Real.log (Z4_4_0H0Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((4,1) : PairSlot)) (w := Z4_4_0H0E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_4_1 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0H0E_4_1_sound : Z4_4_0H0E_4_1.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((4,1) : PairSlot)) Z4_4_0H0E_4_1Log_sound) (by decide +kernel)
def Z4_4_0H0E_5_0LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H0E_5_0Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0H0E_5_0Log_sound : Z4_4_0H0E_5_0Log.Encloses (Real.log (Z4_4_0H0Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 0) ((5,0) : PairSlot)) (w := Z4_4_0H0E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0E_5_0 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H0E_5_0_sound : Z4_4_0H0E_5_0.Encloses (Foundation.entropyTerm (Z4_4_0H0Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 0) ((5,0) : PairSlot)) Z4_4_0H0E_5_0Log_sound) (by decide +kernel)
def Z4_4_0H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | 1, 4 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
  | 4, 1 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_4_0H0Terms_sound (a : PairSlot) :
    (Z4_4_0H0Terms a).Encloses (Foundation.entropyTerm (Z4_4_0H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((0,4) : PairSlot))) Z4_4_0H0E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((1,3) : PairSlot))) Z4_4_0H0E_1_4_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((2,1) : PairSlot))) Z4_4_0H0E_2_2_sound Z4_4_0H0E_2_3_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((3,1) : PairSlot))) Z4_4_0H0E_3_2_sound Z4_4_0H0E_3_3_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((4,0) : PairSlot))) Z4_4_0H0E_4_1_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_4_0H0E_5_0_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 0) ((5,5) : PairSlot)))
def Z4_4_0H0Entropy : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (63490820907 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0Entropy_sound : Z4_4_0H0Entropy.Encloses (Foundation.finiteEntropy Z4_4_0H0Value) := by
  exact contains_sound (entropyPair_enclosed Z4_4_0H0Value Z4_4_0H0Terms Z4_4_0H0Terms_sound) (by decide +kernel)
def Z4_4_0H0Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0Mass_sound : Z4_4_0H0Mass.Encloses (∑ a, Z4_4_0H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_4_0Half 0) Z4_4_0H0Value (Z4_4_0Half_sound 0)) (by decide +kernel)
def Z4_4_0H0MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z4_4_0H0MassTermLog : Ball := ⟨0, (1694065903 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H0MassTermLog_sound : Z4_4_0H0MassTermLog.Encloses (Real.log ((∑ a, Z4_4_0H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0H0Mass_sound) (w := Z4_4_0H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H0MassTerm : Ball := ⟨0, (5293955947 / 12500000000000000000000000000000)⟩
lemma Z4_4_0H0MassTerm_sound : Z4_4_0H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_4_0H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0H0Mass_sound) Z4_4_0H0MassTermLog_sound) (by decide +kernel)
def Z4_4_0H0H : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (105842468483 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H0H_sound : Z4_4_0H0H.Encloses (homogeneousEntropy Z4_4_0H0Value) := by
  exact contains_sound (homogeneous_enclosed Z4_4_0H0Value Z4_4_0H0MassTerm_sound Z4_4_0H0Entropy_sound) (by decide +kernel)
def Z4_4_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 4 4 0) 1 a : ℝ)
def Z4_4_0H1E_5_0LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H1E_5_0Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0H1E_5_0Log_sound : Z4_4_0H1E_5_0Log.Encloses (Real.log (Z4_4_0H1Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((5,0) : PairSlot)) (w := Z4_4_0H1E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_5_0 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H1E_5_0_sound : Z4_4_0H1E_5_0.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((5,0) : PairSlot)) Z4_4_0H1E_5_0Log_sound) (by decide +kernel)
def Z4_4_0H1E_4_1LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H1E_4_1Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1E_4_1Log_sound : Z4_4_0H1E_4_1Log.Encloses (Real.log (Z4_4_0H1Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((4,1) : PairSlot)) (w := Z4_4_0H1E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_4_1 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0H1E_4_1_sound : Z4_4_0H1E_4_1.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((4,1) : PairSlot)) Z4_4_0H1E_4_1Log_sound) (by decide +kernel)
def Z4_4_0H1E_2_2LogWitness : LogWitness := ⟨-1, 59823869115870383240874620994737, 50000000000000000000000000000000⟩
def Z4_4_0H1E_2_2Log : Ball := ⟨(-51376545557549166812453081310857 / 100000000000000000000000000000000), (42351647571 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1E_2_2Log_sound : Z4_4_0H1E_2_2Log.Encloses (Real.log (Z4_4_0H1Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((2,2) : PairSlot)) (w := Z4_4_0H1E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_2_2 : Ball := ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H1E_2_2_sound : Z4_4_0H1E_2_2.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((2,2) : PairSlot)) Z4_4_0H1E_2_2Log_sound) (by decide +kernel)
def Z4_4_0H1E_2_3LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H1E_2_3Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0H1E_2_3Log_sound : Z4_4_0H1E_2_3Log.Encloses (Real.log (Z4_4_0H1Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((2,3) : PairSlot)) (w := Z4_4_0H1E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_2_3 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0H1E_2_3_sound : Z4_4_0H1E_2_3.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((2,3) : PairSlot)) Z4_4_0H1E_2_3Log_sound) (by decide +kernel)
def Z4_4_0H1E_3_2LogWitness : LogWitness := ⟨-4, 1661981174399030590448466000577, 1562500000000000000000000000000⟩
def Z4_4_0H1E_3_2Log : Ball := ⟨(-135543272778774583406226512012229 / 50000000000000000000000000000000), (847032949 / 800000000000000000000000000000)⟩
lemma Z4_4_0H1E_3_2Log_sound : Z4_4_0H1E_3_2Log.Encloses (Real.log (Z4_4_0H1Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((3,2) : PairSlot)) (w := Z4_4_0H1E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_3_2 : Ball := ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
lemma Z4_4_0H1E_3_2_sound : Z4_4_0H1E_3_2.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((3,2) : PairSlot)) Z4_4_0H1E_3_2Log_sound) (by decide +kernel)
def Z4_4_0H1E_3_3LogWitness : LogWitness := ⟨-8, 180940029615764141468627407341, 97656250000000000000000000000⟩
def Z4_4_0H1E_3_3Log : Ball := ⟨(-15401454548673411462889154616633 / 3125000000000000000000000000000), (190582413423 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1E_3_3Log_sound : Z4_4_0H1E_3_3Log.Encloses (Real.log (Z4_4_0H1Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((3,3) : PairSlot)) (w := Z4_4_0H1E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_3_3 : Ball := ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
lemma Z4_4_0H1E_3_3_sound : Z4_4_0H1E_3_3.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((3,3) : PairSlot)) Z4_4_0H1E_3_3Log_sound) (by decide +kernel)
def Z4_4_0H1E_1_4LogWitness : LogWitness := ⟨-3, 12864926472604064794547580018297, 12500000000000000000000000000000⟩
def Z4_4_0H1E_1_4Log : Ball := ⟨(-102533272778774583406226521559951 / 50000000000000000000000000000000), (84703294941 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1E_1_4Log_sound : Z4_4_0H1E_1_4Log.Encloses (Real.log (Z4_4_0H1Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((1,4) : PairSlot)) (w := Z4_4_0H1E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_1_4 : Ball := ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
lemma Z4_4_0H1E_1_4_sound : Z4_4_0H1E_1_4.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((1,4) : PairSlot)) Z4_4_0H1E_1_4Log_sound) (by decide +kernel)
def Z4_4_0H1E_0_5LogWitness : LogWitness := ⟨-9, 13333388289568308767749416709, 12207031250000000000000000000⟩
def Z4_4_0H1E_0_5Log : Ball := ⟨(-615006545557549166812452928547037 / 100000000000000000000000000000000), (105879118649 / 50000000000000000000000000000000)⟩
lemma Z4_4_0H1E_0_5Log_sound : Z4_4_0H1E_0_5Log.Encloses (Real.log (Z4_4_0H1Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_4_0Half_sound 1) ((0,5) : PairSlot)) (w := Z4_4_0H1E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1E_0_5 : Ball := ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H1E_0_5_sound : Z4_4_0H1E_0_5.Encloses (Foundation.entropyTerm (Z4_4_0H1Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 1) ((0,5) : PairSlot)) Z4_4_0H1E_0_5Log_sound) (by decide +kernel)
def Z4_4_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 0 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | 4, 1 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(480241208915683334342627678761 / 1562500000000000000000000000000), (1013455771 / 4000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3604325882796094985265170692573 / 20000000000000000000000000000000), (1407752823 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(1783513370984199948259882031059 / 50000000000000000000000000000000), (172419939 / 12500000000000000000000000000000)⟩
  | 1, 4 => ⟨(26381660305887817562778739090541 / 100000000000000000000000000000000), (1089701667 / 10000000000000000000000000000000)⟩
  | 0, 5 => ⟨(1312019371607181543741200578043 / 100000000000000000000000000000000), (18070111 / 4000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_4_0H1Terms_sound (a : PairSlot) :
    (Z4_4_0H1Terms a).Encloses (Foundation.entropyTerm (Z4_4_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((0,4) : PairSlot))) Z4_4_0H1E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((1,3) : PairSlot))) Z4_4_0H1E_1_4_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((2,1) : PairSlot))) Z4_4_0H1E_2_2_sound Z4_4_0H1E_2_3_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((3,1) : PairSlot))) Z4_4_0H1E_3_2_sound Z4_4_0H1E_3_3_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((4,0) : PairSlot))) Z4_4_0H1E_4_1_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_4_0H1E_5_0_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 1) ((5,5) : PairSlot)))
def Z4_4_0H1Entropy : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (63490820907 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1Entropy_sound : Z4_4_0H1Entropy.Encloses (Foundation.finiteEntropy Z4_4_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z4_4_0H1Value Z4_4_0H1Terms Z4_4_0H1Terms_sound) (by decide +kernel)
def Z4_4_0H1Mass : Ball := ⟨(99999999999999999999999999999999 / 100000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1Mass_sound : Z4_4_0H1Mass.Encloses (∑ a, Z4_4_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_4_0Half 1) Z4_4_0H1Value (Z4_4_0Half_sound 1)) (by decide +kernel)
def Z4_4_0H1MassTermLogWitness : LogWitness := ⟨-1, 99999999999999999999999999999999, 50000000000000000000000000000000⟩
def Z4_4_0H1MassTermLog : Ball := ⟨0, (1694065903 / 4000000000000000000000000000000)⟩
lemma Z4_4_0H1MassTermLog_sound : Z4_4_0H1MassTermLog.Encloses (Real.log ((∑ a, Z4_4_0H1Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z4_4_0H1Mass_sound) (w := Z4_4_0H1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_4_0H1MassTerm : Ball := ⟨0, (5293955947 / 12500000000000000000000000000000)⟩
lemma Z4_4_0H1MassTerm_sound : Z4_4_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_4_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0H1Mass_sound) Z4_4_0H1MassTermLog_sound) (by decide +kernel)
def Z4_4_0H1H : Ball := ⟨(3143327057388077034003488044143 / 2500000000000000000000000000000), (105842468483 / 100000000000000000000000000000000)⟩
lemma Z4_4_0H1H_sound : Z4_4_0H1H.Encloses (homogeneousEntropy Z4_4_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z4_4_0H1Value Z4_4_0H1MassTerm_sound Z4_4_0H1Entropy_sound) (by decide +kernel)
def Z4_4_0H2Value (a : PairSlot) : ℝ := (halfLaw (shape 4 4 0) 2 a : ℝ)
def Z4_4_0H2E_0_0Log : Ball := .exact 0
lemma Z4_4_0H2E_0_0Log_sound : Z4_4_0H2E_0_0Log.Encloses (Real.log (Z4_4_0H2Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z4_4_0Half_sound 2) ((0,0) : PairSlot))
def Z4_4_0H2E_0_0 : Ball := ⟨0, 0⟩
lemma Z4_4_0H2E_0_0_sound : Z4_4_0H2E_0_0.Encloses (Foundation.entropyTerm (Z4_4_0H2Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_4_0Half_sound 2) ((0,0) : PairSlot)) Z4_4_0H2E_0_0Log_sound) (by decide +kernel)
def Z4_4_0H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z4_4_0H2Terms_sound (a : PairSlot) :
    (Z4_4_0H2Terms a).Encloses (Foundation.entropyTerm (Z4_4_0H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z4_4_0H2E_0_0_sound (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_4_0Half_sound 2) ((5,5) : PairSlot)))
def Z4_4_0H2Entropy : Ball := ⟨0, 0⟩
lemma Z4_4_0H2Entropy_sound : Z4_4_0H2Entropy.Encloses (Foundation.finiteEntropy Z4_4_0H2Value) := by
  exact contains_sound (entropyPair_enclosed Z4_4_0H2Value Z4_4_0H2Terms Z4_4_0H2Terms_sound) (by decide +kernel)
def Z4_4_0H2Mass : Ball := ⟨1, 0⟩
lemma Z4_4_0H2Mass_sound : Z4_4_0H2Mass.Encloses (∑ a, Z4_4_0H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_4_0Half 2) Z4_4_0H2Value (Z4_4_0Half_sound 2)) (by decide +kernel)
def Z4_4_0H2MassTermLog : Ball := .exact 0
lemma Z4_4_0H2MassTermLog_sound : Z4_4_0H2MassTermLog.Encloses (Real.log ((∑ a, Z4_4_0H2Value a))) := by
  exact log_exact_one_ball (Z4_4_0H2Mass_sound)
def Z4_4_0H2MassTerm : Ball := ⟨0, 0⟩
lemma Z4_4_0H2MassTerm_sound : Z4_4_0H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_4_0H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_4_0H2Mass_sound) Z4_4_0H2MassTermLog_sound) (by decide +kernel)
def Z4_4_0H2H : Ball := ⟨0, 0⟩
lemma Z4_4_0H2H_sound : Z4_4_0H2H.Encloses (homogeneousEntropy Z4_4_0H2Value) := by
  exact contains_sound (homogeneous_enclosed Z4_4_0H2Value Z4_4_0H2MassTerm_sound Z4_4_0H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
