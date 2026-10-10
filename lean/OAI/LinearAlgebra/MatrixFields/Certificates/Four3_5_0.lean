import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_3_5

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def Z3_5_0Raw (ij : PairSlot) : Ball :=
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
  | 1, 5 => w165
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w207
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w207
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w165
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z3_5_0Raw_sound_0 (j : Fin 6) :
    (Z3_5_0Raw (0,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (0,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (0,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 0 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_1 (j : Fin 6) :
    (Z3_5_0Raw (1,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (1,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (1,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 1 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 1 5 = (-5587) := by decide +kernel
    rw [he]
    exact w165_sound
lemma Z3_5_0Raw_sound_2 (j : Fin 6) :
    (Z3_5_0Raw (2,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (2,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (2,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 4 = (22521) := by decide +kernel
    rw [he]
    exact w207_sound
  · change (Z3_5_0Raw (2,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 2 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_3 (j : Fin 6) :
    (Z3_5_0Raw (3,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (3,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (3,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 3 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_4 (j : Fin 6) :
    (Z3_5_0Raw (4,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (4,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 2 = (22521) := by decide +kernel
    rw [he]
    exact w207_sound
  · change (Z3_5_0Raw (4,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (4,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 4 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound_5 (j : Fin 6) :
    (Z3_5_0Raw (5,j)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 j) : ℝ) := by
  fin_cases j
  · change (Z3_5_0Raw (5,0)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 0) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,1)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 1) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 1 = (-5587) := by decide +kernel
    rw [he]
    exact w165_sound
  · change (Z3_5_0Raw (5,2)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 2) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,3)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 3) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,4)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 4) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_5_0Raw (5,5)).Encloses (weight (orderedPairInteger (shape 3 5 0) 5 5) : ℝ)
    have he : orderedPairInteger (shape 3 5 0) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_5_0Raw_sound (ij : PairSlot) :
    (Z3_5_0Raw ij).Encloses (weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z3_5_0Raw_sound_0 j) (Z3_5_0Raw_sound_1 j) (Z3_5_0Raw_sound_2 j) (Z3_5_0Raw_sound_3 j) (Z3_5_0Raw_sound_4 j) (Z3_5_0Raw_sound_5 j)
def Z3_5_0Den : Ball := ⟨(1107963313523711256690127341051801 / 50000000000000000000000000000000), (1063 / 50000000000000000000000000000000)⟩
lemma Z3_5_0Den_sound : Z3_5_0Den.Encloses
    (((orderedPairs (shape 3 5 0)).map (fun ij => weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 3 5 0)) Z3_5_0Raw
    (fun ij => weight (orderedPairInteger (shape 3 5 0) ij.1 ij.2))
    (fun ij _ => Z3_5_0Raw_sound ij)) (by decide +kernel)
lemma Z3_5_0Den_pos : 0 < Z3_5_0Den.lower := by decide +kernel
def Z3_5_0Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(645274206658629135363561930529 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(21453059186785379874419022991011 / 50000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2256392399897361854853853147931 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(21453059186785379874419022991011 / 50000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2256392399897361854853853147931 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(645274206658629135363561930529 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_5_0Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 3 5 0) →
    contains (.mul (Z3_5_0Raw (i,j)) (.inv Z3_5_0Den)) (Z3_5_0Probs (i,j)) = true := by
  decide +kernel
lemma Z3_5_0Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 3 5 0) → Z3_5_0Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z3_5_0Probs_sound (ij : PairSlot) :
    (Z3_5_0Probs ij).Encloses (zeroPairLaw (shape 3 5 0) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 3 5 0)
  · have hb := contains_sound (Ball.mul_sound (Z3_5_0Raw_sound ij)
      (Ball.inv_sound Z3_5_0Den_sound Z3_5_0Den_pos)) (Z3_5_0Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z3_5_0Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z3_5_0Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 3 5 0) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 3 5 0) then Z3_5_0Probs ij
  else Z3_5_0Probs (kappa ij.1, kappa ij.2)
lemma Z3_5_0Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z3_5_0Half w ij).Encloses (halfLaw (shape 3 5 0) w ij : ℝ) := by
  have hp : positive (shape 3 5 0) = false := by decide +kernel
  simp only [Z3_5_0Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z3_5_0Probs_sound _
  · exact Z3_5_0Probs_sound _

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
def Z3_5_0Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 3 5 0) a.1 a.2 : ℝ)
def Z3_5_0E_1_5LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0E_1_5Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_1_5Log_sound : Z3_5_0E_1_5Log.Encloses (Real.log (Z3_5_0Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((1,5) : PairSlot)) (w := Z3_5_0E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_1_5 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0E_1_5_sound : Z3_5_0E_1_5.Encloses (Foundation.entropyTerm (Z3_5_0Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((1,5) : PairSlot)) Z3_5_0E_1_5Log_sound) (by decide +kernel)
def Z3_5_0E_2_4LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0E_2_4Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_2_4Log_sound : Z3_5_0E_2_4Log.Encloses (Real.log (Z3_5_0Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((2,4) : PairSlot)) (w := Z3_5_0E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_2_4 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_2_4_sound : Z3_5_0E_2_4.Encloses (Foundation.entropyTerm (Z3_5_0Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((2,4) : PairSlot)) Z3_5_0E_2_4Log_sound) (by decide +kernel)
def Z3_5_0E_3_4LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0E_3_4Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0E_3_4Log_sound : Z3_5_0E_3_4Log.Encloses (Real.log (Z3_5_0Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((3,4) : PairSlot)) (w := Z3_5_0E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_3_4 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0E_3_4_sound : Z3_5_0E_3_4.Encloses (Foundation.entropyTerm (Z3_5_0Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((3,4) : PairSlot)) Z3_5_0E_3_4Log_sound) (by decide +kernel)
def Z3_5_0E_4_2LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0E_4_2Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_4_2Log_sound : Z3_5_0E_4_2Log.Encloses (Real.log (Z3_5_0Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((4,2) : PairSlot)) (w := Z3_5_0E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_4_2 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_4_2_sound : Z3_5_0E_4_2.Encloses (Foundation.entropyTerm (Z3_5_0Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((4,2) : PairSlot)) Z3_5_0E_4_2Log_sound) (by decide +kernel)
def Z3_5_0E_4_3LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0E_4_3Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0E_4_3Log_sound : Z3_5_0E_4_3Log.Encloses (Real.log (Z3_5_0Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((4,3) : PairSlot)) (w := Z3_5_0E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_4_3 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0E_4_3_sound : Z3_5_0E_4_3.Encloses (Foundation.entropyTerm (Z3_5_0Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((4,3) : PairSlot)) Z3_5_0E_4_3Log_sound) (by decide +kernel)
def Z3_5_0E_5_1LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0E_5_1Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0E_5_1Log_sound : Z3_5_0E_5_1Log.Encloses (Real.log (Z3_5_0Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0Probs_sound ((5,1) : PairSlot)) (w := Z3_5_0E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0E_5_1 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0E_5_1_sound : Z3_5_0E_5_1.Encloses (Foundation.entropyTerm (Z3_5_0Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0Probs_sound ((5,1) : PairSlot)) Z3_5_0E_5_1Log_sound) (by decide +kernel)
def Z3_5_0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 4, 2 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 5, 1 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_5_0Terms_sound (a : PairSlot) :
    (Z3_5_0Terms a).Encloses (Foundation.entropyTerm (Z3_5_0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((1,4) : PairSlot))) Z3_5_0E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((2,3) : PairSlot))) Z3_5_0E_2_4_sound (entropyTerm_zero_ball (Z3_5_0Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((3,3) : PairSlot))) Z3_5_0E_3_4_sound (entropyTerm_zero_ball (Z3_5_0Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((4,1) : PairSlot))) Z3_5_0E_4_2_sound Z3_5_0E_4_3_sound (entropyTerm_zero_ball (Z3_5_0Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_5_0Probs_sound ((5,0) : PairSlot))) Z3_5_0E_5_1_sound (entropyTerm_zero_ball (Z3_5_0Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z3_5_0Probs_sound ((5,5) : PairSlot)))
def Z3_5_0Entropy : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (7363373569 / 10000000000000000000000000000000)⟩
lemma Z3_5_0Entropy_sound : Z3_5_0Entropy.Encloses (Foundation.finiteEntropy Z3_5_0Value) := by
  exact contains_sound (entropyPair_enclosed Z3_5_0Value Z3_5_0Terms Z3_5_0Terms_sound) (by decide +kernel)
def Z3_5_0Labels : Ball := ⟨(256366745881774017426327259984771 / 50000000000000000000000000000000), (19912540783 / 12500000000000000000000000000000)⟩
lemma Z3_5_0Labels_sound : Z3_5_0Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 3 5 0) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z3_5_0Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z3_5_0Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z3_5_0Four : Ball := ⟨(316092723029333531553691028224521 / 50000000000000000000000000000000), (116467030977 / 50000000000000000000000000000000)⟩
lemma Z3_5_0Four_sound : Z3_5_0Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 3 5 0)) := by
  exact contains_sound (Ball.add_sound Z3_5_0Entropy_sound Z3_5_0Labels_sound) (by decide +kernel)
def Z3_5_0H0Value (a : PairSlot) : ℝ := (halfLaw (shape 3 5 0) 0 a : ℝ)
def Z3_5_0H0E_4_0LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H0E_4_0Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_4_0Log_sound : Z3_5_0H0E_4_0Log.Encloses (Real.log (Z3_5_0H0Value ((4,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((4,0) : PairSlot)) (w := Z3_5_0H0E_4_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_4_0 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0H0E_4_0_sound : Z3_5_0H0E_4_0.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((4,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((4,0) : PairSlot)) Z3_5_0H0E_4_0Log_sound) (by decide +kernel)
def Z3_5_0H0E_2_1LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H0E_2_1Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_2_1Log_sound : Z3_5_0H0E_2_1Log.Encloses (Real.log (Z3_5_0H0Value ((2,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((2,1) : PairSlot)) (w := Z3_5_0H0E_2_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_2_1 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_2_1_sound : Z3_5_0H0E_2_1.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((2,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((2,1) : PairSlot)) Z3_5_0H0E_2_1Log_sound) (by decide +kernel)
def Z3_5_0H0E_3_1LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H0E_3_1Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0H0E_3_1Log_sound : Z3_5_0H0E_3_1Log.Encloses (Real.log (Z3_5_0H0Value ((3,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((3,1) : PairSlot)) (w := Z3_5_0H0E_3_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_3_1 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0H0E_3_1_sound : Z3_5_0H0E_3_1.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((3,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((3,1) : PairSlot)) Z3_5_0H0E_3_1Log_sound) (by decide +kernel)
def Z3_5_0H0E_1_2LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H0E_1_2Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_1_2Log_sound : Z3_5_0H0E_1_2Log.Encloses (Real.log (Z3_5_0H0Value ((1,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((1,2) : PairSlot)) (w := Z3_5_0H0E_1_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_1_2 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_1_2_sound : Z3_5_0H0E_1_2.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((1,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((1,2) : PairSlot)) Z3_5_0H0E_1_2Log_sound) (by decide +kernel)
def Z3_5_0H0E_1_3LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H0E_1_3Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0H0E_1_3Log_sound : Z3_5_0H0E_1_3Log.Encloses (Real.log (Z3_5_0H0Value ((1,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((1,3) : PairSlot)) (w := Z3_5_0H0E_1_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_1_3 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0H0E_1_3_sound : Z3_5_0H0E_1_3.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((1,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((1,3) : PairSlot)) Z3_5_0H0E_1_3Log_sound) (by decide +kernel)
def Z3_5_0H0E_0_4LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H0E_0_4Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0E_0_4Log_sound : Z3_5_0H0E_0_4Log.Encloses (Real.log (Z3_5_0H0Value ((0,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 0) ((0,4) : PairSlot)) (w := Z3_5_0H0E_0_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0E_0_4 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0H0E_0_4_sound : Z3_5_0H0E_0_4.Encloses (Foundation.entropyTerm (Z3_5_0H0Value ((0,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 0) ((0,4) : PairSlot)) Z3_5_0H0E_0_4Log_sound) (by decide +kernel)
def Z3_5_0H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | 2, 1 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 3, 1 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 1, 2 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 1, 3 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 0, 4 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_5_0H0Terms_sound (a : PairSlot) :
    (Z3_5_0H0Terms a).Encloses (Foundation.entropyTerm (Z3_5_0H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((0,3) : PairSlot))) Z3_5_0H0E_0_4_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((1,1) : PairSlot))) Z3_5_0H0E_1_2_sound Z3_5_0H0E_1_3_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((2,0) : PairSlot))) Z3_5_0H0E_2_1_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((3,0) : PairSlot))) Z3_5_0H0E_3_1_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 Z3_5_0H0E_4_0_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 0) ((5,5) : PairSlot)))
def Z3_5_0H0Entropy : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (7363373569 / 10000000000000000000000000000000)⟩
lemma Z3_5_0H0Entropy_sound : Z3_5_0H0Entropy.Encloses (Foundation.finiteEntropy Z3_5_0H0Value) := by
  exact contains_sound (entropyPair_enclosed Z3_5_0H0Value Z3_5_0H0Terms Z3_5_0H0Terms_sound) (by decide +kernel)
def Z3_5_0H0Mass : Ball := ⟨1, (49 / 25000000000000000000000000000000)⟩
lemma Z3_5_0H0Mass_sound : Z3_5_0H0Mass.Encloses (∑ a, Z3_5_0H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_5_0Half 0) Z3_5_0H0Value (Z3_5_0Half_sound 0)) (by decide +kernel)
def Z3_5_0H0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_5_0H0MassTermLog : Ball := ⟨0, (10587911939 / 50000000000000000000000000000000)⟩
lemma Z3_5_0H0MassTermLog_sound : Z3_5_0H0MassTermLog.Encloses (Real.log ((∑ a, Z3_5_0H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0H0Mass_sound) (w := Z3_5_0H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H0MassTerm : Ball := ⟨0, (21175823879 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0MassTerm_sound : Z3_5_0H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_5_0H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0H0Mass_sound) Z3_5_0H0MassTermLog_sound) (by decide +kernel)
def Z3_5_0H0H : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (94809559569 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H0H_sound : Z3_5_0H0H.Encloses (homogeneousEntropy Z3_5_0H0Value) := by
  exact contains_sound (homogeneous_enclosed Z3_5_0H0Value Z3_5_0H0MassTerm_sound Z3_5_0H0Entropy_sound) (by decide +kernel)
def Z3_5_0H1Value (a : PairSlot) : ℝ := (halfLaw (shape 3 5 0) 1 a : ℝ)
def Z3_5_0H1E_1_5LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H1E_1_5Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_1_5Log_sound : Z3_5_0H1E_1_5Log.Encloses (Real.log (Z3_5_0H1Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((1,5) : PairSlot)) (w := Z3_5_0H1E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_1_5 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0H1E_1_5_sound : Z3_5_0H1E_1_5.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((1,5) : PairSlot)) Z3_5_0H1E_1_5Log_sound) (by decide +kernel)
def Z3_5_0H1E_2_4LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H1E_2_4Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_2_4Log_sound : Z3_5_0H1E_2_4Log.Encloses (Real.log (Z3_5_0H1Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((2,4) : PairSlot)) (w := Z3_5_0H1E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_2_4 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_2_4_sound : Z3_5_0H1E_2_4.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((2,4) : PairSlot)) Z3_5_0H1E_2_4Log_sound) (by decide +kernel)
def Z3_5_0H1E_3_4LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H1E_3_4Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0H1E_3_4Log_sound : Z3_5_0H1E_3_4Log.Encloses (Real.log (Z3_5_0H1Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((3,4) : PairSlot)) (w := Z3_5_0H1E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_3_4 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0H1E_3_4_sound : Z3_5_0H1E_3_4.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((3,4) : PairSlot)) Z3_5_0H1E_3_4Log_sound) (by decide +kernel)
def Z3_5_0H1E_4_2LogWitness : LogWitness := ⟨-2, 21453059186785379874419022991011, 12500000000000000000000000000000⟩
def Z3_5_0H1E_4_2Log : Ball := ⟨(-21153893769818758883005723975117 / 25000000000000000000000000000000), (63527471251 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_4_2Log_sound : Z3_5_0H1E_4_2Log.Encloses (Real.log (Z3_5_0H1Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((4,2) : PairSlot)) (w := Z3_5_0H1E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_4_2 : Ball := ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_4_2_sound : Z3_5_0H1E_4_2.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((4,2) : PairSlot)) Z3_5_0H1E_4_2Log_sound) (by decide +kernel)
def Z3_5_0H1E_4_3LogWitness : LogWitness := ⟨-5, 2256392399897361854853853147931, 1562500000000000000000000000000⟩
def Z3_5_0H1E_4_3Log : Ball := ⟨(-309825575079275035532022838613839 / 100000000000000000000000000000000), (31019273 / 24414062500000000000000000000)⟩
lemma Z3_5_0H1E_4_3Log_sound : Z3_5_0H1E_4_3Log.Encloses (Real.log (Z3_5_0H1Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((4,3) : PairSlot)) (w := Z3_5_0H1E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_4_3 : Ball := ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
lemma Z3_5_0H1E_4_3_sound : Z3_5_0H1E_4_3.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((4,3) : PairSlot)) Z3_5_0H1E_4_3Log_sound) (by decide +kernel)
def Z3_5_0H1E_5_1LogWitness : LogWitness := ⟨-6, 645274206658629135363561930529, 390625000000000000000000000000⟩
def Z3_5_0H1E_5_1Log : Ball := ⟨(-365695575079275035532022819518357 / 100000000000000000000000000000000), (148230766013 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1E_5_1Log_sound : Z3_5_0H1E_5_1Log.Encloses (Real.log (Z3_5_0H1Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_5_0Half_sound 1) ((5,1) : PairSlot)) (w := Z3_5_0H1E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1E_5_1 : Ball := ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
lemma Z3_5_0H1E_5_1_sound : Z3_5_0H1E_5_1.Encloses (Foundation.entropyTerm (Z3_5_0H1Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 1) ((5,1) : PairSlot)) Z3_5_0H1E_5_1Log_sound) (by decide +kernel)
def Z3_5_0H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 4, 2 => ⟨(4538157350748923372425986557083 / 12500000000000000000000000000000), (27257172089 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(13981761458054113306784224791891 / 100000000000000000000000000000000), (716714517 / 12500000000000000000000000000000)⟩
  | 5, 1 => ⟨(1887791376702802768234330198239 / 20000000000000000000000000000000), (191298981 / 5000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_5_0H1Terms_sound (a : PairSlot) :
    (Z3_5_0H1Terms a).Encloses (Foundation.entropyTerm (Z3_5_0H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((1,4) : PairSlot))) Z3_5_0H1E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((2,3) : PairSlot))) Z3_5_0H1E_2_4_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((3,3) : PairSlot))) Z3_5_0H1E_3_4_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((4,1) : PairSlot))) Z3_5_0H1E_4_2_sound Z3_5_0H1E_4_3_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((5,0) : PairSlot))) Z3_5_0H1E_5_1_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 1) ((5,5) : PairSlot)))
def Z3_5_0H1Entropy : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (7363373569 / 10000000000000000000000000000000)⟩
lemma Z3_5_0H1Entropy_sound : Z3_5_0H1Entropy.Encloses (Foundation.finiteEntropy Z3_5_0H1Value) := by
  exact contains_sound (entropyPair_enclosed Z3_5_0H1Value Z3_5_0H1Terms Z3_5_0H1Terms_sound) (by decide +kernel)
def Z3_5_0H1Mass : Ball := ⟨1, (49 / 25000000000000000000000000000000)⟩
lemma Z3_5_0H1Mass_sound : Z3_5_0H1Mass.Encloses (∑ a, Z3_5_0H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_5_0Half 1) Z3_5_0H1Value (Z3_5_0Half_sound 1)) (by decide +kernel)
def Z3_5_0H1MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_5_0H1MassTermLog : Ball := ⟨0, (10587911939 / 50000000000000000000000000000000)⟩
lemma Z3_5_0H1MassTermLog_sound : Z3_5_0H1MassTermLog.Encloses (Real.log ((∑ a, Z3_5_0H1Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z3_5_0H1Mass_sound) (w := Z3_5_0H1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_5_0H1MassTerm : Ball := ⟨0, (21175823879 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1MassTerm_sound : Z3_5_0H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_5_0H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0H1Mass_sound) Z3_5_0H1MassTermLog_sound) (by decide +kernel)
def Z3_5_0H1H : Ball := ⟨(238903908590238056509455072959 / 200000000000000000000000000000), (94809559569 / 100000000000000000000000000000000)⟩
lemma Z3_5_0H1H_sound : Z3_5_0H1H.Encloses (homogeneousEntropy Z3_5_0H1Value) := by
  exact contains_sound (homogeneous_enclosed Z3_5_0H1Value Z3_5_0H1MassTerm_sound Z3_5_0H1Entropy_sound) (by decide +kernel)
def Z3_5_0H2Value (a : PairSlot) : ℝ := (halfLaw (shape 3 5 0) 2 a : ℝ)
def Z3_5_0H2E_0_0Log : Ball := .exact 0
lemma Z3_5_0H2E_0_0Log_sound : Z3_5_0H2E_0_0Log.Encloses (Real.log (Z3_5_0H2Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z3_5_0Half_sound 2) ((0,0) : PairSlot))
def Z3_5_0H2E_0_0 : Ball := ⟨0, 0⟩
lemma Z3_5_0H2E_0_0_sound : Z3_5_0H2E_0_0.Encloses (Foundation.entropyTerm (Z3_5_0H2Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_5_0Half_sound 2) ((0,0) : PairSlot)) Z3_5_0H2E_0_0Log_sound) (by decide +kernel)
def Z3_5_0H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z3_5_0H2Terms_sound (a : PairSlot) :
    (Z3_5_0H2Terms a).Encloses (Foundation.entropyTerm (Z3_5_0H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z3_5_0H2E_0_0_sound (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_5_0Half_sound 2) ((5,5) : PairSlot)))
def Z3_5_0H2Entropy : Ball := ⟨0, 0⟩
lemma Z3_5_0H2Entropy_sound : Z3_5_0H2Entropy.Encloses (Foundation.finiteEntropy Z3_5_0H2Value) := by
  exact contains_sound (entropyPair_enclosed Z3_5_0H2Value Z3_5_0H2Terms Z3_5_0H2Terms_sound) (by decide +kernel)
def Z3_5_0H2Mass : Ball := ⟨1, 0⟩
lemma Z3_5_0H2Mass_sound : Z3_5_0H2Mass.Encloses (∑ a, Z3_5_0H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_5_0Half 2) Z3_5_0H2Value (Z3_5_0Half_sound 2)) (by decide +kernel)
def Z3_5_0H2MassTermLog : Ball := .exact 0
lemma Z3_5_0H2MassTermLog_sound : Z3_5_0H2MassTermLog.Encloses (Real.log ((∑ a, Z3_5_0H2Value a))) := by
  exact log_exact_one_ball (Z3_5_0H2Mass_sound)
def Z3_5_0H2MassTerm : Ball := ⟨0, 0⟩
lemma Z3_5_0H2MassTerm_sound : Z3_5_0H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_5_0H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_5_0H2Mass_sound) Z3_5_0H2MassTermLog_sound) (by decide +kernel)
def Z3_5_0H2H : Ball := ⟨0, 0⟩
lemma Z3_5_0H2H_sound : Z3_5_0H2H.Encloses (homogeneousEntropy Z3_5_0H2Value) := by
  exact contains_sound (homogeneous_enclosed Z3_5_0H2Value Z3_5_0H2MassTerm_sound Z3_5_0H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
