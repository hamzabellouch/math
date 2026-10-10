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
def Z0_5_3Raw (ij : PairSlot) : Ball :=
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
  | 1, 5 => w158
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w211
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w211
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w158
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z0_5_3Raw_sound_0 (j : Fin 6) :
    (Z0_5_3Raw (0,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (0,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (0,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 0 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_1 (j : Fin 6) :
    (Z0_5_3Raw (1,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (1,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (1,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 1 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 1 5 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
lemma Z0_5_3Raw_sound_2 (j : Fin 6) :
    (Z0_5_3Raw (2,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (2,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (2,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 4 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (2,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 2 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_3 (j : Fin 6) :
    (Z0_5_3Raw (3,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (3,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (3,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 3 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_4 (j : Fin 6) :
    (Z0_5_3Raw (4,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (4,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 2 = (23895) := by decide +kernel
    rw [he]
    exact w211_sound
  · change (Z0_5_3Raw (4,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (4,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 4 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound_5 (j : Fin 6) :
    (Z0_5_3Raw (5,j)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 j) : ℝ) := by
  fin_cases j
  · change (Z0_5_3Raw (5,0)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 0) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,1)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 1) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 1 = (-6216) := by decide +kernel
    rw [he]
    exact w158_sound
  · change (Z0_5_3Raw (5,2)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 2) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,3)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 3) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,4)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 4) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z0_5_3Raw (5,5)).Encloses (weight (orderedPairInteger (shape 0 5 3) 5 5) : ℝ)
    have he : orderedPairInteger (shape 0 5 3) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z0_5_3Raw_sound (ij : PairSlot) :
    (Z0_5_3Raw ij).Encloses (weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z0_5_3Raw_sound_0 j) (Z0_5_3Raw_sound_1 j) (Z0_5_3Raw_sound_2 j) (Z0_5_3Raw_sound_3 j) (Z0_5_3Raw_sound_4 j) (Z0_5_3Raw_sound_5 j)
def Z0_5_3Den : Ball := ⟨(1244512297472617284129636959856319 / 50000000000000000000000000000000), (59 / 2500000000000000000000000000000)⟩
lemma Z0_5_3Den_sound : Z0_5_3Den.Encloses
    (((orderedPairs (shape 0 5 3)).map (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 0 5 3)) Z0_5_3Raw
    (fun ij => weight (orderedPairInteger (shape 0 5 3) ij.1 ij.2))
    (fun ij _ => Z0_5_3Raw_sound ij)) (by decide +kernel)
lemma Z0_5_3Den_pos : 0 < Z0_5_3Den.lower := by decide +kernel
def Z0_5_3Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(2157810797800214543118318532199 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(4382455112007387232015528108533 / 10000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(4017638082125913136726400382471 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 2 => ⟨(4382455112007387232015528108533 / 10000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(4017638082125913136726400382471 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2157810797800214543118318532199 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_5_3Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 0 5 3) →
    contains (.mul (Z0_5_3Raw (i,j)) (.inv Z0_5_3Den)) (Z0_5_3Probs (i,j)) = true := by
  decide +kernel
lemma Z0_5_3Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 0 5 3) → Z0_5_3Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z0_5_3Probs_sound (ij : PairSlot) :
    (Z0_5_3Probs ij).Encloses (zeroPairLaw (shape 0 5 3) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 0 5 3)
  · have hb := contains_sound (Ball.mul_sound (Z0_5_3Raw_sound ij)
      (Ball.inv_sound Z0_5_3Den_sound Z0_5_3Den_pos)) (Z0_5_3Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z0_5_3Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z0_5_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 0 5 3) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 0 5 3) then Z0_5_3Probs ij
  else Z0_5_3Probs (kappa ij.1, kappa ij.2)
lemma Z0_5_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z0_5_3Half w ij).Encloses (halfLaw (shape 0 5 3) w ij : ℝ) := by
  have hp : positive (shape 0 5 3) = false := by decide +kernel
  simp only [Z0_5_3Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z0_5_3Probs_sound _
  · exact Z0_5_3Probs_sound _

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
def Z0_5_3Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 0 5 3) a.1 a.2 : ℝ)
def Z0_5_3E_1_5LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3E_1_5Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_1_5Log_sound : Z0_5_3E_1_5Log.Encloses (Real.log (Z0_5_3Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((1,5) : PairSlot)) (w := Z0_5_3E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_1_5 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3E_1_5_sound : Z0_5_3E_1_5.Encloses (Foundation.entropyTerm (Z0_5_3Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((1,5) : PairSlot)) Z0_5_3E_1_5Log_sound) (by decide +kernel)
def Z0_5_3E_2_4LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3E_2_4Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_2_4Log_sound : Z0_5_3E_2_4Log.Encloses (Real.log (Z0_5_3Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((2,4) : PairSlot)) (w := Z0_5_3E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_2_4 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3E_2_4_sound : Z0_5_3E_2_4.Encloses (Foundation.entropyTerm (Z0_5_3Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((2,4) : PairSlot)) Z0_5_3E_2_4Log_sound) (by decide +kernel)
def Z0_5_3E_3_4LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3E_3_4Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_3_4Log_sound : Z0_5_3E_3_4Log.Encloses (Real.log (Z0_5_3Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((3,4) : PairSlot)) (w := Z0_5_3E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_3_4 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_3_4_sound : Z0_5_3E_3_4.Encloses (Foundation.entropyTerm (Z0_5_3Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((3,4) : PairSlot)) Z0_5_3E_3_4Log_sound) (by decide +kernel)
def Z0_5_3E_4_2LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3E_4_2Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_4_2Log_sound : Z0_5_3E_4_2Log.Encloses (Real.log (Z0_5_3Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((4,2) : PairSlot)) (w := Z0_5_3E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_4_2 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3E_4_2_sound : Z0_5_3E_4_2.Encloses (Foundation.entropyTerm (Z0_5_3Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((4,2) : PairSlot)) Z0_5_3E_4_2Log_sound) (by decide +kernel)
def Z0_5_3E_4_3LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3E_4_3Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_4_3Log_sound : Z0_5_3E_4_3Log.Encloses (Real.log (Z0_5_3Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((4,3) : PairSlot)) (w := Z0_5_3E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_4_3 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_4_3_sound : Z0_5_3E_4_3.Encloses (Foundation.entropyTerm (Z0_5_3Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((4,3) : PairSlot)) Z0_5_3E_4_3Log_sound) (by decide +kernel)
def Z0_5_3E_5_1LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3E_5_1Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3E_5_1Log_sound : Z0_5_3E_5_1Log.Encloses (Real.log (Z0_5_3Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3Probs_sound ((5,1) : PairSlot)) (w := Z0_5_3E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3E_5_1 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3E_5_1_sound : Z0_5_3E_5_1.Encloses (Foundation.entropyTerm (Z0_5_3Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3Probs_sound ((5,1) : PairSlot)) Z0_5_3E_5_1Log_sound) (by decide +kernel)
def Z0_5_3Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | 2, 4 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 4, 2 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_5_3Terms_sound (a : PairSlot) :
    (Z0_5_3Terms a).Encloses (Foundation.entropyTerm (Z0_5_3Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((1,4) : PairSlot))) Z0_5_3E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((2,3) : PairSlot))) Z0_5_3E_2_4_sound (entropyTerm_zero_ball (Z0_5_3Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((3,3) : PairSlot))) Z0_5_3E_3_4_sound (entropyTerm_zero_ball (Z0_5_3Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((4,1) : PairSlot))) Z0_5_3E_4_2_sound Z0_5_3E_4_3_sound (entropyTerm_zero_ball (Z0_5_3Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z0_5_3Probs_sound ((5,0) : PairSlot))) Z0_5_3E_5_1_sound (entropyTerm_zero_ball (Z0_5_3Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z0_5_3Probs_sound ((5,5) : PairSlot)))
def Z0_5_3Entropy : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (18071888221 / 25000000000000000000000000000000)⟩
lemma Z0_5_3Entropy_sound : Z0_5_3Entropy.Encloses (Foundation.finiteEntropy Z0_5_3Value) := by
  exact contains_sound (entropyPair_enclosed Z0_5_3Value Z0_5_3Terms Z0_5_3Terms_sound) (by decide +kernel)
def Z0_5_3Labels : Ball := ⟨(517959714589889087433695657320217 / 100000000000000000000000000000000), (160646509059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3Labels_sound : Z0_5_3Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 0 5 3) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z0_5_3Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z0_5_3Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z0_5_3Four : Ball := ⟨(632652374949599458782207982366691 / 100000000000000000000000000000000), (232934061943 / 100000000000000000000000000000000)⟩
lemma Z0_5_3Four_sound : Z0_5_3Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 0 5 3)) := by
  exact contains_sound (Ball.add_sound Z0_5_3Entropy_sound Z0_5_3Labels_sound) (by decide +kernel)
def Z0_5_3H0Value (a : PairSlot) : ℝ := (halfLaw (shape 0 5 3) 0 a : ℝ)
def Z0_5_3H0E_0_0Log : Ball := .exact 0
lemma Z0_5_3H0E_0_0Log_sound : Z0_5_3H0E_0_0Log.Encloses (Real.log (Z0_5_3H0Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z0_5_3Half_sound 0) ((0,0) : PairSlot))
def Z0_5_3H0E_0_0 : Ball := ⟨0, 0⟩
lemma Z0_5_3H0E_0_0_sound : Z0_5_3H0E_0_0.Encloses (Foundation.entropyTerm (Z0_5_3H0Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 0) ((0,0) : PairSlot)) Z0_5_3H0E_0_0Log_sound) (by decide +kernel)
def Z0_5_3H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z0_5_3H0Terms_sound (a : PairSlot) :
    (Z0_5_3H0Terms a).Encloses (Foundation.entropyTerm (Z0_5_3H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z0_5_3H0E_0_0_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 0) ((5,5) : PairSlot)))
def Z0_5_3H0Entropy : Ball := ⟨0, 0⟩
lemma Z0_5_3H0Entropy_sound : Z0_5_3H0Entropy.Encloses (Foundation.finiteEntropy Z0_5_3H0Value) := by
  exact contains_sound (entropyPair_enclosed Z0_5_3H0Value Z0_5_3H0Terms Z0_5_3H0Terms_sound) (by decide +kernel)
def Z0_5_3H0Mass : Ball := ⟨1, 0⟩
lemma Z0_5_3H0Mass_sound : Z0_5_3H0Mass.Encloses (∑ a, Z0_5_3H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_5_3Half 0) Z0_5_3H0Value (Z0_5_3Half_sound 0)) (by decide +kernel)
def Z0_5_3H0MassTermLog : Ball := .exact 0
lemma Z0_5_3H0MassTermLog_sound : Z0_5_3H0MassTermLog.Encloses (Real.log ((∑ a, Z0_5_3H0Value a))) := by
  exact log_exact_one_ball (Z0_5_3H0Mass_sound)
def Z0_5_3H0MassTerm : Ball := ⟨0, 0⟩
lemma Z0_5_3H0MassTerm_sound : Z0_5_3H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_5_3H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3H0Mass_sound) Z0_5_3H0MassTermLog_sound) (by decide +kernel)
def Z0_5_3H0H : Ball := ⟨0, 0⟩
lemma Z0_5_3H0H_sound : Z0_5_3H0H.Encloses (homogeneousEntropy Z0_5_3H0Value) := by
  exact contains_sound (homogeneous_enclosed Z0_5_3H0Value Z0_5_3H0MassTerm_sound Z0_5_3H0Entropy_sound) (by decide +kernel)
def Z0_5_3H1Value (a : PairSlot) : ℝ := (halfLaw (shape 0 5 3) 1 a : ℝ)
def Z0_5_3H1E_1_5LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H1E_1_5Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_1_5Log_sound : Z0_5_3H1E_1_5Log.Encloses (Real.log (Z0_5_3H1Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((1,5) : PairSlot)) (w := Z0_5_3H1E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_1_5 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3H1E_1_5_sound : Z0_5_3H1E_1_5.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((1,5) : PairSlot)) Z0_5_3H1E_1_5Log_sound) (by decide +kernel)
def Z0_5_3H1E_2_4LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H1E_2_4Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_2_4Log_sound : Z0_5_3H1E_2_4Log.Encloses (Real.log (Z0_5_3H1Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((2,4) : PairSlot)) (w := Z0_5_3H1E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_2_4 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3H1E_2_4_sound : Z0_5_3H1E_2_4.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((2,4) : PairSlot)) Z0_5_3H1E_2_4Log_sound) (by decide +kernel)
def Z0_5_3H1E_3_4LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H1E_3_4Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_3_4Log_sound : Z0_5_3H1E_3_4Log.Encloses (Real.log (Z0_5_3H1Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((3,4) : PairSlot)) (w := Z0_5_3H1E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_3_4 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_3_4_sound : Z0_5_3H1E_3_4.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((3,4) : PairSlot)) Z0_5_3H1E_3_4Log_sound) (by decide +kernel)
def Z0_5_3H1E_4_2LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H1E_4_2Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_4_2Log_sound : Z0_5_3H1E_4_2Log.Encloses (Real.log (Z0_5_3H1Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((4,2) : PairSlot)) (w := Z0_5_3H1E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_4_2 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3H1E_4_2_sound : Z0_5_3H1E_4_2.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((4,2) : PairSlot)) Z0_5_3H1E_4_2Log_sound) (by decide +kernel)
def Z0_5_3H1E_4_3LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H1E_4_3Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_4_3Log_sound : Z0_5_3H1E_4_3Log.Encloses (Real.log (Z0_5_3H1Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((4,3) : PairSlot)) (w := Z0_5_3H1E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_4_3 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_4_3_sound : Z0_5_3H1E_4_3.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((4,3) : PairSlot)) Z0_5_3H1E_4_3Log_sound) (by decide +kernel)
def Z0_5_3H1E_5_1LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H1E_5_1Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1E_5_1Log_sound : Z0_5_3H1E_5_1Log.Encloses (Real.log (Z0_5_3H1Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 1) ((5,1) : PairSlot)) (w := Z0_5_3H1E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1E_5_1 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3H1E_5_1_sound : Z0_5_3H1E_5_1.Encloses (Foundation.entropyTerm (Z0_5_3H1Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 1) ((5,1) : PairSlot)) Z0_5_3H1E_5_1Log_sound) (by decide +kernel)
def Z0_5_3H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | 2, 4 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 4, 2 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_5_3H1Terms_sound (a : PairSlot) :
    (Z0_5_3H1Terms a).Encloses (Foundation.entropyTerm (Z0_5_3H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((1,4) : PairSlot))) Z0_5_3H1E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((2,3) : PairSlot))) Z0_5_3H1E_2_4_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((3,3) : PairSlot))) Z0_5_3H1E_3_4_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((4,1) : PairSlot))) Z0_5_3H1E_4_2_sound Z0_5_3H1E_4_3_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((5,0) : PairSlot))) Z0_5_3H1E_5_1_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 1) ((5,5) : PairSlot)))
def Z0_5_3H1Entropy : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (18071888221 / 25000000000000000000000000000000)⟩
lemma Z0_5_3H1Entropy_sound : Z0_5_3H1Entropy.Encloses (Foundation.finiteEntropy Z0_5_3H1Value) := by
  exact contains_sound (entropyPair_enclosed Z0_5_3H1Value Z0_5_3H1Terms Z0_5_3H1Terms_sound) (by decide +kernel)
def Z0_5_3H1Mass : Ball := ⟨1, (97 / 50000000000000000000000000000000)⟩
lemma Z0_5_3H1Mass_sound : Z0_5_3H1Mass.Encloses (∑ a, Z0_5_3H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_5_3Half 1) Z0_5_3H1Value (Z0_5_3Half_sound 1)) (by decide +kernel)
def Z0_5_3H1MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z0_5_3H1MassTermLog : Ball := ⟨0, (5293955969 / 25000000000000000000000000000000)⟩
lemma Z0_5_3H1MassTermLog_sound : Z0_5_3H1MassTermLog.Encloses (Real.log ((∑ a, Z0_5_3H1Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3H1Mass_sound) (w := Z0_5_3H1MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H1MassTerm : Ball := ⟨0, (21175823877 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1MassTerm_sound : Z0_5_3H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_5_3H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3H1Mass_sound) Z0_5_3H1MassTermLog_sound) (by decide +kernel)
def Z0_5_3H1H : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (93463376761 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H1H_sound : Z0_5_3H1H.Encloses (homogeneousEntropy Z0_5_3H1Value) := by
  exact contains_sound (homogeneous_enclosed Z0_5_3H1Value Z0_5_3H1MassTerm_sound Z0_5_3H1Entropy_sound) (by decide +kernel)
def Z0_5_3H2Value (a : PairSlot) : ℝ := (halfLaw (shape 0 5 3) 2 a : ℝ)
def Z0_5_3H2E_4_0LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H2E_4_0Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_4_0Log_sound : Z0_5_3H2E_4_0Log.Encloses (Real.log (Z0_5_3H2Value ((4,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((4,0) : PairSlot)) (w := Z0_5_3H2E_4_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_4_0 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3H2E_4_0_sound : Z0_5_3H2E_4_0.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((4,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((4,0) : PairSlot)) Z0_5_3H2E_4_0Log_sound) (by decide +kernel)
def Z0_5_3H2E_2_1LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H2E_2_1Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_2_1Log_sound : Z0_5_3H2E_2_1Log.Encloses (Real.log (Z0_5_3H2Value ((2,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((2,1) : PairSlot)) (w := Z0_5_3H2E_2_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_2_1 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3H2E_2_1_sound : Z0_5_3H2E_2_1.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((2,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((2,1) : PairSlot)) Z0_5_3H2E_2_1Log_sound) (by decide +kernel)
def Z0_5_3H2E_3_1LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H2E_3_1Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_3_1Log_sound : Z0_5_3H2E_3_1Log.Encloses (Real.log (Z0_5_3H2Value ((3,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((3,1) : PairSlot)) (w := Z0_5_3H2E_3_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_3_1 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_3_1_sound : Z0_5_3H2E_3_1.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((3,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((3,1) : PairSlot)) Z0_5_3H2E_3_1Log_sound) (by decide +kernel)
def Z0_5_3H2E_1_2LogWitness : LogWitness := ⟨-2, 4382455112007387232015528108533, 2500000000000000000000000000000⟩
def Z0_5_3H2E_1_2Log : Ball := ⟨(-41248799889359090223264863826827 / 50000000000000000000000000000000), (63527471247 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_1_2Log_sound : Z0_5_3H2E_1_2Log.Encloses (Real.log (Z0_5_3H2Value ((1,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((1,2) : PairSlot)) (w := Z0_5_3H2E_1_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_1_2 : Ball := ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
lemma Z0_5_3H2E_1_2_sound : Z0_5_3H2E_1_2.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((1,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((1,2) : PairSlot)) Z0_5_3H2E_1_2Log_sound) (by decide +kernel)
def Z0_5_3H2E_1_3LogWitness : LogWitness := ⟨-5, 4017638082125913136726400382471, 3125000000000000000000000000000⟩
def Z0_5_3H2E_1_3Log : Ball := ⟨(-321447599778718180446529670366099 / 100000000000000000000000000000000), (127054942197 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_1_3Log_sound : Z0_5_3H2E_1_3Log.Encloses (Real.log (Z0_5_3H2Value ((1,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((1,3) : PairSlot)) (w := Z0_5_3H2E_1_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_1_3 : Ball := ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_1_3_sound : Z0_5_3H2E_1_3.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((1,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((1,3) : PairSlot)) Z0_5_3H2E_1_3Log_sound) (by decide +kernel)
def Z0_5_3H2E_0_4LogWitness : LogWitness := ⟨-6, 2157810797800214543118318532199, 1562500000000000000000000000000⟩
def Z0_5_3H2E_0_4Log : Ball := ⟨(-5993868746542471569477025801103 / 1562500000000000000000000000000), (148230766059 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2E_0_4Log_sound : Z0_5_3H2E_0_4Log.Encloses (Real.log (Z0_5_3H2Value ((0,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z0_5_3Half_sound 2) ((0,4) : PairSlot)) (w := Z0_5_3H2E_0_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2E_0_4 : Ball := ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
lemma Z0_5_3H2E_0_4_sound : Z0_5_3H2E_0_4.Encloses (Foundation.entropyTerm (Z0_5_3H2Value ((0,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z0_5_3Half_sound 2) ((0,4) : PairSlot)) Z0_5_3H2E_0_4Log_sound) (by decide +kernel)
def Z0_5_3H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | 2, 1 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 3, 1 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 1, 2 => ⟨(18077101393929149380776110958019 / 50000000000000000000000000000000), (5568125837 / 20000000000000000000000000000000)⟩
  | 1, 3 => ⟨(1614325147848684263111295424987 / 12500000000000000000000000000000), (5104607757 / 100000000000000000000000000000000)⟩
  | 0, 4 => ⟨(8277526209207412807813577207303 / 100000000000000000000000000000000), (6397079 / 200000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z0_5_3H2Terms_sound (a : PairSlot) :
    (Z0_5_3H2Terms a).Encloses (Foundation.entropyTerm (Z0_5_3H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((0,3) : PairSlot))) Z0_5_3H2E_0_4_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((1,1) : PairSlot))) Z0_5_3H2E_1_2_sound Z0_5_3H2E_1_3_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((2,0) : PairSlot))) Z0_5_3H2E_2_1_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((3,0) : PairSlot))) Z0_5_3H2E_3_1_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 Z0_5_3H2E_4_0_sound (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z0_5_3Half_sound 2) ((5,5) : PairSlot)))
def Z0_5_3H2Entropy : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (18071888221 / 25000000000000000000000000000000)⟩
lemma Z0_5_3H2Entropy_sound : Z0_5_3H2Entropy.Encloses (Foundation.finiteEntropy Z0_5_3H2Value) := by
  exact contains_sound (entropyPair_enclosed Z0_5_3H2Value Z0_5_3H2Terms Z0_5_3H2Terms_sound) (by decide +kernel)
def Z0_5_3H2Mass : Ball := ⟨1, (97 / 50000000000000000000000000000000)⟩
lemma Z0_5_3H2Mass_sound : Z0_5_3H2Mass.Encloses (∑ a, Z0_5_3H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z0_5_3Half 2) Z0_5_3H2Value (Z0_5_3Half_sound 2)) (by decide +kernel)
def Z0_5_3H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z0_5_3H2MassTermLog : Ball := ⟨0, (5293955969 / 25000000000000000000000000000000)⟩
lemma Z0_5_3H2MassTermLog_sound : Z0_5_3H2MassTermLog.Encloses (Real.log ((∑ a, Z0_5_3H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z0_5_3H2Mass_sound) (w := Z0_5_3H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z0_5_3H2MassTerm : Ball := ⟨0, (21175823877 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2MassTerm_sound : Z0_5_3H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z0_5_3H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z0_5_3H2Mass_sound) Z0_5_3H2MassTermLog_sound) (by decide +kernel)
def Z0_5_3H2H : Ball := ⟨(57346330179855185674256162523237 / 50000000000000000000000000000000), (93463376761 / 100000000000000000000000000000000)⟩
lemma Z0_5_3H2H_sound : Z0_5_3H2H.Encloses (homogeneousEntropy Z0_5_3H2Value) := by
  exact contains_sound (homogeneous_enclosed Z0_5_3H2Value Z0_5_3H2MassTerm_sound Z0_5_3H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
