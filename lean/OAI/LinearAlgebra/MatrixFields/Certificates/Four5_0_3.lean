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
def Z5_0_3Raw (ij : PairSlot) : Ball :=
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
  | 1, 5 => w139
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w203
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w203
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w139
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z5_0_3Raw_sound_0 (j : Fin 6) :
    (Z5_0_3Raw (0,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (0,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (0,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 0 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_1 (j : Fin 6) :
    (Z5_0_3Raw (1,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (1,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (1,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 1 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 1 5 = (-7811) := by decide +kernel
    rw [he]
    exact w139_sound
lemma Z5_0_3Raw_sound_2 (j : Fin 6) :
    (Z5_0_3Raw (2,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (2,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (2,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 4 = (21870) := by decide +kernel
    rw [he]
    exact w203_sound
  · change (Z5_0_3Raw (2,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 2 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_3 (j : Fin 6) :
    (Z5_0_3Raw (3,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (3,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (3,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 3 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_4 (j : Fin 6) :
    (Z5_0_3Raw (4,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (4,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 2 = (21870) := by decide +kernel
    rw [he]
    exact w203_sound
  · change (Z5_0_3Raw (4,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (4,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 4 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound_5 (j : Fin 6) :
    (Z5_0_3Raw (5,j)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 j) : ℝ) := by
  fin_cases j
  · change (Z5_0_3Raw (5,0)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 0) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,1)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 1) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 1 = (-7811) := by decide +kernel
    rw [he]
    exact w139_sound
  · change (Z5_0_3Raw (5,2)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 2) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,3)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 3) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,4)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 4) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z5_0_3Raw (5,5)).Encloses (weight (orderedPairInteger (shape 5 0 3) 5 5) : ℝ)
    have he : orderedPairInteger (shape 5 0 3) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z5_0_3Raw_sound (ij : PairSlot) :
    (Z5_0_3Raw ij).Encloses (weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z5_0_3Raw_sound_0 j) (Z5_0_3Raw_sound_1 j) (Z5_0_3Raw_sound_2 j) (Z5_0_3Raw_sound_3 j) (Z5_0_3Raw_sound_4 j) (Z5_0_3Raw_sound_5 j)
def Z5_0_3Den : Ball := ⟨(518317484278105540989009344894649 / 25000000000000000000000000000000), (983 / 50000000000000000000000000000000)⟩
lemma Z5_0_3Den_sound : Z5_0_3Den.Encloses
    (((orderedPairs (shape 5 0 3)).map (fun ij => weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 5 0 3)) Z5_0_3Raw
    (fun ij => weight (orderedPairInteger (shape 5 0 3) ij.1 ij.2))
    (fun ij _ => Z5_0_3Raw_sound ij)) (by decide +kernel)
lemma Z5_0_3Den_pos : 0 < Z5_0_3Den.lower := by decide +kernel
def Z5_0_3Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(2208598281054095678468725843991 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 4 => ⟨(42968103111757469343913723803283 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 3, 4 => ⟨(2411649303594217488808775176363 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(42968103111757469343913723803283 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 4, 3 => ⟨(2411649303594217488808775176363 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(2208598281054095678468725843991 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z5_0_3Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 5 0 3) →
    contains (.mul (Z5_0_3Raw (i,j)) (.inv Z5_0_3Den)) (Z5_0_3Probs (i,j)) = true := by
  decide +kernel
lemma Z5_0_3Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 5 0 3) → Z5_0_3Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z5_0_3Probs_sound (ij : PairSlot) :
    (Z5_0_3Probs ij).Encloses (zeroPairLaw (shape 5 0 3) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 5 0 3)
  · have hb := contains_sound (Ball.mul_sound (Z5_0_3Raw_sound ij)
      (Ball.inv_sound Z5_0_3Den_sound Z5_0_3Den_pos)) (Z5_0_3Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z5_0_3Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z5_0_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 5 0 3) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 5 0 3) then Z5_0_3Probs ij
  else Z5_0_3Probs (kappa ij.1, kappa ij.2)
lemma Z5_0_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z5_0_3Half w ij).Encloses (halfLaw (shape 5 0 3) w ij : ℝ) := by
  have hp : positive (shape 5 0 3) = false := by decide +kernel
  simp only [Z5_0_3Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z5_0_3Probs_sound _
  · exact Z5_0_3Probs_sound _

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
def Z5_0_3Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 5 0 3) a.1 a.2 : ℝ)
def Z5_0_3E_1_5LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3E_1_5Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_1_5Log_sound : Z5_0_3E_1_5Log.Encloses (Real.log (Z5_0_3Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((1,5) : PairSlot)) (w := Z5_0_3E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_1_5 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3E_1_5_sound : Z5_0_3E_1_5.Encloses (Foundation.entropyTerm (Z5_0_3Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((1,5) : PairSlot)) Z5_0_3E_1_5Log_sound) (by decide +kernel)
def Z5_0_3E_2_4LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3E_2_4Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_2_4Log_sound : Z5_0_3E_2_4Log.Encloses (Real.log (Z5_0_3Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((2,4) : PairSlot)) (w := Z5_0_3E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_2_4 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3E_2_4_sound : Z5_0_3E_2_4.Encloses (Foundation.entropyTerm (Z5_0_3Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((2,4) : PairSlot)) Z5_0_3E_2_4Log_sound) (by decide +kernel)
def Z5_0_3E_3_4LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3E_3_4Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_3_4Log_sound : Z5_0_3E_3_4Log.Encloses (Real.log (Z5_0_3Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((3,4) : PairSlot)) (w := Z5_0_3E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_3_4 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3E_3_4_sound : Z5_0_3E_3_4.Encloses (Foundation.entropyTerm (Z5_0_3Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((3,4) : PairSlot)) Z5_0_3E_3_4Log_sound) (by decide +kernel)
def Z5_0_3E_4_2LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3E_4_2Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_4_2Log_sound : Z5_0_3E_4_2Log.Encloses (Real.log (Z5_0_3Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((4,2) : PairSlot)) (w := Z5_0_3E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_4_2 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3E_4_2_sound : Z5_0_3E_4_2.Encloses (Foundation.entropyTerm (Z5_0_3Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((4,2) : PairSlot)) Z5_0_3E_4_2Log_sound) (by decide +kernel)
def Z5_0_3E_4_3LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3E_4_3Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_4_3Log_sound : Z5_0_3E_4_3Log.Encloses (Real.log (Z5_0_3Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((4,3) : PairSlot)) (w := Z5_0_3E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_4_3 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3E_4_3_sound : Z5_0_3E_4_3.Encloses (Foundation.entropyTerm (Z5_0_3Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((4,3) : PairSlot)) Z5_0_3E_4_3Log_sound) (by decide +kernel)
def Z5_0_3E_5_1LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3E_5_1Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3E_5_1Log_sound : Z5_0_3E_5_1Log.Encloses (Real.log (Z5_0_3Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3Probs_sound ((5,1) : PairSlot)) (w := Z5_0_3E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3E_5_1 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3E_5_1_sound : Z5_0_3E_5_1.Encloses (Foundation.entropyTerm (Z5_0_3Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3Probs_sound ((5,1) : PairSlot)) Z5_0_3E_5_1Log_sound) (by decide +kernel)
def Z5_0_3Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 3, 4 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 4, 3 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z5_0_3Terms_sound (a : PairSlot) :
    (Z5_0_3Terms a).Encloses (Foundation.entropyTerm (Z5_0_3Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((1,4) : PairSlot))) Z5_0_3E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((2,3) : PairSlot))) Z5_0_3E_2_4_sound (entropyTerm_zero_ball (Z5_0_3Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((3,3) : PairSlot))) Z5_0_3E_3_4_sound (entropyTerm_zero_ball (Z5_0_3Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((4,1) : PairSlot))) Z5_0_3E_4_2_sound Z5_0_3E_4_3_sound (entropyTerm_zero_ball (Z5_0_3Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z5_0_3Probs_sound ((5,0) : PairSlot))) Z5_0_3E_5_1_sound (entropyTerm_zero_ball (Z5_0_3Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z5_0_3Probs_sound ((5,5) : PairSlot)))
def Z5_0_3Entropy : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (9174652717 / 12500000000000000000000000000000)⟩
lemma Z5_0_3Entropy_sound : Z5_0_3Entropy.Encloses (Foundation.finiteEntropy Z5_0_3Value) := by
  exact contains_sound (entropyPair_enclosed Z5_0_3Value Z5_0_3Terms Z5_0_3Terms_sound) (by decide +kernel)
def Z5_0_3Labels : Ball := ⟨(64195374706788471650300819324119 / 12500000000000000000000000000000), (311595391 / 195312500000000000000000000000)⟩
lemma Z5_0_3Labels_sound : Z5_0_3Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 5 0 3) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z5_0_3Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z5_0_3Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z5_0_3Four : Ball := ⟨(79030250030444364365113856449901 / 12500000000000000000000000000000), (29116757741 / 12500000000000000000000000000000)⟩
lemma Z5_0_3Four_sound : Z5_0_3Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 5 0 3)) := by
  exact contains_sound (Ball.add_sound Z5_0_3Entropy_sound Z5_0_3Labels_sound) (by decide +kernel)
def Z5_0_3H0Value (a : PairSlot) : ℝ := (halfLaw (shape 5 0 3) 0 a : ℝ)
def Z5_0_3H0E_1_5LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H0E_1_5Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_1_5Log_sound : Z5_0_3H0E_1_5Log.Encloses (Real.log (Z5_0_3H0Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((1,5) : PairSlot)) (w := Z5_0_3H0E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_1_5 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3H0E_1_5_sound : Z5_0_3H0E_1_5.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((1,5) : PairSlot)) Z5_0_3H0E_1_5Log_sound) (by decide +kernel)
def Z5_0_3H0E_2_4LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H0E_2_4Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_2_4Log_sound : Z5_0_3H0E_2_4Log.Encloses (Real.log (Z5_0_3H0Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((2,4) : PairSlot)) (w := Z5_0_3H0E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_2_4 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3H0E_2_4_sound : Z5_0_3H0E_2_4.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((2,4) : PairSlot)) Z5_0_3H0E_2_4Log_sound) (by decide +kernel)
def Z5_0_3H0E_3_4LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H0E_3_4Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_3_4Log_sound : Z5_0_3H0E_3_4Log.Encloses (Real.log (Z5_0_3H0Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((3,4) : PairSlot)) (w := Z5_0_3H0E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_3_4 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H0E_3_4_sound : Z5_0_3H0E_3_4.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((3,4) : PairSlot)) Z5_0_3H0E_3_4Log_sound) (by decide +kernel)
def Z5_0_3H0E_4_2LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H0E_4_2Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_4_2Log_sound : Z5_0_3H0E_4_2Log.Encloses (Real.log (Z5_0_3H0Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((4,2) : PairSlot)) (w := Z5_0_3H0E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_4_2 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3H0E_4_2_sound : Z5_0_3H0E_4_2.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((4,2) : PairSlot)) Z5_0_3H0E_4_2Log_sound) (by decide +kernel)
def Z5_0_3H0E_4_3LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H0E_4_3Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_4_3Log_sound : Z5_0_3H0E_4_3Log.Encloses (Real.log (Z5_0_3H0Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((4,3) : PairSlot)) (w := Z5_0_3H0E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_4_3 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H0E_4_3_sound : Z5_0_3H0E_4_3.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((4,3) : PairSlot)) Z5_0_3H0E_4_3Log_sound) (by decide +kernel)
def Z5_0_3H0E_5_1LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H0E_5_1Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0E_5_1Log_sound : Z5_0_3H0E_5_1Log.Encloses (Real.log (Z5_0_3H0Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 0) ((5,1) : PairSlot)) (w := Z5_0_3H0E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0E_5_1 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3H0E_5_1_sound : Z5_0_3H0E_5_1.Encloses (Foundation.entropyTerm (Z5_0_3H0Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 0) ((5,1) : PairSlot)) Z5_0_3H0E_5_1Log_sound) (by decide +kernel)
def Z5_0_3H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 3, 4 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 4, 3 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z5_0_3H0Terms_sound (a : PairSlot) :
    (Z5_0_3H0Terms a).Encloses (Foundation.entropyTerm (Z5_0_3H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((1,4) : PairSlot))) Z5_0_3H0E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((2,3) : PairSlot))) Z5_0_3H0E_2_4_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((3,3) : PairSlot))) Z5_0_3H0E_3_4_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((4,1) : PairSlot))) Z5_0_3H0E_4_2_sound Z5_0_3H0E_4_3_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((5,0) : PairSlot))) Z5_0_3H0E_5_1_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 0) ((5,5) : PairSlot)))
def Z5_0_3H0Entropy : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (9174652717 / 12500000000000000000000000000000)⟩
lemma Z5_0_3H0Entropy_sound : Z5_0_3H0Entropy.Encloses (Foundation.finiteEntropy Z5_0_3H0Value) := by
  exact contains_sound (entropyPair_enclosed Z5_0_3H0Value Z5_0_3H0Terms Z5_0_3H0Terms_sound) (by decide +kernel)
def Z5_0_3H0Mass : Ball := ⟨1, (3 / 1562500000000000000000000000000)⟩
lemma Z5_0_3H0Mass_sound : Z5_0_3H0Mass.Encloses (∑ a, Z5_0_3H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z5_0_3Half 0) Z5_0_3H0Value (Z5_0_3Half_sound 0)) (by decide +kernel)
def Z5_0_3H0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z5_0_3H0MassTermLog : Ball := ⟨0, (10587911937 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H0MassTermLog_sound : Z5_0_3H0MassTermLog.Encloses (Real.log ((∑ a, Z5_0_3H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3H0Mass_sound) (w := Z5_0_3H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H0MassTerm : Ball := ⟨0, (169406591 / 800000000000000000000000000000)⟩
lemma Z5_0_3H0MassTerm_sound : Z5_0_3H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z5_0_3H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3H0Mass_sound) Z5_0_3H0MassTermLog_sound) (by decide +kernel)
def Z5_0_3H0H : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (94573045611 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H0H_sound : Z5_0_3H0H.Encloses (homogeneousEntropy Z5_0_3H0Value) := by
  exact contains_sound (homogeneous_enclosed Z5_0_3H0Value Z5_0_3H0MassTerm_sound Z5_0_3H0Entropy_sound) (by decide +kernel)
def Z5_0_3H1Value (a : PairSlot) : ℝ := (halfLaw (shape 5 0 3) 1 a : ℝ)
def Z5_0_3H1E_0_0Log : Ball := .exact 0
lemma Z5_0_3H1E_0_0Log_sound : Z5_0_3H1E_0_0Log.Encloses (Real.log (Z5_0_3H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z5_0_3Half_sound 1) ((0,0) : PairSlot))
def Z5_0_3H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z5_0_3H1E_0_0_sound : Z5_0_3H1E_0_0.Encloses (Foundation.entropyTerm (Z5_0_3H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 1) ((0,0) : PairSlot)) Z5_0_3H1E_0_0Log_sound) (by decide +kernel)
def Z5_0_3H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z5_0_3H1Terms_sound (a : PairSlot) :
    (Z5_0_3H1Terms a).Encloses (Foundation.entropyTerm (Z5_0_3H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z5_0_3H1E_0_0_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 1) ((5,5) : PairSlot)))
def Z5_0_3H1Entropy : Ball := ⟨0, 0⟩
lemma Z5_0_3H1Entropy_sound : Z5_0_3H1Entropy.Encloses (Foundation.finiteEntropy Z5_0_3H1Value) := by
  exact contains_sound (entropyPair_enclosed Z5_0_3H1Value Z5_0_3H1Terms Z5_0_3H1Terms_sound) (by decide +kernel)
def Z5_0_3H1Mass : Ball := ⟨1, 0⟩
lemma Z5_0_3H1Mass_sound : Z5_0_3H1Mass.Encloses (∑ a, Z5_0_3H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z5_0_3Half 1) Z5_0_3H1Value (Z5_0_3Half_sound 1)) (by decide +kernel)
def Z5_0_3H1MassTermLog : Ball := .exact 0
lemma Z5_0_3H1MassTermLog_sound : Z5_0_3H1MassTermLog.Encloses (Real.log ((∑ a, Z5_0_3H1Value a))) := by
  exact log_exact_one_ball (Z5_0_3H1Mass_sound)
def Z5_0_3H1MassTerm : Ball := ⟨0, 0⟩
lemma Z5_0_3H1MassTerm_sound : Z5_0_3H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z5_0_3H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3H1Mass_sound) Z5_0_3H1MassTermLog_sound) (by decide +kernel)
def Z5_0_3H1H : Ball := ⟨0, 0⟩
lemma Z5_0_3H1H_sound : Z5_0_3H1H.Encloses (homogeneousEntropy Z5_0_3H1Value) := by
  exact contains_sound (homogeneous_enclosed Z5_0_3H1Value Z5_0_3H1MassTerm_sound Z5_0_3H1Entropy_sound) (by decide +kernel)
def Z5_0_3H2Value (a : PairSlot) : ℝ := (halfLaw (shape 5 0 3) 2 a : ℝ)
def Z5_0_3H2E_4_0LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H2E_4_0Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_4_0Log_sound : Z5_0_3H2E_4_0Log.Encloses (Real.log (Z5_0_3H2Value ((4,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((4,0) : PairSlot)) (w := Z5_0_3H2E_4_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_4_0 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3H2E_4_0_sound : Z5_0_3H2E_4_0.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((4,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((4,0) : PairSlot)) Z5_0_3H2E_4_0Log_sound) (by decide +kernel)
def Z5_0_3H2E_2_1LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H2E_2_1Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_2_1Log_sound : Z5_0_3H2E_2_1Log.Encloses (Real.log (Z5_0_3H2Value ((2,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((2,1) : PairSlot)) (w := Z5_0_3H2E_2_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_2_1 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3H2E_2_1_sound : Z5_0_3H2E_2_1.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((2,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((2,1) : PairSlot)) Z5_0_3H2E_2_1Log_sound) (by decide +kernel)
def Z5_0_3H2E_3_1LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H2E_3_1Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_3_1Log_sound : Z5_0_3H2E_3_1Log.Encloses (Real.log (Z5_0_3H2Value ((3,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((3,1) : PairSlot)) (w := Z5_0_3H2E_3_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_3_1 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H2E_3_1_sound : Z5_0_3H2E_3_1.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((3,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((3,1) : PairSlot)) Z5_0_3H2E_3_1Log_sound) (by decide +kernel)
def Z5_0_3H2E_1_2LogWitness : LogWitness := ⟨-2, 42968103111757469343913723803283, 25000000000000000000000000000000⟩
def Z5_0_3H2E_1_2Log : Ball := ⟨(-42235606682705802179939545154249 / 50000000000000000000000000000000), (63527471249 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_1_2Log_sound : Z5_0_3H2E_1_2Log.Encloses (Real.log (Z5_0_3H2Value ((1,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((1,2) : PairSlot)) (w := Z5_0_3H2E_1_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_1_2 : Ball := ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
lemma Z5_0_3H2E_1_2_sound : Z5_0_3H2E_1_2.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((1,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((1,2) : PairSlot)) Z5_0_3H2E_1_2Log_sound) (by decide +kernel)
def Z5_0_3H2E_1_3LogWitness : LogWitness := ⟨-5, 2411649303594217488808775176363, 1562500000000000000000000000000⟩
def Z5_0_3H2E_1_3Log : Ball := ⟨(-303171213365411604359879033021803 / 100000000000000000000000000000000), (127054942201 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_1_3Log_sound : Z5_0_3H2E_1_3Log.Encloses (Real.log (Z5_0_3H2Value ((1,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((1,3) : PairSlot)) (w := Z5_0_3H2E_1_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_1_3 : Ball := ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H2E_1_3_sound : Z5_0_3H2E_1_3.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((1,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((1,3) : PairSlot)) Z5_0_3H2E_1_3Log_sound) (by decide +kernel)
def Z5_0_3H2E_0_4LogWitness : LogWitness := ⟨-6, 2208598281054095678468725843991, 1562500000000000000000000000000⟩
def Z5_0_3H2E_0_4Log : Ball := ⟨(-381281213365411604359879013926363 / 100000000000000000000000000000000), (148230766007 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2E_0_4Log_sound : Z5_0_3H2E_0_4Log.Encloses (Real.log (Z5_0_3H2Value ((0,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z5_0_3Half_sound 2) ((0,4) : PairSlot)) (w := Z5_0_3H2E_0_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2E_0_4 : Ball := ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
lemma Z5_0_3H2E_0_4_sound : Z5_0_3H2E_0_4.Encloses (Foundation.entropyTerm (Z5_0_3H2Value ((0,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z5_0_3Half_sound 2) ((0,4) : PairSlot)) Z5_0_3H2E_0_4Log_sound) (by decide +kernel)
def Z5_0_3H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | 2, 1 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 3, 1 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 1, 2 => ⟨(36295678058602714916587164090917 / 100000000000000000000000000000000), (1706034339 / 6250000000000000000000000000000)⟩
  | 1, 3 => ⟨(7311426455825088170477182923379 / 50000000000000000000000000000000), (3064119637 / 50000000000000000000000000000000)⟩
  | 0, 4 => ⟨(8420970324370679601710618565453 / 100000000000000000000000000000000), (327382217 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z5_0_3H2Terms_sound (a : PairSlot) :
    (Z5_0_3H2Terms a).Encloses (Foundation.entropyTerm (Z5_0_3H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((0,3) : PairSlot))) Z5_0_3H2E_0_4_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((1,1) : PairSlot))) Z5_0_3H2E_1_2_sound Z5_0_3H2E_1_3_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((2,0) : PairSlot))) Z5_0_3H2E_2_1_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((3,0) : PairSlot))) Z5_0_3H2E_3_1_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 Z5_0_3H2E_4_0_sound (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z5_0_3Half_sound 2) ((5,5) : PairSlot)))
def Z5_0_3H2Entropy : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (9174652717 / 12500000000000000000000000000000)⟩
lemma Z5_0_3H2Entropy_sound : Z5_0_3H2Entropy.Encloses (Foundation.finiteEntropy Z5_0_3H2Value) := by
  exact contains_sound (entropyPair_enclosed Z5_0_3H2Value Z5_0_3H2Terms Z5_0_3H2Terms_sound) (by decide +kernel)
def Z5_0_3H2Mass : Ball := ⟨1, (3 / 1562500000000000000000000000000)⟩
lemma Z5_0_3H2Mass_sound : Z5_0_3H2Mass.Encloses (∑ a, Z5_0_3H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z5_0_3Half 2) Z5_0_3H2Value (Z5_0_3Half_sound 2)) (by decide +kernel)
def Z5_0_3H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z5_0_3H2MassTermLog : Ball := ⟨0, (10587911937 / 50000000000000000000000000000000)⟩
lemma Z5_0_3H2MassTermLog_sound : Z5_0_3H2MassTermLog.Encloses (Real.log ((∑ a, Z5_0_3H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z5_0_3H2Mass_sound) (w := Z5_0_3H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z5_0_3H2MassTerm : Ball := ⟨0, (169406591 / 800000000000000000000000000000)⟩
lemma Z5_0_3H2MassTerm_sound : Z5_0_3H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z5_0_3H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z5_0_3H2Mass_sound) Z5_0_3H2MassTermLog_sound) (by decide +kernel)
def Z5_0_3H2H : Ball := ⟨(7417437661827946357406518562891 / 6250000000000000000000000000000), (94573045611 / 100000000000000000000000000000000)⟩
lemma Z5_0_3H2H_sound : Z5_0_3H2H.Encloses (homogeneousEntropy Z5_0_3H2Value) := by
  exact contains_sound (homogeneous_enclosed Z5_0_3H2Value Z5_0_3H2MassTerm_sound Z5_0_3H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
