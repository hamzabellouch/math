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
def Z4_0_4Raw (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 0 => w195
  | 0, 1 => w195
  | 0, 2 => w195
  | 0, 3 => w195
  | 0, 4 => w195
  | 0, 5 => w132
  | 1, 0 => w195
  | 1, 1 => w195
  | 1, 2 => w195
  | 1, 3 => w195
  | 1, 4 => w213
  | 1, 5 => w195
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w220
  | 2, 3 => w206
  | 2, 4 => w195
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w206
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w213
  | 4, 2 => w195
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w132
  | 5, 1 => w195
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z4_0_4Raw_sound_0 (j : Fin 6) :
    (Z4_0_4Raw (0,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (0,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (0,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 0 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 0 5 = (-9766) := by decide +kernel
    rw [he]
    exact w132_sound
lemma Z4_0_4Raw_sound_1 (j : Fin 6) :
    (Z4_0_4Raw (1,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (1,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (1,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 4 = (28961) := by decide +kernel
    rw [he]
    exact w213_sound
  · change (Z4_0_4Raw (1,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 1 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 1 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_2 (j : Fin 6) :
    (Z4_0_4Raw (2,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (2,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 2 = (43809) := by decide +kernel
    rw [he]
    exact w220_sound
  · change (Z4_0_4Raw (2,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 3 = (22299) := by decide +kernel
    rw [he]
    exact w206_sound
  · change (Z4_0_4Raw (2,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (2,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 2 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_3 (j : Fin 6) :
    (Z4_0_4Raw (3,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (3,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 2 = (22299) := by decide +kernel
    rw [he]
    exact w206_sound
  · change (Z4_0_4Raw (3,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (3,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 3 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_4 (j : Fin 6) :
    (Z4_0_4Raw (4,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (4,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 1 = (28961) := by decide +kernel
    rw [he]
    exact w213_sound
  · change (Z4_0_4Raw (4,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (4,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 4 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound_5 (j : Fin 6) :
    (Z4_0_4Raw (5,j)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 j) : ℝ) := by
  fin_cases j
  · change (Z4_0_4Raw (5,0)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 0) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 0 = (-9766) := by decide +kernel
    rw [he]
    exact w132_sound
  · change (Z4_0_4Raw (5,1)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 1) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,2)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 2) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,3)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 3) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,4)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 4) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z4_0_4Raw (5,5)).Encloses (weight (orderedPairInteger (shape 4 0 4) 5 5) : ℝ)
    have he : orderedPairInteger (shape 4 0 4) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z4_0_4Raw_sound (ij : PairSlot) :
    (Z4_0_4Raw ij).Encloses (weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z4_0_4Raw_sound_0 j) (Z4_0_4Raw_sound_1 j) (Z4_0_4Raw_sound_2 j) (Z4_0_4Raw_sound_3 j) (Z4_0_4Raw_sound_4 j) (Z4_0_4Raw_sound_5 j)
def Z4_0_4Den : Ball := ⟨(13646777938944276882364160176219867 / 100000000000000000000000000000000), (13969 / 100000000000000000000000000000000)⟩
lemma Z4_0_4Den_sound : Z4_0_4Den.Encloses
    (((orderedPairs (shape 4 0 4)).map (fun ij => weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 4 0 4)) Z4_0_4Raw
    (fun ij => weight (orderedPairInteger (shape 4 0 4) ij.1 ij.2))
    (fun ij _ => Z4_0_4Raw_sound ij)) (by decide +kernel)
lemma Z4_0_4Den_pos : 0 < Z4_0_4Den.lower := by decide +kernel
def Z4_0_4Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 0, 5 => ⟨(55190951304569688595534186513 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4 => ⟨(6632849277085335226067309879167 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 2, 2 => ⟨(5855588794422561384849059336303 / 10000000000000000000000000000000), (121 / 100000000000000000000000000000000)⟩
  | 2, 3 => ⟨(3407007932926322989871260497747 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 2 => ⟨(3407007932926322989871260497747 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 3 => ⟨(146554740536411280359956652837 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1 => ⟨(6632849277085335226067309879167 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 5, 0 => ⟨(55190951304569688595534186513 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_0_4Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 4 0 4) →
    contains (.mul (Z4_0_4Raw (i,j)) (.inv Z4_0_4Den)) (Z4_0_4Probs (i,j)) = true := by
  decide +kernel
lemma Z4_0_4Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 4 0 4) → Z4_0_4Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z4_0_4Probs_sound (ij : PairSlot) :
    (Z4_0_4Probs ij).Encloses (zeroPairLaw (shape 4 0 4) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 4 0 4)
  · have hb := contains_sound (Ball.mul_sound (Z4_0_4Raw_sound ij)
      (Ball.inv_sound Z4_0_4Den_sound Z4_0_4Den_pos)) (Z4_0_4Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z4_0_4Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z4_0_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 4 0 4) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 4 0 4) then Z4_0_4Probs ij
  else Z4_0_4Probs (kappa ij.1, kappa ij.2)
lemma Z4_0_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z4_0_4Half w ij).Encloses (halfLaw (shape 4 0 4) w ij : ℝ) := by
  have hp : positive (shape 4 0 4) = false := by decide +kernel
  simp only [Z4_0_4Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z4_0_4Probs_sound _
  · exact Z4_0_4Probs_sound _

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
def Z4_0_4Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 4 0 4) a.1 a.2 : ℝ)
def Z4_0_4E_0_5LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4E_0_5Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4E_0_5Log_sound : Z4_0_4E_0_5Log.Encloses (Real.log (Z4_0_4Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((0,5) : PairSlot)) (w := Z4_0_4E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_0_5 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4E_0_5_sound : Z4_0_4E_0_5.Encloses (Foundation.entropyTerm (Z4_0_4Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((0,5) : PairSlot)) Z4_0_4E_0_5Log_sound) (by decide +kernel)
def Z4_0_4E_1_4LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4E_1_4Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4E_1_4Log_sound : Z4_0_4E_1_4Log.Encloses (Real.log (Z4_0_4Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((1,4) : PairSlot)) (w := Z4_0_4E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_1_4 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4E_1_4_sound : Z4_0_4E_1_4.Encloses (Foundation.entropyTerm (Z4_0_4Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((1,4) : PairSlot)) Z4_0_4E_1_4Log_sound) (by decide +kernel)
def Z4_0_4E_2_2LogWitness : LogWitness := ⟨-1, 5855588794422561384849059336303, 5000000000000000000000000000000⟩
def Z4_0_4E_2_2Log : Ball := ⟨(-53518853833220841124255752885733 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
lemma Z4_0_4E_2_2Log_sound : Z4_0_4E_2_2Log.Encloses (Real.log (Z4_0_4Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((2,2) : PairSlot)) (w := Z4_0_4E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_2_2 : Ball := ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
lemma Z4_0_4E_2_2_sound : Z4_0_4E_2_2.Encloses (Foundation.entropyTerm (Z4_0_4Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((2,2) : PairSlot)) Z4_0_4E_2_2Log_sound) (by decide +kernel)
def Z4_0_4E_2_3LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4E_2_3Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4E_2_3Log_sound : Z4_0_4E_2_3Log.Encloses (Real.log (Z4_0_4Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((2,3) : PairSlot)) (w := Z4_0_4E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_2_3 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4E_2_3_sound : Z4_0_4E_2_3.Encloses (Foundation.entropyTerm (Z4_0_4Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((2,3) : PairSlot)) Z4_0_4E_2_3Log_sound) (by decide +kernel)
def Z4_0_4E_3_2LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4E_3_2Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4E_3_2Log_sound : Z4_0_4E_3_2Log.Encloses (Real.log (Z4_0_4Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((3,2) : PairSlot)) (w := Z4_0_4E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_3_2 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4E_3_2_sound : Z4_0_4E_3_2.Encloses (Foundation.entropyTerm (Z4_0_4Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((3,2) : PairSlot)) Z4_0_4E_3_2Log_sound) (by decide +kernel)
def Z4_0_4E_3_3LogWitness : LogWitness := ⟨-8, 146554740536411280359956652837, 78125000000000000000000000000⟩
def Z4_0_4E_3_3Log : Ball := ⟨(-245804426916610420562127809721047 / 50000000000000000000000000000000), (190582413283 / 100000000000000000000000000000000)⟩
lemma Z4_0_4E_3_3Log_sound : Z4_0_4E_3_3Log.Encloses (Real.log (Z4_0_4Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((3,3) : PairSlot)) (w := Z4_0_4E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_3_3 : Ball := ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
lemma Z4_0_4E_3_3_sound : Z4_0_4E_3_3.Encloses (Foundation.entropyTerm (Z4_0_4Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((3,3) : PairSlot)) Z4_0_4E_3_3Log_sound) (by decide +kernel)
def Z4_0_4E_4_1LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4E_4_1Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4E_4_1Log_sound : Z4_0_4E_4_1Log.Encloses (Real.log (Z4_0_4Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((4,1) : PairSlot)) (w := Z4_0_4E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_4_1 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4E_4_1_sound : Z4_0_4E_4_1.Encloses (Foundation.entropyTerm (Z4_0_4Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((4,1) : PairSlot)) Z4_0_4E_4_1Log_sound) (by decide +kernel)
def Z4_0_4E_5_0LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4E_5_0Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4E_5_0Log_sound : Z4_0_4E_5_0Log.Encloses (Real.log (Z4_0_4Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4Probs_sound ((5,0) : PairSlot)) (w := Z4_0_4E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4E_5_0 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4E_5_0_sound : Z4_0_4E_5_0.Encloses (Foundation.entropyTerm (Z4_0_4Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4Probs_sound ((5,0) : PairSlot)) Z4_0_4E_5_0Log_sound) (by decide +kernel)
def Z4_0_4Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | 1, 4 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
  | 2, 3 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
  | 4, 1 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_0_4Terms_sound (a : PairSlot) :
    (Z4_0_4Terms a).Encloses (Foundation.entropyTerm (Z4_0_4Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_0_4Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((0,4) : PairSlot))) Z4_0_4E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_0_4Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((1,3) : PairSlot))) Z4_0_4E_1_4_sound (entropyTerm_zero_ball (Z4_0_4Probs_sound ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_0_4Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((2,1) : PairSlot))) Z4_0_4E_2_2_sound Z4_0_4E_2_3_sound (entropyTerm_zero_ball (Z4_0_4Probs_sound ((2,4) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_0_4Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((3,1) : PairSlot))) Z4_0_4E_3_2_sound Z4_0_4E_3_3_sound (entropyTerm_zero_ball (Z4_0_4Probs_sound ((3,4) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z4_0_4Probs_sound ((4,0) : PairSlot))) Z4_0_4E_4_1_sound (entropyTerm_zero_ball (Z4_0_4Probs_sound ((4,2) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((4,3) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_0_4E_5_0_sound (entropyTerm_zero_ball (Z4_0_4Probs_sound ((5,1) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z4_0_4Probs_sound ((5,5) : PairSlot)))
def Z4_0_4Entropy : Ball := ⟨(64196816022403144530458719913309 / 50000000000000000000000000000000), (16066710667 / 25000000000000000000000000000000)⟩
lemma Z4_0_4Entropy_sound : Z4_0_4Entropy.Encloses (Foundation.finiteEntropy Z4_0_4Value) := by
  exact contains_sound (entropyPair_enclosed Z4_0_4Value Z4_0_4Terms Z4_0_4Terms_sound) (by decide +kernel)
def Z4_0_4Labels : Ball := ⟨(55347887687580346776034112349573 / 10000000000000000000000000000000), (565953783 / 312500000000000000000000000000)⟩
lemma Z4_0_4Labels_sound : Z4_0_4Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 4 0 4) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z4_0_4Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z4_0_4Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z4_0_4Four : Ball := ⟨(170468127230152439205314640830587 / 25000000000000000000000000000000), (61343013307 / 25000000000000000000000000000000)⟩
lemma Z4_0_4Four_sound : Z4_0_4Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 4 0 4)) := by
  exact contains_sound (Ball.add_sound Z4_0_4Entropy_sound Z4_0_4Labels_sound) (by decide +kernel)
def Z4_0_4H0Value (a : PairSlot) : ℝ := (halfLaw (shape 4 0 4) 0 a : ℝ)
def Z4_0_4H0E_0_5LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H0E_0_5Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4H0E_0_5Log_sound : Z4_0_4H0E_0_5Log.Encloses (Real.log (Z4_0_4H0Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((0,5) : PairSlot)) (w := Z4_0_4H0E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_0_5 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4H0E_0_5_sound : Z4_0_4H0E_0_5.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((0,5) : PairSlot)) Z4_0_4H0E_0_5Log_sound) (by decide +kernel)
def Z4_0_4H0E_1_4LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H0E_1_4Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H0E_1_4Log_sound : Z4_0_4H0E_1_4Log.Encloses (Real.log (Z4_0_4H0Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((1,4) : PairSlot)) (w := Z4_0_4H0E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_1_4 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H0E_1_4_sound : Z4_0_4H0E_1_4.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((1,4) : PairSlot)) Z4_0_4H0E_1_4Log_sound) (by decide +kernel)
def Z4_0_4H0E_2_2LogWitness : LogWitness := ⟨-1, 5855588794422561384849059336303, 5000000000000000000000000000000⟩
def Z4_0_4H0E_2_2Log : Ball := ⟨(-53518853833220841124255752885733 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H0E_2_2Log_sound : Z4_0_4H0E_2_2Log.Encloses (Real.log (Z4_0_4H0Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((2,2) : PairSlot)) (w := Z4_0_4H0E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_2_2 : Ball := ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
lemma Z4_0_4H0E_2_2_sound : Z4_0_4H0E_2_2.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((2,2) : PairSlot)) Z4_0_4H0E_2_2Log_sound) (by decide +kernel)
def Z4_0_4H0E_2_3LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H0E_2_3Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H0E_2_3Log_sound : Z4_0_4H0E_2_3Log.Encloses (Real.log (Z4_0_4H0Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((2,3) : PairSlot)) (w := Z4_0_4H0E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_2_3 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H0E_2_3_sound : Z4_0_4H0E_2_3.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((2,3) : PairSlot)) Z4_0_4H0E_2_3Log_sound) (by decide +kernel)
def Z4_0_4H0E_3_2LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H0E_3_2Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H0E_3_2Log_sound : Z4_0_4H0E_3_2Log.Encloses (Real.log (Z4_0_4H0Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((3,2) : PairSlot)) (w := Z4_0_4H0E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_3_2 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H0E_3_2_sound : Z4_0_4H0E_3_2.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((3,2) : PairSlot)) Z4_0_4H0E_3_2Log_sound) (by decide +kernel)
def Z4_0_4H0E_3_3LogWitness : LogWitness := ⟨-8, 146554740536411280359956652837, 78125000000000000000000000000⟩
def Z4_0_4H0E_3_3Log : Ball := ⟨(-245804426916610420562127809721047 / 50000000000000000000000000000000), (190582413283 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H0E_3_3Log_sound : Z4_0_4H0E_3_3Log.Encloses (Real.log (Z4_0_4H0Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((3,3) : PairSlot)) (w := Z4_0_4H0E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_3_3 : Ball := ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H0E_3_3_sound : Z4_0_4H0E_3_3.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((3,3) : PairSlot)) Z4_0_4H0E_3_3Log_sound) (by decide +kernel)
def Z4_0_4H0E_4_1LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H0E_4_1Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H0E_4_1Log_sound : Z4_0_4H0E_4_1Log.Encloses (Real.log (Z4_0_4H0Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((4,1) : PairSlot)) (w := Z4_0_4H0E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_4_1 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H0E_4_1_sound : Z4_0_4H0E_4_1.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((4,1) : PairSlot)) Z4_0_4H0E_4_1Log_sound) (by decide +kernel)
def Z4_0_4H0E_5_0LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H0E_5_0Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4H0E_5_0Log_sound : Z4_0_4H0E_5_0Log.Encloses (Real.log (Z4_0_4H0Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 0) ((5,0) : PairSlot)) (w := Z4_0_4H0E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0E_5_0 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4H0E_5_0_sound : Z4_0_4H0E_5_0.Encloses (Foundation.entropyTerm (Z4_0_4H0Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 0) ((5,0) : PairSlot)) Z4_0_4H0E_5_0Log_sound) (by decide +kernel)
def Z4_0_4H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 5 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | 1, 4 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
  | 2, 3 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
  | 4, 1 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 5, 0 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_0_4H0Terms_sound (a : PairSlot) :
    (Z4_0_4H0Terms a).Encloses (Foundation.entropyTerm (Z4_0_4H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((0,4) : PairSlot))) Z4_0_4H0E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((1,3) : PairSlot))) Z4_0_4H0E_1_4_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((2,1) : PairSlot))) Z4_0_4H0E_2_2_sound Z4_0_4H0E_2_3_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((3,1) : PairSlot))) Z4_0_4H0E_3_2_sound Z4_0_4H0E_3_3_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((4,0) : PairSlot))) Z4_0_4H0E_4_1_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_0_4H0E_5_0_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 0) ((5,5) : PairSlot)))
def Z4_0_4H0Entropy : Ball := ⟨(64196816022403144530458719913309 / 50000000000000000000000000000000), (16066710667 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H0Entropy_sound : Z4_0_4H0Entropy.Encloses (Foundation.finiteEntropy Z4_0_4H0Value) := by
  exact contains_sound (entropyPair_enclosed Z4_0_4H0Value Z4_0_4H0Terms Z4_0_4H0Terms_sound) (by decide +kernel)
def Z4_0_4H0Mass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (21 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H0Mass_sound : Z4_0_4H0Mass.Encloses (∑ a, Z4_0_4H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_0_4Half 0) Z4_0_4H0Value (Z4_0_4Half_sound 0)) (by decide +kernel)
def Z4_0_4H0MassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def Z4_0_4H0MassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (5293955973 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H0MassTermLog_sound : Z4_0_4H0MassTermLog.Encloses (Real.log ((∑ a, Z4_0_4H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4H0Mass_sound) (w := Z4_0_4H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H0MassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823893 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H0MassTerm_sound : Z4_0_4H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_0_4H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4H0Mass_sound) Z4_0_4H0MassTermLog_sound) (by decide +kernel)
def Z4_0_4H0H : Ball := ⟨(128393632044806289060917439826619 / 100000000000000000000000000000000), (85442666561 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H0H_sound : Z4_0_4H0H.Encloses (homogeneousEntropy Z4_0_4H0Value) := by
  exact contains_sound (homogeneous_enclosed Z4_0_4H0Value Z4_0_4H0MassTerm_sound Z4_0_4H0Entropy_sound) (by decide +kernel)
def Z4_0_4H1Value (a : PairSlot) : ℝ := (halfLaw (shape 4 0 4) 1 a : ℝ)
def Z4_0_4H1E_0_0Log : Ball := .exact 0
lemma Z4_0_4H1E_0_0Log_sound : Z4_0_4H1E_0_0Log.Encloses (Real.log (Z4_0_4H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z4_0_4Half_sound 1) ((0,0) : PairSlot))
def Z4_0_4H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z4_0_4H1E_0_0_sound : Z4_0_4H1E_0_0.Encloses (Foundation.entropyTerm (Z4_0_4H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 1) ((0,0) : PairSlot)) Z4_0_4H1E_0_0Log_sound) (by decide +kernel)
def Z4_0_4H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z4_0_4H1Terms_sound (a : PairSlot) :
    (Z4_0_4H1Terms a).Encloses (Foundation.entropyTerm (Z4_0_4H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z4_0_4H1E_0_0_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 1) ((5,5) : PairSlot)))
def Z4_0_4H1Entropy : Ball := ⟨0, 0⟩
lemma Z4_0_4H1Entropy_sound : Z4_0_4H1Entropy.Encloses (Foundation.finiteEntropy Z4_0_4H1Value) := by
  exact contains_sound (entropyPair_enclosed Z4_0_4H1Value Z4_0_4H1Terms Z4_0_4H1Terms_sound) (by decide +kernel)
def Z4_0_4H1Mass : Ball := ⟨1, 0⟩
lemma Z4_0_4H1Mass_sound : Z4_0_4H1Mass.Encloses (∑ a, Z4_0_4H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_0_4Half 1) Z4_0_4H1Value (Z4_0_4Half_sound 1)) (by decide +kernel)
def Z4_0_4H1MassTermLog : Ball := .exact 0
lemma Z4_0_4H1MassTermLog_sound : Z4_0_4H1MassTermLog.Encloses (Real.log ((∑ a, Z4_0_4H1Value a))) := by
  exact log_exact_one_ball (Z4_0_4H1Mass_sound)
def Z4_0_4H1MassTerm : Ball := ⟨0, 0⟩
lemma Z4_0_4H1MassTerm_sound : Z4_0_4H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_0_4H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4H1Mass_sound) Z4_0_4H1MassTermLog_sound) (by decide +kernel)
def Z4_0_4H1H : Ball := ⟨0, 0⟩
lemma Z4_0_4H1H_sound : Z4_0_4H1H.Encloses (homogeneousEntropy Z4_0_4H1Value) := by
  exact contains_sound (homogeneous_enclosed Z4_0_4H1Value Z4_0_4H1MassTerm_sound Z4_0_4H1Entropy_sound) (by decide +kernel)
def Z4_0_4H2Value (a : PairSlot) : ℝ := (halfLaw (shape 4 0 4) 2 a : ℝ)
def Z4_0_4H2E_5_0LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H2E_5_0Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4H2E_5_0Log_sound : Z4_0_4H2E_5_0Log.Encloses (Real.log (Z4_0_4H2Value ((5,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((5,0) : PairSlot)) (w := Z4_0_4H2E_5_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_5_0 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4H2E_5_0_sound : Z4_0_4H2E_5_0.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((5,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((5,0) : PairSlot)) Z4_0_4H2E_5_0Log_sound) (by decide +kernel)
def Z4_0_4H2E_4_1LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H2E_4_1Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H2E_4_1Log_sound : Z4_0_4H2E_4_1Log.Encloses (Real.log (Z4_0_4H2Value ((4,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((4,1) : PairSlot)) (w := Z4_0_4H2E_4_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_4_1 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H2E_4_1_sound : Z4_0_4H2E_4_1.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((4,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((4,1) : PairSlot)) Z4_0_4H2E_4_1Log_sound) (by decide +kernel)
def Z4_0_4H2E_2_2LogWitness : LogWitness := ⟨-1, 5855588794422561384849059336303, 5000000000000000000000000000000⟩
def Z4_0_4H2E_2_2Log : Ball := ⟨(-53518853833220841124255752885733 / 100000000000000000000000000000000), (10587911893 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H2E_2_2Log_sound : Z4_0_4H2E_2_2Log.Encloses (Real.log (Z4_0_4H2Value ((2,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((2,2) : PairSlot)) (w := Z4_0_4H2E_2_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_2_2 : Ball := ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
lemma Z4_0_4H2E_2_2_sound : Z4_0_4H2E_2_2.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((2,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((2,2) : PairSlot)) Z4_0_4H2E_2_2Log_sound) (by decide +kernel)
def Z4_0_4H2E_2_3LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H2E_2_3Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H2E_2_3Log_sound : Z4_0_4H2E_2_3Log.Encloses (Real.log (Z4_0_4H2Value ((2,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((2,3) : PairSlot)) (w := Z4_0_4H2E_2_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_2_3 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H2E_2_3_sound : Z4_0_4H2E_2_3.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((2,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((2,3) : PairSlot)) Z4_0_4H2E_2_3Log_sound) (by decide +kernel)
def Z4_0_4H2E_3_2LogWitness : LogWitness := ⟨-4, 3407007932926322989871260497747, 3125000000000000000000000000000⟩
def Z4_0_4H2E_3_2Log : Ball := ⟨(-6715471345830521028106392389981 / 2500000000000000000000000000000), (52939559317 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H2E_3_2Log_sound : Z4_0_4H2E_3_2Log.Encloses (Real.log (Z4_0_4H2Value ((3,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((3,2) : PairSlot)) (w := Z4_0_4H2E_3_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_3_2 : Ball := ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H2E_3_2_sound : Z4_0_4H2E_3_2.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((3,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((3,2) : PairSlot)) Z4_0_4H2E_3_2Log_sound) (by decide +kernel)
def Z4_0_4H2E_3_3LogWitness : LogWitness := ⟨-8, 146554740536411280359956652837, 78125000000000000000000000000⟩
def Z4_0_4H2E_3_3Log : Ball := ⟨(-245804426916610420562127809721047 / 50000000000000000000000000000000), (190582413283 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H2E_3_3Log_sound : Z4_0_4H2E_3_3Log.Encloses (Real.log (Z4_0_4H2Value ((3,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((3,3) : PairSlot)) (w := Z4_0_4H2E_3_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_3_3 : Ball := ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H2E_3_3_sound : Z4_0_4H2E_3_3.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((3,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((3,3) : PairSlot)) Z4_0_4H2E_3_3Log_sound) (by decide +kernel)
def Z4_0_4H2E_1_4LogWitness : LogWitness := ⟨-3, 6632849277085335226067309879167, 6250000000000000000000000000000⟩
def Z4_0_4H2E_1_4Log : Ball := ⟨(-201998853833220841124255714694749 / 100000000000000000000000000000000), (42351647471 / 50000000000000000000000000000000)⟩
lemma Z4_0_4H2E_1_4Log_sound : Z4_0_4H2E_1_4Log.Encloses (Real.log (Z4_0_4H2Value ((1,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((1,4) : PairSlot)) (w := Z4_0_4H2E_1_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_1_4 : Ball := ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H2E_1_4_sound : Z4_0_4H2E_1_4.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((1,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((1,4) : PairSlot)) Z4_0_4H2E_1_4Log_sound) (by decide +kernel)
def Z4_0_4H2E_0_5LogWitness : LogWitness := ⟨-9, 55190951304569688595534186513, 39062500000000000000000000000⟩
def Z4_0_4H2E_0_5Log : Ball := ⟨(-589268853833220841124255600121907 / 100000000000000000000000000000000), (26469779649 / 12500000000000000000000000000000)⟩
lemma Z4_0_4H2E_0_5Log_sound : Z4_0_4H2E_0_5Log.Encloses (Real.log (Z4_0_4H2Value ((0,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z4_0_4Half_sound 2) ((0,5) : PairSlot)) (w := Z4_0_4H2E_0_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2E_0_5 : Ball := ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
lemma Z4_0_4H2E_0_5_sound : Z4_0_4H2E_0_5.Encloses (Foundation.entropyTerm (Z4_0_4H2Value ((0,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z4_0_4Half_sound 2) ((0,5) : PairSlot)) Z4_0_4H2E_0_5Log_sound) (by decide +kernel)
def Z4_0_4H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 5, 0 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | 4, 1 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 2, 2 => ⟨(31338440079614690320574653450617 / 100000000000000000000000000000000), (77498073 / 312500000000000000000000000000)⟩
  | 2, 3 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 2 => ⟨(18303731318867196612732623716901 / 100000000000000000000000000000000), (7214619983 / 100000000000000000000000000000000)⟩
  | 3, 3 => ⟨(3602380400946510922725768272093 / 100000000000000000000000000000000), (349134453 / 25000000000000000000000000000000)⟩
  | 1, 4 => ⟨(837392469762340720305966731003 / 3125000000000000000000000000000), (1123648383 / 10000000000000000000000000000000)⟩
  | 0, 5 => ⟨(1626115430860444246284949942957 / 100000000000000000000000000000000), (116871387 / 20000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z4_0_4H2Terms_sound (a : PairSlot) :
    (Z4_0_4H2Terms a).Encloses (Foundation.entropyTerm (Z4_0_4H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((0,4) : PairSlot))) Z4_0_4H2E_0_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((1,3) : PairSlot))) Z4_0_4H2E_1_4_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((2,1) : PairSlot))) Z4_0_4H2E_2_2_sound Z4_0_4H2E_2_3_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((3,1) : PairSlot))) Z4_0_4H2E_3_2_sound Z4_0_4H2E_3_3_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((4,0) : PairSlot))) Z4_0_4H2E_4_1_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 Z4_0_4H2E_5_0_sound (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z4_0_4Half_sound 2) ((5,5) : PairSlot)))
def Z4_0_4H2Entropy : Ball := ⟨(64196816022403144530458719913309 / 50000000000000000000000000000000), (16066710667 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H2Entropy_sound : Z4_0_4H2Entropy.Encloses (Foundation.finiteEntropy Z4_0_4H2Value) := by
  exact contains_sound (entropyPair_enclosed Z4_0_4H2Value Z4_0_4H2Terms Z4_0_4H2Terms_sound) (by decide +kernel)
def Z4_0_4H2Mass : Ball := ⟨(100000000000000000000000000000001 / 100000000000000000000000000000000), (21 / 10000000000000000000000000000000)⟩
lemma Z4_0_4H2Mass_sound : Z4_0_4H2Mass.Encloses (∑ a, Z4_0_4H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z4_0_4Half 2) Z4_0_4H2Value (Z4_0_4Half_sound 2)) (by decide +kernel)
def Z4_0_4H2MassTermLogWitness : LogWitness := ⟨0, 100000000000000000000000000000001, 100000000000000000000000000000000⟩
def Z4_0_4H2MassTermLog : Ball := ⟨(1 / 100000000000000000000000000000000), (5293955973 / 25000000000000000000000000000000)⟩
lemma Z4_0_4H2MassTermLog_sound : Z4_0_4H2MassTermLog.Encloses (Real.log ((∑ a, Z4_0_4H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z4_0_4H2Mass_sound) (w := Z4_0_4H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z4_0_4H2MassTerm : Ball := ⟨(-1 / 100000000000000000000000000000000), (21175823893 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H2MassTerm_sound : Z4_0_4H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z4_0_4H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z4_0_4H2Mass_sound) Z4_0_4H2MassTermLog_sound) (by decide +kernel)
def Z4_0_4H2H : Ball := ⟨(128393632044806289060917439826619 / 100000000000000000000000000000000), (85442666561 / 100000000000000000000000000000000)⟩
lemma Z4_0_4H2H_sound : Z4_0_4H2H.Encloses (homogeneousEntropy Z4_0_4H2Value) := by
  exact contains_sound (homogeneous_enclosed Z4_0_4H2Value Z4_0_4H2MassTerm_sound Z4_0_4H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
