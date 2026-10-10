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
def Z3_0_5Raw (ij : PairSlot) : Ball :=
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
  | 1, 5 => w189
  | 2, 0 => w195
  | 2, 1 => w195
  | 2, 2 => w195
  | 2, 3 => w195
  | 2, 4 => w202
  | 2, 5 => w195
  | 3, 0 => w195
  | 3, 1 => w195
  | 3, 2 => w195
  | 3, 3 => w195
  | 3, 4 => w195
  | 3, 5 => w195
  | 4, 0 => w195
  | 4, 1 => w195
  | 4, 2 => w202
  | 4, 3 => w195
  | 4, 4 => w195
  | 4, 5 => w195
  | 5, 0 => w195
  | 5, 1 => w189
  | 5, 2 => w195
  | 5, 3 => w195
  | 5, 4 => w195
  | 5, 5 => w195
  | _, _ => (.exact 0)
lemma Z3_0_5Raw_sound_0 (j : Fin 6) :
    (Z3_0_5Raw (0,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (0,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (0,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 0 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 0 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_1 (j : Fin 6) :
    (Z3_0_5Raw (1,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (1,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (1,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 1 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 1 5 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
lemma Z3_0_5Raw_sound_2 (j : Fin 6) :
    (Z3_0_5Raw (2,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (2,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (2,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 4 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (2,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 2 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 2 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_3 (j : Fin 6) :
    (Z3_0_5Raw (3,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (3,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (3,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 3 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 3 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_4 (j : Fin 6) :
    (Z3_0_5Raw (4,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (4,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 1 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 2 = (21564) := by decide +kernel
    rw [he]
    exact w202_sound
  · change (Z3_0_5Raw (4,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (4,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 4 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 4 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound_5 (j : Fin 6) :
    (Z3_0_5Raw (5,j)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 j) : ℝ) := by
  fin_cases j
  · change (Z3_0_5Raw (5,0)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 0) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 0 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,1)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 1) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 1 = (-2174) := by decide +kernel
    rw [he]
    exact w189_sound
  · change (Z3_0_5Raw (5,2)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 2) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 2 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,3)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 3) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 3 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,4)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 4) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 4 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
  · change (Z3_0_5Raw (5,5)).Encloses (weight (orderedPairInteger (shape 3 0 5) 5 5) : ℝ)
    have he : orderedPairInteger (shape 3 0 5) 5 5 = (0) := by decide +kernel
    rw [he]
    exact w195_sound
lemma Z3_0_5Raw_sound (ij : PairSlot) :
    (Z3_0_5Raw ij).Encloses (weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2) : ℝ) := by
  rcases ij with ⟨i,j⟩
  revert i
  exact forall_fin6 (Z3_0_5Raw_sound_0 j) (Z3_0_5Raw_sound_1 j) (Z3_0_5Raw_sound_2 j) (Z3_0_5Raw_sound_3 j) (Z3_0_5Raw_sound_4 j) (Z3_0_5Raw_sound_5 j)
def Z3_0_5Den : Ball := ⟨(522229287310098961532365085049411 / 25000000000000000000000000000000), (1017 / 50000000000000000000000000000000)⟩
lemma Z3_0_5Den_sound : Z3_0_5Den.Encloses
    (((orderedPairs (shape 3 0 5)).map (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (orderedPairs (shape 3 0 5)) Z3_0_5Raw
    (fun ij => weight (orderedPairInteger (shape 3 0 5) ij.1 ij.2))
    (fun ij _ => Z3_0_5Raw_sound ij)) (by decide +kernel)
lemma Z3_0_5Den_pos : 0 < Z3_0_5Den.lower := by decide +kernel
def Z3_0_5Probs (ij : PairSlot) : Ball :=
  match ij.1.val, ij.2.val with
  | 1, 5 => ⟨(3851794993380545981064826935537 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 4 => ⟨(41361035729160865645318261676507 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1196792319364647093404227846989 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2 => ⟨(41361035729160865645318261676507 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1196792319364647093404227846989 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 5, 1 => ⟨(3851794993380545981064826935537 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_0_5Contains : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j = shapeMax (shape 3 0 5) →
    contains (.mul (Z3_0_5Raw (i,j)) (.inv Z3_0_5Den)) (Z3_0_5Probs (i,j)) = true := by
  decide +kernel
lemma Z3_0_5Zero : ∀ i j : Fin 6,
    statisticWeight i + statisticWeight j ≠ shapeMax (shape 3 0 5) → Z3_0_5Probs (i,j) = .exact 0 := by
  decide +kernel
lemma Z3_0_5Probs_sound (ij : PairSlot) :
    (Z3_0_5Probs ij).Encloses (zeroPairLaw (shape 3 0 5) ij.1 ij.2 : ℝ) := by
  by_cases h : statisticWeight ij.1 + statisticWeight ij.2 = shapeMax (shape 3 0 5)
  · have hb := contains_sound (Ball.mul_sound (Z3_0_5Raw_sound ij)
      (Ball.inv_sound Z3_0_5Den_sound Z3_0_5Den_pos)) (Z3_0_5Contains ij.1 ij.2 h)
    simpa only [zeroPairLaw, h, ite_true, Rat.cast_div, Rat.cast_mul,
      Rat.cast_inv, div_eq_mul_inv] using hb
  · rw [Z3_0_5Zero ij.1 ij.2 h]
    simpa only [zeroPairLaw, h, ite_false] using Ball.exact_sound 0

def Z3_0_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  if (shape 3 0 5) w = 0 then if ij = (0,0) then .exact 1 else .exact 0
  else if w = halfMaxAxis (shape 3 0 5) then Z3_0_5Probs ij
  else Z3_0_5Probs (kappa ij.1, kappa ij.2)
lemma Z3_0_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (Z3_0_5Half w ij).Encloses (halfLaw (shape 3 0 5) w ij : ℝ) := by
  have hp : positive (shape 3 0 5) = false := by decide +kernel
  simp only [Z3_0_5Half, halfLaw, hp, Bool.false_eq_true, ite_false]
  split_ifs
  · exact Ball.exact_sound 1
  · exact Ball.exact_sound 0
  · exact Z3_0_5Probs_sound _
  · exact Z3_0_5Probs_sound _

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
def Z3_0_5Value (a : PairSlot) : ℝ := (zeroPairLaw (shape 3 0 5) a.1 a.2 : ℝ)
def Z3_0_5E_1_5LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5E_1_5Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5E_1_5Log_sound : Z3_0_5E_1_5Log.Encloses (Real.log (Z3_0_5Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((1,5) : PairSlot)) (w := Z3_0_5E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_1_5 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_1_5_sound : Z3_0_5E_1_5.Encloses (Foundation.entropyTerm (Z3_0_5Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((1,5) : PairSlot)) Z3_0_5E_1_5Log_sound) (by decide +kernel)
def Z3_0_5E_2_4LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5E_2_4Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_2_4Log_sound : Z3_0_5E_2_4Log.Encloses (Real.log (Z3_0_5Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((2,4) : PairSlot)) (w := Z3_0_5E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_2_4 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5E_2_4_sound : Z3_0_5E_2_4.Encloses (Foundation.entropyTerm (Z3_0_5Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((2,4) : PairSlot)) Z3_0_5E_2_4Log_sound) (by decide +kernel)
def Z3_0_5E_3_4LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5E_3_4Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_3_4Log_sound : Z3_0_5E_3_4Log.Encloses (Real.log (Z3_0_5Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((3,4) : PairSlot)) (w := Z3_0_5E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_3_4 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_3_4_sound : Z3_0_5E_3_4.Encloses (Foundation.entropyTerm (Z3_0_5Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((3,4) : PairSlot)) Z3_0_5E_3_4Log_sound) (by decide +kernel)
def Z3_0_5E_4_2LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5E_4_2Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_4_2Log_sound : Z3_0_5E_4_2Log.Encloses (Real.log (Z3_0_5Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((4,2) : PairSlot)) (w := Z3_0_5E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_4_2 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5E_4_2_sound : Z3_0_5E_4_2.Encloses (Foundation.entropyTerm (Z3_0_5Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((4,2) : PairSlot)) Z3_0_5E_4_2Log_sound) (by decide +kernel)
def Z3_0_5E_4_3LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5E_4_3Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_4_3Log_sound : Z3_0_5E_4_3Log.Encloses (Real.log (Z3_0_5Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((4,3) : PairSlot)) (w := Z3_0_5E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_4_3 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_4_3_sound : Z3_0_5E_4_3.Encloses (Foundation.entropyTerm (Z3_0_5Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((4,3) : PairSlot)) Z3_0_5E_4_3Log_sound) (by decide +kernel)
def Z3_0_5E_5_1LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5E_5_1Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5E_5_1Log_sound : Z3_0_5E_5_1Log.Encloses (Real.log (Z3_0_5Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5Probs_sound ((5,1) : PairSlot)) (w := Z3_0_5E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5E_5_1 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5E_5_1_sound : Z3_0_5E_5_1.Encloses (Foundation.entropyTerm (Z3_0_5Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5Probs_sound ((5,1) : PairSlot)) Z3_0_5E_5_1Log_sound) (by decide +kernel)
def Z3_0_5Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_0_5Terms_sound (a : PairSlot) :
    (Z3_0_5Terms a).Encloses (Foundation.entropyTerm (Z3_0_5Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,0) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,1) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,2) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,3) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,4) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((1,0) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((1,1) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((1,2) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((1,3) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((1,4) : PairSlot))) Z3_0_5E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((2,0) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((2,1) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((2,2) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((2,3) : PairSlot))) Z3_0_5E_2_4_sound (entropyTerm_zero_ball (Z3_0_5Probs_sound ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((3,0) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((3,1) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((3,2) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((3,3) : PairSlot))) Z3_0_5E_3_4_sound (entropyTerm_zero_ball (Z3_0_5Probs_sound ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((4,0) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((4,1) : PairSlot))) Z3_0_5E_4_2_sound Z3_0_5E_4_3_sound (entropyTerm_zero_ball (Z3_0_5Probs_sound ((4,4) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball (Z3_0_5Probs_sound ((5,0) : PairSlot))) Z3_0_5E_5_1_sound (entropyTerm_zero_ball (Z3_0_5Probs_sound ((5,2) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((5,3) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((5,4) : PairSlot))) (entropyTerm_zero_ball (Z3_0_5Probs_sound ((5,5) : PairSlot)))
def Z3_0_5Entropy : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (1490074051 / 2000000000000000000000000000000)⟩
lemma Z3_0_5Entropy_sound : Z3_0_5Entropy.Encloses (Foundation.finiteEntropy Z3_0_5Value) := by
  exact contains_sound (entropyPair_enclosed Z3_0_5Value Z3_0_5Terms Z3_0_5Terms_sound) (by decide +kernel)
def Z3_0_5Labels : Ball := ⟨(125791752768670849860793716024527 / 25000000000000000000000000000000), (78399530397 / 50000000000000000000000000000000)⟩
lemma Z3_0_5Labels_sound : Z3_0_5Labels.Encloses
    (∑ a : PairSlot, (zeroPairLaw (shape 3 0 5) a.1 a.2 : ℝ) *
      Real.log (AllFieldParameters.multiplicity a.1 * AllFieldParameters.multiplicity a.2 : ℕ)) := by
  exact contains_sound (pairSumBall_sound (fun a => .mul (Z3_0_5Probs a) (multLogs a))
    _ (fun a => Ball.mul_sound (Z3_0_5Probs_sound a) (multLogs_sound a))) (by decide +kernel)
def Z3_0_5Four : Ball := ⟨(315191494037234842527202671660589 / 50000000000000000000000000000000), (14456422709 / 6250000000000000000000000000000)⟩
lemma Z3_0_5Four_sound : Z3_0_5Four.Encloses (AllFieldZeroLeafRates.fourRate (shape 3 0 5)) := by
  exact contains_sound (Ball.add_sound Z3_0_5Entropy_sound Z3_0_5Labels_sound) (by decide +kernel)
def Z3_0_5H0Value (a : PairSlot) : ℝ := (halfLaw (shape 3 0 5) 0 a : ℝ)
def Z3_0_5H0E_4_0LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H0E_4_0Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0E_4_0Log_sound : Z3_0_5H0E_4_0Log.Encloses (Real.log (Z3_0_5H0Value ((4,0) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((4,0) : PairSlot)) (w := Z3_0_5H0E_4_0LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_4_0 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_4_0_sound : Z3_0_5H0E_4_0.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((4,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((4,0) : PairSlot)) Z3_0_5H0E_4_0Log_sound) (by decide +kernel)
def Z3_0_5H0E_2_1LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H0E_2_1Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_2_1Log_sound : Z3_0_5H0E_2_1Log.Encloses (Real.log (Z3_0_5H0Value ((2,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((2,1) : PairSlot)) (w := Z3_0_5H0E_2_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_2_1 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0E_2_1_sound : Z3_0_5H0E_2_1.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((2,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((2,1) : PairSlot)) Z3_0_5H0E_2_1Log_sound) (by decide +kernel)
def Z3_0_5H0E_3_1LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H0E_3_1Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_3_1Log_sound : Z3_0_5H0E_3_1Log.Encloses (Real.log (Z3_0_5H0Value ((3,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((3,1) : PairSlot)) (w := Z3_0_5H0E_3_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_3_1 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_3_1_sound : Z3_0_5H0E_3_1.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((3,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((3,1) : PairSlot)) Z3_0_5H0E_3_1Log_sound) (by decide +kernel)
def Z3_0_5H0E_1_2LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H0E_1_2Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_1_2Log_sound : Z3_0_5H0E_1_2Log.Encloses (Real.log (Z3_0_5H0Value ((1,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((1,2) : PairSlot)) (w := Z3_0_5H0E_1_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_1_2 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0E_1_2_sound : Z3_0_5H0E_1_2.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((1,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((1,2) : PairSlot)) Z3_0_5H0E_1_2Log_sound) (by decide +kernel)
def Z3_0_5H0E_1_3LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H0E_1_3Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_1_3Log_sound : Z3_0_5H0E_1_3Log.Encloses (Real.log (Z3_0_5H0Value ((1,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((1,3) : PairSlot)) (w := Z3_0_5H0E_1_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_1_3 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_1_3_sound : Z3_0_5H0E_1_3.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((1,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((1,3) : PairSlot)) Z3_0_5H0E_1_3Log_sound) (by decide +kernel)
def Z3_0_5H0E_0_4LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H0E_0_4Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0E_0_4Log_sound : Z3_0_5H0E_0_4Log.Encloses (Real.log (Z3_0_5H0Value ((0,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 0) ((0,4) : PairSlot)) (w := Z3_0_5H0E_0_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0E_0_4 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0E_0_4_sound : Z3_0_5H0E_0_4.Encloses (Foundation.entropyTerm (Z3_0_5H0Value ((0,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 0) ((0,4) : PairSlot)) Z3_0_5H0E_0_4Log_sound) (by decide +kernel)
def Z3_0_5H0Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 4, 0 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | 2, 1 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 3, 1 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 1, 2 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 1, 3 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 0, 4 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_0_5H0Terms_sound (a : PairSlot) :
    (Z3_0_5H0Terms a).Encloses (Foundation.entropyTerm (Z3_0_5H0Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((0,3) : PairSlot))) Z3_0_5H0E_0_4_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((1,1) : PairSlot))) Z3_0_5H0E_1_2_sound Z3_0_5H0E_1_3_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((2,0) : PairSlot))) Z3_0_5H0E_2_1_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((3,0) : PairSlot))) Z3_0_5H0E_3_1_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((3,5) : PairSlot)))
  · exact forall_fin6 Z3_0_5H0E_4_0_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 0) ((5,5) : PairSlot)))
def Z3_0_5H0Entropy : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (1490074051 / 2000000000000000000000000000000)⟩
lemma Z3_0_5H0Entropy_sound : Z3_0_5H0Entropy.Encloses (Foundation.finiteEntropy Z3_0_5H0Value) := by
  exact contains_sound (entropyPair_enclosed Z3_0_5H0Value Z3_0_5H0Terms Z3_0_5H0Terms_sound) (by decide +kernel)
def Z3_0_5H0Mass : Ball := ⟨1, (1 / 500000000000000000000000000000)⟩
lemma Z3_0_5H0Mass_sound : Z3_0_5H0Mass.Encloses (∑ a, Z3_0_5H0Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_0_5Half 0) Z3_0_5H0Value (Z3_0_5Half_sound 0)) (by decide +kernel)
def Z3_0_5H0MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_0_5H0MassTermLog : Ball := ⟨0, (10587911941 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H0MassTermLog_sound : Z3_0_5H0MassTermLog.Encloses (Real.log ((∑ a, Z3_0_5H0Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5H0Mass_sound) (w := Z3_0_5H0MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H0MassTerm : Ball := ⟨0, (21175823883 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0MassTerm_sound : Z3_0_5H0MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_0_5H0Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5H0Mass_sound) Z3_0_5H0MassTermLog_sound) (by decide +kernel)
def Z3_0_5H0H : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (95679526433 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H0H_sound : Z3_0_5H0H.Encloses (homogeneousEntropy Z3_0_5H0Value) := by
  exact contains_sound (homogeneous_enclosed Z3_0_5H0Value Z3_0_5H0MassTerm_sound Z3_0_5H0Entropy_sound) (by decide +kernel)
def Z3_0_5H1Value (a : PairSlot) : ℝ := (halfLaw (shape 3 0 5) 1 a : ℝ)
def Z3_0_5H1E_0_0Log : Ball := .exact 0
lemma Z3_0_5H1E_0_0Log_sound : Z3_0_5H1E_0_0Log.Encloses (Real.log (Z3_0_5H1Value ((0,0) : PairSlot))) := by
  exact log_exact_one_ball ((Z3_0_5Half_sound 1) ((0,0) : PairSlot))
def Z3_0_5H1E_0_0 : Ball := ⟨0, 0⟩
lemma Z3_0_5H1E_0_0_sound : Z3_0_5H1E_0_0.Encloses (Foundation.entropyTerm (Z3_0_5H1Value ((0,0) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 1) ((0,0) : PairSlot)) Z3_0_5H1E_0_0Log_sound) (by decide +kernel)
def Z3_0_5H1Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 0, 0 => ⟨0, 0⟩
  | _, _ => (.exact 0)
lemma Z3_0_5H1Terms_sound (a : PairSlot) :
    (Z3_0_5H1Terms a).Encloses (Foundation.entropyTerm (Z3_0_5H1Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 Z3_0_5H1E_0_0_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((1,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 1) ((5,5) : PairSlot)))
def Z3_0_5H1Entropy : Ball := ⟨0, 0⟩
lemma Z3_0_5H1Entropy_sound : Z3_0_5H1Entropy.Encloses (Foundation.finiteEntropy Z3_0_5H1Value) := by
  exact contains_sound (entropyPair_enclosed Z3_0_5H1Value Z3_0_5H1Terms Z3_0_5H1Terms_sound) (by decide +kernel)
def Z3_0_5H1Mass : Ball := ⟨1, 0⟩
lemma Z3_0_5H1Mass_sound : Z3_0_5H1Mass.Encloses (∑ a, Z3_0_5H1Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_0_5Half 1) Z3_0_5H1Value (Z3_0_5Half_sound 1)) (by decide +kernel)
def Z3_0_5H1MassTermLog : Ball := .exact 0
lemma Z3_0_5H1MassTermLog_sound : Z3_0_5H1MassTermLog.Encloses (Real.log ((∑ a, Z3_0_5H1Value a))) := by
  exact log_exact_one_ball (Z3_0_5H1Mass_sound)
def Z3_0_5H1MassTerm : Ball := ⟨0, 0⟩
lemma Z3_0_5H1MassTerm_sound : Z3_0_5H1MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_0_5H1Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5H1Mass_sound) Z3_0_5H1MassTermLog_sound) (by decide +kernel)
def Z3_0_5H1H : Ball := ⟨0, 0⟩
lemma Z3_0_5H1H_sound : Z3_0_5H1H.Encloses (homogeneousEntropy Z3_0_5H1Value) := by
  exact contains_sound (homogeneous_enclosed Z3_0_5H1Value Z3_0_5H1MassTerm_sound Z3_0_5H1Entropy_sound) (by decide +kernel)
def Z3_0_5H2Value (a : PairSlot) : ℝ := (halfLaw (shape 3 0 5) 2 a : ℝ)
def Z3_0_5H2E_1_5LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H2E_1_5Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2E_1_5Log_sound : Z3_0_5H2E_1_5Log.Encloses (Real.log (Z3_0_5H2Value ((1,5) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((1,5) : PairSlot)) (w := Z3_0_5H2E_1_5LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_1_5 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_1_5_sound : Z3_0_5H2E_1_5.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((1,5) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((1,5) : PairSlot)) Z3_0_5H2E_1_5Log_sound) (by decide +kernel)
def Z3_0_5H2E_2_4LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H2E_2_4Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_2_4Log_sound : Z3_0_5H2E_2_4Log.Encloses (Real.log (Z3_0_5H2Value ((2,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((2,4) : PairSlot)) (w := Z3_0_5H2E_2_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_2_4 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2E_2_4_sound : Z3_0_5H2E_2_4.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((2,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((2,4) : PairSlot)) Z3_0_5H2E_2_4Log_sound) (by decide +kernel)
def Z3_0_5H2E_3_4LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H2E_3_4Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_3_4Log_sound : Z3_0_5H2E_3_4Log.Encloses (Real.log (Z3_0_5H2Value ((3,4) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((3,4) : PairSlot)) (w := Z3_0_5H2E_3_4LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_3_4 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_3_4_sound : Z3_0_5H2E_3_4.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((3,4) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((3,4) : PairSlot)) Z3_0_5H2E_3_4Log_sound) (by decide +kernel)
def Z3_0_5H2E_4_2LogWitness : LogWitness := ⟨-2, 41361035729160865645318261676507, 25000000000000000000000000000000⟩
def Z3_0_5H2E_4_2Log : Ball := ⟨(-17656618285877881114758420265571 / 20000000000000000000000000000000), (31763735627 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_4_2Log_sound : Z3_0_5H2E_4_2Log.Encloses (Real.log (Z3_0_5H2Value ((4,2) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((4,2) : PairSlot)) (w := Z3_0_5H2E_4_2LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_4_2 : Ball := ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2E_4_2_sound : Z3_0_5H2E_4_2.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((4,2) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((4,2) : PairSlot)) Z3_0_5H2E_4_2Log_sound) (by decide +kernel)
def Z3_0_5H2E_4_3LogWitness : LogWitness := ⟨-5, 1196792319364647093404227846989, 781250000000000000000000000000⟩
def Z3_0_5H2E_4_3Log : Ball := ⟨(-303923091429389405573792044041373 / 100000000000000000000000000000000), (63527471101 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_4_3Log_sound : Z3_0_5H2E_4_3Log.Encloses (Real.log (Z3_0_5H2Value ((4,3) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((4,3) : PairSlot)) (w := Z3_0_5H2E_4_3LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_4_3 : Ball := ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_4_3_sound : Z3_0_5H2E_4_3.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((4,3) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((4,3) : PairSlot)) Z3_0_5H2E_4_3Log_sound) (by decide +kernel)
def Z3_0_5H2E_5_1LogWitness : LogWitness := ⟨-5, 3851794993380545981064826935537, 3125000000000000000000000000000⟩
def Z3_0_5H2E_5_1Log : Ball := ⟨(-2605304731435115244590336352331 / 800000000000000000000000000000), (127054942357 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2E_5_1Log_sound : Z3_0_5H2E_5_1Log.Encloses (Real.log (Z3_0_5H2Value ((5,1) : PairSlot))) := by
  exact checkLog_sound logTwoBall_sound ((Z3_0_5Half_sound 2) ((5,1) : PairSlot)) (w := Z3_0_5H2E_5_1LogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2E_5_1 : Ball := ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2E_5_1_sound : Z3_0_5H2E_5_1.Encloses (Foundation.entropyTerm (Z3_0_5H2Value ((5,1) : PairSlot))) := by
  exact contains_sound (entropyTerm_ball ((Z3_0_5Half_sound 2) ((5,1) : PairSlot)) Z3_0_5H2E_5_1Log_sound) (by decide +kernel)
def Z3_0_5H2Terms (a : PairSlot) : Ball :=
  match a.1.val, a.2.val with
  | 1, 5 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | 2, 4 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 3, 4 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 4, 2 => ⟨(36514800988917506010651666724087 / 100000000000000000000000000000000), (26275620159 / 100000000000000000000000000000000)⟩
  | 4, 3 => ⟨(1454931286001010573435377377673 / 10000000000000000000000000000000), (3041167587 / 50000000000000000000000000000000)⟩
  | 5, 1 => ⟨(6271937325482765530304899555359 / 50000000000000000000000000000000), (2446947971 / 50000000000000000000000000000000)⟩
  | _, _ => (.exact 0)
lemma Z3_0_5H2Terms_sound (a : PairSlot) :
    (Z3_0_5H2Terms a).Encloses (Foundation.entropyTerm (Z3_0_5H2Value a)) := by
  rcases a with ⟨i,j⟩
  revert j i
  apply forall_fin6
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((0,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((1,4) : PairSlot))) Z3_0_5H2E_1_5_sound
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,3) : PairSlot))) Z3_0_5H2E_2_4_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((2,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,1) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,3) : PairSlot))) Z3_0_5H2E_3_4_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((3,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,0) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,1) : PairSlot))) Z3_0_5H2E_4_2_sound Z3_0_5H2E_4_3_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((4,5) : PairSlot)))
  · exact forall_fin6 (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,0) : PairSlot))) Z3_0_5H2E_5_1_sound (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,2) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,3) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,4) : PairSlot))) (entropyTerm_zero_ball ((Z3_0_5Half_sound 2) ((5,5) : PairSlot)))
def Z3_0_5H2Entropy : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (1490074051 / 2000000000000000000000000000000)⟩
lemma Z3_0_5H2Entropy_sound : Z3_0_5H2Entropy.Encloses (Foundation.finiteEntropy Z3_0_5H2Value) := by
  exact contains_sound (entropyPair_enclosed Z3_0_5H2Value Z3_0_5H2Terms Z3_0_5H2Terms_sound) (by decide +kernel)
def Z3_0_5H2Mass : Ball := ⟨1, (1 / 500000000000000000000000000000)⟩
lemma Z3_0_5H2Mass_sound : Z3_0_5H2Mass.Encloses (∑ a, Z3_0_5H2Value a) := by
  exact contains_sound (pairSumBall_sound (Z3_0_5Half 2) Z3_0_5H2Value (Z3_0_5Half_sound 2)) (by decide +kernel)
def Z3_0_5H2MassTermLogWitness : LogWitness := ⟨0, 1, 1⟩
def Z3_0_5H2MassTermLog : Ball := ⟨0, (10587911941 / 50000000000000000000000000000000)⟩
lemma Z3_0_5H2MassTermLog_sound : Z3_0_5H2MassTermLog.Encloses (Real.log ((∑ a, Z3_0_5H2Value a))) := by
  exact checkLog_sound logTwoBall_sound (Z3_0_5H2Mass_sound) (w := Z3_0_5H2MassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def Z3_0_5H2MassTerm : Ball := ⟨0, (21175823883 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2MassTerm_sound : Z3_0_5H2MassTerm.Encloses (Foundation.entropyTerm ((∑ a, Z3_0_5H2Value a))) := by
  exact contains_sound (entropyTerm_ball (Z3_0_5H2Mass_sound) Z3_0_5H2MassTermLog_sound) (by decide +kernel)
def Z3_0_5H2H : Ball := ⟨(12721597699978628561123047922307 / 10000000000000000000000000000000), (95679526433 / 100000000000000000000000000000000)⟩
lemma Z3_0_5H2H_sound : Z3_0_5H2H.Encloses (homogeneousEntropy Z3_0_5H2Value) := by
  exact contains_sound (homogeneous_enclosed Z3_0_5H2Value Z3_0_5H2MassTerm_sound Z3_0_5H2Entropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
