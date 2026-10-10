import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_1_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B4_3_1_below : below (shape 4 3 1) = [
  (shape 0 3 1),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B4_3_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(39716959361056311017780307549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(15598428718166136993941318394257 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(768108580374508289602379874323 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(768108580374508289602379874323 / 25000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(15598428718166136993941318394257 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(39716959361056311017780307549 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_3_1Raw_0_3_1 : (B4_3_1Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 0 3 1)
    (-55133) (-16247) (0) w30 w106 w195
    (by decide +kernel) w30_sound w106_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_1_2_1 : (B4_3_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 1 2 1)
    (-18580) (0) (0) w92 w195 w195
    (by decide +kernel) w92_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_1_3_0 : (B4_3_1Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 1 3 0)
    (-18580) (-16247) (0) w92 w106 w195
    (by decide +kernel) w92_sound w106_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_2_1_1 : (B4_3_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_2_2_0 : (B4_3_1Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 2 2 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_3_0_1 : (B4_3_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 3 0 1)
    (-18580) (-16247) (0) w92 w106 w195
    (by decide +kernel) w92_sound w106_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_3_1_0 : (B4_3_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 3 1 0)
    (-18580) (0) (0) w92 w195 w195
    (by decide +kernel) w92_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_4_0_0 : (B4_3_1Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 3 1) (shape 4 0 0)
    (-55133) (-16247) (0) w30 w106 w195
    (by decide +kernel) w30_sound w106_sound w195_sound) (by decide +kernel)
lemma B4_3_1Raw_sound (u : Shape) (hu : u ∈ below (shape 4 3 1)) :
    (B4_3_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 4 3 1) u : ℝ) := by
  rw [B4_3_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_3_1Raw_0_3_1
  · exact B4_3_1Raw_1_2_1
  · exact B4_3_1Raw_1_3_0
  · exact B4_3_1Raw_2_1_1
  · exact B4_3_1Raw_2_2_0
  · exact B4_3_1Raw_3_0_1
  · exact B4_3_1Raw_3_1_0
  · exact B4_3_1Raw_4_0_0
def B4_3_1Den : Ball := ⟨(118750296958386282774386398506647 / 50000000000000000000000000000000), (17 / 25000000000000000000000000000000)⟩
lemma B4_3_1Den_sound : B4_3_1Den.Encloses (((below (shape 4 3 1)).map (splitWeight positiveSecond tablep (shape 4 3 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 3 1)) B4_3_1Raw (splitWeight positiveSecond tablep (shape 4 3 1)) B4_3_1Raw_sound) (by decide +kernel)
lemma B4_3_1Den_positive : 0 < B4_3_1Den.lower := by decide +kernel
def B4_3_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(8421031573086763956728433893807 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(8421031573086763956728433893807 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(1293653321378517322144444232489 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(205241969884719280749621373729 / 3125000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_3_1Law (u : Shape) : Ball := if u ∈ below (shape 4 3 1) then B4_3_1Table u else .exact 0
lemma B4_3_1Law_check_0_3_1 : contains (.mul (B4_3_1Raw (shape 0 3 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 0 3 1)) = true := by decide +kernel
lemma B4_3_1Law_check_1_2_1 : contains (.mul (B4_3_1Raw (shape 1 2 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B4_3_1Law_check_1_3_0 : contains (.mul (B4_3_1Raw (shape 1 3 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 1 3 0)) = true := by decide +kernel
lemma B4_3_1Law_check_2_1_1 : contains (.mul (B4_3_1Raw (shape 2 1 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_3_1Law_check_2_2_0 : contains (.mul (B4_3_1Raw (shape 2 2 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B4_3_1Law_check_3_0_1 : contains (.mul (B4_3_1Raw (shape 3 0 1)) (.inv B4_3_1Den)) (B4_3_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_3_1Law_check_3_1_0 : contains (.mul (B4_3_1Raw (shape 3 1 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_3_1Law_check_4_0_0 : contains (.mul (B4_3_1Raw (shape 4 0 0)) (.inv B4_3_1Den)) (B4_3_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_3_1Law_check (u : Shape) (hu : u ∈ below (shape 4 3 1)) :
    contains (.mul (B4_3_1Raw u) (.inv B4_3_1Den)) (B4_3_1Table u) = true := by
  rw [B4_3_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_3_1Law_check_0_3_1
  · exact B4_3_1Law_check_1_2_1
  · exact B4_3_1Law_check_1_3_0
  · exact B4_3_1Law_check_2_1_1
  · exact B4_3_1Law_check_2_2_0
  · exact B4_3_1Law_check_3_0_1
  · exact B4_3_1Law_check_3_1_0
  · exact B4_3_1Law_check_4_0_0
lemma B4_3_1Law_sound (u : Shape) :
    (B4_3_1Law u).Encloses (stageBLaw (shape 4 3 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 3 1)
  · have h := contains_sound (Ball.mul_sound (B4_3_1Raw_sound u hu)
      (Ball.inv_sound B4_3_1Den_sound B4_3_1Den_positive)) (B4_3_1Law_check u hu)
    simpa only [B4_3_1Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_3_1Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

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
def B4_3_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (42189 / 1000000)
  | 2, 1, 1 => (2967 / 1000000)
  | 2, 2, 0 => (48021 / 500000)
  | _, _, _ => 0
lemma B4_3_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 4 3 1) u = B4_3_1Binary u := by
  rw [shapes4_list] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
def B4_3_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_3_1Binary u else if i = 3 then B4_3_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_3_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_3_1LittleRat u w i)
  else .exact (littleLaw (shape 4 3 1) u w i)

lemma B4_3_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B4_3_1Little u w i).Encloses (littleLaw (shape 4 3 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B4_3_1Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B4_3_1LittleRat, littleLaw, B4_3_1Binary_eq u hu]
  · simp only [B4_3_1Little, hu, ite_false]
    exact Ball.exact_sound _
def B4_3_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(7861396357689534306132328191817 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(1517934657342094088384406991891 / 2000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(4144793288664198085105361786561 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(4144793288664198085105361786561 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(23996286434538977853265770399 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(7861396357689534306132328191817 / 100000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(33445776876645910225502339149 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(22175975409536958176216013675929 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(864190016534184083039605215301 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(663549549127581616184973285819 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(50000000000000000000000000000001 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_3_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((0 : Fin 6),j)) (B4_3_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((1 : Fin 6),j)) (B4_3_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((2 : Fin 6),j)) (B4_3_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((3 : Fin 6),j)) (B4_3_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((4 : Fin 6),j)) (B4_3_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 0) ((5 : Fin 6),j)) (B4_3_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((0 : Fin 6),j)) (B4_3_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((1 : Fin 6),j)) (B4_3_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((2 : Fin 6),j)) (B4_3_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((3 : Fin 6),j)) (B4_3_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((4 : Fin 6),j)) (B4_3_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 1) ((5 : Fin 6),j)) (B4_3_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((0 : Fin 6),j)) (B4_3_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((1 : Fin 6),j)) (B4_3_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((2 : Fin 6),j)) (B4_3_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((3 : Fin 6),j)) (B4_3_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((4 : Fin 6),j)) (B4_3_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B4_3_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u 2) ((5 : Fin 6),j)) (B4_3_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B4_3_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (B4_3_1Half w ij).Encloses (halfLaw (shape 4 3 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 4 3 1)) (shape 4 3 1) B4_3_1Law
      (fun u => B4_3_1Little u w) ij) (B4_3_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B4_3_1Half_check_0_0 j) (B4_3_1Half_check_0_1 j) (B4_3_1Half_check_0_2 j) (B4_3_1Half_check_0_3 j) (B4_3_1Half_check_0_4 j) (B4_3_1Half_check_0_5 j)
    · exact forall_fin6 (B4_3_1Half_check_1_0 j) (B4_3_1Half_check_1_1 j) (B4_3_1Half_check_1_2 j) (B4_3_1Half_check_1_3 j) (B4_3_1Half_check_1_4 j) (B4_3_1Half_check_1_5 j)
    · exact forall_fin6 (B4_3_1Half_check_2_0 j) (B4_3_1Half_check_2_1 j) (B4_3_1Half_check_2_2 j) (B4_3_1Half_check_2_3 j) (B4_3_1Half_check_2_4 j) (B4_3_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 4 3 1)) (shape 4 3 1)
    B4_3_1Law (fun u => (stageBLaw (shape 4 3 1) u : ℝ))
    (fun u => B4_3_1Little u w) (fun u i => (littleLaw (shape 4 3 1) u w i : ℝ))
    (fun u _ => B4_3_1Law_sound u) (fun u i => B4_3_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 4 3 1) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

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
def B4_3_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_3_1U0_3_1Leaf_sound : B4_3_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_3_1U0_3_1Mass : Ball := ⟨(136748963356297381050269443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_3_1U0_3_1Mass_sound : B4_3_1U0_3_1Mass.Encloses (littleMass (shape 4 3 1) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 0 3 1))) (by decide +kernel)
def B4_3_1U1_2_1D : Ball := .exact (42189 / 1000000)
lemma B4_3_1U1_2_1D_sound : B4_3_1U1_2_1D.Encloses (binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_3_1U1_2_1OneD : Ball := .exact (957811 / 1000000)
lemma B4_3_1U1_2_1OneD_sound : B4_3_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 4 3 1) (shape 1 2 1) = (42189 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((957811 / 1000000) : ℚ) using 1 <;> norm_num [B4_3_1U1_2_1OneD, Ball.exact]
def B4_3_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 42189, 31250⟩
def B4_3_1U1_2_1EDLog : Ball := ⟨(-316559575542591669352988093304233 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1EDLog_sound : B4_3_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U1_2_1D_sound) (w := B4_3_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U1_2_1ED : Ball := ⟨(3338832983141599984583303667103 / 25000000000000000000000000000000), (5360320953 / 100000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1ED_sound : B4_3_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U1_2_1D_sound) B4_3_1U1_2_1EDLog_sound) (by decide +kernel)
def B4_3_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 957811, 500000⟩
def B4_3_1U1_2_1EOneDLog : Ball := ⟨(-4310480648724792521258507583371 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1EOneDLog_sound : B4_3_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U1_2_1OneD_sound) (w := B4_3_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U1_2_1EOneD : Ball := ⟨(516078222579467781197391550867 / 12500000000000000000000000000000), (10141218429 / 25000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1EOneD_sound : B4_3_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U1_2_1OneD_sound) B4_3_1U1_2_1EOneDLog_sound) (by decide +kernel)
def B4_3_1U1_2_1BinaryEntropy : Ball := ⟨(5102069088316623863453176716737 / 25000000000000000000000000000000), (47711968321 / 100000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1BinaryEntropy_sound : B4_3_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 3 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_3_1U1_2_1EOneD_sound B4_3_1U1_2_1ED_sound)
    (Ball.mul_sound B4_3_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B4_3_1U1_2_1Leaf : Ball := ⟨(315097524878051848849748648323579 / 100000000000000000000000000000000), (62187390811 / 50000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1Leaf_sound : B4_3_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1957811 / 1000000)).Encloses (2 - (binaryParameter (shape 4 3 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 4 3 1) (shape 1 2 1) = (42189 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1957811 / 1000000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_3_1U1_2_1Mass : Ball := ⟨(26853376888763757073709961953 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B4_3_1U1_2_1Mass_sound : B4_3_1U1_2_1Mass.Encloses (littleMass (shape 4 3 1) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 1 2 1))) (by decide +kernel)
def B4_3_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_3_1U1_3_0Leaf_sound : B4_3_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_3_1U1_3_0Mass : Ball := ⟨(2644664994528363790023240491 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_3_1U1_3_0Mass_sound : B4_3_1U1_3_0Mass.Encloses (littleMass (shape 4 3 1) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 1 3 0))) (by decide +kernel)
def B4_3_1U2_1_1D : Ball := .exact (2967 / 1000000)
lemma B4_3_1U2_1_1D_sound : B4_3_1U2_1_1D.Encloses (binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_3_1U2_1_1OneD : Ball := .exact (997033 / 1000000)
lemma B4_3_1U2_1_1OneD_sound : B4_3_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 4 3 1) (shape 2 1 1) = (2967 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((997033 / 1000000) : ℚ) using 1 <;> norm_num [B4_3_1U2_1_1OneD, Ball.exact]
def B4_3_1U2_1_1EDLogWitness : LogWitness := ⟨-9, 23736, 15625⟩
def B4_3_1U2_1_1EDLog : Ball := ⟨(-582020393767345229843310642743373 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1EDLog_sound : B4_3_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U2_1_1D_sound) (w := B4_3_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U2_1_1ED : Ball := ⟨(86342725415385664847255133851 / 5000000000000000000000000000000), (62828669 / 10000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1ED_sound : B4_3_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U2_1_1D_sound) B4_3_1U2_1_1EDLog_sound) (by decide +kernel)
def B4_3_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 997033, 500000⟩
def B4_3_1U2_1_1EOneDLog : Ball := ⟨(-148570513508735706819130119317 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1EOneDLog_sound : B4_3_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U2_1_1OneD_sound) (w := B4_3_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U2_1_1EOneD : Ball := ⟨(148129704795155287976997760253 / 50000000000000000000000000000000), (42225990029 / 100000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1EOneD_sound : B4_3_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U2_1_1OneD_sound) B4_3_1U2_1_1EOneDLog_sound) (by decide +kernel)
def B4_3_1U2_1_1BinaryEntropy : Ball := ⟨(1114385343185079823101595455653 / 50000000000000000000000000000000), (21489967029 / 50000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1BinaryEntropy_sound : B4_3_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 3 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_3_1U2_1_1EOneD_sound B4_3_1U2_1_1ED_sound)
    (Ball.mul_sound B4_3_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B4_3_1U2_1_1Leaf : Ball := ⟨(5022032222784388708421996016913 / 1562500000000000000000000000000), (31716614023 / 25000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1Leaf_sound : B4_3_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1997033 / 1000000)).Encloses (2 - (binaryParameter (shape 4 3 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 4 3 1) (shape 2 1 1) = (2967 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1997033 / 1000000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_3_1U2_1_1Mass : Ball := ⟨(34430874255289519189291326717 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma B4_3_1U2_1_1Mass_sound : B4_3_1U2_1_1Mass.Encloses (littleMass (shape 4 3 1) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 2 1 1))) (by decide +kernel)
def B4_3_1U2_2_0D : Ball := .exact (48021 / 500000)
lemma B4_3_1U2_2_0D_sound : B4_3_1U2_2_0D.Encloses (binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_3_1U2_2_0OneD : Ball := .exact (451979 / 500000)
lemma B4_3_1U2_2_0OneD_sound : B4_3_1U2_2_0OneD.Encloses (1 - (binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 4 3 1) (shape 2 2 0) = (48021 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((451979 / 500000) : ℚ) using 1 <;> norm_num [B4_3_1U2_2_0OneD, Ball.exact]
def B4_3_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 48021, 31250⟩
def B4_3_1U2_2_0EDLog : Ball := ⟨(-234296968318952155799785664084377 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0EDLog_sound : B4_3_1U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U2_2_0D_sound) (w := B4_3_1U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U2_2_0ED : Ball := ⟨(2812793678911100368415376843749 / 12500000000000000000000000000000), (10168842291 / 100000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0ED_sound : B4_3_1U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U2_2_0D_sound) B4_3_1U2_2_0EDLog_sound) (by decide +kernel)
def B4_3_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 451979, 250000⟩
def B4_3_1U2_2_0EOneDLog : Ball := ⟨(-1009723798462591586934335088673 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0EOneDLog_sound : B4_3_1U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_3_1U2_2_0OneD_sound) (w := B4_3_1U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_3_1U2_2_0EOneD : Ball := ⟨(9127479054106473657419876780867 / 100000000000000000000000000000000), (765682209 / 2000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0EOneD_sound : B4_3_1U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 3 1) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_3_1U2_2_0OneD_sound) B4_3_1U2_2_0EOneDLog_sound) (by decide +kernel)
def B4_3_1U2_2_0BinaryEntropy : Ball := ⟨(38286952636929103345447870437799 / 100000000000000000000000000000000), (26260244829 / 50000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0BinaryEntropy_sound : B4_3_1U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 3 1) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_3_1U2_2_0EOneD_sound B4_3_1U2_2_0ED_sound)
    (Ball.mul_sound B4_3_1U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B4_3_1U2_2_0Leaf : Ball := ⟨(16462990396327500231505922123031 / 5000000000000000000000000000000), (10460801313 / 6250000000000000000000000000000)⟩
lemma B4_3_1U2_2_0Leaf_sound : B4_3_1U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B4_3_1U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B4_3_1U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B4_3_1U2_2_0Mass : Ball := ⟨(34430874255289519189291326717 / 10000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
lemma B4_3_1U2_2_0Mass_sound : B4_3_1U2_2_0Mass.Encloses (littleMass (shape 4 3 1) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 2 2 0))) (by decide +kernel)
def B4_3_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_3_1U3_0_1Leaf_sound : B4_3_1U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_3_1U3_0_1Mass : Ball := ⟨(2644664994528363790023240491 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_3_1U3_0_1Mass_sound : B4_3_1U3_0_1Mass.Encloses (littleMass (shape 4 3 1) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 3 0 1))) (by decide +kernel)
def B4_3_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_3_1U3_1_0Leaf_sound : B4_3_1U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_3_1U3_1_0Mass : Ball := ⟨(26853376888763757073709961953 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B4_3_1U3_1_0Mass_sound : B4_3_1U3_1_0Mass.Encloses (littleMass (shape 4 3 1) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 3 1 0))) (by decide +kernel)
def B4_3_1U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B4_3_1U4_0_0Leaf_sound : B4_3_1U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B4_3_1U4_0_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B4_3_1U4_0_0Mass : Ball := ⟨(136748963356297381050269443 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_3_1U4_0_0Mass_sound : B4_3_1U4_0_0Mass.Encloses (littleMass (shape 4 3 1) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_3_1))
    (B4_3_1Law_sound (shape 4 0 0))) (by decide +kernel)
def B4_3_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B4_3_1U0_3_1Leaf
  | 1, 2, 1 => B4_3_1U1_2_1Leaf
  | 1, 3, 0 => B4_3_1U1_3_0Leaf
  | 2, 1, 1 => B4_3_1U2_1_1Leaf
  | 2, 2, 0 => B4_3_1U2_2_0Leaf
  | 3, 0, 1 => B4_3_1U3_0_1Leaf
  | 3, 1, 0 => B4_3_1U3_1_0Leaf
  | 4, 0, 0 => B4_3_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B4_3_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 4 3 1)) :
    (B4_3_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 3 1) u) := by
  rw [B4_3_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_3_1U0_3_1Leaf_sound
  · exact B4_3_1U1_2_1Leaf_sound
  · exact B4_3_1U1_3_0Leaf_sound
  · exact B4_3_1U2_1_1Leaf_sound
  · exact B4_3_1U2_2_0Leaf_sound
  · exact B4_3_1U3_0_1Leaf_sound
  · exact B4_3_1U3_1_0Leaf_sound
  · exact B4_3_1U4_0_0Leaf_sound
def B4_3_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B4_3_1U0_3_1Mass
  | 1, 2, 1 => B4_3_1U1_2_1Mass
  | 1, 3, 0 => B4_3_1U1_3_0Mass
  | 2, 1, 1 => B4_3_1U2_1_1Mass
  | 2, 2, 0 => B4_3_1U2_2_0Mass
  | 3, 0, 1 => B4_3_1U3_0_1Mass
  | 3, 1, 0 => B4_3_1U3_1_0Mass
  | 4, 0, 0 => B4_3_1U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B4_3_1Masses_sound (u : Shape) (hu : u ∈ below (shape 4 3 1)) :
    (B4_3_1Masses u).Encloses ((fun u => (littleMass (shape 4 3 1) u : ℝ)) u) := by
  rw [B4_3_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_3_1U0_3_1Mass_sound
  · exact B4_3_1U1_2_1Mass_sound
  · exact B4_3_1U1_3_0Mass_sound
  · exact B4_3_1U2_1_1Mass_sound
  · exact B4_3_1U2_2_0Mass_sound
  · exact B4_3_1U3_0_1Mass_sound
  · exact B4_3_1U3_1_0Mass_sound
  · exact B4_3_1U4_0_0Mass_sound
def B4_3_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B4_3_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B4_3_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B4_3_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B4_3_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 4 3 1)).filter positive) :
    (B4_3_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 4 3 1) u)) u) := by
  have hl : (below (shape 4 3 1)).filter positive = [(shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B4_3_1U1_2_1BinaryEntropy_sound
  · exact B4_3_1U2_1_1BinaryEntropy_sound
def B4_3_1S2 : Ball := ⟨(2582552552478173297939862688551 / 100000000000000000000000000000000), (285883319 / 25000000000000000000000000000000)⟩
lemma B4_3_1S2_sound : B4_3_1S2.Encloses
    (((below (shape 4 3 1)).map fun u => (littleMass (shape 4 3 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 4 3 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 4 3 1))
    (fun u => .mul (B4_3_1Masses u) (B4_3_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B4_3_1Masses_sound u hu) (B4_3_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
