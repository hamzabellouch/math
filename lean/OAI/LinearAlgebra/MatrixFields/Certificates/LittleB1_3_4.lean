import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma shapes4_list : shapes 4 = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B1_1_6Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (63 / 1000000)
  | _, _, _ => 0
lemma B1_1_6Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 1 6) u = B1_1_6Binary u := by
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
def B1_1_6LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_1_6Binary u else if i = 3 then B1_1_6Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_1_6Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_1_6LittleRat u w i)
  else .exact (littleLaw (shape 1 1 6) u w i)

lemma B1_1_6Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_1_6Little u w i).Encloses (littleLaw (shape 1 1 6) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_1_6Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_1_6LittleRat, littleLaw, B1_1_6Binary_eq u hu]
  · simp only [B1_1_6Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_1_6Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (3 / 50000000000000000000000000000000)⟩
  | 2, 5, 2 => ⟨(23395434846455848905473447711 / 2500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 5, 3 => ⟨(58960210306318037278141611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 4 => ⟨(49064123645931459725743783949949 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 5 => ⟨(23395434846455848905473447711 / 2500000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 3, 5 => ⟨(58960210306318037278141611 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_1_6Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((0 : Fin 6),j)) (B1_1_6Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((1 : Fin 6),j)) (B1_1_6Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((2 : Fin 6),j)) (B1_1_6Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((3 : Fin 6),j)) (B1_1_6Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((4 : Fin 6),j)) (B1_1_6Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 0) ((5 : Fin 6),j)) (B1_1_6Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((0 : Fin 6),j)) (B1_1_6Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((1 : Fin 6),j)) (B1_1_6Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((2 : Fin 6),j)) (B1_1_6Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((3 : Fin 6),j)) (B1_1_6Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((4 : Fin 6),j)) (B1_1_6Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 1) ((5 : Fin 6),j)) (B1_1_6Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((0 : Fin 6),j)) (B1_1_6Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((1 : Fin 6),j)) (B1_1_6Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((2 : Fin 6),j)) (B1_1_6Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((3 : Fin 6),j)) (B1_1_6Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((4 : Fin 6),j)) (B1_1_6Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_1_6Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u 2) ((5 : Fin 6),j)) (B1_1_6Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_1_6Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_1_6Half w ij).Encloses (halfLaw (shape 1 1 6) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 1 6)) (shape 1 1 6) B1_1_6Law
      (fun u => B1_1_6Little u w) ij) (B1_1_6Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_1_6Half_check_0_0 j) (B1_1_6Half_check_0_1 j) (B1_1_6Half_check_0_2 j) (B1_1_6Half_check_0_3 j) (B1_1_6Half_check_0_4 j) (B1_1_6Half_check_0_5 j)
    · exact forall_fin6 (B1_1_6Half_check_1_0 j) (B1_1_6Half_check_1_1 j) (B1_1_6Half_check_1_2 j) (B1_1_6Half_check_1_3 j) (B1_1_6Half_check_1_4 j) (B1_1_6Half_check_1_5 j)
    · exact forall_fin6 (B1_1_6Half_check_2_0 j) (B1_1_6Half_check_2_1 j) (B1_1_6Half_check_2_2 j) (B1_1_6Half_check_2_3 j) (B1_1_6Half_check_2_4 j) (B1_1_6Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 1 6)) (shape 1 1 6)
    B1_1_6Law (fun u => (stageBLaw (shape 1 1 6) u : ℝ))
    (fun u => B1_1_6Little u w) (fun u i => (littleLaw (shape 1 1 6) u w i : ℝ))
    (fun u _ => B1_1_6Law_sound u) (fun u i => B1_1_6Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 1 6) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B1_2_5_below : below (shape 1 2 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1)] := by decide +kernel
def B1_2_5Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(14279668505343149815259750483 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨1, 0⟩
  | 0, 2, 2 => ⟨(11468822577910492362546082899621 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(11468822577910492362546082899621 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(14279668505343149815259750483 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_2_5Raw_0_0_4 : (B1_2_5Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 0 4)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_0_1_3 : (B1_2_5Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 1 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_0_2_2 : (B1_2_5Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 0 2 2)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_0_3 : (B1_2_5Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 0 3)
    (0) (-5561) (0) w195 w167 w195
    (by decide +kernel) w195_sound w167_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_1_2 : (B1_2_5Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_2_5Raw_1_2_1 : (B1_2_5Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 2 5) (shape 1 2 1)
    (0) (-5561) (-55254) w195 w167 w27
    (by decide +kernel) w195_sound w167_sound w27_sound) (by decide +kernel)
lemma B1_2_5Raw_sound (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    (B1_2_5Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 2 5) u : ℝ) := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Raw_0_0_4
  · exact B1_2_5Raw_0_1_3
  · exact B1_2_5Raw_0_2_2
  · exact B1_2_5Raw_1_0_3
  · exact B1_2_5Raw_1_1_2
  · exact B1_2_5Raw_1_2_1
def B1_2_5Den : Ball := ⟨(157572587585637952209774570505833 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
lemma B1_2_5Den_sound : B1_2_5Den.Encloses (((below (shape 1 2 5)).map (splitWeight positiveSecond tablep (shape 1 2 5))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 2 5)) B1_2_5Raw (splitWeight positiveSecond tablep (shape 1 2 5)) B1_2_5Raw_sound) (by decide +kernel)
lemma B1_2_5Den_positive : 0 < B1_2_5Den.lower := by decide +kernel
def B1_2_5Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(9098047091850119065057057298309 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(9098047091850119065057057298309 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(396642594740867223667445521291 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_2_5Law (u : Shape) : Ball := if u ∈ below (shape 1 2 5) then B1_2_5Table u else .exact 0
lemma B1_2_5Law_check_0_0_4 : contains (.mul (B1_2_5Raw (shape 0 0 4)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 0 4)) = true := by decide +kernel
lemma B1_2_5Law_check_0_1_3 : contains (.mul (B1_2_5Raw (shape 0 1 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 1 3)) = true := by decide +kernel
lemma B1_2_5Law_check_0_2_2 : contains (.mul (B1_2_5Raw (shape 0 2 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 0 2 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_0_3 : contains (.mul (B1_2_5Raw (shape 1 0 3)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 0 3)) = true := by decide +kernel
lemma B1_2_5Law_check_1_1_2 : contains (.mul (B1_2_5Raw (shape 1 1 2)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 1 2)) = true := by decide +kernel
lemma B1_2_5Law_check_1_2_1 : contains (.mul (B1_2_5Raw (shape 1 2 1)) (.inv B1_2_5Den)) (B1_2_5Table (shape 1 2 1)) = true := by decide +kernel
lemma B1_2_5Law_check (u : Shape) (hu : u ∈ below (shape 1 2 5)) :
    contains (.mul (B1_2_5Raw u) (.inv B1_2_5Den)) (B1_2_5Table u) = true := by
  rw [B1_2_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_2_5Law_check_0_0_4
  · exact B1_2_5Law_check_0_1_3
  · exact B1_2_5Law_check_0_2_2
  · exact B1_2_5Law_check_1_0_3
  · exact B1_2_5Law_check_1_1_2
  · exact B1_2_5Law_check_1_2_1
lemma B1_2_5Law_sound (u : Shape) :
    (B1_2_5Law u).Encloses (stageBLaw (shape 1 2 5) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 2 5)
  · have h := contains_sound (Ball.mul_sound (B1_2_5Raw_sound u hu)
      (Ball.inv_sound B1_2_5Den_sound B1_2_5Den_positive)) (B1_2_5Law_check u hu)
    simpa only [B1_2_5Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B1_2_5Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_2_5Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (19531 / 200000)
  | 1, 2, 1 => (10533 / 250000)
  | _, _, _ => 0
lemma B1_2_5Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 2 5) u = B1_2_5Binary u := by
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
def B1_2_5LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_2_5Binary u else if i = 3 then B1_2_5Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_2_5Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_2_5LittleRat u w i)
  else .exact (littleLaw (shape 1 2 5) u w i)

lemma B1_2_5Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_2_5Little u w i).Encloses (littleLaw (shape 1 2 5) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_2_5Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_2_5LittleRat, littleLaw, B1_2_5Binary_eq u hu]
  · simp only [B1_2_5Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_2_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (1 / 2000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(3297719669499762242862115497643 / 20000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(355998814646362178458756161701 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(396642594740867223667445521291 / 625000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(3297719669499762242862115497643 / 20000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(355998814646362178458756161701 / 20000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(9630112437092073853782692487793 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 2, 4, 3 => ⟨(1776939577509246754596293860933 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(9630112437092073853782692487793 / 20000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 2, 3, 4 => ⟨(1776939577509246754596293860933 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(36249118515191988245121850051 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_2_5Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((0 : Fin 6),j)) (B1_2_5Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((1 : Fin 6),j)) (B1_2_5Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((2 : Fin 6),j)) (B1_2_5Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((3 : Fin 6),j)) (B1_2_5Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((4 : Fin 6),j)) (B1_2_5Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 0) ((5 : Fin 6),j)) (B1_2_5Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((0 : Fin 6),j)) (B1_2_5Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((1 : Fin 6),j)) (B1_2_5Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((2 : Fin 6),j)) (B1_2_5Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((3 : Fin 6),j)) (B1_2_5Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((4 : Fin 6),j)) (B1_2_5Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 1) ((5 : Fin 6),j)) (B1_2_5Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((0 : Fin 6),j)) (B1_2_5Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((1 : Fin 6),j)) (B1_2_5Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((2 : Fin 6),j)) (B1_2_5Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((3 : Fin 6),j)) (B1_2_5Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((4 : Fin 6),j)) (B1_2_5Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_2_5Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u 2) ((5 : Fin 6),j)) (B1_2_5Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_2_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_2_5Half w ij).Encloses (halfLaw (shape 1 2 5) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 2 5)) (shape 1 2 5) B1_2_5Law
      (fun u => B1_2_5Little u w) ij) (B1_2_5Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_2_5Half_check_0_0 j) (B1_2_5Half_check_0_1 j) (B1_2_5Half_check_0_2 j) (B1_2_5Half_check_0_3 j) (B1_2_5Half_check_0_4 j) (B1_2_5Half_check_0_5 j)
    · exact forall_fin6 (B1_2_5Half_check_1_0 j) (B1_2_5Half_check_1_1 j) (B1_2_5Half_check_1_2 j) (B1_2_5Half_check_1_3 j) (B1_2_5Half_check_1_4 j) (B1_2_5Half_check_1_5 j)
    · exact forall_fin6 (B1_2_5Half_check_2_0 j) (B1_2_5Half_check_2_1 j) (B1_2_5Half_check_2_2 j) (B1_2_5Half_check_2_3 j) (B1_2_5Half_check_2_4 j) (B1_2_5Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 2 5)) (shape 1 2 5)
    B1_2_5Law (fun u => (stageBLaw (shape 1 2 5) u : ℝ))
    (fun u => B1_2_5Little u w) (fun u i => (littleLaw (shape 1 2 5) u w i : ℝ))
    (fun u _ => B1_2_5Law_sound u) (fun u i => B1_2_5Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 2 5) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

def B1_3_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (46483 / 500000)
  | 1, 1, 2 => (301 / 250000)
  | 1, 2, 1 => (10537 / 250000)
  | _, _, _ => 0
lemma B1_3_4Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 3 4) u = B1_3_4Binary u := by
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
def B1_3_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_3_4Binary u else if i = 3 then B1_3_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_3_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_3_4LittleRat u w i)
  else .exact (littleLaw (shape 1 3 4) u w i)

lemma B1_3_4Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_3_4Little u w i).Encloses (littleLaw (shape 1 3 4) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_3_4Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_3_4LittleRat, littleLaw, B1_3_4Binary_eq u hu]
  · simp only [B1_3_4Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_3_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(132732360120937838226056869067 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(22225619795436123996567854910187 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(1055359201979593406150930372239 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(22225619795436123996567854910187 / 50000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(1055359201979593406150930372239 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(132732360120937838226056869067 / 10000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(1456119070923005006600137580027 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(77369303606423225289931508632371 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(4011596667753851198216770545993 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(4011596667753851198216770545993 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(4779571502687297343271865947 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(1456119070923005006600137580027 / 20000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(18376602916823826473515371739 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_3_4Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((0 : Fin 6),j)) (B1_3_4Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((1 : Fin 6),j)) (B1_3_4Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((2 : Fin 6),j)) (B1_3_4Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((3 : Fin 6),j)) (B1_3_4Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((4 : Fin 6),j)) (B1_3_4Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 0) ((5 : Fin 6),j)) (B1_3_4Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((0 : Fin 6),j)) (B1_3_4Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((1 : Fin 6),j)) (B1_3_4Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((2 : Fin 6),j)) (B1_3_4Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((3 : Fin 6),j)) (B1_3_4Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((4 : Fin 6),j)) (B1_3_4Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 1) ((5 : Fin 6),j)) (B1_3_4Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((0 : Fin 6),j)) (B1_3_4Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((1 : Fin 6),j)) (B1_3_4Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((2 : Fin 6),j)) (B1_3_4Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((3 : Fin 6),j)) (B1_3_4Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((4 : Fin 6),j)) (B1_3_4Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_3_4Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u 2) ((5 : Fin 6),j)) (B1_3_4Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_3_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_3_4Half w ij).Encloses (halfLaw (shape 1 3 4) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 3 4)) (shape 1 3 4) B1_3_4Law
      (fun u => B1_3_4Little u w) ij) (B1_3_4Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_3_4Half_check_0_0 j) (B1_3_4Half_check_0_1 j) (B1_3_4Half_check_0_2 j) (B1_3_4Half_check_0_3 j) (B1_3_4Half_check_0_4 j) (B1_3_4Half_check_0_5 j)
    · exact forall_fin6 (B1_3_4Half_check_1_0 j) (B1_3_4Half_check_1_1 j) (B1_3_4Half_check_1_2 j) (B1_3_4Half_check_1_3 j) (B1_3_4Half_check_1_4 j) (B1_3_4Half_check_1_5 j)
    · exact forall_fin6 (B1_3_4Half_check_2_0 j) (B1_3_4Half_check_2_1 j) (B1_3_4Half_check_2_2 j) (B1_3_4Half_check_2_3 j) (B1_3_4Half_check_2_4 j) (B1_3_4Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 3 4)) (shape 1 3 4)
    B1_3_4Law (fun u => (stageBLaw (shape 1 3 4) u : ℝ))
    (fun u => B1_3_4Little u w) (fun u i => (littleLaw (shape 1 3 4) u w i : ℝ))
    (fun u _ => B1_3_4Law_sound u) (fun u i => B1_3_4Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 3 4) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
