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
lemma B1_6_1_below : below (shape 1 6 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0)] := by decide +kernel
def B1_6_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨1, 0⟩
  | 0, 4, 0 => ⟨(7768490128715345018830058107081 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(7768490128715345018830058107081 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨1, 0⟩
  | _, _, _ => (.exact 0)
lemma B1_6_1Raw_0_3_1 : (B1_6_1Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 0 3 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_0_4_0 : (B1_6_1Raw (shape 0 4 0)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 0 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 0 4 0)
    (0) (-11688) (0) w195 w124 w195
    (by decide +kernel) w195_sound w124_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_1_2_1 : (B1_6_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 1 2 1)
    (0) (-11688) (0) w195 w124 w195
    (by decide +kernel) w195_sound w124_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_1_3_0 : (B1_6_1Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 1 6 1) (shape 1 3 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B1_6_1Raw_sound (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    (B1_6_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 1 6 1) u : ℝ) := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1Raw_0_3_1
  · exact B1_6_1Raw_0_4_0
  · exact B1_6_1Raw_1_2_1
  · exact B1_6_1Raw_1_3_0
def B1_6_1Den : Ball := ⟨(32768490128715345018830058107081 / 12500000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
lemma B1_6_1Den_sound : B1_6_1Den.Encloses (((below (shape 1 6 1)).map (splitWeight positiveSecond tablep (shape 1 6 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 6 1)) B1_6_1Raw (splitWeight positiveSecond tablep (shape 1 6 1)) B1_6_1Raw_sound) (by decide +kernel)
lemma B1_6_1Den_positive : 0 < B1_6_1Den.lower := by decide +kernel
def B1_6_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(476830025998288559780831570863 / 1250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(148169974001711440219168429137 / 1250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(148169974001711440219168429137 / 1250000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(476830025998288559780831570863 / 1250000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B1_6_1Law (u : Shape) : Ball := if u ∈ below (shape 1 6 1) then B1_6_1Table u else .exact 0
lemma B1_6_1Law_check_0_3_1 : contains (.mul (B1_6_1Raw (shape 0 3 1)) (.inv B1_6_1Den)) (B1_6_1Table (shape 0 3 1)) = true := by decide +kernel
lemma B1_6_1Law_check_0_4_0 : contains (.mul (B1_6_1Raw (shape 0 4 0)) (.inv B1_6_1Den)) (B1_6_1Table (shape 0 4 0)) = true := by decide +kernel
lemma B1_6_1Law_check_1_2_1 : contains (.mul (B1_6_1Raw (shape 1 2 1)) (.inv B1_6_1Den)) (B1_6_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B1_6_1Law_check_1_3_0 : contains (.mul (B1_6_1Raw (shape 1 3 0)) (.inv B1_6_1Den)) (B1_6_1Table (shape 1 3 0)) = true := by decide +kernel
lemma B1_6_1Law_check (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    contains (.mul (B1_6_1Raw u) (.inv B1_6_1Den)) (B1_6_1Table u) = true := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1Law_check_0_3_1
  · exact B1_6_1Law_check_0_4_0
  · exact B1_6_1Law_check_1_2_1
  · exact B1_6_1Law_check_1_3_0
lemma B1_6_1Law_sound (u : Shape) :
    (B1_6_1Law u).Encloses (stageBLaw (shape 1 6 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 6 1)
  · have h := contains_sound (Ball.mul_sound (B1_6_1Raw_sound u hu)
      (Ball.inv_sound B1_6_1Den_sound B1_6_1Den_positive)) (B1_6_1Law_check u hu)
    simpa only [B1_6_1Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B1_6_1Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B1_6_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (41991 / 1000000)
  | _, _, _ => 0
lemma B1_6_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 6 1) u = B1_6_1Binary u := by
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
def B1_6_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_6_1Binary u else if i = 3 then B1_6_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_6_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_6_1LittleRat u w i)
  else .exact (littleLaw (shape 1 6 1) u w i)

lemma B1_6_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_6_1Little u w i).Encloses (littleLaw (shape 1 6 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_6_1Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_6_1LittleRat, littleLaw, B1_6_1Binary_eq u hu]
  · simp only [B1_6_1Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_6_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 1, 4, 4 => ⟨(476830025998288559780831570863 / 625000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(11355853489872446010634026210329 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 5, 3 => ⟨(497744430264469206899448120631 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(11355853489872446010634026210329 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 5 => ⟨(497744430264469206899448120631 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (17 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_6_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((0 : Fin 6),j)) (B1_6_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((1 : Fin 6),j)) (B1_6_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((2 : Fin 6),j)) (B1_6_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((3 : Fin 6),j)) (B1_6_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((4 : Fin 6),j)) (B1_6_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 0) ((5 : Fin 6),j)) (B1_6_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((0 : Fin 6),j)) (B1_6_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((1 : Fin 6),j)) (B1_6_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((2 : Fin 6),j)) (B1_6_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((3 : Fin 6),j)) (B1_6_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((4 : Fin 6),j)) (B1_6_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 1) ((5 : Fin 6),j)) (B1_6_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((0 : Fin 6),j)) (B1_6_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((1 : Fin 6),j)) (B1_6_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((2 : Fin 6),j)) (B1_6_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((3 : Fin 6),j)) (B1_6_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((4 : Fin 6),j)) (B1_6_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_6_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u 2) ((5 : Fin 6),j)) (B1_6_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_6_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_6_1Half w ij).Encloses (halfLaw (shape 1 6 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 6 1)) (shape 1 6 1) B1_6_1Law
      (fun u => B1_6_1Little u w) ij) (B1_6_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_6_1Half_check_0_0 j) (B1_6_1Half_check_0_1 j) (B1_6_1Half_check_0_2 j) (B1_6_1Half_check_0_3 j) (B1_6_1Half_check_0_4 j) (B1_6_1Half_check_0_5 j)
    · exact forall_fin6 (B1_6_1Half_check_1_0 j) (B1_6_1Half_check_1_1 j) (B1_6_1Half_check_1_2 j) (B1_6_1Half_check_1_3 j) (B1_6_1Half_check_1_4 j) (B1_6_1Half_check_1_5 j)
    · exact forall_fin6 (B1_6_1Half_check_2_0 j) (B1_6_1Half_check_2_1 j) (B1_6_1Half_check_2_2 j) (B1_6_1Half_check_2_3 j) (B1_6_1Half_check_2_4 j) (B1_6_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 6 1)) (shape 1 6 1)
    B1_6_1Law (fun u => (stageBLaw (shape 1 6 1) u : ℝ))
    (fun u => B1_6_1Little u w) (fun u i => (littleLaw (shape 1 6 1) u w i : ℝ))
    (fun u _ => B1_6_1Law_sound u) (fun u i => B1_6_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 6 1) = true := by decide +kernel
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
def B1_6_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_6_1U0_3_1Leaf_sound : B1_6_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_6_1U0_3_1Mass : Ball := ⟨(2506339406252300091999692633 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B1_6_1U0_3_1Mass_sound : B1_6_1U0_3_1Mass.Encloses (littleMass (shape 1 6 1) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_6_1))
    (B1_6_1Law_sound (shape 0 3 1))) (by decide +kernel)
def B1_6_1U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B1_6_1U0_4_0Leaf_sound : B1_6_1U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B1_6_1U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B1_6_1U0_4_0Mass : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_6_1U0_4_0Mass_sound : B1_6_1U0_4_0Mass.Encloses (littleMass (shape 1 6 1) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_6_1))
    (B1_6_1Law_sound (shape 0 4 0))) (by decide +kernel)
def B1_6_1U1_2_1D : Ball := .exact (41991 / 1000000)
lemma B1_6_1U1_2_1D_sound : B1_6_1U1_2_1D.Encloses (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_6_1U1_2_1OneD : Ball := .exact (958009 / 1000000)
lemma B1_6_1U1_2_1OneD_sound : B1_6_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 1 6 1) (shape 1 2 1) = (41991 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((958009 / 1000000) : ℚ) using 1 <;> norm_num [B1_6_1U1_2_1OneD, Ball.exact]
def B1_6_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 41991, 31250⟩
def B1_6_1U1_2_1EDLog : Ball := ⟨(-63405999387510370889753295440677 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1EDLog_sound : B1_6_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_6_1U1_2_1D_sound) (w := B1_6_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_6_1U1_2_1ED : Ball := ⟨(13312406601404739920158153144247 / 100000000000000000000000000000000), (2667582037 / 50000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1ED_sound : B1_6_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_6_1U1_2_1D_sound) B1_6_1U1_2_1EDLog_sound) (by decide +kernel)
def B1_6_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 958009, 500000⟩
def B1_6_1U1_2_1EOneDLog : Ball := ⟨(-857962129667603414297940708059 / 20000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1EOneDLog_sound : B1_6_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_6_1U1_2_1OneD_sound) (w := B1_6_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_6_1U1_2_1EOneD : Ball := ⟨(2054838604701827698320389699467 / 50000000000000000000000000000000), (40573259341 / 100000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1EOneD_sound : B1_6_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_6_1U1_2_1OneD_sound) B1_6_1U1_2_1EOneDLog_sound) (by decide +kernel)
def B1_6_1U1_2_1BinaryEntropy : Ball := ⟨(20332678136697661665572831142557 / 100000000000000000000000000000000), (596085143 / 1250000000000000000000000000000)⟩
lemma B1_6_1U1_2_1BinaryEntropy_sound : B1_6_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 6 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_6_1U1_2_1EOneD_sound B1_6_1U1_2_1ED_sound)
    (Ball.mul_sound B1_6_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B1_6_1U1_2_1Leaf : Ball := ⟨(63025878349743608807433148670163 / 20000000000000000000000000000000), (62193680031 / 50000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1Leaf_sound : B1_6_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1958009 / 1000000)).Encloses (2 - (binaryParameter (shape 1 6 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 1 6 1) (shape 1 2 1) = (41991 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1958009 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_6_1U1_2_1Mass : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_6_1U1_2_1Mass_sound : B1_6_1U1_2_1Mass.Encloses (littleMass (shape 1 6 1) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_6_1))
    (B1_6_1Law_sound (shape 1 2 1))) (by decide +kernel)
def B1_6_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_6_1U1_3_0Leaf_sound : B1_6_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_6_1U1_3_0Mass : Ball := ⟨(2506339406252300091999692633 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B1_6_1U1_3_0Mass_sound : B1_6_1U1_3_0Mass.Encloses (littleMass (shape 1 6 1) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_6_1))
    (B1_6_1Law_sound (shape 1 3 0))) (by decide +kernel)
def B1_6_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B1_6_1U0_3_1Leaf
  | 0, 4, 0 => B1_6_1U0_4_0Leaf
  | 1, 2, 1 => B1_6_1U1_2_1Leaf
  | 1, 3, 0 => B1_6_1U1_3_0Leaf
  | _, _, _ => (.exact 0)
lemma B1_6_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    (B1_6_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 6 1) u) := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1U0_3_1Leaf_sound
  · exact B1_6_1U0_4_0Leaf_sound
  · exact B1_6_1U1_2_1Leaf_sound
  · exact B1_6_1U1_3_0Leaf_sound
def B1_6_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B1_6_1U0_3_1Mass
  | 0, 4, 0 => B1_6_1U0_4_0Mass
  | 1, 2, 1 => B1_6_1U1_2_1Mass
  | 1, 3, 0 => B1_6_1U1_3_0Mass
  | _, _, _ => (.exact 0)
lemma B1_6_1Masses_sound (u : Shape) (hu : u ∈ below (shape 1 6 1)) :
    (B1_6_1Masses u).Encloses ((fun u => (littleMass (shape 1 6 1) u : ℝ)) u) := by
  rw [B1_6_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_6_1U0_3_1Mass_sound
  · exact B1_6_1U0_4_0Mass_sound
  · exact B1_6_1U1_2_1Mass_sound
  · exact B1_6_1U1_3_0Mass_sound
def B1_6_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B1_6_1U1_2_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_6_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 6 1)).filter positive) :
    (B1_6_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 6 1) u)) u) := by
  have hl : (below (shape 1 6 1)).filter positive = [(shape 1 2 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact B1_6_1U1_2_1BinaryEntropy_sound
def B1_6_1S2 : Ball := ⟨(6998203413539342705601595361 / 50000000000000000000000000000000), (5214669 / 100000000000000000000000000000000)⟩
lemma B1_6_1S2_sound : B1_6_1S2.Encloses
    (((below (shape 1 6 1)).map fun u => (littleMass (shape 1 6 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 6 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 6 1))
    (fun u => .mul (B1_6_1Masses u) (B1_6_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_6_1Masses_sound u hu) (B1_6_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
