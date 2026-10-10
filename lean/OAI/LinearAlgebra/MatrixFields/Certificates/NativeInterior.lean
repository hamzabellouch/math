import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_1_7
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_5_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_7_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Four0_8_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four1_0_7
import OAI.LinearAlgebra.MatrixFields.Certificates.Four1_7_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four2_0_6
import OAI.LinearAlgebra.MatrixFields.Certificates.Four2_6_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four3_0_5
import OAI.LinearAlgebra.MatrixFields.Certificates.Four3_5_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four4_0_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Four4_4_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four5_0_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Four5_3_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four6_0_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Four6_2_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four7_0_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Four7_1_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Four8_0_0
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_2_5
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_3_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_4_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_5_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal1_6_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_1_5
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_2_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_3_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_4_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal2_5_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_1_4
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_2_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_3_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal3_4_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_1_3
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_2_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal4_3_1
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal5_1_2
import OAI.LinearAlgebra.MatrixFields.Certificates.Terminal5_2_1

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma B6_1_1_below : below (shape 6 1 1) = [
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B6_1_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => ⟨(19757482365589500963001701230393 / 20000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨1, 0⟩
  | 3, 1, 0 => ⟨1, 0⟩
  | 4, 0, 0 => ⟨(19757482365589500963001701230393 / 20000000000000000000000000000000), (63 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B6_1_1Raw_2_1_1 : (B6_1_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 2 1 1)
    (-122) (0) (0) w193 w195 w195
    (by decide +kernel) w193_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_3_0_1 : (B6_1_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 3 0 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_3_1_0 : (B6_1_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 3 1 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_4_0_0 : (B6_1_1Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 6 1 1) (shape 4 0 0)
    (-122) (0) (0) w193 w195 w195
    (by decide +kernel) w193_sound w195_sound w195_sound) (by decide +kernel)
lemma B6_1_1Raw_sound (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    (B6_1_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 6 1 1) u : ℝ) := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1Raw_2_1_1
  · exact B6_1_1Raw_3_0_1
  · exact B6_1_1Raw_3_1_0
  · exact B6_1_1Raw_4_0_0
def B6_1_1Den : Ball := ⟨(39757482365589500963001701230393 / 10000000000000000000000000000000), (63 / 25000000000000000000000000000000)⟩
lemma B6_1_1Den_sound : B6_1_1Den.Encloses (((below (shape 6 1 1)).map (splitWeight positiveSecond tablep (shape 6 1 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 6 1 1)) B6_1_1Raw (splitWeight positiveSecond tablep (shape 6 1 1)) B6_1_1Raw_sound) (by decide +kernel)
lemma B6_1_1Den_positive : 0 < B6_1_1Den.lower := by decide +kernel
def B6_1_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => ⟨(124237509457400902736572326499 / 500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(125762490542599097263427673501 / 500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(125762490542599097263427673501 / 500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(124237509457400902736572326499 / 500000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B6_1_1Law (u : Shape) : Ball := if u ∈ below (shape 6 1 1) then B6_1_1Table u else .exact 0
lemma B6_1_1Law_check_2_1_1 : contains (.mul (B6_1_1Raw (shape 2 1 1)) (.inv B6_1_1Den)) (B6_1_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B6_1_1Law_check_3_0_1 : contains (.mul (B6_1_1Raw (shape 3 0 1)) (.inv B6_1_1Den)) (B6_1_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B6_1_1Law_check_3_1_0 : contains (.mul (B6_1_1Raw (shape 3 1 0)) (.inv B6_1_1Den)) (B6_1_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B6_1_1Law_check_4_0_0 : contains (.mul (B6_1_1Raw (shape 4 0 0)) (.inv B6_1_1Den)) (B6_1_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B6_1_1Law_check (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    contains (.mul (B6_1_1Raw u) (.inv B6_1_1Den)) (B6_1_1Table u) = true := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1Law_check_2_1_1
  · exact B6_1_1Law_check_3_0_1
  · exact B6_1_1Law_check_3_1_0
  · exact B6_1_1Law_check_4_0_0
lemma B6_1_1Law_sound (u : Shape) :
    (B6_1_1Law u).Encloses (stageBLaw (shape 6 1 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 6 1 1)
  · have h := contains_sound (Ball.mul_sound (B6_1_1Raw_sound u hu)
      (Ball.inv_sound B6_1_1Den_sound B6_1_1Den_positive)) (B6_1_1Law_check u hu)
    simpa only [B6_1_1Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B6_1_1Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B6_1_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 2, 1, 1 => (60257 / 1000000)
  | _, _, _ => 0
lemma B6_1_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 6 1 1) u = B6_1_1Binary u := by
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
def B6_1_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B6_1_1Binary u else if i = 3 then B6_1_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B6_1_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B6_1_1LittleRat u w i)
  else .exact (littleLaw (shape 6 1 1) u w i)

lemma B6_1_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B6_1_1Little u w i).Encloses (littleLaw (shape 6 1 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B6_1_1Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B6_1_1LittleRat, littleLaw, B6_1_1Binary_eq u hu]
  · simp only [B6_1_1Little, hu, ite_false]
    exact Ball.exact_sound _
def B6_1_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 2, 5 => ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(125762490542599097263427673501 / 250000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 0, 5, 2 => ⟨(2335026597000525930807493756423 / 10000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(149723592147492123923952773557 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (13 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B6_1_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((0 : Fin 6),j)) (B6_1_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((1 : Fin 6),j)) (B6_1_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((2 : Fin 6),j)) (B6_1_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((3 : Fin 6),j)) (B6_1_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((4 : Fin 6),j)) (B6_1_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 0) ((5 : Fin 6),j)) (B6_1_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((0 : Fin 6),j)) (B6_1_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((1 : Fin 6),j)) (B6_1_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((2 : Fin 6),j)) (B6_1_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((3 : Fin 6),j)) (B6_1_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((4 : Fin 6),j)) (B6_1_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 1) ((5 : Fin 6),j)) (B6_1_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((0 : Fin 6),j)) (B6_1_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((1 : Fin 6),j)) (B6_1_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((2 : Fin 6),j)) (B6_1_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((3 : Fin 6),j)) (B6_1_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((4 : Fin 6),j)) (B6_1_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B6_1_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u 2) ((5 : Fin 6),j)) (B6_1_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B6_1_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (B6_1_1Half w ij).Encloses (halfLaw (shape 6 1 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 6 1 1)) (shape 6 1 1) B6_1_1Law
      (fun u => B6_1_1Little u w) ij) (B6_1_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B6_1_1Half_check_0_0 j) (B6_1_1Half_check_0_1 j) (B6_1_1Half_check_0_2 j) (B6_1_1Half_check_0_3 j) (B6_1_1Half_check_0_4 j) (B6_1_1Half_check_0_5 j)
    · exact forall_fin6 (B6_1_1Half_check_1_0 j) (B6_1_1Half_check_1_1 j) (B6_1_1Half_check_1_2 j) (B6_1_1Half_check_1_3 j) (B6_1_1Half_check_1_4 j) (B6_1_1Half_check_1_5 j)
    · exact forall_fin6 (B6_1_1Half_check_2_0 j) (B6_1_1Half_check_2_1 j) (B6_1_1Half_check_2_2 j) (B6_1_1Half_check_2_3 j) (B6_1_1Half_check_2_4 j) (B6_1_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 6 1 1)) (shape 6 1 1)
    B6_1_1Law (fun u => (stageBLaw (shape 6 1 1) u : ℝ))
    (fun u => B6_1_1Little u w) (fun u i => (littleLaw (shape 6 1 1) u w i : ℝ))
    (fun u _ => B6_1_1Law_sound u) (fun u i => B6_1_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 6 1 1) = true := by decide +kernel
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
def B6_1_1U2_1_1D : Ball := .exact (60257 / 1000000)
lemma B6_1_1U2_1_1D_sound : B6_1_1U2_1_1D.Encloses (binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B6_1_1U2_1_1OneD : Ball := .exact (939743 / 1000000)
lemma B6_1_1U2_1_1OneD_sound : B6_1_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 6 1 1) (shape 2 1 1) = (60257 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((939743 / 1000000) : ℚ) using 1 <;> norm_num [B6_1_1U2_1_1OneD, Ball.exact]
def B6_1_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 60257, 31250⟩
def B6_1_1U2_1_1EDLog : Ball := ⟨(-70228413269685773586736117896293 / 25000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1EDLog_sound : B6_1_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B6_1_1U2_1_1D_sound) (w := B6_1_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B6_1_1U2_1_1ED : Ball := ⟨(4231753498391455659015958256077 / 25000000000000000000000000000000), (7655949647 / 100000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1ED_sound : B6_1_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B6_1_1U2_1_1D_sound) B6_1_1U2_1_1EDLog_sound) (by decide +kernel)
def B6_1_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 939743, 500000⟩
def B6_1_1U2_1_1EOneDLog : Ball := ⟨(-124297690710327487232327528573 / 2000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1EOneDLog_sound : B6_1_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B6_1_1U2_1_1OneD_sound) (w := B6_1_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B6_1_1U2_1_1EOneD : Ball := ⟨(5840394238059764191708458434189 / 100000000000000000000000000000000), (39799664151 / 100000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1EOneD_sound : B6_1_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B6_1_1U2_1_1OneD_sound) B6_1_1U2_1_1EOneDLog_sound) (by decide +kernel)
def B6_1_1U2_1_1BinaryEntropy : Ball := ⟨(26944105197525649278727705902131 / 100000000000000000000000000000000), (25003798507 / 50000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1BinaryEntropy_sound : B6_1_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 6 1 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B6_1_1U2_1_1EOneD_sound B6_1_1U2_1_1ED_sound)
    (Ball.mul_sound B6_1_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B6_1_1U2_1_1Leaf : Ball := ⟨(312189592457865916292919997050341 / 100000000000000000000000000000000), (30806741819 / 25000000000000000000000000000000)⟩
lemma B6_1_1U2_1_1Leaf_sound : B6_1_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 6 1 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1939743 / 1000000)).Encloses (2 - (binaryParameter (shape 6 1 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 6 1 1) (shape 2 1 1) = (60257 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1939743 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B6_1_1U2_1_1Mass : Ball := ⟨0, 0⟩
lemma B6_1_1U2_1_1Mass_sound : B6_1_1U2_1_1Mass.Encloses (littleMass (shape 6 1 1) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_6_1_1))
    (B6_1_1Law_sound (shape 2 1 1))) (by decide +kernel)
def B6_1_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B6_1_1U3_0_1Leaf_sound : B6_1_1U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 6 1 1) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B6_1_1U3_0_1Mass : Ball := ⟨0, 0⟩
lemma B6_1_1U3_0_1Mass_sound : B6_1_1U3_0_1Mass.Encloses (littleMass (shape 6 1 1) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_6_1_1))
    (B6_1_1Law_sound (shape 3 0 1))) (by decide +kernel)
def B6_1_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B6_1_1U3_1_0Leaf_sound : B6_1_1U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 6 1 1) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B6_1_1U3_1_0Mass : Ball := ⟨0, 0⟩
lemma B6_1_1U3_1_0Mass_sound : B6_1_1U3_1_0Mass.Encloses (littleMass (shape 6 1 1) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_6_1_1))
    (B6_1_1Law_sound (shape 3 1 0))) (by decide +kernel)
def B6_1_1U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B6_1_1U4_0_0Leaf_sound : B6_1_1U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 6 1 1) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B6_1_1U4_0_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B6_1_1U4_0_0Mass : Ball := ⟨0, 0⟩
lemma B6_1_1U4_0_0Mass_sound : B6_1_1U4_0_0Mass.Encloses (littleMass (shape 6 1 1) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_6_1_1))
    (B6_1_1Law_sound (shape 4 0 0))) (by decide +kernel)
def B6_1_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1Leaf
  | 3, 0, 1 => B6_1_1U3_0_1Leaf
  | 3, 1, 0 => B6_1_1U3_1_0Leaf
  | 4, 0, 0 => B6_1_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B6_1_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    (B6_1_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 6 1 1) u) := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1U2_1_1Leaf_sound
  · exact B6_1_1U3_0_1Leaf_sound
  · exact B6_1_1U3_1_0Leaf_sound
  · exact B6_1_1U4_0_0Leaf_sound
def B6_1_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1Mass
  | 3, 0, 1 => B6_1_1U3_0_1Mass
  | 3, 1, 0 => B6_1_1U3_1_0Mass
  | 4, 0, 0 => B6_1_1U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B6_1_1Masses_sound (u : Shape) (hu : u ∈ below (shape 6 1 1)) :
    (B6_1_1Masses u).Encloses ((fun u => (littleMass (shape 6 1 1) u : ℝ)) u) := by
  rw [B6_1_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B6_1_1U2_1_1Mass_sound
  · exact B6_1_1U3_0_1Mass_sound
  · exact B6_1_1U3_1_0Mass_sound
  · exact B6_1_1U4_0_0Mass_sound
def B6_1_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 2, 1, 1 => B6_1_1U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B6_1_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 6 1 1)).filter positive) :
    (B6_1_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 6 1 1) u)) u) := by
  have hl : (below (shape 6 1 1)).filter positive = [(shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact B6_1_1U2_1_1BinaryEntropy_sound
def B6_1_1S2 : Ball := ⟨0, 0⟩
lemma B6_1_1S2_sound : B6_1_1S2.Encloses
    (((below (shape 6 1 1)).map fun u => (littleMass (shape 6 1 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 6 1 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 6 1 1))
    (fun u => .mul (B6_1_1Masses u) (B6_1_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B6_1_1Masses_sound u hu) (B6_1_1Leaves_sound u hu))) (by decide +kernel)

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
open AllFieldTerminalRates AllFieldVolumeCertificate
def fourRateBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8Four
  | 0, 1, 7 => Z0_1_7Four
  | 0, 2, 6 => Z0_2_6Four
  | 0, 3, 5 => Z0_3_5Four
  | 0, 4, 4 => Z0_4_4Four
  | 0, 5, 3 => Z0_5_3Four
  | 0, 6, 2 => Z0_6_2Four
  | 0, 7, 1 => Z0_7_1Four
  | 0, 8, 0 => Z0_8_0Four
  | 1, 0, 7 => Z1_0_7Four
  | 1, 7, 0 => Z1_7_0Four
  | 2, 0, 6 => Z2_0_6Four
  | 2, 6, 0 => Z2_6_0Four
  | 3, 0, 5 => Z3_0_5Four
  | 3, 5, 0 => Z3_5_0Four
  | 4, 0, 4 => Z4_0_4Four
  | 4, 4, 0 => Z4_4_0Four
  | 5, 0, 3 => Z5_0_3Four
  | 5, 3, 0 => Z5_3_0Four
  | 6, 0, 2 => Z6_0_2Four
  | 6, 2, 0 => Z6_2_0Four
  | 7, 0, 1 => Z7_0_1Four
  | 7, 1, 0 => Z7_1_0Four
  | 8, 0, 0 => Z8_0_0Four
  | _, _, _ => (.exact 0)
lemma fourRateBalls_sound (t : Shape) (ht : t ∈ zeroSecond) :
    (fourRateBalls t).Encloses (AllFieldZeroLeafRates.fourRate t) := by
  rw [zeroSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8Four_sound
  · exact Z0_1_7Four_sound
  · exact Z0_2_6Four_sound
  · exact Z0_3_5Four_sound
  · exact Z0_4_4Four_sound
  · exact Z0_5_3Four_sound
  · exact Z0_6_2Four_sound
  · exact Z0_7_1Four_sound
  · exact Z0_8_0Four_sound
  · exact Z1_0_7Four_sound
  · exact Z1_7_0Four_sound
  · exact Z2_0_6Four_sound
  · exact Z2_6_0Four_sound
  · exact Z3_0_5Four_sound
  · exact Z3_5_0Four_sound
  · exact Z4_0_4Four_sound
  · exact Z4_4_0Four_sound
  · exact Z5_0_3Four_sound
  · exact Z5_3_0Four_sound
  · exact Z6_0_2Four_sound
  · exact Z6_2_0Four_sound
  · exact Z7_0_1Four_sound
  · exact Z7_1_0Four_sound
  · exact Z8_0_0Four_sound
def nativeS1Ball : Ball := ⟨(88236223598149624413852945550479 / 100000000000000000000000000000000), (32131158713 / 100000000000000000000000000000000)⟩
lemma nativeS1Ball_sound : nativeS1Ball.Encloses S1 := by
  exact contains_sound (listSumBall_sound zeroSecond
    (fun t => .mul (secondProbs t) (fourRateBalls t)) _
    (fun t ht => Ball.mul_sound (secondProbs_sound t (List.mem_filter.mp ht).1)
      (fourRateBalls_sound t ht))) (by decide +kernel)
def s2ParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6S2
  | 1, 2, 5 => B1_2_5S2
  | 1, 3, 4 => B1_3_4S2
  | 1, 4, 3 => B1_4_3S2
  | 1, 5, 2 => B1_5_2S2
  | 1, 6, 1 => B1_6_1S2
  | 2, 1, 5 => B2_1_5S2
  | 2, 2, 4 => B2_2_4S2
  | 2, 3, 3 => B2_3_3S2
  | 2, 4, 2 => B2_4_2S2
  | 2, 5, 1 => B2_5_1S2
  | 3, 1, 4 => B3_1_4S2
  | 3, 2, 3 => B3_2_3S2
  | 3, 3, 2 => B3_3_2S2
  | 3, 4, 1 => B3_4_1S2
  | 4, 1, 3 => B4_1_3S2
  | 4, 2, 2 => B4_2_2S2
  | 4, 3, 1 => B4_3_1S2
  | 5, 1, 2 => B5_1_2S2
  | 5, 2, 1 => B5_2_1S2
  | 6, 1, 1 => B6_1_1S2
  | _, _, _ => (.exact 0)
lemma s2ParentBalls_sound (t : Shape) (ht : t ∈ positiveSecond) :
    (s2ParentBalls t).Encloses (((below t).map fun u =>
      (littleMass t u : ℝ) * secondLeafRate t u).sum) := by
  rw [positiveSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_1_6S2_sound
  · exact B1_2_5S2_sound
  · exact B1_3_4S2_sound
  · exact B1_4_3S2_sound
  · exact B1_5_2S2_sound
  · exact B1_6_1S2_sound
  · exact B2_1_5S2_sound
  · exact B2_2_4S2_sound
  · exact B2_3_3S2_sound
  · exact B2_4_2S2_sound
  · exact B2_5_1S2_sound
  · exact B3_1_4S2_sound
  · exact B3_2_3S2_sound
  · exact B3_3_2S2_sound
  · exact B3_4_1S2_sound
  · exact B4_1_3S2_sound
  · exact B4_2_2S2_sound
  · exact B4_3_1S2_sound
  · exact B5_1_2S2_sound
  · exact B5_2_1S2_sound
  · exact B6_1_1S2_sound
def nativeS2Ball : Ball := ⟨(233614080284104308981345775925091 / 20000000000000000000000000000000), (7783352389 / 1562500000000000000000000000000)⟩
lemma nativeS2Ball_sound : nativeS2Ball.Encloses S2 := by
  exact contains_sound (listSumBall_sound positiveSecond s2ParentBalls _
    s2ParentBalls_sound) (by decide +kernel)
def nativeSBall : Ball := ⟨(1259477032159467636236050651212461 / 100000000000000000000000000000000), (531265093341 / 100000000000000000000000000000000)⟩
lemma nativeSBall_sound : nativeSBall.Encloses S := by
  exact contains_sound (Ball.add_sound (Ball.add_sound nativeS0_enclosed
    nativeS1Ball_sound) nativeS2Ball_sound) (by decide +kernel)

theorem native_volume_positive : 0 < S := by
  have hl := (Ball.bounds nativeSBall_sound).1
  have hp : (0 : ℝ) < nativeSBall.lower := by norm_num [nativeSBall, Ball.lower]
  exact hp.trans_le hl

theorem nativeS1_strict_bounds :
    (882362235981496244 : ℝ)/10^18 < S1 ∧ S1 < (882362235981496245 : ℝ)/10^18 := by
  have hb := Ball.bounds nativeS1Ball_sound
  norm_num [nativeS1Ball, Ball.lower, Ball.upper] at hb ⊢
  constructor <;> linarith
theorem nativeS2_strict_bounds :
    (11680704014205215449 : ℝ)/10^18 < S2 ∧ S2 < (11680704014205215450 : ℝ)/10^18 := by
  have hb := Ball.bounds nativeS2Ball_sound
  norm_num [nativeS2Ball, Ball.lower, Ball.upper] at hb ⊢
  constructor <;> linarith

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
lemma interior_fold (f : Shape × Shape → ℝ) :
    (interiorPairs.map f).sum = (positiveSecond.map (fun t =>
      (((below t).filter positive).map (fun u => f (t,u))).sum)).sum := by
  have h (xs : List Shape) :
      ((xs.flatMap (fun t => ((below t).filter positive).map (fun u => (t,u)))).map f).sum =
      (xs.map (fun t => (((below t).filter positive).map (fun u => f (t,u))).sum)).sum := by
    induction xs with
    | nil => simp
    | cons t xs ih => simp only [List.flatMap_cons, List.map_append, List.sum_append,
        List.map_map, Function.comp_def, List.map_cons, List.sum_cons, ih]
  exact h positiveSecond
def B1_1_6Ttotal : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_1_6Ttotal_sound : B1_1_6Ttotal.Encloses
    ((((below (shape 1 1 6)).filter positive).map (fun u => (littleMass (shape 1 1 6) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 1 6)).filter positive)
    B1_1_6Masses _ (fun u hu => B1_1_6Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_1_6Btotal : Ball := ⟨(10292390592644662403454216507 / 100000000000000000000000000000000), (1178709 / 12500000000000000000000000000000)⟩
lemma B1_1_6Btotal_sound : B1_1_6Btotal.Encloses
    ((((below (shape 1 1 6)).filter positive).map (fun u => (littleMass (shape 1 1 6) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 1 6) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 1 6)).filter positive)
    (fun u => .mul (B1_1_6Masses u) (.add (.mul (.exact 2) logN2) (B1_1_6Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_1_6Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_1_6Binaries_sound u hu)))) (by decide +kernel)
def B1_2_5Ttotal : Ball := ⟨(4755163798532963526151893931759 / 100000000000000000000000000000000), (57 / 100000000000000000000000000000000)⟩
lemma B1_2_5Ttotal_sound : B1_2_5Ttotal.Encloses
    ((((below (shape 1 2 5)).filter positive).map (fun u => (littleMass (shape 1 2 5) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 2 5)).filter positive)
    B1_2_5Masses _ (fun u hu => B1_2_5Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_2_5Btotal : Ball := ⟨(263770662946704051420489805631 / 4000000000000000000000000000000), (4032951479 / 100000000000000000000000000000000)⟩
lemma B1_2_5Btotal_sound : B1_2_5Btotal.Encloses
    ((((below (shape 1 2 5)).filter positive).map (fun u => (littleMass (shape 1 2 5) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 2 5) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 2 5)).filter positive)
    (fun u => .mul (B1_2_5Masses u) (.add (.mul (.exact 2) logN2) (B1_2_5Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_2_5Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_2_5Binaries_sound u hu)))) (by decide +kernel)
def B1_3_4Ttotal : Ball := ⟨(7480325224810645241814099259701 / 25000000000000000000000000000000), (151 / 50000000000000000000000000000000)⟩
lemma B1_3_4Ttotal_sound : B1_3_4Ttotal.Encloses
    ((((below (shape 1 3 4)).filter positive).map (fun u => (littleMass (shape 1 3 4) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 3 4)).filter positive)
    B1_3_4Masses _ (fun u hu => B1_3_4Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_3_4Btotal : Ball := ⟨(10623575146720639793993756588557 / 25000000000000000000000000000000), (38286699949 / 100000000000000000000000000000000)⟩
lemma B1_3_4Btotal_sound : B1_3_4Btotal.Encloses
    ((((below (shape 1 3 4)).filter positive).map (fun u => (littleMass (shape 1 3 4) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 3 4) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 3 4)).filter positive)
    (fun u => .mul (B1_3_4Masses u) (.add (.mul (.exact 2) logN2) (B1_3_4Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_3_4Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_3_4Binaries_sound u hu)))) (by decide +kernel)
def B1_4_3Ttotal : Ball := ⟨(6944605000406853487412318907203 / 50000000000000000000000000000000), (159 / 100000000000000000000000000000000)⟩
lemma B1_4_3Ttotal_sound : B1_4_3Ttotal.Encloses
    ((((below (shape 1 4 3)).filter positive).map (fun u => (littleMass (shape 1 4 3) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 4 3)).filter positive)
    B1_4_3Masses _ (fun u hu => B1_4_3Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_4_3Btotal : Ball := ⟨(19909829730949708038768839279537 / 100000000000000000000000000000000), (17824415679 / 100000000000000000000000000000000)⟩
lemma B1_4_3Btotal_sound : B1_4_3Btotal.Encloses
    ((((below (shape 1 4 3)).filter positive).map (fun u => (littleMass (shape 1 4 3) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 4 3) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 4 3)).filter positive)
    (fun u => .mul (B1_4_3Masses u) (.add (.mul (.exact 2) logN2) (B1_4_3Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_4_3Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_4_3Binaries_sound u hu)))) (by decide +kernel)
def B1_5_2Ttotal : Ball := ⟨(403356547772450802156337181231 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B1_5_2Ttotal_sound : B1_5_2Ttotal.Encloses
    ((((below (shape 1 5 2)).filter positive).map (fun u => (littleMass (shape 1 5 2) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 5 2)).filter positive)
    B1_5_2Masses _ (fun u hu => B1_5_2Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_5_2Btotal : Ball := ⟨(571743387204363003226748332669 / 100000000000000000000000000000000), (516090839 / 100000000000000000000000000000000)⟩
lemma B1_5_2Btotal_sound : B1_5_2Btotal.Encloses
    ((((below (shape 1 5 2)).filter positive).map (fun u => (littleMass (shape 1 5 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 5 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 5 2)).filter positive)
    (fun u => .mul (B1_5_2Masses u) (.add (.mul (.exact 2) logN2) (B1_5_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_5_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_5_2Binaries_sound u hu)))) (by decide +kernel)
def B1_6_1Ttotal : Ball := ⟨(77881891746725088607012689 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_6_1Ttotal_sound : B1_6_1Ttotal.Encloses
    ((((below (shape 1 6 1)).filter positive).map (fun u => (littleMass (shape 1 6 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 6 1)).filter positive)
    B1_6_1Masses _ (fun u hu => B1_6_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B1_6_1Btotal : Ball := ⟨(619013508687338257205025789 / 50000000000000000000000000000000), (1031081 / 100000000000000000000000000000000)⟩
lemma B1_6_1Btotal_sound : B1_6_1Btotal.Encloses
    ((((below (shape 1 6 1)).filter positive).map (fun u => (littleMass (shape 1 6 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 1 6 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 1 6 1)).filter positive)
    (fun u => .mul (B1_6_1Masses u) (.add (.mul (.exact 2) logN2) (B1_6_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B1_6_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B1_6_1Binaries_sound u hu)))) (by decide +kernel)
def B2_1_5Ttotal : Ball := ⟨(535927124963214472545786930867 / 25000000000000000000000000000000), (29 / 100000000000000000000000000000000)⟩
lemma B2_1_5Ttotal_sound : B2_1_5Ttotal.Encloses
    ((((below (shape 2 1 5)).filter positive).map (fun u => (littleMass (shape 2 1 5) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 1 5)).filter positive)
    B2_1_5Masses _ (fun u hu => B2_1_5Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B2_1_5Btotal : Ball := ⟨(1486547718243755829261660863071 / 50000000000000000000000000000000), (681006439 / 25000000000000000000000000000000)⟩
lemma B2_1_5Btotal_sound : B2_1_5Btotal.Encloses
    ((((below (shape 2 1 5)).filter positive).map (fun u => (littleMass (shape 2 1 5) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 1 5) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 1 5)).filter positive)
    (fun u => .mul (B2_1_5Masses u) (.add (.mul (.exact 2) logN2) (B2_1_5Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_1_5Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_1_5Binaries_sound u hu)))) (by decide +kernel)
def B2_2_4Ttotal : Ball := ⟨(20957935808074261818840608407343 / 50000000000000000000000000000000), (113 / 25000000000000000000000000000000)⟩
lemma B2_2_4Ttotal_sound : B2_2_4Ttotal.Encloses
    ((((below (shape 2 2 4)).filter positive).map (fun u => (littleMass (shape 2 2 4) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 2 4)).filter positive)
    B2_2_4Masses _ (fun u hu => B2_2_4Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B2_2_4Btotal : Ball := ⟨(61259431592020676095074322312553 / 100000000000000000000000000000000), (54088775631 / 100000000000000000000000000000000)⟩
lemma B2_2_4Btotal_sound : B2_2_4Btotal.Encloses
    ((((below (shape 2 2 4)).filter positive).map (fun u => (littleMass (shape 2 2 4) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 2 4) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 2 4)).filter positive)
    (fun u => .mul (B2_2_4Masses u) (.add (.mul (.exact 2) logN2) (B2_2_4Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_2_4Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_2_4Binaries_sound u hu)))) (by decide +kernel)
def B2_3_3Ttotal : Ball := ⟨(31969784226000540926113589340621 / 50000000000000000000000000000000), (153 / 25000000000000000000000000000000)⟩
lemma B2_3_3Ttotal_sound : B2_3_3Ttotal.Encloses
    ((((below (shape 2 3 3)).filter positive).map (fun u => (littleMass (shape 2 3 3) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 3 3)).filter positive)
    B2_3_3Masses _ (fun u hu => B2_3_3Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B2_3_3Btotal : Ball := ⟨(97155091397592012920594654935737 / 100000000000000000000000000000000), (8346926389 / 10000000000000000000000000000000)⟩
lemma B2_3_3Btotal_sound : B2_3_3Btotal.Encloses
    ((((below (shape 2 3 3)).filter positive).map (fun u => (littleMass (shape 2 3 3) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 3 3) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 3 3)).filter positive)
    (fun u => .mul (B2_3_3Masses u) (.add (.mul (.exact 2) logN2) (B2_3_3Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_3_3Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_3_3Binaries_sound u hu)))) (by decide +kernel)
def B2_4_2Ttotal : Ball := ⟨(4469292299776841640211258871473 / 50000000000000000000000000000000), (121 / 100000000000000000000000000000000)⟩
lemma B2_4_2Ttotal_sound : B2_4_2Ttotal.Encloses
    ((((below (shape 2 4 2)).filter positive).map (fun u => (littleMass (shape 2 4 2) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 4 2)).filter positive)
    B2_4_2Masses _ (fun u hu => B2_4_2Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B2_4_2Btotal : Ball := ⟨(13184565128477558357944470754293 / 100000000000000000000000000000000), (11573072161 / 100000000000000000000000000000000)⟩
lemma B2_4_2Btotal_sound : B2_4_2Btotal.Encloses
    ((((below (shape 2 4 2)).filter positive).map (fun u => (littleMass (shape 2 4 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 4 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 4 2)).filter positive)
    (fun u => .mul (B2_4_2Masses u) (.add (.mul (.exact 2) logN2) (B2_4_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_4_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_4_2Binaries_sound u hu)))) (by decide +kernel)
def B2_5_1Ttotal : Ball := ⟨(31645095109351479784189369397 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B2_5_1Ttotal_sound : B2_5_1Ttotal.Encloses
    ((((below (shape 2 5 1)).filter positive).map (fun u => (littleMass (shape 2 5 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 5 1)).filter positive)
    B2_5_1Masses _ (fun u hu => B2_5_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B2_5_1Btotal : Ball := ⟨(17929724936204266029568343331 / 20000000000000000000000000000000), (20239527 / 25000000000000000000000000000000)⟩
lemma B2_5_1Btotal_sound : B2_5_1Btotal.Encloses
    ((((below (shape 2 5 1)).filter positive).map (fun u => (littleMass (shape 2 5 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 2 5 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 2 5 1)).filter positive)
    (fun u => .mul (B2_5_1Masses u) (.add (.mul (.exact 2) logN2) (B2_5_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B2_5_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B2_5_1Binaries_sound u hu)))) (by decide +kernel)
def B3_1_4Ttotal : Ball := ⟨(907559782261289135363984197323 / 12500000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
lemma B3_1_4Ttotal_sound : B3_1_4Ttotal.Encloses
    ((((below (shape 3 1 4)).filter positive).map (fun u => (littleMass (shape 3 1 4) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 1 4)).filter positive)
    B3_1_4Masses _ (fun u hu => B3_1_4Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B3_1_4Btotal : Ball := ⟨(103669017590719797550293135229 / 1000000000000000000000000000000), (4652487271 / 50000000000000000000000000000000)⟩
lemma B3_1_4Btotal_sound : B3_1_4Btotal.Encloses
    ((((below (shape 3 1 4)).filter positive).map (fun u => (littleMass (shape 3 1 4) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 1 4) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 1 4)).filter positive)
    (fun u => .mul (B3_1_4Masses u) (.add (.mul (.exact 2) logN2) (B3_1_4Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_1_4Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_1_4Binaries_sound u hu)))) (by decide +kernel)
def B3_2_3Ttotal : Ball := ⟨(1150430302257331587531431126831 / 3125000000000000000000000000000), (79 / 20000000000000000000000000000000)⟩
lemma B3_2_3Ttotal_sound : B3_2_3Ttotal.Encloses
    ((((below (shape 3 2 3)).filter positive).map (fun u => (littleMass (shape 3 2 3) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 2 3)).filter positive)
    B3_2_3Masses _ (fun u hu => B3_2_3Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B3_2_3Btotal : Ball := ⟨(55952151483018865110434847256319 / 100000000000000000000000000000000), (12015665981 / 25000000000000000000000000000000)⟩
lemma B3_2_3Btotal_sound : B3_2_3Btotal.Encloses
    ((((below (shape 3 2 3)).filter positive).map (fun u => (littleMass (shape 3 2 3) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 2 3) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 2 3)).filter positive)
    (fun u => .mul (B3_2_3Masses u) (.add (.mul (.exact 2) logN2) (B3_2_3Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_2_3Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_2_3Binaries_sound u hu)))) (by decide +kernel)
def B3_3_2Ttotal : Ball := ⟨(8758499276755162714699464520641 / 50000000000000000000000000000000), (209 / 100000000000000000000000000000000)⟩
lemma B3_3_2Ttotal_sound : B3_3_2Ttotal.Encloses
    ((((below (shape 3 3 2)).filter positive).map (fun u => (littleMass (shape 3 3 2) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 3 2)).filter positive)
    B3_3_2Masses _ (fun u hu => B3_3_2Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B3_3_2Btotal : Ball := ⟨(13315199039969247677694047381629 / 50000000000000000000000000000000), (11435850877 / 50000000000000000000000000000000)⟩
lemma B3_3_2Btotal_sound : B3_3_2Btotal.Encloses
    ((((below (shape 3 3 2)).filter positive).map (fun u => (littleMass (shape 3 3 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 3 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 3 2)).filter positive)
    (fun u => .mul (B3_3_2Masses u) (.add (.mul (.exact 2) logN2) (B3_3_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_3_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_3_2Binaries_sound u hu)))) (by decide +kernel)
def B3_4_1Ttotal : Ball := ⟨(564009300736610125456854593833 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma B3_4_1Ttotal_sound : B3_4_1Ttotal.Encloses
    ((((below (shape 3 4 1)).filter positive).map (fun u => (littleMass (shape 3 4 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 4 1)).filter positive)
    B3_4_1Masses _ (fun u hu => B3_4_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B3_4_1Btotal : Ball := ⟨(202057355425613495053354661181 / 25000000000000000000000000000000), (144745553 / 20000000000000000000000000000000)⟩
lemma B3_4_1Btotal_sound : B3_4_1Btotal.Encloses
    ((((below (shape 3 4 1)).filter positive).map (fun u => (littleMass (shape 3 4 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 3 4 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 3 4 1)).filter positive)
    (fun u => .mul (B3_4_1Masses u) (.add (.mul (.exact 2) logN2) (B3_4_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B3_4_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B3_4_1Binaries_sound u hu)))) (by decide +kernel)
def B4_1_3Ttotal : Ball := ⟨(2233079177302622918447096359641 / 100000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
lemma B4_1_3Ttotal_sound : B4_1_3Ttotal.Encloses
    ((((below (shape 4 1 3)).filter positive).map (fun u => (littleMass (shape 4 1 3) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 1 3)).filter positive)
    B4_1_3Masses _ (fun u hu => B4_1_3Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B4_1_3Btotal : Ball := ⟨(64014500780045741535225896199 / 2000000000000000000000000000000), (2865674341 / 100000000000000000000000000000000)⟩
lemma B4_1_3Btotal_sound : B4_1_3Btotal.Encloses
    ((((below (shape 4 1 3)).filter positive).map (fun u => (littleMass (shape 4 1 3) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 4 1 3) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 1 3)).filter positive)
    (fun u => .mul (B4_1_3Masses u) (.add (.mul (.exact 2) logN2) (B4_1_3Binaries u))) _
    (fun u hu => Ball.mul_sound (B4_1_3Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B4_1_3Binaries_sound u hu)))) (by decide +kernel)
def B4_2_2Ttotal : Ball := ⟨(3767097545009369306050857272327 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
lemma B4_2_2Ttotal_sound : B4_2_2Ttotal.Encloses
    ((((below (shape 4 2 2)).filter positive).map (fun u => (littleMass (shape 4 2 2) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 2 2)).filter positive)
    B4_2_2Masses _ (fun u hu => B4_2_2Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B4_2_2Btotal : Ball := ⟨(5557262538143694155705675547867 / 100000000000000000000000000000000), (4877621647 / 100000000000000000000000000000000)⟩
lemma B4_2_2Btotal_sound : B4_2_2Btotal.Encloses
    ((((below (shape 4 2 2)).filter positive).map (fun u => (littleMass (shape 4 2 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 4 2 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 2 2)).filter positive)
    (fun u => .mul (B4_2_2Masses u) (.add (.mul (.exact 2) logN2) (B4_2_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B4_2_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B4_2_2Binaries_sound u hu)))) (by decide +kernel)
def B4_3_1Ttotal : Ball := ⟨(99503874082605676510083297769 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B4_3_1Ttotal_sound : B4_3_1Ttotal.Encloses
    ((((below (shape 4 3 1)).filter positive).map (fun u => (littleMass (shape 4 3 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 3 1)).filter positive)
    B4_3_1Masses _ (fun u hu => B4_3_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B4_3_1Btotal : Ball := ⟨(570401113257114350350352476201 / 100000000000000000000000000000000), (510740473 / 100000000000000000000000000000000)⟩
lemma B4_3_1Btotal_sound : B4_3_1Btotal.Encloses
    ((((below (shape 4 3 1)).filter positive).map (fun u => (littleMass (shape 4 3 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 4 3 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 4 3 1)).filter positive)
    (fun u => .mul (B4_3_1Masses u) (.add (.mul (.exact 2) logN2) (B4_3_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B4_3_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B4_3_1Binaries_sound u hu)))) (by decide +kernel)
def B5_1_2Ttotal : Ball := ⟨(47463286326287333481085364697 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
lemma B5_1_2Ttotal_sound : B5_1_2Ttotal.Encloses
    ((((below (shape 5 1 2)).filter positive).map (fun u => (littleMass (shape 5 1 2) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 5 1 2)).filter positive)
    B5_1_2Masses _ (fun u hu => B5_1_2Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B5_1_2Btotal : Ball := ⟨(67347402449400564801926883563 / 100000000000000000000000000000000), (60713289 / 100000000000000000000000000000000)⟩
lemma B5_1_2Btotal_sound : B5_1_2Btotal.Encloses
    ((((below (shape 5 1 2)).filter positive).map (fun u => (littleMass (shape 5 1 2) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 5 1 2) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 5 1 2)).filter positive)
    (fun u => .mul (B5_1_2Masses u) (.add (.mul (.exact 2) logN2) (B5_1_2Binaries u))) _
    (fun u hu => Ball.mul_sound (B5_1_2Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B5_1_2Binaries_sound u hu)))) (by decide +kernel)
def B5_2_1Ttotal : Ball := ⟨(408525735543637671783520101 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B5_2_1Ttotal_sound : B5_2_1Ttotal.Encloses
    ((((below (shape 5 2 1)).filter positive).map (fun u => (littleMass (shape 5 2 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 5 2 1)).filter positive)
    B5_2_1Masses _ (fun u hu => B5_2_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B5_2_1Btotal : Ball := ⟨(23171910014948039061690049419 / 100000000000000000000000000000000), (20911247 / 100000000000000000000000000000000)⟩
lemma B5_2_1Btotal_sound : B5_2_1Btotal.Encloses
    ((((below (shape 5 2 1)).filter positive).map (fun u => (littleMass (shape 5 2 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 5 2 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 5 2 1)).filter positive)
    (fun u => .mul (B5_2_1Masses u) (.add (.mul (.exact 2) logN2) (B5_2_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B5_2_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B5_2_1Binaries_sound u hu)))) (by decide +kernel)
def B6_1_1Ttotal : Ball := ⟨0, 0⟩
lemma B6_1_1Ttotal_sound : B6_1_1Ttotal.Encloses
    ((((below (shape 6 1 1)).filter positive).map (fun u => (littleMass (shape 6 1 1) u : ℝ))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 6 1 1)).filter positive)
    B6_1_1Masses _ (fun u hu => B6_1_1Masses_sound u (List.mem_filter.mp hu).1)) (by decide +kernel)
def B6_1_1Btotal : Ball := ⟨0, 0⟩
lemma B6_1_1Btotal_sound : B6_1_1Btotal.Encloses
    ((((below (shape 6 1 1)).filter positive).map (fun u => (littleMass (shape 6 1 1) u : ℝ) * (2 * Real.log 2 + binaryEntropyRate (binaryParameter (shape 6 1 1) u)))).sum) := by
  exact contains_sound (listSumBall_sound ((below (shape 6 1 1)).filter positive)
    (fun u => .mul (B6_1_1Masses u) (.add (.mul (.exact 2) logN2) (B6_1_1Binaries u))) _
    (fun u hu => Ball.mul_sound (B6_1_1Masses_sound u (List.mem_filter.mp hu).1)
      (Ball.add_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
        logN2_sound) (B6_1_1Binaries_sound u hu)))) (by decide +kernel)
def TParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6Ttotal
  | 1, 2, 5 => B1_2_5Ttotal
  | 1, 3, 4 => B1_3_4Ttotal
  | 1, 4, 3 => B1_4_3Ttotal
  | 1, 5, 2 => B1_5_2Ttotal
  | 1, 6, 1 => B1_6_1Ttotal
  | 2, 1, 5 => B2_1_5Ttotal
  | 2, 2, 4 => B2_2_4Ttotal
  | 2, 3, 3 => B2_3_3Ttotal
  | 2, 4, 2 => B2_4_2Ttotal
  | 2, 5, 1 => B2_5_1Ttotal
  | 3, 1, 4 => B3_1_4Ttotal
  | 3, 2, 3 => B3_2_3Ttotal
  | 3, 3, 2 => B3_3_2Ttotal
  | 3, 4, 1 => B3_4_1Ttotal
  | 4, 1, 3 => B4_1_3Ttotal
  | 4, 2, 2 => B4_2_2Ttotal
  | 4, 3, 1 => B4_3_1Ttotal
  | 5, 1, 2 => B5_1_2Ttotal
  | 5, 2, 1 => B5_2_1Ttotal
  | 6, 1, 1 => B6_1_1Ttotal
  | _, _, _ => (.exact 0)
lemma TParentBalls_sound (t : Shape) (ht : t ∈ positiveSecond) :
    (TParentBalls t).Encloses ((((below t).filter positive).map
      (fun u => interiorMass (t,u))).sum) := by
  rw [positiveSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_1_6Ttotal_sound
  · exact B1_2_5Ttotal_sound
  · exact B1_3_4Ttotal_sound
  · exact B1_4_3Ttotal_sound
  · exact B1_5_2Ttotal_sound
  · exact B1_6_1Ttotal_sound
  · exact B2_1_5Ttotal_sound
  · exact B2_2_4Ttotal_sound
  · exact B2_3_3Ttotal_sound
  · exact B2_4_2Ttotal_sound
  · exact B2_5_1Ttotal_sound
  · exact B3_1_4Ttotal_sound
  · exact B3_2_3Ttotal_sound
  · exact B3_3_2Ttotal_sound
  · exact B3_4_1Ttotal_sound
  · exact B4_1_3Ttotal_sound
  · exact B4_2_2Ttotal_sound
  · exact B4_3_1Ttotal_sound
  · exact B5_1_2Ttotal_sound
  · exact B5_2_1Ttotal_sound
  · exact B6_1_1Ttotal_sound
def BParentBalls (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 6 => B1_1_6Btotal
  | 1, 2, 5 => B1_2_5Btotal
  | 1, 3, 4 => B1_3_4Btotal
  | 1, 4, 3 => B1_4_3Btotal
  | 1, 5, 2 => B1_5_2Btotal
  | 1, 6, 1 => B1_6_1Btotal
  | 2, 1, 5 => B2_1_5Btotal
  | 2, 2, 4 => B2_2_4Btotal
  | 2, 3, 3 => B2_3_3Btotal
  | 2, 4, 2 => B2_4_2Btotal
  | 2, 5, 1 => B2_5_1Btotal
  | 3, 1, 4 => B3_1_4Btotal
  | 3, 2, 3 => B3_2_3Btotal
  | 3, 3, 2 => B3_3_2Btotal
  | 3, 4, 1 => B3_4_1Btotal
  | 4, 1, 3 => B4_1_3Btotal
  | 4, 2, 2 => B4_2_2Btotal
  | 4, 3, 1 => B4_3_1Btotal
  | 5, 1, 2 => B5_1_2Btotal
  | 5, 2, 1 => B5_2_1Btotal
  | 6, 1, 1 => B6_1_1Btotal
  | _, _, _ => (.exact 0)
lemma BParentBalls_sound (t : Shape) (ht : t ∈ positiveSecond) :
    (BParentBalls t).Encloses ((((below t).filter positive).map
      (fun u => (fun tu => interiorMass tu * (2 * Real.log 2 + interiorEntropy tu)) (t,u))).sum) := by
  rw [positiveSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B1_1_6Btotal_sound
  · exact B1_2_5Btotal_sound
  · exact B1_3_4Btotal_sound
  · exact B1_4_3Btotal_sound
  · exact B1_5_2Btotal_sound
  · exact B1_6_1Btotal_sound
  · exact B2_1_5Btotal_sound
  · exact B2_2_4Btotal_sound
  · exact B2_3_3Btotal_sound
  · exact B2_4_2Btotal_sound
  · exact B2_5_1Btotal_sound
  · exact B3_1_4Btotal_sound
  · exact B3_2_3Btotal_sound
  · exact B3_3_2Btotal_sound
  · exact B3_4_1Btotal_sound
  · exact B4_1_3Btotal_sound
  · exact B4_2_2Btotal_sound
  · exact B4_3_1Btotal_sound
  · exact B5_1_2Btotal_sound
  · exact B5_2_1Btotal_sound
  · exact B6_1_1Btotal_sound
def nativeTBall : Ball := ⟨(7331109571865792290176153698167 / 3125000000000000000000000000000), (637 / 25000000000000000000000000000000)⟩
lemma nativeTBall_sound : nativeTBall.Encloses nativeT := by
  rw [nativeT, interior_fold]
  exact contains_sound (listSumBall_sound positiveSecond TParentBalls _ TParentBalls_sound)
    (by decide +kernel)
def nativeBBall : Ball := ⟨(926453577659126052246485196733 / 800000000000000000000000000000), (100635147743 / 100000000000000000000000000000000)⟩
lemma nativeBBall_sound : nativeBBall.Encloses nativeB := by
  rw [nativeB, interior_fold]
  have hb := contains_sound (Ball.mul_sound
    (listSumBall_sound positiveSecond BParentBalls _ BParentBalls_sound)
    (show (Ball.exact (1/3)).Encloses (1/(3 : ℝ)) by
      convert Ball.exact_sound (1/3) using 1
      norm_num))
    (show contains (.mul (listSumBall positiveSecond BParentBalls) (.exact (1/3))) nativeBBall = true by decide +kernel)
  simpa only [one_div, div_eq_mul_inv, one_mul] using hb
def nativeHighBall : Ball := ⟨(81304606881836826911861830543749 / 50000000000000000000000000000000), (99355063329 / 100000000000000000000000000000000)⟩
lemma nativeHighBall_sound : nativeHighBall.Encloses nativeHigh := by
  exact contains_sound (Ball.mul_sound nativeTBall_sound logN2_sound) (by decide +kernel)

theorem native_denominator_gap : nativeB < nativeHigh := by
  have hb := (Ball.bounds nativeBBall_sound).2
  have ht := (Ball.bounds nativeHighBall_sound).1
  have hi : (nativeBBall.upper : ℝ) < nativeHighBall.lower := by
    norm_num [nativeBBall, nativeHighBall, Ball.lower, Ball.upper]
  exact hb.trans_lt (hi.trans_le ht)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
