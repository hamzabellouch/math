import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_5_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (109933 / 1000000)
  | 1, 1, 2 => (10523 / 250000)
  | 1, 2, 1 => (3747 / 1000000)
  | _, _, _ => 0
lemma B1_5_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 5 2) u = B1_5_2Binary u := by
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
def B1_5_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_5_2Binary u else if i = 3 then B1_5_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_5_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_5_2LittleRat u w i)
  else .exact (littleLaw (shape 1 5 2) u w i)

lemma B1_5_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_5_2Little u w i).Encloses (littleLaw (shape 1 5 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_5_2Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_5_2LittleRat, littleLaw, B1_5_2Binary_eq u hu]
  · simp only [B1_5_2Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_5_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (51 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (51 / 100000000000000000000000000000000)⟩
  | 1, 2, 4 => ⟨(944296764805115665482085327337 / 2000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(518340583815889402541057141607 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 4, 2 => ⟨(944296764805115665482085327337 / 2000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(518340583815889402541057141607 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 5, 1 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 5 => ⟨(355899712240329557865752533361 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(2064129144151554264168571077709 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(1985286600756920686097122080759 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31501680246030645200554309297569 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(2064129144151554264168571077709 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(1985286600756920686097122080759 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_5_2Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((0 : Fin 6),j)) (B1_5_2Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((1 : Fin 6),j)) (B1_5_2Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((2 : Fin 6),j)) (B1_5_2Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((3 : Fin 6),j)) (B1_5_2Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((4 : Fin 6),j)) (B1_5_2Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 0) ((5 : Fin 6),j)) (B1_5_2Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((0 : Fin 6),j)) (B1_5_2Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((1 : Fin 6),j)) (B1_5_2Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((2 : Fin 6),j)) (B1_5_2Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((3 : Fin 6),j)) (B1_5_2Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((4 : Fin 6),j)) (B1_5_2Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 1) ((5 : Fin 6),j)) (B1_5_2Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((0 : Fin 6),j)) (B1_5_2Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((1 : Fin 6),j)) (B1_5_2Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((2 : Fin 6),j)) (B1_5_2Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((3 : Fin 6),j)) (B1_5_2Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((4 : Fin 6),j)) (B1_5_2Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_5_2Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u 2) ((5 : Fin 6),j)) (B1_5_2Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_5_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_5_2Half w ij).Encloses (halfLaw (shape 1 5 2) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 5 2)) (shape 1 5 2) B1_5_2Law
      (fun u => B1_5_2Little u w) ij) (B1_5_2Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_5_2Half_check_0_0 j) (B1_5_2Half_check_0_1 j) (B1_5_2Half_check_0_2 j) (B1_5_2Half_check_0_3 j) (B1_5_2Half_check_0_4 j) (B1_5_2Half_check_0_5 j)
    · exact forall_fin6 (B1_5_2Half_check_1_0 j) (B1_5_2Half_check_1_1 j) (B1_5_2Half_check_1_2 j) (B1_5_2Half_check_1_3 j) (B1_5_2Half_check_1_4 j) (B1_5_2Half_check_1_5 j)
    · exact forall_fin6 (B1_5_2Half_check_2_0 j) (B1_5_2Half_check_2_1 j) (B1_5_2Half_check_2_2 j) (B1_5_2Half_check_2_3 j) (B1_5_2Half_check_2_4 j) (B1_5_2Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 5 2)) (shape 1 5 2)
    B1_5_2Law (fun u => (stageBLaw (shape 1 5 2) u : ℝ))
    (fun u => B1_5_2Little u w) (fun u i => (littleLaw (shape 1 5 2) u w i : ℝ))
    (fun u _ => B1_5_2Law_sound u) (fun u i => B1_5_2Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 5 2) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
