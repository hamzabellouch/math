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
def B2_3_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (55041 / 500000)
  | 1, 1, 2 => (573 / 125000)
  | 1, 2, 1 => (1687 / 40000)
  | 2, 0, 2 => (104091 / 1000000)
  | 2, 1, 1 => (19419 / 500000)
  | 2, 2, 0 => (102383 / 1000000)
  | _, _, _ => 0
lemma B2_3_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 2 3 3) u = B2_3_3Binary u := by
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
def B2_3_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_3_3Binary u else if i = 3 then B2_3_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_3_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_3_3LittleRat u w i)
  else .exact (littleLaw (shape 2 3 3) u w i)

lemma B2_3_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B2_3_3Little u w i).Encloses (littleLaw (shape 2 3 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B2_3_3Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B2_3_3LittleRat, littleLaw, B2_3_3Binary_eq u hu]
  · simp only [B2_3_3Little, hu, ite_false]
    exact Ball.exact_sound _
def B2_3_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8811526653339407816212002016803 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(173415754401812546184280998437 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(31509867921312121636654590974209 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8811526653339407816212002016803 / 50000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(173415754401812546184280998437 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(45457112926707713088575555921683 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(3220843048653859968603717052973 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(45457112926707713088575555921683 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(3220843048653859968603717052973 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(20656937884975420981573859771 / 1562500000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(20656937884975420981573859771 / 1562500000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(46643247536423404746233613795319 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(2045463446821258958742105416673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(46643247536423404746233613795319 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(2045463446821258958742105416673 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(163911127094417036878035098501 / 12500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_3_3Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((0 : Fin 6),j)) (B2_3_3Half 0 (0,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((1 : Fin 6),j)) (B2_3_3Half 0 (1,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((2 : Fin 6),j)) (B2_3_3Half 0 (2,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((3 : Fin 6),j)) (B2_3_3Half 0 (3,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((4 : Fin 6),j)) (B2_3_3Half 0 (4,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 0) ((5 : Fin 6),j)) (B2_3_3Half 0 (5,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((0 : Fin 6),j)) (B2_3_3Half 1 (0,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((1 : Fin 6),j)) (B2_3_3Half 1 (1,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((2 : Fin 6),j)) (B2_3_3Half 1 (2,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((3 : Fin 6),j)) (B2_3_3Half 1 (3,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((4 : Fin 6),j)) (B2_3_3Half 1 (4,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 1) ((5 : Fin 6),j)) (B2_3_3Half 1 (5,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((0 : Fin 6),j)) (B2_3_3Half 2 (0,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((1 : Fin 6),j)) (B2_3_3Half 2 (1,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((2 : Fin 6),j)) (B2_3_3Half 2 (2,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((3 : Fin 6),j)) (B2_3_3Half 2 (3,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((4 : Fin 6),j)) (B2_3_3Half 2 (4,j)) = true := by
  decide +kernel
lemma B2_3_3Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u 2) ((5 : Fin 6),j)) (B2_3_3Half 2 (5,j)) = true := by
  decide +kernel
lemma B2_3_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (B2_3_3Half w ij).Encloses (halfLaw (shape 2 3 3) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 2 3 3)) (shape 2 3 3) B2_3_3Law
      (fun u => B2_3_3Little u w) ij) (B2_3_3Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B2_3_3Half_check_0_0 j) (B2_3_3Half_check_0_1 j) (B2_3_3Half_check_0_2 j) (B2_3_3Half_check_0_3 j) (B2_3_3Half_check_0_4 j) (B2_3_3Half_check_0_5 j)
    · exact forall_fin6 (B2_3_3Half_check_1_0 j) (B2_3_3Half_check_1_1 j) (B2_3_3Half_check_1_2 j) (B2_3_3Half_check_1_3 j) (B2_3_3Half_check_1_4 j) (B2_3_3Half_check_1_5 j)
    · exact forall_fin6 (B2_3_3Half_check_2_0 j) (B2_3_3Half_check_2_1 j) (B2_3_3Half_check_2_2 j) (B2_3_3Half_check_2_3 j) (B2_3_3Half_check_2_4 j) (B2_3_3Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 2 3 3)) (shape 2 3 3)
    B2_3_3Law (fun u => (stageBLaw (shape 2 3 3) u : ℝ))
    (fun u => B2_3_3Little u w) (fun u i => (littleLaw (shape 2 3 3) u w i : ℝ))
    (fun u _ => B2_3_3Law_sound u) (fun u i => B2_3_3Little_sound u w i) ij) hcheck
  have hp : positive (shape 2 3 3) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
