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
def B1_4_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (23901 / 250000)
  | 1, 1, 2 => (41743 / 1000000)
  | 1, 2, 1 => (3057 / 1000000)
  | _, _, _ => 0
lemma B1_4_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 1 4 3) u = B1_4_3Binary u := by
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
def B1_4_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B1_4_3Binary u else if i = 3 then B1_4_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B1_4_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B1_4_3LittleRat u w i)
  else .exact (littleLaw (shape 1 4 3) u w i)

lemma B1_4_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B1_4_3Little u w i).Encloses (littleLaw (shape 1 4 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B1_4_3Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B1_4_3LittleRat, littleLaw, B1_4_3Binary_eq u hu]
  · simp only [B1_4_3Little, hu, ite_false]
    exact Ball.exact_sound _
def B1_4_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 0, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(1966519024111033745643559687113 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(18979543218321732038291109031929 / 25000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(4129064322164561216004098570321 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(4129064322164561216004098570321 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(3076084781593046714415474453 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(1966519024111033745643559687113 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(33468805621467537981782719557 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(1305555413502823769500199931759 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(44394219774093180020469714786281 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(107505620310099905250752132049 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(44394219774093180020469714786281 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(107505620310099905250752132049 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(1305555413502823769500199931759 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B1_4_3Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((0 : Fin 6),j)) (B1_4_3Half 0 (0,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((1 : Fin 6),j)) (B1_4_3Half 0 (1,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((2 : Fin 6),j)) (B1_4_3Half 0 (2,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((3 : Fin 6),j)) (B1_4_3Half 0 (3,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((4 : Fin 6),j)) (B1_4_3Half 0 (4,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 0) ((5 : Fin 6),j)) (B1_4_3Half 0 (5,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((0 : Fin 6),j)) (B1_4_3Half 1 (0,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((1 : Fin 6),j)) (B1_4_3Half 1 (1,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((2 : Fin 6),j)) (B1_4_3Half 1 (2,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((3 : Fin 6),j)) (B1_4_3Half 1 (3,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((4 : Fin 6),j)) (B1_4_3Half 1 (4,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 1) ((5 : Fin 6),j)) (B1_4_3Half 1 (5,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((0 : Fin 6),j)) (B1_4_3Half 2 (0,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((1 : Fin 6),j)) (B1_4_3Half 2 (1,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((2 : Fin 6),j)) (B1_4_3Half 2 (2,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((3 : Fin 6),j)) (B1_4_3Half 2 (3,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((4 : Fin 6),j)) (B1_4_3Half 2 (4,j)) = true := by
  decide +kernel
lemma B1_4_3Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u 2) ((5 : Fin 6),j)) (B1_4_3Half 2 (5,j)) = true := by
  decide +kernel
lemma B1_4_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (B1_4_3Half w ij).Encloses (halfLaw (shape 1 4 3) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 1 4 3)) (shape 1 4 3) B1_4_3Law
      (fun u => B1_4_3Little u w) ij) (B1_4_3Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B1_4_3Half_check_0_0 j) (B1_4_3Half_check_0_1 j) (B1_4_3Half_check_0_2 j) (B1_4_3Half_check_0_3 j) (B1_4_3Half_check_0_4 j) (B1_4_3Half_check_0_5 j)
    · exact forall_fin6 (B1_4_3Half_check_1_0 j) (B1_4_3Half_check_1_1 j) (B1_4_3Half_check_1_2 j) (B1_4_3Half_check_1_3 j) (B1_4_3Half_check_1_4 j) (B1_4_3Half_check_1_5 j)
    · exact forall_fin6 (B1_4_3Half_check_2_0 j) (B1_4_3Half_check_2_1 j) (B1_4_3Half_check_2_2 j) (B1_4_3Half_check_2_3 j) (B1_4_3Half_check_2_4 j) (B1_4_3Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 1 4 3)) (shape 1 4 3)
    B1_4_3Law (fun u => (stageBLaw (shape 1 4 3) u : ℝ))
    (fun u => B1_4_3Little u w) (fun u i => (littleLaw (shape 1 4 3) u w i : ℝ))
    (fun u _ => B1_4_3Law_sound u) (fun u i => B1_4_3Little_sound u w i) ij) hcheck
  have hp : positive (shape 1 4 3) = true := by decide +kernel
  simpa only [halfLaw, hp, ite_true, pairLaw, positiveHalfLaw, Rat.cast_list_sum,
    List.map_map, Function.comp_def, Rat.cast_mul] using h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
