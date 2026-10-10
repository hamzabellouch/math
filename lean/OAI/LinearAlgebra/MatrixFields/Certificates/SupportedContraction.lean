import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_4_3
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB1_5_2
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB2_3_3
import OAI.LinearAlgebra.MatrixFields.Certificates.LittleB2_5_1
import OAI.LinearAlgebra.MatrixFields.Certificates.NativeInterior

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B3_2_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (20837 / 200000)
  | 1, 1, 2 => (947 / 200000)
  | 1, 2, 1 => (38889 / 1000000)
  | 2, 0, 2 => (22013 / 200000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (25593 / 250000)
  | _, _, _ => 0
lemma B3_2_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 2 3) u = B3_2_3Binary u := by
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
def B3_2_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_2_3Binary u else if i = 3 then B3_2_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_2_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_2_3LittleRat u w i)
  else .exact (littleLaw (shape 3 2 3) u w i)

lemma B3_2_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_2_3Little u w i).Encloses (littleLaw (shape 3 2 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_2_3Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B3_2_3LittleRat, littleLaw, B3_2_3Binary_eq u hu]
  · simp only [B3_2_3Little, hu, ite_false]
    exact Ball.exact_sound _
def B3_2_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(660954401694675365284077503627 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(22728942148145327387716240679751 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(805051725079998623499840908311 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(22728942148145327387716240679751 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(805051725079998623499840908311 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(660954401694675365284077503627 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(7877790787272644406002286888011 / 12500000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8810343598851601529271500513163 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(86814965320621931744785142163 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8810343598851601529271500513163 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(86814965320621931744785142163 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(657827693429655515259251577397 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(2331743502850952336234925741329 / 5000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(1024737278060821122391491009313 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(2331743502850952336234925741329 / 5000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(1024737278060821122391491009313 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(657827693429655515259251577397 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_2_3Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((0 : Fin 6),j)) (B3_2_3Half 0 (0,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((1 : Fin 6),j)) (B3_2_3Half 0 (1,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((2 : Fin 6),j)) (B3_2_3Half 0 (2,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((3 : Fin 6),j)) (B3_2_3Half 0 (3,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((4 : Fin 6),j)) (B3_2_3Half 0 (4,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 0) ((5 : Fin 6),j)) (B3_2_3Half 0 (5,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((0 : Fin 6),j)) (B3_2_3Half 1 (0,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((1 : Fin 6),j)) (B3_2_3Half 1 (1,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((2 : Fin 6),j)) (B3_2_3Half 1 (2,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((3 : Fin 6),j)) (B3_2_3Half 1 (3,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((4 : Fin 6),j)) (B3_2_3Half 1 (4,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 1) ((5 : Fin 6),j)) (B3_2_3Half 1 (5,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((0 : Fin 6),j)) (B3_2_3Half 2 (0,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((1 : Fin 6),j)) (B3_2_3Half 2 (1,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((2 : Fin 6),j)) (B3_2_3Half 2 (2,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((3 : Fin 6),j)) (B3_2_3Half 2 (3,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((4 : Fin 6),j)) (B3_2_3Half 2 (4,j)) = true := by
  decide +kernel
lemma B3_2_3Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u 2) ((5 : Fin 6),j)) (B3_2_3Half 2 (5,j)) = true := by
  decide +kernel
lemma B3_2_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (B3_2_3Half w ij).Encloses (halfLaw (shape 3 2 3) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 3 2 3)) (shape 3 2 3) B3_2_3Law
      (fun u => B3_2_3Little u w) ij) (B3_2_3Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B3_2_3Half_check_0_0 j) (B3_2_3Half_check_0_1 j) (B3_2_3Half_check_0_2 j) (B3_2_3Half_check_0_3 j) (B3_2_3Half_check_0_4 j) (B3_2_3Half_check_0_5 j)
    · exact forall_fin6 (B3_2_3Half_check_1_0 j) (B3_2_3Half_check_1_1 j) (B3_2_3Half_check_1_2 j) (B3_2_3Half_check_1_3 j) (B3_2_3Half_check_1_4 j) (B3_2_3Half_check_1_5 j)
    · exact forall_fin6 (B3_2_3Half_check_2_0 j) (B3_2_3Half_check_2_1 j) (B3_2_3Half_check_2_2 j) (B3_2_3Half_check_2_3 j) (B3_2_3Half_check_2_4 j) (B3_2_3Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 3 2 3)) (shape 3 2 3)
    B3_2_3Law (fun u => (stageBLaw (shape 3 2 3) u : ℝ))
    (fun u => B3_2_3Little u w) (fun u i => (littleLaw (shape 3 2 3) u w i : ℝ))
    (fun u _ => B3_2_3Law_sound u) (fun u i => B3_2_3Little_sound u w i) ij) hcheck
  have hp : positive (shape 3 2 3) = true := by decide +kernel
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
def B5_1_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (42047 / 1000000)
  | 2, 0, 2 => (6867 / 62500)
  | 2, 1, 1 => (1993 / 500000)
  | _, _, _ => 0
lemma B5_1_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 5 1 2) u = B5_1_2Binary u := by
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
def B5_1_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B5_1_2Binary u else if i = 3 then B5_1_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B5_1_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B5_1_2LittleRat u w i)
  else .exact (littleLaw (shape 5 1 2) u w i)

lemma B5_1_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B5_1_2Little u w i).Encloses (littleLaw (shape 5 1 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B5_1_2Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B5_1_2LittleRat, littleLaw, B5_1_2Binary_eq u hu]
  · simp only [B5_1_2Little, hu, ite_false]
    exact Ball.exact_sound _
def B5_1_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 1, 5 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 2, 4 => ⟨(47206419312694013248239704463141 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 3, 4 => ⟨(519584286845206224103933984759 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 2 => ⟨(47206419312694013248239704463141 / 100000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 4, 3 => ⟨(519584286845206224103933984759 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 5, 1 => ⟨(715243539925161855344559597823 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31511980945550098409741104667589 / 50000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(16505214817994806105572714739171 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(49570105911377387117154514831 / 2500000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B5_1_2Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((0 : Fin 6),j)) (B5_1_2Half 0 (0,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((1 : Fin 6),j)) (B5_1_2Half 0 (1,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((2 : Fin 6),j)) (B5_1_2Half 0 (2,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((3 : Fin 6),j)) (B5_1_2Half 0 (3,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((4 : Fin 6),j)) (B5_1_2Half 0 (4,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 0) ((5 : Fin 6),j)) (B5_1_2Half 0 (5,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((0 : Fin 6),j)) (B5_1_2Half 1 (0,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((1 : Fin 6),j)) (B5_1_2Half 1 (1,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((2 : Fin 6),j)) (B5_1_2Half 1 (2,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((3 : Fin 6),j)) (B5_1_2Half 1 (3,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((4 : Fin 6),j)) (B5_1_2Half 1 (4,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 1) ((5 : Fin 6),j)) (B5_1_2Half 1 (5,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((0 : Fin 6),j)) (B5_1_2Half 2 (0,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((1 : Fin 6),j)) (B5_1_2Half 2 (1,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((2 : Fin 6),j)) (B5_1_2Half 2 (2,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((3 : Fin 6),j)) (B5_1_2Half 2 (3,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((4 : Fin 6),j)) (B5_1_2Half 2 (4,j)) = true := by
  decide +kernel
lemma B5_1_2Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u 2) ((5 : Fin 6),j)) (B5_1_2Half 2 (5,j)) = true := by
  decide +kernel
lemma B5_1_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (B5_1_2Half w ij).Encloses (halfLaw (shape 5 1 2) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 5 1 2)) (shape 5 1 2) B5_1_2Law
      (fun u => B5_1_2Little u w) ij) (B5_1_2Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B5_1_2Half_check_0_0 j) (B5_1_2Half_check_0_1 j) (B5_1_2Half_check_0_2 j) (B5_1_2Half_check_0_3 j) (B5_1_2Half_check_0_4 j) (B5_1_2Half_check_0_5 j)
    · exact forall_fin6 (B5_1_2Half_check_1_0 j) (B5_1_2Half_check_1_1 j) (B5_1_2Half_check_1_2 j) (B5_1_2Half_check_1_3 j) (B5_1_2Half_check_1_4 j) (B5_1_2Half_check_1_5 j)
    · exact forall_fin6 (B5_1_2Half_check_2_0 j) (B5_1_2Half_check_2_1 j) (B5_1_2Half_check_2_2 j) (B5_1_2Half_check_2_3 j) (B5_1_2Half_check_2_4 j) (B5_1_2Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 5 1 2)) (shape 5 1 2)
    B5_1_2Law (fun u => (stageBLaw (shape 5 1 2) u : ℝ))
    (fun u => B5_1_2Little u w) (fun u i => (littleLaw (shape 5 1 2) u w i : ℝ))
    (fun u _ => B5_1_2Law_sound u) (fun u i => B5_1_2Little_sound u w i) ij) hcheck
  have hp : positive (shape 5 1 2) = true := by decide +kernel
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
def halfTable (s : Shape) (w : Fin 3) (ij : PairSlot) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => Z0_0_8Half w ij
  | 0, 1, 7 => Z0_1_7Half w ij
  | 0, 2, 6 => Z0_2_6Half w ij
  | 0, 3, 5 => Z0_3_5Half w ij
  | 0, 4, 4 => Z0_4_4Half w ij
  | 0, 5, 3 => Z0_5_3Half w ij
  | 0, 6, 2 => Z0_6_2Half w ij
  | 0, 7, 1 => Z0_7_1Half w ij
  | 0, 8, 0 => Z0_8_0Half w ij
  | 1, 0, 7 => Z1_0_7Half w ij
  | 1, 1, 6 => B1_1_6Half w ij
  | 1, 2, 5 => B1_2_5Half w ij
  | 1, 3, 4 => B1_3_4Half w ij
  | 1, 4, 3 => B1_4_3Half w ij
  | 1, 5, 2 => B1_5_2Half w ij
  | 1, 6, 1 => B1_6_1Half w ij
  | 1, 7, 0 => Z1_7_0Half w ij
  | 2, 0, 6 => Z2_0_6Half w ij
  | 2, 1, 5 => B2_1_5Half w ij
  | 2, 2, 4 => B2_2_4Half w ij
  | 2, 3, 3 => B2_3_3Half w ij
  | 2, 4, 2 => B2_4_2Half w ij
  | 2, 5, 1 => B2_5_1Half w ij
  | 2, 6, 0 => Z2_6_0Half w ij
  | 3, 0, 5 => Z3_0_5Half w ij
  | 3, 1, 4 => B3_1_4Half w ij
  | 3, 2, 3 => B3_2_3Half w ij
  | 3, 3, 2 => B3_3_2Half w ij
  | 3, 4, 1 => B3_4_1Half w ij
  | 3, 5, 0 => Z3_5_0Half w ij
  | 4, 0, 4 => Z4_0_4Half w ij
  | 4, 1, 3 => B4_1_3Half w ij
  | 4, 2, 2 => B4_2_2Half w ij
  | 4, 3, 1 => B4_3_1Half w ij
  | 4, 4, 0 => Z4_4_0Half w ij
  | 5, 0, 3 => Z5_0_3Half w ij
  | 5, 1, 2 => B5_1_2Half w ij
  | 5, 2, 1 => B5_2_1Half w ij
  | 5, 3, 0 => Z5_3_0Half w ij
  | 6, 0, 2 => Z6_0_2Half w ij
  | 6, 1, 1 => B6_1_1Half w ij
  | 6, 2, 0 => Z6_2_0Half w ij
  | 7, 0, 1 => Z7_0_1Half w ij
  | 7, 1, 0 => Z7_1_0Half w ij
  | 8, 0, 0 => Z8_0_0Half w ij
  | _, _, _ => (.exact 0)
lemma halfTable_sound (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3) (ij : PairSlot) :
    (halfTable t w ij).Encloses (halfLaw t w ij : ℝ) := by
  rw [allSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Z0_0_8Half_sound w ij
  · exact Z0_1_7Half_sound w ij
  · exact Z0_2_6Half_sound w ij
  · exact Z0_3_5Half_sound w ij
  · exact Z0_4_4Half_sound w ij
  · exact Z0_5_3Half_sound w ij
  · exact Z0_6_2Half_sound w ij
  · exact Z0_7_1Half_sound w ij
  · exact Z0_8_0Half_sound w ij
  · exact Z1_0_7Half_sound w ij
  · exact B1_1_6Half_sound w ij
  · exact B1_2_5Half_sound w ij
  · exact B1_3_4Half_sound w ij
  · exact B1_4_3Half_sound w ij
  · exact B1_5_2Half_sound w ij
  · exact B1_6_1Half_sound w ij
  · exact Z1_7_0Half_sound w ij
  · exact Z2_0_6Half_sound w ij
  · exact B2_1_5Half_sound w ij
  · exact B2_2_4Half_sound w ij
  · exact B2_3_3Half_sound w ij
  · exact B2_4_2Half_sound w ij
  · exact B2_5_1Half_sound w ij
  · exact Z2_6_0Half_sound w ij
  · exact Z3_0_5Half_sound w ij
  · exact B3_1_4Half_sound w ij
  · exact B3_2_3Half_sound w ij
  · exact B3_3_2Half_sound w ij
  · exact B3_4_1Half_sound w ij
  · exact Z3_5_0Half_sound w ij
  · exact Z4_0_4Half_sound w ij
  · exact B4_1_3Half_sound w ij
  · exact B4_2_2Half_sound w ij
  · exact B4_3_1Half_sound w ij
  · exact Z4_4_0Half_sound w ij
  · exact Z5_0_3Half_sound w ij
  · exact B5_1_2Half_sound w ij
  · exact B5_2_1Half_sound w ij
  · exact Z5_3_0Half_sound w ij
  · exact Z6_0_2Half_sound w ij
  · exact B6_1_1Half_sound w ij
  · exact Z6_2_0Half_sound w ij
  · exact Z7_0_1Half_sound w ij
  · exact Z7_1_0Half_sound w ij
  · exact Z8_0_0Half_sound w ij
def halfProbs (t : Shape) (w : Fin 3) (ij : PairSlot) : Ball :=
  if t ∈ shapes 8 then halfTable t w ij else .exact (halfLaw t w ij)
lemma halfProbs_sound (t : Shape) (w : Fin 3) (ij : PairSlot) :
    (halfProbs t w ij).Encloses (halfLaw t w ij : ℝ) := by
  by_cases ht : t ∈ shapes 8
  · simpa only [halfProbs, ht, ite_true] using halfTable_sound t ht w ij
  · simp only [halfProbs, ht, ite_false]
    exact Ball.exact_sound _

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

def pairDegree (ij : PairSlot) : ℕ := statisticWeight ij.1 + statisticWeight ij.2

lemma halfTable_degree_zero_0 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 0 → halfTable t 0 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_1 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 1 → halfTable t 1 ij = .exact 0 := by
  decide +kernel
lemma halfTable_degree_zero_2 : ∀ t ∈ shapes 8, ∀ ij : PairSlot,
    pairDegree ij ≠ t 2 → halfTable t 2 ij = .exact 0 := by
  decide +kernel

lemma halfTable_degree_zero (t : Shape) (ht : t ∈ shapes 8) (w : Fin 3)
    (ij : PairSlot) (h : pairDegree ij ≠ t w) : halfTable t w ij = .exact 0 := by
  fin_cases w
  · exact halfTable_degree_zero_0 t ht ij h
  · exact halfTable_degree_zero_1 t ht ij h
  · exact halfTable_degree_zero_2 t ht ij h

lemma listSumBall_eq_zero {A : Type*} (xs : List A) (b : A → Ball)
    (h : ∀ x ∈ xs, b x = .exact 0) : listSumBall xs b = .exact 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change Ball.add (b x) (listSumBall xs b) = .exact 0
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
    decide +kernel

lemma stageAPairBall_zero (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot)
    (h : pairDegree ij.1 + pairDegree ij.2 ≠ s w) :
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij = .exact 0 := by
  apply listSumBall_eq_zero
  intro u hu
  have hc := stageA_support_complement s hs u hu
  by_cases hl : pairDegree ij.1 = u w
  · have hr : pairDegree ij.2 ≠ (complement s u) w := by
      simp only [complement]
      have hu_le := hc.2 w
      omega
    have hz := halfTable_degree_zero (complement s u)
      (stageA_children_size s hs _ hc.1) w ij.2 hr
    simp only [sparseTripleBall, hz, or_true, ite_true]
  · have hz := halfTable_degree_zero u (stageA_children_size s hs u hu) w ij.1 hl
    simp only [sparseTripleBall, hz, true_or, ite_true]

def stageAPairBall (s : Shape) (bs : Shape → Ball) (w : Fin 3)
    (ij : PairSlot × PairSlot) : Ball :=
  if pairDegree ij.1 + pairDegree ij.2 = s w then
    sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij
  else .exact 0

lemma stageAPairBall_eq (s : Shape) (hs : s ∈ positiveInitial) (bs : Shape → Ball)
    (w : Fin 3) (ij : PairSlot × PairSlot) :
    stageAPairBall s bs w ij =
      sparsePairLawBall (below s) s bs (fun u => halfTable u w) ij := by
  unfold stageAPairBall
  split_ifs with h
  · rfl
  · exact (stageAPairBall_zero s hs bs w ij h).symm

lemma stageAPairBall_sound (s : Shape) (hs : s ∈ positiveInitial)
    (bs : Shape → Ball) (p : Shape → ℝ)
    (hp : ∀ u ∈ below s, (bs u).Encloses (p u)) (w : Fin 3) (ij : PairSlot × PairSlot) :
    (stageAPairBall s bs w ij).Encloses
      (pairLaw (below s) s p (fun u a => (halfLaw u w a : ℝ)) ij) := by
  rw [stageAPairBall_eq s hs]
  exact sparsePairLawBall_sound_on (below s) s bs p (fun u => halfTable u w)
    (fun u a => (halfLaw u w a : ℝ)) hp
    (fun u hu a => halfTable_sound u (stageA_children_size s hs u hu) w a)
    (fun u hu a => halfTable_sound (complement s u)
      (stageA_children_size s hs _ (stageA_support_complement s hs u hu).1) w a) ij

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
