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
lemma B2_1_5_below : below (shape 2 1 5) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1)] := by decide +kernel
def B2_1_5Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(143477508024585653583089862491 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(28769707349155561859531613298219 / 50000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨1, 0⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 2, 0, 2 => ⟨(28769707349155561859531613298219 / 50000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(143477508024585653583089862491 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_1_5Raw_0_0_4 : (B2_1_5Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 0 0 4)
    (-5527) (0) (-53009) w170 w195 w34
    (by decide +kernel) w170_sound w195_sound w34_sound) (by decide +kernel)
lemma B2_1_5Raw_0_1_3 : (B2_1_5Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 0 1 3)
    (-5527) (0) (0) w170 w195 w195
    (by decide +kernel) w170_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_1_5Raw_1_0_3 : (B2_1_5Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 1 0 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_1_5Raw_1_1_2 : (B2_1_5Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_1_5Raw_2_0_2 : (B2_1_5Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 2 0 2)
    (-5527) (0) (0) w170 w195 w195
    (by decide +kernel) w170_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_1_5Raw_2_1_1 : (B2_1_5Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 1 5) (shape 2 1 1)
    (-5527) (0) (-53009) w170 w195 w34
    (by decide +kernel) w170_sound w195_sound w34_sound) (by decide +kernel)
lemma B2_1_5Raw_sound (u : Shape) (hu : u ∈ below (shape 2 1 5)) :
    (B2_1_5Raw u).Encloses (splitWeight positiveSecond tablep (shape 2 1 5) u : ℝ) := by
  rw [B2_1_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_1_5Raw_0_0_4
  · exact B2_1_5Raw_0_1_3
  · exact B2_1_5Raw_1_0_3
  · exact B2_1_5Raw_1_1_2
  · exact B2_1_5Raw_2_0_2
  · exact B2_1_5Raw_2_1_1
def B2_1_5Den : Ball := ⟨(7891318485718014751311470316071 / 2500000000000000000000000000000), (3 / 2000000000000000000000000000000)⟩
lemma B2_1_5Den_sound : B2_1_5Den.Encloses (((below (shape 2 1 5)).map (splitWeight positiveSecond tablep (shape 2 1 5))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 1 5)) B2_1_5Raw (splitWeight positiveSecond tablep (shape 2 1 5)) B2_1_5Raw_sound) (by decide +kernel)
lemma B2_1_5Den_positive : 0 < B2_1_5Den.lower := by decide +kernel
def B2_1_5Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(9114353767758831519889785991183 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(7920096003363024098980124774863 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(7920096003363024098980124774863 / 25000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(9114353767758831519889785991183 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_1_5Law (u : Shape) : Ball := if u ∈ below (shape 2 1 5) then B2_1_5Table u else .exact 0
lemma B2_1_5Law_check_0_0_4 : contains (.mul (B2_1_5Raw (shape 0 0 4)) (.inv B2_1_5Den)) (B2_1_5Table (shape 0 0 4)) = true := by decide +kernel
lemma B2_1_5Law_check_0_1_3 : contains (.mul (B2_1_5Raw (shape 0 1 3)) (.inv B2_1_5Den)) (B2_1_5Table (shape 0 1 3)) = true := by decide +kernel
lemma B2_1_5Law_check_1_0_3 : contains (.mul (B2_1_5Raw (shape 1 0 3)) (.inv B2_1_5Den)) (B2_1_5Table (shape 1 0 3)) = true := by decide +kernel
lemma B2_1_5Law_check_1_1_2 : contains (.mul (B2_1_5Raw (shape 1 1 2)) (.inv B2_1_5Den)) (B2_1_5Table (shape 1 1 2)) = true := by decide +kernel
lemma B2_1_5Law_check_2_0_2 : contains (.mul (B2_1_5Raw (shape 2 0 2)) (.inv B2_1_5Den)) (B2_1_5Table (shape 2 0 2)) = true := by decide +kernel
lemma B2_1_5Law_check_2_1_1 : contains (.mul (B2_1_5Raw (shape 2 1 1)) (.inv B2_1_5Den)) (B2_1_5Table (shape 2 1 1)) = true := by decide +kernel
lemma B2_1_5Law_check (u : Shape) (hu : u ∈ below (shape 2 1 5)) :
    contains (.mul (B2_1_5Raw u) (.inv B2_1_5Den)) (B2_1_5Table u) = true := by
  rw [B2_1_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_1_5Law_check_0_0_4
  · exact B2_1_5Law_check_0_1_3
  · exact B2_1_5Law_check_1_0_3
  · exact B2_1_5Law_check_1_1_2
  · exact B2_1_5Law_check_2_0_2
  · exact B2_1_5Law_check_2_1_1
lemma B2_1_5Law_sound (u : Shape) :
    (B2_1_5Law u).Encloses (stageBLaw (shape 2 1 5) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 1 5)
  · have h := contains_sound (Ball.mul_sound (B2_1_5Raw_sound u hu)
      (Ball.inv_sound B2_1_5Den_sound B2_1_5Den_positive)) (B2_1_5Law_check u hu)
    simpa only [B2_1_5Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B2_1_5Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B2_1_5Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (1 / 1000000)
  | 2, 0, 2 => (50311 / 500000)
  | 2, 1, 1 => (21083 / 500000)
  | _, _, _ => 0
lemma B2_1_5Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 2 1 5) u = B2_1_5Binary u := by
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
def B2_1_5LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_1_5Binary u else if i = 3 then B2_1_5Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_1_5Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_1_5LittleRat u w i)
  else .exact (littleLaw (shape 2 1 5) u w i)

lemma B2_1_5Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B2_1_5Little u w i).Encloses (littleLaw (shape 2 1 5) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B2_1_5Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B2_1_5LittleRat, littleLaw, B2_1_5Binary_eq u hu]
  · simp only [B2_1_5Little, hu, ite_false]
    exact Ball.exact_sound _
def B2_1_5Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8240786865581452095028265002887 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(919021127692499707011485447387 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(7920096003363024098980124774863 / 12500000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8240786865581452095028265002887 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(919021127692499707011485447387 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (49 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (49 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(48074850858946887693214975069309 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 4, 3 => ⟨(1834240690022871742485096012509 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(48074850858946887693214975069309 / 100000000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 3, 4 => ⟨(1834240690022871742485096012509 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(45454225515120282149964459091 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_1_5Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((0 : Fin 6),j)) (B2_1_5Half 0 (0,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((1 : Fin 6),j)) (B2_1_5Half 0 (1,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((2 : Fin 6),j)) (B2_1_5Half 0 (2,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((3 : Fin 6),j)) (B2_1_5Half 0 (3,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((4 : Fin 6),j)) (B2_1_5Half 0 (4,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 0) ((5 : Fin 6),j)) (B2_1_5Half 0 (5,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((0 : Fin 6),j)) (B2_1_5Half 1 (0,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((1 : Fin 6),j)) (B2_1_5Half 1 (1,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((2 : Fin 6),j)) (B2_1_5Half 1 (2,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((3 : Fin 6),j)) (B2_1_5Half 1 (3,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((4 : Fin 6),j)) (B2_1_5Half 1 (4,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 1) ((5 : Fin 6),j)) (B2_1_5Half 1 (5,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((0 : Fin 6),j)) (B2_1_5Half 2 (0,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((1 : Fin 6),j)) (B2_1_5Half 2 (1,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((2 : Fin 6),j)) (B2_1_5Half 2 (2,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((3 : Fin 6),j)) (B2_1_5Half 2 (3,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((4 : Fin 6),j)) (B2_1_5Half 2 (4,j)) = true := by
  decide +kernel
lemma B2_1_5Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u 2) ((5 : Fin 6),j)) (B2_1_5Half 2 (5,j)) = true := by
  decide +kernel
lemma B2_1_5Half_sound (w : Fin 3) (ij : PairSlot) :
    (B2_1_5Half w ij).Encloses (halfLaw (shape 2 1 5) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 2 1 5)) (shape 2 1 5) B2_1_5Law
      (fun u => B2_1_5Little u w) ij) (B2_1_5Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B2_1_5Half_check_0_0 j) (B2_1_5Half_check_0_1 j) (B2_1_5Half_check_0_2 j) (B2_1_5Half_check_0_3 j) (B2_1_5Half_check_0_4 j) (B2_1_5Half_check_0_5 j)
    · exact forall_fin6 (B2_1_5Half_check_1_0 j) (B2_1_5Half_check_1_1 j) (B2_1_5Half_check_1_2 j) (B2_1_5Half_check_1_3 j) (B2_1_5Half_check_1_4 j) (B2_1_5Half_check_1_5 j)
    · exact forall_fin6 (B2_1_5Half_check_2_0 j) (B2_1_5Half_check_2_1 j) (B2_1_5Half_check_2_2 j) (B2_1_5Half_check_2_3 j) (B2_1_5Half_check_2_4 j) (B2_1_5Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 2 1 5)) (shape 2 1 5)
    B2_1_5Law (fun u => (stageBLaw (shape 2 1 5) u : ℝ))
    (fun u => B2_1_5Little u w) (fun u i => (littleLaw (shape 2 1 5) u w i : ℝ))
    (fun u _ => B2_1_5Law_sound u) (fun u i => B2_1_5Little_sound u w i) ij) hcheck
  have hp : positive (shape 2 1 5) = true := by decide +kernel
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
def B2_1_5U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B2_1_5U0_0_4Leaf_sound : B2_1_5U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B2_1_5U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B2_1_5U0_0_4Mass : Ball := ⟨(11980229688179108495838363 / 195312500000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_1_5U0_0_4Mass_sound : B2_1_5U0_0_4Mass.Encloses (littleMass (shape 2 1 5) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 0 0 4))) (by decide +kernel)
def B2_1_5U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_1_5U0_1_3Leaf_sound : B2_1_5U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_1_5U0_1_3Mass : Ball := ⟨(153743490797966165833014949619 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma B2_1_5U0_1_3Mass_sound : B2_1_5U0_1_3Mass.Encloses (littleMass (shape 2 1 5) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 0 1 3))) (by decide +kernel)
def B2_1_5U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_1_5U1_0_3Leaf_sound : B2_1_5U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_1_5U1_0_3Mass : Ball := ⟨(534393655563127546658319620403 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
lemma B2_1_5U1_0_3Mass_sound : B2_1_5U1_0_3Mass.Encloses (littleMass (shape 2 1 5) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 1 0 3))) (by decide +kernel)
def B2_1_5U1_1_2D : Ball := .exact (1 / 1000000)
lemma B2_1_5U1_1_2D_sound : B2_1_5U1_1_2D.Encloses (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_1_5U1_1_2OneD : Ball := .exact (999999 / 1000000)
lemma B2_1_5U1_1_2OneD_sound : B2_1_5U1_1_2OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 1 1 2) = (1 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((999999 / 1000000) : ℚ) using 1 <;> norm_num [B2_1_5U1_1_2OneD, Ball.exact]
def B2_1_5U1_1_2EDLogWitness : LogWitness := ⟨-20, 16384, 15625⟩
def B2_1_5U1_1_2EDLog : Ball := ⟨(-276310211159285482082158898180173 / 20000000000000000000000000000000), (222346148671 / 50000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2EDLog_sound : B2_1_5U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U1_1_2D_sound) (w := B2_1_5U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U1_1_2ED : Ball := ⟨(1381551055796427410410794491 / 100000000000000000000000000000000), (444693 / 100000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2ED_sound : B2_1_5U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U1_1_2D_sound) B2_1_5U1_1_2EDLog_sound) (by decide +kernel)
def B2_1_5U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 999999, 500000⟩
def B2_1_5U1_1_2EOneDLog : Ball := ⟨(-100000050000033333358332099 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2EOneDLog_sound : B2_1_5U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U1_1_2OneD_sound) (w := B2_1_5U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U1_1_2EOneD : Ball := ⟨(99999949999983333324998741 / 100000000000000000000000000000000), (8470321003 / 20000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2EOneD_sound : B2_1_5U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U1_1_2OneD_sound) B2_1_5U1_1_2EOneDLog_sound) (by decide +kernel)
def B2_1_5U1_1_2BinaryEntropy : Ball := ⟨(62034628954096210987100657 / 4000000000000000000000000000000), (2117604603 / 5000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2BinaryEntropy_sound : B2_1_5U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U1_1_2EOneD_sound B2_1_5U1_1_2ED_sound)
    (Ball.mul_sound B2_1_5U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B2_1_5U1_1_2Leaf : Ball := ⟨(321887421543028831510114330187393 / 100000000000000000000000000000000), (127054878571 / 100000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2Leaf_sound : B2_1_5U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1999999 / 1000000)).Encloses (2 - (binaryParameter (shape 2 1 5) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 1 5) (shape 1 1 2) = (1 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1999999 / 1000000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_1_5U1_1_2Mass : Ball := ⟨(534393655563127546658319620403 / 25000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
lemma B2_1_5U1_1_2Mass_sound : B2_1_5U1_1_2Mass.Encloses (littleMass (shape 2 1 5) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 1 1 2))) (by decide +kernel)
def B2_1_5U2_0_2D : Ball := .exact (50311 / 500000)
lemma B2_1_5U2_0_2D_sound : B2_1_5U2_0_2D.Encloses (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_1_5U2_0_2OneD : Ball := .exact (449689 / 500000)
lemma B2_1_5U2_0_2OneD_sound : B2_1_5U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 2 0 2) = (50311 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((449689 / 500000) : ℚ) using 1 <;> norm_num [B2_1_5U2_0_2OneD, Ball.exact]
def B2_1_5U2_0_2EDLogWitness : LogWitness := ⟨-4, 50311, 31250⟩
def B2_1_5U2_0_2EDLog : Ball := ⟨(-229638435735244201494939716178541 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2EDLog_sound : B2_1_5U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_0_2D_sound) (w := B2_1_5U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U2_0_2ED : Ball := ⟨(23106678680551742042823824121317 / 100000000000000000000000000000000), (5326884327 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2ED_sound : B2_1_5U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_0_2D_sound) B2_1_5U2_0_2EDLog_sound) (by decide +kernel)
def B2_1_5U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 449689, 250000⟩
def B2_1_5U2_0_2EOneDLog : Ball := ⟨(-2651296642407782012789413805853 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2EOneDLog_sound : B2_1_5U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_0_2OneD_sound) (w := B2_1_5U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U2_0_2EOneD : Ball := ⟨(4769035743310852342197034819761 / 50000000000000000000000000000000), (7618027981 / 20000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2EOneD_sound : B2_1_5U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_0_2OneD_sound) B2_1_5U2_0_2EOneDLog_sound) (by decide +kernel)
def B2_1_5U2_0_2BinaryEntropy : Ball := ⟨(39619335727403728419635964891949 / 100000000000000000000000000000000), (53005416021 / 100000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2BinaryEntropy_sound : B2_1_5U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U2_0_2EOneD_sound B2_1_5U2_0_2ED_sound)
    (Ball.mul_sound B2_1_5U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B2_1_5U2_0_2Leaf : Ball := ⟨(82279486472308748440293060428841 / 25000000000000000000000000000000), (20909479467 / 12500000000000000000000000000000)⟩
lemma B2_1_5U2_0_2Leaf_sound : B2_1_5U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_1_5U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_1_5U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_1_5U2_0_2Mass : Ball := ⟨(153743490797966165833014949619 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_0_2Mass_sound : B2_1_5U2_0_2Mass.Encloses (littleMass (shape 2 1 5) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 2 0 2))) (by decide +kernel)
def B2_1_5U2_1_1D : Ball := .exact (21083 / 500000)
lemma B2_1_5U2_1_1D_sound : B2_1_5U2_1_1D.Encloses (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_1_5U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B2_1_5U2_1_1OneD_sound : B2_1_5U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 1 5) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B2_1_5U2_1_1OneD, Ball.exact]
def B2_1_5U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B2_1_5U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1EDLog_sound : B2_1_5U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_1_1D_sound) (w := B2_1_5U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1ED_sound : B2_1_5U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_1_1D_sound) B2_1_5U2_1_1EDLog_sound) (by decide +kernel)
def B2_1_5U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B2_1_5U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1EOneDLog_sound : B2_1_5U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_1_5U2_1_1OneD_sound) (w := B2_1_5U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_1_5U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1EOneD_sound : B2_1_5U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_1_5U2_1_1OneD_sound) B2_1_5U2_1_1EOneDLog_sound) (by decide +kernel)
def B2_1_5U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1BinaryEntropy_sound : B2_1_5U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 1 5) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_1_5U2_1_1EOneD_sound B2_1_5U2_1_1ED_sound)
    (Ball.mul_sound B2_1_5U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B2_1_5U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1Leaf_sound : B2_1_5U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 2 1 5) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 1 5) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_1_5U2_1_1Mass : Ball := ⟨(11980229688179108495838363 / 195312500000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_1_5U2_1_1Mass_sound : B2_1_5U2_1_1Mass.Encloses (littleMass (shape 2 1 5) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_1_5))
    (B2_1_5Law_sound (shape 2 1 1))) (by decide +kernel)
def B2_1_5Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_1_5U0_0_4Leaf
  | 0, 1, 3 => B2_1_5U0_1_3Leaf
  | 1, 0, 3 => B2_1_5U1_0_3Leaf
  | 1, 1, 2 => B2_1_5U1_1_2Leaf
  | 2, 0, 2 => B2_1_5U2_0_2Leaf
  | 2, 1, 1 => B2_1_5U2_1_1Leaf
  | _, _, _ => (.exact 0)
lemma B2_1_5Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 1 5)) :
    (B2_1_5Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 1 5) u) := by
  rw [B2_1_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_1_5U0_0_4Leaf_sound
  · exact B2_1_5U0_1_3Leaf_sound
  · exact B2_1_5U1_0_3Leaf_sound
  · exact B2_1_5U1_1_2Leaf_sound
  · exact B2_1_5U2_0_2Leaf_sound
  · exact B2_1_5U2_1_1Leaf_sound
def B2_1_5Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_1_5U0_0_4Mass
  | 0, 1, 3 => B2_1_5U0_1_3Mass
  | 1, 0, 3 => B2_1_5U1_0_3Mass
  | 1, 1, 2 => B2_1_5U1_1_2Mass
  | 2, 0, 2 => B2_1_5U2_0_2Mass
  | 2, 1, 1 => B2_1_5U2_1_1Mass
  | _, _, _ => (.exact 0)
lemma B2_1_5Masses_sound (u : Shape) (hu : u ∈ below (shape 2 1 5)) :
    (B2_1_5Masses u).Encloses ((fun u => (littleMass (shape 2 1 5) u : ℝ)) u) := by
  rw [B2_1_5_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_1_5U0_0_4Mass_sound
  · exact B2_1_5U0_1_3Mass_sound
  · exact B2_1_5U1_0_3Mass_sound
  · exact B2_1_5U1_1_2Mass_sound
  · exact B2_1_5U2_0_2Mass_sound
  · exact B2_1_5U2_1_1Mass_sound
def B2_1_5Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B2_1_5U1_1_2BinaryEntropy
  | 2, 0, 2 => B2_1_5U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_1_5U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B2_1_5Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 1 5)).filter positive) :
    (B2_1_5Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 1 5) u)) u) := by
  have hl : (below (shape 2 1 5)).filter positive = [(shape 1 1 2), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B2_1_5U1_1_2BinaryEntropy_sound
  · exact B2_1_5U2_1_1BinaryEntropy_sound
def B2_1_5S2 : Ball := ⟨(187018983303151686119192103891 / 1000000000000000000000000000000), (7633330409 / 100000000000000000000000000000000)⟩
lemma B2_1_5S2_sound : B2_1_5S2.Encloses
    (((below (shape 2 1 5)).map fun u => (littleMass (shape 2 1 5) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 1 5) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 1 5))
    (fun u => .mul (B2_1_5Masses u) (B2_1_5Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_1_5Masses_sound u hu) (B2_1_5Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
