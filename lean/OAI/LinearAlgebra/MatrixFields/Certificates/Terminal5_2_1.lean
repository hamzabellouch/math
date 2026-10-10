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
lemma B5_2_1_below : below (shape 5 2 1) = [
  (shape 1 2 1),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B5_2_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => ⟨(453587208715962055977755498999 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(1128226781795963371037633404631 / 2000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(1128226781795963371037633404631 / 2000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨1, 0⟩
  | 4, 0, 0 => ⟨(453587208715962055977755498999 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B5_2_1Raw_1_2_1 : (B5_2_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 1 2 1)
    (-32138) (-5725) (0) w65 w162 w195
    (by decide +kernel) w65_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_2_1_1 : (B5_2_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_2_2_0 : (B5_2_1Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 2 2 0)
    (0) (-5725) (0) w195 w162 w195
    (by decide +kernel) w195_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_3_0_1 : (B5_2_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 3 0 1)
    (0) (-5725) (0) w195 w162 w195
    (by decide +kernel) w195_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_3_1_0 : (B5_2_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 3 1 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_4_0_0 : (B5_2_1Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 5 2 1) (shape 4 0 0)
    (-32138) (-5725) (0) w65 w162 w195
    (by decide +kernel) w65_sound w162_sound w195_sound) (by decide +kernel)
lemma B5_2_1Raw_sound (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    (B5_2_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 5 2 1) u : ℝ) := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1Raw_1_2_1
  · exact B5_2_1Raw_2_1_1
  · exact B5_2_1Raw_2_2_0
  · exact B5_2_1Raw_3_0_1
  · exact B5_2_1Raw_3_1_0
  · exact B5_2_1Raw_4_0_0
def B5_2_1Den : Ball := ⟨(31735855026675595766354089545309 / 10000000000000000000000000000000), (1 / 625000000000000000000000000000)⟩
lemma B5_2_1Den_sound : B5_2_1Den.Encloses (((below (shape 5 2 1)).map (splitWeight positiveSecond tablep (shape 5 2 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 5 2 1)) B5_2_1Raw (splitWeight positiveSecond tablep (shape 5 2 1)) B5_2_1Raw_sound) (by decide +kernel)
lemma B5_2_1Den_positive : 0 < B5_2_1Den.lower := by decide +kernel
def B5_2_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3151010108785313270505790947861 / 10000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(2221908746525876524763592917167 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(2221908746525876524763592917167 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3151010108785313270505790947861 / 10000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B5_2_1Law (u : Shape) : Ball := if u ∈ below (shape 5 2 1) then B5_2_1Table u else .exact 0
lemma B5_2_1Law_check_1_2_1 : contains (.mul (B5_2_1Raw (shape 1 2 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B5_2_1Law_check_2_1_1 : contains (.mul (B5_2_1Raw (shape 2 1 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B5_2_1Law_check_2_2_0 : contains (.mul (B5_2_1Raw (shape 2 2 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B5_2_1Law_check_3_0_1 : contains (.mul (B5_2_1Raw (shape 3 0 1)) (.inv B5_2_1Den)) (B5_2_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B5_2_1Law_check_3_1_0 : contains (.mul (B5_2_1Raw (shape 3 1 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B5_2_1Law_check_4_0_0 : contains (.mul (B5_2_1Raw (shape 4 0 0)) (.inv B5_2_1Den)) (B5_2_1Table (shape 4 0 0)) = true := by decide +kernel
lemma B5_2_1Law_check (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    contains (.mul (B5_2_1Raw u) (.inv B5_2_1Den)) (B5_2_1Table u) = true := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1Law_check_1_2_1
  · exact B5_2_1Law_check_2_1_1
  · exact B5_2_1Law_check_2_2_0
  · exact B5_2_1Law_check_3_0_1
  · exact B5_2_1Law_check_3_1_0
  · exact B5_2_1Law_check_4_0_0
lemma B5_2_1Law_sound (u : Shape) :
    (B5_2_1Law u).Encloses (stageBLaw (shape 5 2 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 5 2 1)
  · have h := contains_sound (Ball.mul_sound (B5_2_1Raw_sound u hu)
      (Ball.inv_sound B5_2_1Den_sound B5_2_1Den_positive)) (B5_2_1Law_check u hu)
    simpa only [B5_2_1Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B5_2_1Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B5_2_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (211 / 5000)
  | 2, 1, 1 => (1917 / 500000)
  | 2, 2, 0 => (55053 / 500000)
  | _, _, _ => 0
lemma B5_2_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 5 2 1) u = B5_2_1Binary u := by
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
def B5_2_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B5_2_1Binary u else if i = 3 then B5_2_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B5_2_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B5_2_1LittleRat u w i)
  else .exact (littleLaw (shape 5 2 1) u w i)

lemma B5_2_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B5_2_1Little u w i).Encloses (littleLaw (shape 5 2 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B5_2_1Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B5_2_1LittleRat, littleLaw, B5_2_1Binary_eq u hu]
  · simp only [B5_2_1Little, hu, ite_false]
    exact Ball.exact_sound _
def B5_2_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 1, 5 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 2, 4 => ⟨(2950462341058093169205656218569 / 6250000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 3, 4 => ⟨(1038986801565327097938076659421 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 4, 2 => ⟨(2950462341058093169205656218569 / 6250000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
  | 0, 4, 3 => ⟨(1038986801565327097938076659421 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 5, 1 => ⟨(357314469969927548416673592027 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(3151010108785313270505790947861 / 5000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8251288847660790062385380988161 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(496830304206321792542832136267 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (53 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B5_2_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((0 : Fin 6),j)) (B5_2_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((1 : Fin 6),j)) (B5_2_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((2 : Fin 6),j)) (B5_2_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((3 : Fin 6),j)) (B5_2_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((4 : Fin 6),j)) (B5_2_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 0) ((5 : Fin 6),j)) (B5_2_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((0 : Fin 6),j)) (B5_2_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((1 : Fin 6),j)) (B5_2_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((2 : Fin 6),j)) (B5_2_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((3 : Fin 6),j)) (B5_2_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((4 : Fin 6),j)) (B5_2_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 1) ((5 : Fin 6),j)) (B5_2_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((0 : Fin 6),j)) (B5_2_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((1 : Fin 6),j)) (B5_2_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((2 : Fin 6),j)) (B5_2_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((3 : Fin 6),j)) (B5_2_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((4 : Fin 6),j)) (B5_2_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B5_2_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u 2) ((5 : Fin 6),j)) (B5_2_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B5_2_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (B5_2_1Half w ij).Encloses (halfLaw (shape 5 2 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 5 2 1)) (shape 5 2 1) B5_2_1Law
      (fun u => B5_2_1Little u w) ij) (B5_2_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B5_2_1Half_check_0_0 j) (B5_2_1Half_check_0_1 j) (B5_2_1Half_check_0_2 j) (B5_2_1Half_check_0_3 j) (B5_2_1Half_check_0_4 j) (B5_2_1Half_check_0_5 j)
    · exact forall_fin6 (B5_2_1Half_check_1_0 j) (B5_2_1Half_check_1_1 j) (B5_2_1Half_check_1_2 j) (B5_2_1Half_check_1_3 j) (B5_2_1Half_check_1_4 j) (B5_2_1Half_check_1_5 j)
    · exact forall_fin6 (B5_2_1Half_check_2_0 j) (B5_2_1Half_check_2_1 j) (B5_2_1Half_check_2_2 j) (B5_2_1Half_check_2_3 j) (B5_2_1Half_check_2_4 j) (B5_2_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 5 2 1)) (shape 5 2 1)
    B5_2_1Law (fun u => (stageBLaw (shape 5 2 1) u : ℝ))
    (fun u => B5_2_1Little u w) (fun u i => (littleLaw (shape 5 2 1) u w i : ℝ))
    (fun u _ => B5_2_1Law_sound u) (fun u i => B5_2_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 5 2 1) = true := by decide +kernel
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
def B5_2_1U1_2_1D : Ball := .exact (211 / 5000)
lemma B5_2_1U1_2_1D_sound : B5_2_1U1_2_1D.Encloses (binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_2_1U1_2_1OneD : Ball := .exact (4789 / 5000)
lemma B5_2_1U1_2_1OneD_sound : B5_2_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 5 2 1) (shape 1 2 1) = (211 / 5000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((4789 / 5000) : ℚ) using 1 <;> norm_num [B5_2_1U1_2_1OneD, Ball.exact]
def B5_2_1U1_2_1EDLogWitness : LogWitness := ⟨-5, 844, 625⟩
def B5_2_1U1_2_1EDLog : Ball := ⟨(-158266752897008546545638823852531 / 50000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1EDLog_sound : B5_2_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U1_2_1D_sound) (w := B5_2_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U1_2_1ED : Ball := ⟨(6678856972253760664225958366577 / 50000000000000000000000000000000), (5361718557 / 100000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1ED_sound : B5_2_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U1_2_1D_sound) B5_2_1U1_2_1EDLog_sound) (by decide +kernel)
def B5_2_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 4789, 2500⟩
def B5_2_1U1_2_1EOneDLog : Ball := ⟨(-431162910736280628338599195593 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1EOneDLog_sound : B5_2_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U1_2_1OneD_sound) (w := B5_2_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U1_2_1EOneD : Ball := ⟨(412967835903209585822710309539 / 10000000000000000000000000000000), (5070550981 / 12500000000000000000000000000000)⟩
lemma B5_2_1U1_2_1EOneD_sound : B5_2_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U1_2_1OneD_sound) B5_2_1U1_2_1EOneDLog_sound) (by decide +kernel)
def B5_2_1U1_2_1BinaryEntropy : Ball := ⟨(5103118351375646598104934643817 / 25000000000000000000000000000000), (11928341481 / 25000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1BinaryEntropy_sound : B5_2_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 2 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_2_1U1_2_1EOneD_sound B5_2_1U1_2_1ED_sound)
    (Ball.mul_sound B5_2_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B5_2_1U1_2_1Leaf : Ball := ⟨(315095754496348171339336587488733 / 100000000000000000000000000000000), (124374082821 / 100000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1Leaf_sound : B5_2_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (9789 / 5000)).Encloses (2 - (binaryParameter (shape 5 2 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 5 2 1) (shape 1 2 1) = (211 / 5000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((9789 / 5000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B5_2_1U1_2_1Mass : Ball := ⟨(362385426444727423821804449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U1_2_1Mass_sound : B5_2_1U1_2_1Mass.Encloses (littleMass (shape 5 2 1) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 1 2 1))) (by decide +kernel)
def B5_2_1U2_1_1D : Ball := .exact (1917 / 500000)
lemma B5_2_1U2_1_1D_sound : B5_2_1U2_1_1D.Encloses (binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_2_1U2_1_1OneD : Ball := .exact (498083 / 500000)
lemma B5_2_1U2_1_1OneD_sound : B5_2_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 5 2 1) (shape 2 1 1) = (1917 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((498083 / 500000) : ℚ) using 1 <;> norm_num [B5_2_1U2_1_1OneD, Ball.exact]
def B5_2_1U2_1_1EDLogWitness : LogWitness := ⟨-9, 30672, 15625⟩
def B5_2_1U2_1_1EDLog : Ball := ⟨(-69548082929483553739694058747031 / 12500000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1EDLog_sound : B5_2_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U2_1_1D_sound) (w := B5_2_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U2_1_1ED : Ball := ⟨(2133178799613119560303896169889 / 100000000000000000000000000000000), (811881081 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1ED_sound : B5_2_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U2_1_1D_sound) B5_2_1U2_1_1EDLog_sound) (by decide +kernel)
def B5_2_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 498083, 250000⟩
def B5_2_1U2_1_1EOneDLog : Ball := ⟨(-19206843091090117849948028057 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1EOneDLog_sound : B5_2_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U2_1_1OneD_sound) (w := B5_2_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U2_1_1EOneD : Ball := ⟨(382664081093577566762226546349 / 100000000000000000000000000000000), (42189271151 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1EOneD_sound : B5_2_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U2_1_1OneD_sound) B5_2_1U2_1_1EOneDLog_sound) (by decide +kernel)
def B5_2_1U2_1_1BinaryEntropy : Ball := ⟨(2781595509733380158696689438393 / 100000000000000000000000000000000), (43163528449 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1BinaryEntropy_sound : B5_2_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 2 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_2_1U2_1_1EOneD_sound B5_2_1U2_1_1ED_sound)
    (Ball.mul_sound B5_2_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B5_2_1U2_1_1Leaf : Ball := ⟨(321270523991192840836529859281353 / 100000000000000000000000000000000), (5072455111 / 4000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1Leaf_sound : B5_2_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (998083 / 500000)).Encloses (2 - (binaryParameter (shape 5 2 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 5 2 1) (shape 2 1 1) = (1917 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((998083 / 500000) : ℚ) using 1; norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B5_2_1U2_1_1Mass : Ball := ⟨(15978643995300779447518999591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_1_1Mass_sound : B5_2_1U2_1_1Mass.Encloses (littleMass (shape 5 2 1) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 2 1 1))) (by decide +kernel)
def B5_2_1U2_2_0D : Ball := .exact (55053 / 500000)
lemma B5_2_1U2_2_0D_sound : B5_2_1U2_2_0D.Encloses (binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B5_2_1U2_2_0OneD : Ball := .exact (444947 / 500000)
lemma B5_2_1U2_2_0OneD_sound : B5_2_1U2_2_0OneD.Encloses (1 - (binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 5 2 1) (shape 2 2 0) = (55053 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((444947 / 500000) : ℚ) using 1 <;> norm_num [B5_2_1U2_2_0OneD, Ball.exact]
def B5_2_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 55053, 31250⟩
def B5_2_1U2_2_0EDLog : Ball := ⟨(-110315587041277227232948872211851 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0EDLog_sound : B5_2_1U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U2_2_0D_sound) (w := B5_2_1U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U2_2_0ED : Ball := ⟨(6073204013383435190855534261879 / 25000000000000000000000000000000), (11657926213 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0ED_sound : B5_2_1U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U2_2_0D_sound) B5_2_1U2_2_0EDLog_sound) (by decide +kernel)
def B5_2_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 444947, 250000⟩
def B5_2_1U2_2_0EOneDLog : Ball := ⟨(-11665292447264905939613678307427 / 100000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0EOneDLog_sound : B5_2_1U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B5_2_1U2_2_0OneD_sound) (w := B5_2_1U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B5_2_1U2_2_0EOneD : Ball := ⟨(10380873757066356206226574643709 / 100000000000000000000000000000000), (37688476881 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0EOneD_sound : B5_2_1U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 5 2 1) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B5_2_1U2_2_0OneD_sound) B5_2_1U2_2_0EOneDLog_sound) (by decide +kernel)
def B5_2_1U2_2_0BinaryEntropy : Ball := ⟨(1692226246274937231740723423409 / 4000000000000000000000000000000), (2700478679 / 5000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0BinaryEntropy_sound : B5_2_1U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 5 2 1) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B5_2_1U2_2_0EOneD_sound B5_2_1U2_2_0ED_sound)
    (Ball.mul_sound B5_2_1U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B5_2_1U2_2_0Leaf : Ball := ⟨(328751484486399694544511642829783 / 100000000000000000000000000000000), (2610546941 / 1562500000000000000000000000000)⟩
lemma B5_2_1U2_2_0Leaf_sound : B5_2_1U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B5_2_1U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B5_2_1U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B5_2_1U2_2_0Mass : Ball := ⟨(563360440383799776936723959 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U2_2_0Mass_sound : B5_2_1U2_2_0Mass.Encloses (littleMass (shape 5 2 1) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 2 2 0))) (by decide +kernel)
def B5_2_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B5_2_1U3_0_1Leaf_sound : B5_2_1U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B5_2_1U3_0_1Mass : Ball := ⟨(563360440383799776936723959 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U3_0_1Mass_sound : B5_2_1U3_0_1Mass.Encloses (littleMass (shape 5 2 1) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 3 0 1))) (by decide +kernel)
def B5_2_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B5_2_1U3_1_0Leaf_sound : B5_2_1U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B5_2_1U3_1_0Mass : Ball := ⟨(15978643995300779447518999591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U3_1_0Mass_sound : B5_2_1U3_1_0Mass.Encloses (littleMass (shape 5 2 1) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 3 1 0))) (by decide +kernel)
def B5_2_1U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B5_2_1U4_0_0Leaf_sound : B5_2_1U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B5_2_1U4_0_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B5_2_1U4_0_0Mass : Ball := ⟨(362385426444727423821804449 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B5_2_1U4_0_0Mass_sound : B5_2_1U4_0_0Mass.Encloses (littleMass (shape 5 2 1) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_5_2_1))
    (B5_2_1Law_sound (shape 4 0 0))) (by decide +kernel)
def B5_2_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1Leaf
  | 2, 1, 1 => B5_2_1U2_1_1Leaf
  | 2, 2, 0 => B5_2_1U2_2_0Leaf
  | 3, 0, 1 => B5_2_1U3_0_1Leaf
  | 3, 1, 0 => B5_2_1U3_1_0Leaf
  | 4, 0, 0 => B5_2_1U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B5_2_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    (B5_2_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 5 2 1) u) := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1U1_2_1Leaf_sound
  · exact B5_2_1U2_1_1Leaf_sound
  · exact B5_2_1U2_2_0Leaf_sound
  · exact B5_2_1U3_0_1Leaf_sound
  · exact B5_2_1U3_1_0Leaf_sound
  · exact B5_2_1U4_0_0Leaf_sound
def B5_2_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1Mass
  | 2, 1, 1 => B5_2_1U2_1_1Mass
  | 2, 2, 0 => B5_2_1U2_2_0Mass
  | 3, 0, 1 => B5_2_1U3_0_1Mass
  | 3, 1, 0 => B5_2_1U3_1_0Mass
  | 4, 0, 0 => B5_2_1U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B5_2_1Masses_sound (u : Shape) (hu : u ∈ below (shape 5 2 1)) :
    (B5_2_1Masses u).Encloses ((fun u => (littleMass (shape 5 2 1) u : ℝ)) u) := by
  rw [B5_2_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl
  · exact B5_2_1U1_2_1Mass_sound
  · exact B5_2_1U2_1_1Mass_sound
  · exact B5_2_1U2_2_0Mass_sound
  · exact B5_2_1U3_0_1Mass_sound
  · exact B5_2_1U3_1_0Mass_sound
  · exact B5_2_1U4_0_0Mass_sound
def B5_2_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B5_2_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B5_2_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B5_2_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B5_2_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 5 2 1)).filter positive) :
    (B5_2_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 5 2 1) u)) u) := by
  have hl : (below (shape 5 2 1)).filter positive = [(shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B5_2_1U1_2_1BinaryEntropy_sound
  · exact B5_2_1U2_1_1BinaryEntropy_sound
def B5_2_1S2 : Ball := ⟨(69828290229183920558225491291 / 50000000000000000000000000000000), (28471307 / 50000000000000000000000000000000)⟩
lemma B5_2_1S2_sound : B5_2_1S2.Encloses
    (((below (shape 5 2 1)).map fun u => (littleMass (shape 5 2 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 5 2 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 5 2 1))
    (fun u => .mul (B5_2_1Masses u) (B5_2_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B5_2_1Masses_sound u hu) (B5_2_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
