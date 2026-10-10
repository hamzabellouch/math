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
lemma B3_1_4_below : below (shape 3 1 4) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
def B3_1_4Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(59283170615264302211580917627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(768953964689050330179336197851 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(14976318486789256799246113282771 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 2, 0, 2 => ⟨1, 0⟩
  | 2, 1, 1 => ⟨(14976318486789256799246113282771 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(768953964689050330179336197851 / 25000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(59283170615264302211580917627 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_1_4Raw_0_0_4 : (B3_1_4Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 0 0 4)
    (-15829) (0) (-58477) w110 w195 w22
    (by decide +kernel) w110_sound w195_sound w22_sound) (by decide +kernel)
lemma B3_1_4Raw_0_1_3 : (B3_1_4Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 0 1 3)
    (-15829) (0) (-18987) w110 w195 w90
    (by decide +kernel) w110_sound w195_sound w90_sound) (by decide +kernel)
lemma B3_1_4Raw_1_0_3 : (B3_1_4Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 1 0 3)
    (0) (0) (-18987) w195 w195 w90
    (by decide +kernel) w195_sound w195_sound w90_sound) (by decide +kernel)
lemma B3_1_4Raw_1_1_2 : (B3_1_4Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_1_4Raw_2_0_2 : (B3_1_4Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 2 0 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_1_4Raw_2_1_1 : (B3_1_4Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 2 1 1)
    (0) (0) (-18987) w195 w195 w90
    (by decide +kernel) w195_sound w195_sound w90_sound) (by decide +kernel)
lemma B3_1_4Raw_3_0_1 : (B3_1_4Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 3 0 1)
    (-15829) (0) (-18987) w110 w195 w90
    (by decide +kernel) w110_sound w195_sound w90_sound) (by decide +kernel)
lemma B3_1_4Raw_3_1_0 : (B3_1_4Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 1 4) (shape 3 1 0)
    (-15829) (0) (-58477) w110 w195 w22
    (by decide +kernel) w110_sound w195_sound w22_sound) (by decide +kernel)
lemma B3_1_4Raw_sound (u : Shape) (hu : u ∈ below (shape 3 1 4)) :
    (B3_1_4Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 1 4) u : ℝ) := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_1_4Raw_0_0_4
  · exact B3_1_4Raw_0_1_3
  · exact B3_1_4Raw_1_0_3
  · exact B3_1_4Raw_1_1_2
  · exact B3_1_4Raw_2_0_2
  · exact B3_1_4Raw_2_1_1
  · exact B3_1_4Raw_3_0_1
  · exact B3_1_4Raw_3_1_0
def B3_1_4Den : Ball := ⟨(59055708758080361211087519495901 / 25000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
lemma B3_1_4Den_sound : B3_1_4Den.Encloses (((below (shape 3 1 4)).map (splitWeight positiveSecond tablep (shape 3 1 4))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 1 4)) B3_1_4Raw (splitWeight positiveSecond tablep (shape 3 1 4)) B3_1_4Raw_sound) (by decide +kernel)
lemma B3_1_4Den_positive : 0 < B3_1_4Den.lower := by decide +kernel
def B3_1_4Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(8138014732824595179881072909 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(21166454967471157448510264727337 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3169955708291305924669541513661 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(8138014732824595179881072909 / 625000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_1_4Law (u : Shape) : Ball := if u ∈ below (shape 3 1 4) then B3_1_4Table u else .exact 0
lemma B3_1_4Law_check_0_0_4 : contains (.mul (B3_1_4Raw (shape 0 0 4)) (.inv B3_1_4Den)) (B3_1_4Table (shape 0 0 4)) = true := by decide +kernel
lemma B3_1_4Law_check_0_1_3 : contains (.mul (B3_1_4Raw (shape 0 1 3)) (.inv B3_1_4Den)) (B3_1_4Table (shape 0 1 3)) = true := by decide +kernel
lemma B3_1_4Law_check_1_0_3 : contains (.mul (B3_1_4Raw (shape 1 0 3)) (.inv B3_1_4Den)) (B3_1_4Table (shape 1 0 3)) = true := by decide +kernel
lemma B3_1_4Law_check_1_1_2 : contains (.mul (B3_1_4Raw (shape 1 1 2)) (.inv B3_1_4Den)) (B3_1_4Table (shape 1 1 2)) = true := by decide +kernel
lemma B3_1_4Law_check_2_0_2 : contains (.mul (B3_1_4Raw (shape 2 0 2)) (.inv B3_1_4Den)) (B3_1_4Table (shape 2 0 2)) = true := by decide +kernel
lemma B3_1_4Law_check_2_1_1 : contains (.mul (B3_1_4Raw (shape 2 1 1)) (.inv B3_1_4Den)) (B3_1_4Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_1_4Law_check_3_0_1 : contains (.mul (B3_1_4Raw (shape 3 0 1)) (.inv B3_1_4Den)) (B3_1_4Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_1_4Law_check_3_1_0 : contains (.mul (B3_1_4Raw (shape 3 1 0)) (.inv B3_1_4Den)) (B3_1_4Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_1_4Law_check (u : Shape) (hu : u ∈ below (shape 3 1 4)) :
    contains (.mul (B3_1_4Raw u) (.inv B3_1_4Den)) (B3_1_4Table u) = true := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_1_4Law_check_0_0_4
  · exact B3_1_4Law_check_0_1_3
  · exact B3_1_4Law_check_1_0_3
  · exact B3_1_4Law_check_1_1_2
  · exact B3_1_4Law_check_2_0_2
  · exact B3_1_4Law_check_2_1_1
  · exact B3_1_4Law_check_3_0_1
  · exact B3_1_4Law_check_3_1_0
lemma B3_1_4Law_sound (u : Shape) :
    (B3_1_4Law u).Encloses (stageBLaw (shape 3 1 4) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 1 4)
  · have h := contains_sound (Ball.mul_sound (B3_1_4Raw_sound u hu)
      (Ball.inv_sound B3_1_4Den_sound B3_1_4Den_positive)) (B3_1_4Law_check u hu)
    simpa only [B3_1_4Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_1_4Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B3_1_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (2207 / 1000000)
  | 2, 0, 2 => (5923 / 62500)
  | 2, 1, 1 => (21083 / 500000)
  | _, _, _ => 0
lemma B3_1_4Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 1 4) u = B3_1_4Binary u := by
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
def B3_1_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_1_4Binary u else if i = 3 then B3_1_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_1_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_1_4LittleRat u w i)
  else .exact (littleLaw (shape 3 1 4) u w i)

lemma B3_1_4Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_1_4Little u w i).Encloses (littleLaw (shape 3 1 4) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_1_4Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B3_1_4LittleRat, littleLaw, B3_1_4Binary_eq u hu]
  · simp only [B3_1_4Little, hu, ite_false]
    exact Ball.exact_sound _
def B3_1_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(331794662118768313410096879501 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(8878737487603738207391907834341 / 20000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(4279133913506235709400073310291 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(8878737487603738207391907834341 / 20000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(4279133913506235709400073310291 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(331794662118768313410096879501 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(3820996886917273539060027346381 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(76473060096193834122862009176151 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(408752583274976468404048388933 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(408752583274976468404048388933 / 10000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(17708108191266303098081954537 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(3820996886917273539060027346381 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(6274072805784506214853963141 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_1_4Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((0 : Fin 6),j)) (B3_1_4Half 0 (0,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((1 : Fin 6),j)) (B3_1_4Half 0 (1,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((2 : Fin 6),j)) (B3_1_4Half 0 (2,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((3 : Fin 6),j)) (B3_1_4Half 0 (3,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((4 : Fin 6),j)) (B3_1_4Half 0 (4,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 0) ((5 : Fin 6),j)) (B3_1_4Half 0 (5,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((0 : Fin 6),j)) (B3_1_4Half 1 (0,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((1 : Fin 6),j)) (B3_1_4Half 1 (1,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((2 : Fin 6),j)) (B3_1_4Half 1 (2,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((3 : Fin 6),j)) (B3_1_4Half 1 (3,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((4 : Fin 6),j)) (B3_1_4Half 1 (4,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 1) ((5 : Fin 6),j)) (B3_1_4Half 1 (5,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((0 : Fin 6),j)) (B3_1_4Half 2 (0,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((1 : Fin 6),j)) (B3_1_4Half 2 (1,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((2 : Fin 6),j)) (B3_1_4Half 2 (2,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((3 : Fin 6),j)) (B3_1_4Half 2 (3,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((4 : Fin 6),j)) (B3_1_4Half 2 (4,j)) = true := by
  decide +kernel
lemma B3_1_4Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u 2) ((5 : Fin 6),j)) (B3_1_4Half 2 (5,j)) = true := by
  decide +kernel
lemma B3_1_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (B3_1_4Half w ij).Encloses (halfLaw (shape 3 1 4) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 3 1 4)) (shape 3 1 4) B3_1_4Law
      (fun u => B3_1_4Little u w) ij) (B3_1_4Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B3_1_4Half_check_0_0 j) (B3_1_4Half_check_0_1 j) (B3_1_4Half_check_0_2 j) (B3_1_4Half_check_0_3 j) (B3_1_4Half_check_0_4 j) (B3_1_4Half_check_0_5 j)
    · exact forall_fin6 (B3_1_4Half_check_1_0 j) (B3_1_4Half_check_1_1 j) (B3_1_4Half_check_1_2 j) (B3_1_4Half_check_1_3 j) (B3_1_4Half_check_1_4 j) (B3_1_4Half_check_1_5 j)
    · exact forall_fin6 (B3_1_4Half_check_2_0 j) (B3_1_4Half_check_2_1 j) (B3_1_4Half_check_2_2 j) (B3_1_4Half_check_2_3 j) (B3_1_4Half_check_2_4 j) (B3_1_4Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 3 1 4)) (shape 3 1 4)
    B3_1_4Law (fun u => (stageBLaw (shape 3 1 4) u : ℝ))
    (fun u => B3_1_4Little u w) (fun u i => (littleLaw (shape 3 1 4) u w i : ℝ))
    (fun u _ => B3_1_4Law_sound u) (fun u i => B3_1_4Little_sound u w i) ij) hcheck
  have hp : positive (shape 3 1 4) = true := by decide +kernel
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
def B3_1_4U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B3_1_4U0_0_4Leaf_sound : B3_1_4U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B3_1_4U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B3_1_4U0_0_4Mass : Ball := ⟨(3743589784293194240021197981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_1_4U0_0_4Mass_sound : B3_1_4U0_0_4Mass.Encloses (littleMass (shape 3 1 4) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 0 0 4))) (by decide +kernel)
def B3_1_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_1_4U0_1_3Leaf_sound : B3_1_4U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_1_4U0_1_3Mass : Ball := ⟨(194230381197626472204352679303 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B3_1_4U0_1_3Mass_sound : B3_1_4U0_1_3Mass.Encloses (littleMass (shape 3 1 4) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 0 1 3))) (by decide +kernel)
def B3_1_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_1_4U1_0_3Leaf_sound : B3_1_4U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_1_4U1_0_3Mass : Ball := ⟨(23642963218565539071319859767 / 2500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma B3_1_4U1_0_3Mass_sound : B3_1_4U1_0_3Mass.Encloses (littleMass (shape 3 1 4) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 1 0 3))) (by decide +kernel)
def B3_1_4U1_1_2D : Ball := .exact (2207 / 1000000)
lemma B3_1_4U1_1_2D_sound : B3_1_4U1_1_2D.Encloses (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_1_4U1_1_2OneD : Ball := .exact (997793 / 1000000)
lemma B3_1_4U1_1_2OneD_sound : B3_1_4U1_1_2OneD.Encloses (1 - (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 3 1 4) (shape 1 1 2) = (2207 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((997793 / 1000000) : ℚ) using 1 <;> norm_num [B3_1_4U1_1_2OneD, Ball.exact]
def B3_1_4U1_1_2EDLogWitness : LogWitness := ⟨-9, 17656, 15625⟩
def B3_1_4U1_1_2EDLog : Ball := ⟨(-305806057585376885208270506013229 / 50000000000000000000000000000000), (211758236829 / 100000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2EDLog_sound : B3_1_4U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U1_1_2D_sound) (w := B3_1_4U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U1_1_2ED : Ball := ⟨(674913969090926785654653006771 / 50000000000000000000000000000000), (46735043 / 10000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2ED_sound : B3_1_4U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U1_1_2D_sound) B3_1_4U1_1_2EDLog_sound) (by decide +kernel)
def B3_1_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 997793, 500000⟩
def B3_1_4U1_1_2EOneDLog : Ball := ⟨(-55235975344075793717215518041 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2EOneDLog_sound : B3_1_4U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U1_1_2OneD_sound) (w := B3_1_4U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U1_1_2EOneD : Ball := ⟨(220456278185965673761926493571 / 100000000000000000000000000000000), (42258177281 / 100000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2EOneD_sound : B3_1_4U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U1_1_2OneD_sound) B3_1_4U1_1_2EOneDLog_sound) (by decide +kernel)
def B3_1_4U1_1_2BinaryEntropy : Ball := ⟨(68930471964695966994384623767 / 4000000000000000000000000000000), (42818997797 / 100000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2BinaryEntropy_sound : B3_1_4U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 1 4) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_1_4U1_1_2EOneD_sound B3_1_4U1_1_2ED_sound)
    (Ball.mul_sound B3_1_4U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B3_1_4U1_1_2Leaf : Ball := ⟨(80383094884886467241869350690683 / 25000000000000000000000000000000), (12691473697 / 10000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2Leaf_sound : B3_1_4U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1997793 / 1000000)).Encloses (2 - (binaryParameter (shape 3 1 4) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 3 1 4) (shape 1 1 2) = (2207 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1997793 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_1_4U1_1_2Mass : Ball := ⟨(98668120771057680000923112311 / 1562500000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
lemma B3_1_4U1_1_2Mass_sound : B3_1_4U1_1_2Mass.Encloses (littleMass (shape 3 1 4) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 1 1 2))) (by decide +kernel)
def B3_1_4U2_0_2D : Ball := .exact (5923 / 62500)
lemma B3_1_4U2_0_2D_sound : B3_1_4U2_0_2D.Encloses (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_1_4U2_0_2OneD : Ball := .exact (56577 / 62500)
lemma B3_1_4U2_0_2OneD_sound : B3_1_4U2_0_2OneD.Encloses (1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 3 1 4) (shape 2 0 2) = (5923 / 62500) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((56577 / 62500) : ℚ) using 1 <;> norm_num [B3_1_4U2_0_2OneD, Ball.exact]
def B3_1_4U2_0_2EDLogWitness : LogWitness := ⟨-4, 23692, 15625⟩
def B3_1_4U2_0_2EDLog : Ball := ⟨(-235632347944752769756850307028051 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2EDLog_sound : B3_1_4U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_0_2D_sound) (w := B3_1_4U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U2_0_2ED : Ball := ⟨(11165203175014165242158594948217 / 50000000000000000000000000000000), (2006790459 / 20000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2ED_sound : B3_1_4U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_0_2D_sound) B3_1_4U2_0_2EDLog_sound) (by decide +kernel)
def B3_1_4U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 56577, 31250⟩
def B3_1_4U2_0_2EOneDLog : Ball := ⟨(-9956401454401802915036069658881 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2EOneDLog_sound : B3_1_4U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_0_2OneD_sound) (w := B3_1_4U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U2_0_2EOneD : Ball := ⟨(1126606650171381607047991426181 / 12500000000000000000000000000000), (38338066449 / 100000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2EOneD_sound : B3_1_4U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 1 4) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_0_2OneD_sound) B3_1_4U2_0_2EOneDLog_sound) (by decide +kernel)
def B3_1_4U2_0_2BinaryEntropy : Ball := ⟨(9478019188032468262246586216219 / 25000000000000000000000000000000), (26192799831 / 50000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2BinaryEntropy_sound : B3_1_4U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 1 4) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_1_4U2_0_2EOneD_sound B3_1_4U2_0_2ED_sound)
    (Ball.mul_sound B3_1_4U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B3_1_4U2_0_2Leaf : Ball := ⟨(329295016821838983109105190268493 / 100000000000000000000000000000000), (5231243719 / 3125000000000000000000000000000)⟩
lemma B3_1_4U2_0_2Leaf_sound : B3_1_4U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_1_4U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_1_4U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B3_1_4U2_0_2Mass : Ball := ⟨(98668120771057680000923112311 / 1562500000000000000000000000000), (3 / 4000000000000000000000000000000)⟩
lemma B3_1_4U2_0_2Mass_sound : B3_1_4U2_0_2Mass.Encloses (littleMass (shape 3 1 4) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 2 0 2))) (by decide +kernel)
def B3_1_4U2_1_1D : Ball := .exact (21083 / 500000)
lemma B3_1_4U2_1_1D_sound : B3_1_4U2_1_1D.Encloses (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_1_4U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B3_1_4U2_1_1OneD_sound : B3_1_4U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 1 4) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B3_1_4U2_1_1OneD, Ball.exact]
def B3_1_4U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_1_4U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1EDLog_sound : B3_1_4U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_1_1D_sound) (w := B3_1_4U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1ED_sound : B3_1_4U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_1_1D_sound) B3_1_4U2_1_1EDLog_sound) (by decide +kernel)
def B3_1_4U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_1_4U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1EOneDLog_sound : B3_1_4U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_1_4U2_1_1OneD_sound) (w := B3_1_4U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_1_4U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1EOneD_sound : B3_1_4U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_1_4U2_1_1OneD_sound) B3_1_4U2_1_1EOneDLog_sound) (by decide +kernel)
def B3_1_4U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1BinaryEntropy_sound : B3_1_4U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 1 4) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_1_4U2_1_1EOneD_sound B3_1_4U2_1_1ED_sound)
    (Ball.mul_sound B3_1_4U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B3_1_4U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1Leaf_sound : B3_1_4U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 1 4) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 1 4) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_1_4U2_1_1Mass : Ball := ⟨(23642963218565539071319859767 / 2500000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
lemma B3_1_4U2_1_1Mass_sound : B3_1_4U2_1_1Mass.Encloses (littleMass (shape 3 1 4) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 2 1 1))) (by decide +kernel)
def B3_1_4U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_1_4U3_0_1Leaf_sound : B3_1_4U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_1_4U3_0_1Mass : Ball := ⟨(194230381197626472204352679303 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B3_1_4U3_0_1Mass_sound : B3_1_4U3_0_1Mass.Encloses (littleMass (shape 3 1 4) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 3 0 1))) (by decide +kernel)
def B3_1_4U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_1_4U3_1_0Leaf_sound : B3_1_4U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_1_4U3_1_0Mass : Ball := ⟨(3743589784293194240021197981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_1_4U3_1_0Mass_sound : B3_1_4U3_1_0Mass.Encloses (littleMass (shape 3 1 4) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_1_4))
    (B3_1_4Law_sound (shape 3 1 0))) (by decide +kernel)
def B3_1_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B3_1_4U0_0_4Leaf
  | 0, 1, 3 => B3_1_4U0_1_3Leaf
  | 1, 0, 3 => B3_1_4U1_0_3Leaf
  | 1, 1, 2 => B3_1_4U1_1_2Leaf
  | 2, 0, 2 => B3_1_4U2_0_2Leaf
  | 2, 1, 1 => B3_1_4U2_1_1Leaf
  | 3, 0, 1 => B3_1_4U3_0_1Leaf
  | 3, 1, 0 => B3_1_4U3_1_0Leaf
  | _, _, _ => (.exact 0)
lemma B3_1_4Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 1 4)) :
    (B3_1_4Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 1 4) u) := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_1_4U0_0_4Leaf_sound
  · exact B3_1_4U0_1_3Leaf_sound
  · exact B3_1_4U1_0_3Leaf_sound
  · exact B3_1_4U1_1_2Leaf_sound
  · exact B3_1_4U2_0_2Leaf_sound
  · exact B3_1_4U2_1_1Leaf_sound
  · exact B3_1_4U3_0_1Leaf_sound
  · exact B3_1_4U3_1_0Leaf_sound
def B3_1_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B3_1_4U0_0_4Mass
  | 0, 1, 3 => B3_1_4U0_1_3Mass
  | 1, 0, 3 => B3_1_4U1_0_3Mass
  | 1, 1, 2 => B3_1_4U1_1_2Mass
  | 2, 0, 2 => B3_1_4U2_0_2Mass
  | 2, 1, 1 => B3_1_4U2_1_1Mass
  | 3, 0, 1 => B3_1_4U3_0_1Mass
  | 3, 1, 0 => B3_1_4U3_1_0Mass
  | _, _, _ => (.exact 0)
lemma B3_1_4Masses_sound (u : Shape) (hu : u ∈ below (shape 3 1 4)) :
    (B3_1_4Masses u).Encloses ((fun u => (littleMass (shape 3 1 4) u : ℝ)) u) := by
  rw [B3_1_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_1_4U0_0_4Mass_sound
  · exact B3_1_4U0_1_3Mass_sound
  · exact B3_1_4U1_0_3Mass_sound
  · exact B3_1_4U1_1_2Mass_sound
  · exact B3_1_4U2_0_2Mass_sound
  · exact B3_1_4U2_1_1Mass_sound
  · exact B3_1_4U3_0_1Mass_sound
  · exact B3_1_4U3_1_0Mass_sound
def B3_1_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B3_1_4U1_1_2BinaryEntropy
  | 2, 0, 2 => B3_1_4U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_1_4U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B3_1_4Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 1 4)).filter positive) :
    (B3_1_4Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 1 4) u)) u) := by
  have hl : (below (shape 3 1 4)).filter positive = [(shape 1 1 2), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B3_1_4U1_1_2BinaryEntropy_sound
  · exact B3_1_4U2_1_1BinaryEntropy_sound
def B3_1_4S2 : Ball := ⟨(23579419149144914744355152585039 / 50000000000000000000000000000000), (2089477031 / 10000000000000000000000000000000)⟩
lemma B3_1_4S2_sound : B3_1_4S2.Encloses
    (((below (shape 3 1 4)).map fun u => (littleMass (shape 3 1 4) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 1 4) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 1 4))
    (fun u => .mul (B3_1_4Masses u) (B3_1_4Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_1_4Masses_sound u hu) (B3_1_4Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
