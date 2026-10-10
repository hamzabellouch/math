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
lemma B3_4_1_below : below (shape 3 4 1) = [
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
def B3_4_1Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(38409269753660833180056353669 / 1250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(15831277194442435596433763391 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(7793756819393451250565121368561 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(7793756819393451250565121368561 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(15831277194442435596433763391 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(38409269753660833180056353669 / 1250000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_4_1Raw_0_3_1 : (B3_4_1Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 0 3 1)
    (-16239) (-18587) (0) w107 w91 w195
    (by decide +kernel) w107_sound w91_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_0_4_0 : (B3_4_1Raw (shape 0 4 0)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 0 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 0 4 0)
    (-16239) (-55176) (0) w107 w29 w195
    (by decide +kernel) w107_sound w29_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_1_2_1 : (B3_4_1Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 1 2 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_1_3_0 : (B3_4_1Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 1 3 0)
    (0) (-18587) (0) w195 w91 w195
    (by decide +kernel) w195_sound w91_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_2_1_1 : (B3_4_1Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 2 1 1)
    (0) (-18587) (0) w195 w91 w195
    (by decide +kernel) w195_sound w91_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_2_2_0 : (B3_4_1Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 2 2 0)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_3_0_1 : (B3_4_1Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 3 0 1)
    (-16239) (-55176) (0) w107 w29 w195
    (by decide +kernel) w107_sound w29_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_3_1_0 : (B3_4_1Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 4 1) (shape 3 1 0)
    (-16239) (-18587) (0) w107 w91 w195
    (by decide +kernel) w107_sound w91_sound w195_sound) (by decide +kernel)
lemma B3_4_1Raw_sound (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    (B3_4_1Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 4 1) u : ℝ) := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1Raw_0_3_1
  · exact B3_4_1Raw_0_4_0
  · exact B3_4_1Raw_1_2_1
  · exact B3_4_1Raw_1_3_0
  · exact B3_4_1Raw_2_1_1
  · exact B3_4_1Raw_2_2_0
  · exact B3_4_1Raw_3_0_1
  · exact B3_4_1Raw_3_1_0
def B3_4_1Den : Ball := ⟨(118739411605051981333516919847597 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
lemma B3_4_1Den_sound : B3_4_1Den.Encloses (((below (shape 3 4 1)).map (splitWeight positiveSecond tablep (shape 3 4 1))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 4 1)) B3_4_1Raw (splitWeight positiveSecond tablep (shape 3 4 1)) B3_4_1Raw_sound) (by decide +kernel)
lemma B3_4_1Den_positive : 0 < B3_4_1Den.lower := by decide +kernel
def B3_4_1Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(21054508913312090338702518135663 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(3281874448442126136287678136153 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3281874448442126136287678136153 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(21054508913312090338702518135663 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(80868831238226048857523902691 / 6250000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_4_1Law (u : Shape) : Ball := if u ∈ below (shape 3 4 1) then B3_4_1Table u else .exact 0
lemma B3_4_1Law_check_0_3_1 : contains (.mul (B3_4_1Raw (shape 0 3 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 0 3 1)) = true := by decide +kernel
lemma B3_4_1Law_check_0_4_0 : contains (.mul (B3_4_1Raw (shape 0 4 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 0 4 0)) = true := by decide +kernel
lemma B3_4_1Law_check_1_2_1 : contains (.mul (B3_4_1Raw (shape 1 2 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_4_1Law_check_1_3_0 : contains (.mul (B3_4_1Raw (shape 1 3 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 1 3 0)) = true := by decide +kernel
lemma B3_4_1Law_check_2_1_1 : contains (.mul (B3_4_1Raw (shape 2 1 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_4_1Law_check_2_2_0 : contains (.mul (B3_4_1Raw (shape 2 2 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_4_1Law_check_3_0_1 : contains (.mul (B3_4_1Raw (shape 3 0 1)) (.inv B3_4_1Den)) (B3_4_1Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_4_1Law_check_3_1_0 : contains (.mul (B3_4_1Raw (shape 3 1 0)) (.inv B3_4_1Den)) (B3_4_1Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_4_1Law_check (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    contains (.mul (B3_4_1Raw u) (.inv B3_4_1Den)) (B3_4_1Table u) = true := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1Law_check_0_3_1
  · exact B3_4_1Law_check_0_4_0
  · exact B3_4_1Law_check_1_2_1
  · exact B3_4_1Law_check_1_3_0
  · exact B3_4_1Law_check_2_1_1
  · exact B3_4_1Law_check_2_2_0
  · exact B3_4_1Law_check_3_0_1
  · exact B3_4_1Law_check_3_1_0
lemma B3_4_1Law_sound (u : Shape) :
    (B3_4_1Law u).Encloses (stageBLaw (shape 3 4 1) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 4 1)
  · have h := contains_sound (Ball.mul_sound (B3_4_1Raw_sound u hu)
      (Ball.inv_sound B3_4_1Den_sound B3_4_1Den_positive)) (B3_4_1Law_check u hu)
    simpa only [B3_4_1Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_4_1Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B3_4_1Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 2, 1 => (2953 / 1000000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (12 / 125)
  | _, _, _ => 0
lemma B3_4_1Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 4 1) u = B3_4_1Binary u := by
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
def B3_4_1LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_4_1Binary u else if i = 3 then B3_4_1Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_4_1Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_4_1LittleRat u w i)
  else .exact (littleLaw (shape 3 4 1) u w i)

lemma B3_4_1Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_4_1Little u w i).Encloses (littleLaw (shape 3 4 1) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_4_1Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B3_4_1LittleRat, littleLaw, B3_4_1Binary_eq u hu]
  · simp only [B3_4_1Little, hu, ite_false]
    exact Ball.exact_sound _
def B3_4_1Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(44353533976166490223624096589007 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(34553861978735541810850367637 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(82952079780722940626225466023 / 6250000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(3928825098347934527147869357681 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(9488535396717968040641412979023 / 12500000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(517867354813334309888438519539 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(517867354813334309888438519539 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(4774960498253614292750479569 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(3928825098347934527147869357681 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(520812135624222942175390833 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 0 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | 2, 0, 1 => ⟨(1 / 2), (27 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_4_1Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((0 : Fin 6),j)) (B3_4_1Half 0 (0,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((1 : Fin 6),j)) (B3_4_1Half 0 (1,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((2 : Fin 6),j)) (B3_4_1Half 0 (2,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((3 : Fin 6),j)) (B3_4_1Half 0 (3,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((4 : Fin 6),j)) (B3_4_1Half 0 (4,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 0) ((5 : Fin 6),j)) (B3_4_1Half 0 (5,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((0 : Fin 6),j)) (B3_4_1Half 1 (0,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((1 : Fin 6),j)) (B3_4_1Half 1 (1,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((2 : Fin 6),j)) (B3_4_1Half 1 (2,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((3 : Fin 6),j)) (B3_4_1Half 1 (3,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((4 : Fin 6),j)) (B3_4_1Half 1 (4,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 1) ((5 : Fin 6),j)) (B3_4_1Half 1 (5,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((0 : Fin 6),j)) (B3_4_1Half 2 (0,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((1 : Fin 6),j)) (B3_4_1Half 2 (1,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((2 : Fin 6),j)) (B3_4_1Half 2 (2,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((3 : Fin 6),j)) (B3_4_1Half 2 (3,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((4 : Fin 6),j)) (B3_4_1Half 2 (4,j)) = true := by
  decide +kernel
lemma B3_4_1Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u 2) ((5 : Fin 6),j)) (B3_4_1Half 2 (5,j)) = true := by
  decide +kernel
lemma B3_4_1Half_sound (w : Fin 3) (ij : PairSlot) :
    (B3_4_1Half w ij).Encloses (halfLaw (shape 3 4 1) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 3 4 1)) (shape 3 4 1) B3_4_1Law
      (fun u => B3_4_1Little u w) ij) (B3_4_1Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B3_4_1Half_check_0_0 j) (B3_4_1Half_check_0_1 j) (B3_4_1Half_check_0_2 j) (B3_4_1Half_check_0_3 j) (B3_4_1Half_check_0_4 j) (B3_4_1Half_check_0_5 j)
    · exact forall_fin6 (B3_4_1Half_check_1_0 j) (B3_4_1Half_check_1_1 j) (B3_4_1Half_check_1_2 j) (B3_4_1Half_check_1_3 j) (B3_4_1Half_check_1_4 j) (B3_4_1Half_check_1_5 j)
    · exact forall_fin6 (B3_4_1Half_check_2_0 j) (B3_4_1Half_check_2_1 j) (B3_4_1Half_check_2_2 j) (B3_4_1Half_check_2_3 j) (B3_4_1Half_check_2_4 j) (B3_4_1Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 3 4 1)) (shape 3 4 1)
    B3_4_1Law (fun u => (stageBLaw (shape 3 4 1) u : ℝ))
    (fun u => B3_4_1Little u w) (fun u i => (littleLaw (shape 3 4 1) u w i : ℝ))
    (fun u _ => B3_4_1Law_sound u) (fun u i => B3_4_1Little_sound u w i) ij) hcheck
  have hp : positive (shape 3 4 1) = true := by decide +kernel
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
def B3_4_1U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_4_1U0_3_1Leaf_sound : B3_4_1U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B3_4_1U0_3_1Mass : Ball := ⟨(14993443283684725396667285643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_4_1U0_3_1Mass_sound : B3_4_1U0_3_1Mass.Encloses (littleMass (shape 3 4 1) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 0 3 1))) (by decide +kernel)
def B3_4_1U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B3_4_1U0_4_0Leaf_sound : B3_4_1U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  change (Ball.exact 0).Encloses 0
  simpa only [Rat.cast_zero] using Ball.exact_sound 0
def B3_4_1U0_4_0Mass : Ball := ⟨(386243604482581519325542989 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_4_1U0_4_0Mass_sound : B3_4_1U0_4_0Mass.Encloses (littleMass (shape 3 4 1) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 0 4 0))) (by decide +kernel)
def B3_4_1U1_2_1D : Ball := .exact (2953 / 1000000)
lemma B3_4_1U1_2_1D_sound : B3_4_1U1_2_1D.Encloses (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_4_1U1_2_1OneD : Ball := .exact (997047 / 1000000)
lemma B3_4_1U1_2_1OneD_sound : B3_4_1U1_2_1OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 1 2 1) = (2953 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((997047 / 1000000) : ℚ) using 1 <;> norm_num [B3_4_1U1_2_1OneD, Ball.exact]
def B3_4_1U1_2_1EDLogWitness : LogWitness := ⟨-9, 23624, 15625⟩
def B3_4_1U1_2_1EDLog : Ball := ⟨(-582493367622035143525726017920939 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1EDLog_sound : B3_4_1U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U1_2_1D_sound) (w := B3_4_1U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U1_2_1ED : Ball := ⟨(1720102914587869778831468930921 / 100000000000000000000000000000000), (312661037 / 50000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1ED_sound : B3_4_1U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U1_2_1D_sound) B3_4_1U1_2_1EDLog_sound) (by decide +kernel)
def B3_4_1U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 997047, 500000⟩
def B3_4_1U1_2_1EOneDLog : Ball := ⟨(-295736870714792481357949825269 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1EOneDLog_sound : B3_4_1U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U1_2_1OneD_sound) (w := B3_4_1U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U1_2_1EOneD : Ball := ⟨(58972711947114339832099959887 / 20000000000000000000000000000000), (5278322869 / 12500000000000000000000000000000)⟩
lemma B3_4_1U1_2_1EOneD_sound : B3_4_1U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U1_2_1OneD_sound) B3_4_1U1_2_1EOneDLog_sound) (by decide +kernel)
def B3_4_1U1_2_1BinaryEntropy : Ball := ⟨(1109826418371396663931438659717 / 50000000000000000000000000000000), (21488484721 / 50000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1BinaryEntropy_sound : B3_4_1U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U1_2_1EOneD_sound B3_4_1U1_2_1ED_sound)
    (Ball.mul_sound B3_4_1U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B3_4_1U1_2_1Leaf : Ball := ⟨(80353078867819571269883046536241 / 25000000000000000000000000000000), (126867345477 / 100000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1Leaf_sound : B3_4_1U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1997047 / 1000000)).Encloses (2 - (binaryParameter (shape 3 4 1) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 3 4 1) (shape 1 2 1) = (2953 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1997047 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_4_1U1_2_1Mass : Ball := ⟨(487950024168829794196947866917 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B3_4_1U1_2_1Mass_sound : B3_4_1U1_2_1Mass.Encloses (littleMass (shape 3 4 1) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 1 2 1))) (by decide +kernel)
def B3_4_1U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_4_1U1_3_0Leaf_sound : B3_4_1U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B3_4_1U1_3_0Mass : Ball := ⟨(19014819141945082814976681729 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B3_4_1U1_3_0Mass_sound : B3_4_1U1_3_0Mass.Encloses (littleMass (shape 3 4 1) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 1 3 0))) (by decide +kernel)
def B3_4_1U2_1_1D : Ball := .exact (21083 / 500000)
lemma B3_4_1U2_1_1D_sound : B3_4_1U2_1_1D.Encloses (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_4_1U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B3_4_1U2_1_1OneD_sound : B3_4_1U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B3_4_1U2_1_1OneD, Ball.exact]
def B3_4_1U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_4_1U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1EDLog_sound : B3_4_1U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_1_1D_sound) (w := B3_4_1U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1ED_sound : B3_4_1U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_1_1D_sound) B3_4_1U2_1_1EDLog_sound) (by decide +kernel)
def B3_4_1U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_4_1U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1EOneDLog_sound : B3_4_1U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_1_1OneD_sound) (w := B3_4_1U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1EOneD_sound : B3_4_1U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_1_1OneD_sound) B3_4_1U2_1_1EOneDLog_sound) (by decide +kernel)
def B3_4_1U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1BinaryEntropy_sound : B3_4_1U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U2_1_1EOneD_sound B3_4_1U2_1_1ED_sound)
    (Ball.mul_sound B3_4_1U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B3_4_1U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1Leaf_sound : B3_4_1U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 4 1) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 4 1) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_4_1U2_1_1Mass : Ball := ⟨(19014819141945082814976681729 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B3_4_1U2_1_1Mass_sound : B3_4_1U2_1_1Mass.Encloses (littleMass (shape 3 4 1) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 2 1 1))) (by decide +kernel)
def B3_4_1U2_2_0D : Ball := .exact (12 / 125)
lemma B3_4_1U2_2_0D_sound : B3_4_1U2_2_0D.Encloses (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_4_1U2_2_0OneD : Ball := .exact (113 / 125)
lemma B3_4_1U2_2_0OneD_sound : B3_4_1U2_2_0OneD.Encloses (1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 3 4 1) (shape 2 2 0) = (12 / 125) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((113 / 125) : ℚ) using 1 <;> norm_num [B3_4_1U2_2_0OneD, Ball.exact]
def B3_4_1U2_2_0EDLogWitness : LogWitness := ⟨-4, 192, 125⟩
def B3_4_1U2_2_0EDLog : Ball := ⟨(-117170354375715040678628387801009 / 50000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0EDLog_sound : B3_4_1U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_2_0D_sound) (w := B3_4_1U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U2_2_0ED : Ball := ⟨(11248354020068643905148325228897 / 50000000000000000000000000000000), (10164395369 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0ED_sound : B3_4_1U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_2_0D_sound) B3_4_1U2_2_0EDLog_sound) (by decide +kernel)
def B3_4_1U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 226, 125⟩
def B3_4_1U2_2_0EOneDLog : Ball := ⟨(-2523147964749013880503657881131 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0EOneDLog_sound : B3_4_1U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_4_1U2_2_0OneD_sound) (w := B3_4_1U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_4_1U2_2_0EOneD : Ball := ⟨(912370304053243419190122689817 / 10000000000000000000000000000000), (38285889219 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0EOneD_sound : B3_4_1U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 4 1) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_4_1U2_2_0OneD_sound) B3_4_1U2_2_0EOneDLog_sound) (by decide +kernel)
def B3_4_1U2_2_0BinaryEntropy : Ball := ⟨(9568656003511299243150825972199 / 25000000000000000000000000000000), (3282252671 / 6250000000000000000000000000000)⟩
lemma B3_4_1U2_2_0BinaryEntropy_sound : B3_4_1U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 4 1) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_4_1U2_2_0EOneD_sound B3_4_1U2_2_0ED_sound)
    (Ball.mul_sound B3_4_1U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B3_4_1U2_2_0Leaf : Ball := ⟨(41157624822766318087552565285851 / 12500000000000000000000000000000), (167373710393 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0Leaf_sound : B3_4_1U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_4_1U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_4_1U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B3_4_1U2_2_0Mass : Ball := ⟨(487950024168829794196947866917 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B3_4_1U2_2_0Mass_sound : B3_4_1U2_2_0Mass.Encloses (littleMass (shape 3 4 1) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 2 2 0))) (by decide +kernel)
def B3_4_1U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_4_1U3_0_1Leaf_sound : B3_4_1U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B3_4_1U3_0_1Mass : Ball := ⟨(386243604482581519325542989 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_4_1U3_0_1Mass_sound : B3_4_1U3_0_1Mass.Encloses (littleMass (shape 3 4 1) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 3 0 1))) (by decide +kernel)
def B3_4_1U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_4_1U3_1_0Leaf_sound : B3_4_1U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  change logN10.Encloses (Real.log 10)
  exact logN10_sound
def B3_4_1U3_1_0Mass : Ball := ⟨(14993443283684725396667285643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_4_1U3_1_0Mass_sound : B3_4_1U3_1_0Mass.Encloses (littleMass (shape 3 4 1) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_4_1))
    (B3_4_1Law_sound (shape 3 1 0))) (by decide +kernel)
def B3_4_1Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B3_4_1U0_3_1Leaf
  | 0, 4, 0 => B3_4_1U0_4_0Leaf
  | 1, 2, 1 => B3_4_1U1_2_1Leaf
  | 1, 3, 0 => B3_4_1U1_3_0Leaf
  | 2, 1, 1 => B3_4_1U2_1_1Leaf
  | 2, 2, 0 => B3_4_1U2_2_0Leaf
  | 3, 0, 1 => B3_4_1U3_0_1Leaf
  | 3, 1, 0 => B3_4_1U3_1_0Leaf
  | _, _, _ => (.exact 0)
lemma B3_4_1Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    (B3_4_1Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 4 1) u) := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1U0_3_1Leaf_sound
  · exact B3_4_1U0_4_0Leaf_sound
  · exact B3_4_1U1_2_1Leaf_sound
  · exact B3_4_1U1_3_0Leaf_sound
  · exact B3_4_1U2_1_1Leaf_sound
  · exact B3_4_1U2_2_0Leaf_sound
  · exact B3_4_1U3_0_1Leaf_sound
  · exact B3_4_1U3_1_0Leaf_sound
def B3_4_1Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 3, 1 => B3_4_1U0_3_1Mass
  | 0, 4, 0 => B3_4_1U0_4_0Mass
  | 1, 2, 1 => B3_4_1U1_2_1Mass
  | 1, 3, 0 => B3_4_1U1_3_0Mass
  | 2, 1, 1 => B3_4_1U2_1_1Mass
  | 2, 2, 0 => B3_4_1U2_2_0Mass
  | 3, 0, 1 => B3_4_1U3_0_1Mass
  | 3, 1, 0 => B3_4_1U3_1_0Mass
  | _, _, _ => (.exact 0)
lemma B3_4_1Masses_sound (u : Shape) (hu : u ∈ below (shape 3 4 1)) :
    (B3_4_1Masses u).Encloses ((fun u => (littleMass (shape 3 4 1) u : ℝ)) u) := by
  rw [B3_4_1_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_4_1U0_3_1Mass_sound
  · exact B3_4_1U0_4_0Mass_sound
  · exact B3_4_1U1_2_1Mass_sound
  · exact B3_4_1U1_3_0Mass_sound
  · exact B3_4_1U2_1_1Mass_sound
  · exact B3_4_1U2_2_0Mass_sound
  · exact B3_4_1U3_0_1Mass_sound
  · exact B3_4_1U3_1_0Mass_sound
def B3_4_1Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 2, 1 => B3_4_1U1_2_1BinaryEntropy
  | 2, 1, 1 => B3_4_1U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_4_1U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B3_4_1Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 4 1)).filter positive) :
    (B3_4_1Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 4 1) u)) u) := by
  have hl : (below (shape 3 4 1)).filter positive = [(shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B3_4_1U1_2_1BinaryEntropy_sound
  · exact B3_4_1U2_1_1BinaryEntropy_sound
def B3_4_1S2 : Ball := ⟨(1829846989875417228160241011411 / 50000000000000000000000000000000), (810250403 / 50000000000000000000000000000000)⟩
lemma B3_4_1S2_sound : B3_4_1S2.Encloses
    (((below (shape 3 4 1)).map fun u => (littleMass (shape 3 4 1) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 4 1) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 4 1))
    (fun u => .mul (B3_4_1Masses u) (B3_4_1Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_4_1Masses_sound u hu) (B3_4_1Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
