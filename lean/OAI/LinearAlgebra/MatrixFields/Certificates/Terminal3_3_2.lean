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
lemma B3_3_2_below : below (shape 3 3 2) = [
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0)] := by decide +kernel
def B3_3_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(3703099552999836306590899387483 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(514412495980659443970973192587 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3223866655228713372649086705233 / 6250000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(115502198241018120143768739669 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(115502198241018120143768739669 / 3125000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(3223866655228713372649086705233 / 6250000000000000000000000000000), (13 / 20000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(514412495980659443970973192587 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3703099552999836306590899387483 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_3_2Raw_0_2_2 : (B3_3_2Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 0 2 2)
    (-26340) (0) (-6620) w73 w195 w154
    (by decide +kernel) w73_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_0_3_1 : (B3_3_2Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 0 3 1)
    (-26340) (-26359) (0) w73 w72 w195
    (by decide +kernel) w73_sound w72_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_1_1_2 : (B3_3_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 1 2)
    (0) (0) (-6620) w195 w195 w154
    (by decide +kernel) w195_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_1_2_1 : (B3_3_2Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 2 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_1_3_0 : (B3_3_2Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 1 3 0)
    (0) (-26359) (-6620) w195 w72 w154
    (by decide +kernel) w195_sound w72_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_2_0_2 : (B3_3_2Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 0 2)
    (0) (-26359) (-6620) w195 w72 w154
    (by decide +kernel) w195_sound w72_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_2_1_1 : (B3_3_2Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_2_2_0 : (B3_3_2Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 2 2 0)
    (0) (0) (-6620) w195 w195 w154
    (by decide +kernel) w195_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_3_0_1 : (B3_3_2Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 3 0 1)
    (-26340) (-26359) (0) w73 w72 w195
    (by decide +kernel) w73_sound w72_sound w195_sound) (by decide +kernel)
lemma B3_3_2Raw_3_1_0 : (B3_3_2Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 3 3 2) (shape 3 1 0)
    (-26340) (0) (-6620) w73 w195 w154
    (by decide +kernel) w73_sound w195_sound w154_sound) (by decide +kernel)
lemma B3_3_2Raw_sound (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    (B3_3_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 3 3 2) u : ℝ) := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2Raw_0_2_2
  · exact B3_3_2Raw_0_3_1
  · exact B3_3_2Raw_1_1_2
  · exact B3_3_2Raw_1_2_1
  · exact B3_3_2Raw_1_3_0
  · exact B3_3_2Raw_2_0_2
  · exact B3_3_2Raw_2_1_1
  · exact B3_3_2Raw_2_2_0
  · exact B3_3_2Raw_3_0_1
  · exact B3_3_2Raw_3_1_0
def B3_3_2Den : Ball := ⟨(79747724438176244778773929766603 / 25000000000000000000000000000000), (11 / 6250000000000000000000000000000)⟩
lemma B3_3_2Den_sound : B3_3_2Den.Encloses (((below (shape 3 3 2)).map (splitWeight positiveSecond tablep (shape 3 3 2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 3 2)) B3_3_2Raw (splitWeight positiveSecond tablep (shape 3 3 2)) B3_3_2Raw_sound) (by decide +kernel)
lemma B3_3_2Den_positive : 0 < B3_3_2Den.lower := by decide +kernel
def B3_3_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(580439689515942428146703134263 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(16126243714309786405990264147 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1617032550052504124618182388813 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(15674428440513710546549123442641 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1158675802272554940366620316593 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(1158675802272554940366620316593 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(15674428440513710546549123442641 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(1617032550052504124618182388813 / 10000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(16126243714309786405990264147 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(580439689515942428146703134263 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B3_3_2Law (u : Shape) : Ball := if u ∈ below (shape 3 3 2) then B3_3_2Table u else .exact 0
lemma B3_3_2Law_check_0_2_2 : contains (.mul (B3_3_2Raw (shape 0 2 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B3_3_2Law_check_0_3_1 : contains (.mul (B3_3_2Raw (shape 0 3 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 0 3 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_1_2 : contains (.mul (B3_3_2Raw (shape 1 1 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B3_3_2Law_check_1_2_1 : contains (.mul (B3_3_2Raw (shape 1 2 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B3_3_2Law_check_1_3_0 : contains (.mul (B3_3_2Raw (shape 1 3 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 1 3 0)) = true := by decide +kernel
lemma B3_3_2Law_check_2_0_2 : contains (.mul (B3_3_2Raw (shape 2 0 2)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B3_3_2Law_check_2_1_1 : contains (.mul (B3_3_2Raw (shape 2 1 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B3_3_2Law_check_2_2_0 : contains (.mul (B3_3_2Raw (shape 2 2 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B3_3_2Law_check_3_0_1 : contains (.mul (B3_3_2Raw (shape 3 0 1)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B3_3_2Law_check_3_1_0 : contains (.mul (B3_3_2Raw (shape 3 1 0)) (.inv B3_3_2Den)) (B3_3_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B3_3_2Law_check (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    contains (.mul (B3_3_2Raw u) (.inv B3_3_2Den)) (B3_3_2Table u) = true := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2Law_check_0_2_2
  · exact B3_3_2Law_check_0_3_1
  · exact B3_3_2Law_check_1_1_2
  · exact B3_3_2Law_check_1_2_1
  · exact B3_3_2Law_check_1_3_0
  · exact B3_3_2Law_check_2_0_2
  · exact B3_3_2Law_check_2_1_1
  · exact B3_3_2Law_check_2_2_0
  · exact B3_3_2Law_check_3_0_1
  · exact B3_3_2Law_check_3_1_0
lemma B3_3_2Law_sound (u : Shape) :
    (B3_3_2Law u).Encloses (stageBLaw (shape 3 3 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 3 2)
  · have h := contains_sound (Ball.mul_sound (B3_3_2Raw_sound u hu)
      (Ball.inv_sound B3_3_2Den_sound B3_3_2Den_positive)) (B3_3_2Law_check u hu)
    simpa only [B3_3_2Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B3_3_2Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B3_3_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (52157 / 500000)
  | 1, 1, 2 => (9739 / 250000)
  | 1, 2, 1 => (1219 / 250000)
  | 2, 0, 2 => (20479 / 200000)
  | 2, 1, 1 => (21083 / 500000)
  | 2, 2, 0 => (27517 / 250000)
  | _, _, _ => 0
lemma B3_3_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 3 3 2) u = B3_3_2Binary u := by
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
def B3_3_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B3_3_2Binary u else if i = 3 then B3_3_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B3_3_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B3_3_2LittleRat u w i)
  else .exact (littleLaw (shape 3 3 2) u w i)

lemma B3_3_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B3_3_2Little u w i).Encloses (littleLaw (shape 3 3 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B3_3_2Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B3_3_2LittleRat, littleLaw, B3_3_2Binary_eq u hu]
  · simp only [B3_3_2Little, hu, ite_false]
    exact Ball.exact_sound _
def B3_3_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 4 => ⟨(330535454043745680088327227499 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 1, 2 => ⟨(11364381072153531634707882333201 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(3220333895210890740815161757201 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 2, 1 => ⟨(11364381072153531634707882333201 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(3220333895210890740815161757201 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(330535454043745680088327227499 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(2914142085981020950846212413557 / 6250000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
  | 1, 3, 1 => ⟨(1026894192444005991017039212513 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 4, 0 => ⟨(1319938239415652804426522958063 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(2914142085981020950846212413557 / 6250000000000000000000000000000), (1 / 2000000000000000000000000000000)⟩
  | 1, 1, 3 => ⟨(1026894192444005991017039212513 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 4 => ⟨(1319938239415652804426522958063 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(352404218026259944720747217461 / 2000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(869669780516483806804489600199 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(984691228692828717411192172711 / 1562500000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(352404218026259944720747217461 / 2000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(869669780516483806804489600199 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B3_3_2Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((0 : Fin 6),j)) (B3_3_2Half 0 (0,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((1 : Fin 6),j)) (B3_3_2Half 0 (1,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((2 : Fin 6),j)) (B3_3_2Half 0 (2,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((3 : Fin 6),j)) (B3_3_2Half 0 (3,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((4 : Fin 6),j)) (B3_3_2Half 0 (4,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 0) ((5 : Fin 6),j)) (B3_3_2Half 0 (5,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((0 : Fin 6),j)) (B3_3_2Half 1 (0,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((1 : Fin 6),j)) (B3_3_2Half 1 (1,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((2 : Fin 6),j)) (B3_3_2Half 1 (2,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((3 : Fin 6),j)) (B3_3_2Half 1 (3,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((4 : Fin 6),j)) (B3_3_2Half 1 (4,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 1) ((5 : Fin 6),j)) (B3_3_2Half 1 (5,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((0 : Fin 6),j)) (B3_3_2Half 2 (0,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((1 : Fin 6),j)) (B3_3_2Half 2 (1,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((2 : Fin 6),j)) (B3_3_2Half 2 (2,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((3 : Fin 6),j)) (B3_3_2Half 2 (3,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((4 : Fin 6),j)) (B3_3_2Half 2 (4,j)) = true := by
  decide +kernel
lemma B3_3_2Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u 2) ((5 : Fin 6),j)) (B3_3_2Half 2 (5,j)) = true := by
  decide +kernel
lemma B3_3_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (B3_3_2Half w ij).Encloses (halfLaw (shape 3 3 2) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 3 3 2)) (shape 3 3 2) B3_3_2Law
      (fun u => B3_3_2Little u w) ij) (B3_3_2Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B3_3_2Half_check_0_0 j) (B3_3_2Half_check_0_1 j) (B3_3_2Half_check_0_2 j) (B3_3_2Half_check_0_3 j) (B3_3_2Half_check_0_4 j) (B3_3_2Half_check_0_5 j)
    · exact forall_fin6 (B3_3_2Half_check_1_0 j) (B3_3_2Half_check_1_1 j) (B3_3_2Half_check_1_2 j) (B3_3_2Half_check_1_3 j) (B3_3_2Half_check_1_4 j) (B3_3_2Half_check_1_5 j)
    · exact forall_fin6 (B3_3_2Half_check_2_0 j) (B3_3_2Half_check_2_1 j) (B3_3_2Half_check_2_2 j) (B3_3_2Half_check_2_3 j) (B3_3_2Half_check_2_4 j) (B3_3_2Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 3 3 2)) (shape 3 3 2)
    B3_3_2Law (fun u => (stageBLaw (shape 3 3 2) u : ℝ))
    (fun u => B3_3_2Little u w) (fun u i => (littleLaw (shape 3 3 2) u w i : ℝ))
    (fun u _ => B3_3_2Law_sound u) (fun u i => B3_3_2Little_sound u w i) ij) hcheck
  have hp : positive (shape 3 3 2) = true := by decide +kernel
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
def B3_3_2U0_2_2D : Ball := .exact (52157 / 500000)
lemma B3_3_2U0_2_2D_sound : B3_3_2U0_2_2D.Encloses (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U0_2_2OneD : Ball := .exact (447843 / 500000)
lemma B3_3_2U0_2_2OneD_sound : B3_3_2U0_2_2OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 0 2 2) = (52157 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((447843 / 500000) : ℚ) using 1 <;> norm_num [B3_3_2U0_2_2OneD, Ball.exact]
def B3_3_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 52157, 31250⟩
def B3_3_2U0_2_2EDLog : Ball := ⟨(-226034969779528798511424963779123 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2EDLog_sound : B3_3_2U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U0_2_2D_sound) (w := B3_3_2U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U0_2_2ED : Ball := ⟨(4715722367516353417584156734331 / 20000000000000000000000000000000), (11044674359 / 100000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2ED_sound : B3_3_2U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U0_2_2D_sound) B3_3_2U0_2_2EDLog_sound) (by decide +kernel)
def B3_3_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 447843, 250000⟩
def B3_3_2U0_2_2EOneDLog : Ball := ⟨(-1101653738564778545821473882577 / 10000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2EOneDLog_sound : B3_3_2U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U0_2_2OneD_sound) (w := B3_3_2U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U0_2_2EOneD : Ball := ⟨(9867358304801322365926526559899 / 100000000000000000000000000000000), (4741722203 / 12500000000000000000000000000000)⟩
lemma B3_3_2U0_2_2EOneD_sound : B3_3_2U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U0_2_2OneD_sound) B3_3_2U0_2_2EOneDLog_sound) (by decide +kernel)
def B3_3_2U0_2_2BinaryEntropy : Ball := ⟨(20338232820838051477251111695703 / 50000000000000000000000000000000), (53396321727 / 100000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2BinaryEntropy_sound : B3_3_2U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U0_2_2EOneD_sound B3_3_2U0_2_2ED_sound)
    (Ball.mul_sound B3_3_2U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U0_2_2Leaf : Ball := ⟨(328986666848966028579433299805169 / 100000000000000000000000000000000), (41799413649 / 25000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2Leaf_sound : B3_3_2U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_3_2U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B3_3_2U0_2_2Mass : Ball := ⟨(257837301312875337408670808073 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B3_3_2U0_2_2Mass_sound : B3_3_2U0_2_2Mass.Encloses (littleMass (shape 3 3 2) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 0 2 2))) (by decide +kernel)
def B3_3_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_3_2U0_3_1Leaf_sound : B3_3_2U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_3_2U0_3_1Mass : Ball := ⟨(7163443911078640424744493343 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_3_2U0_3_1Mass_sound : B3_3_2U0_3_1Mass.Encloses (littleMass (shape 3 3 2) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 0 3 1))) (by decide +kernel)
def B3_3_2U1_1_2D : Ball := .exact (9739 / 250000)
lemma B3_3_2U1_1_2D_sound : B3_3_2U1_1_2D.Encloses (binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U1_1_2OneD : Ball := .exact (240261 / 250000)
lemma B3_3_2U1_1_2OneD_sound : B3_3_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 1 1 2) = (9739 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((240261 / 250000) : ℚ) using 1 <;> norm_num [B3_3_2U1_1_2OneD, Ball.exact]
def B3_3_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 19478, 15625⟩
def B3_3_2U1_1_2EDLog : Ball := ⟨(-324532247488318424096291773816019 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2EDLog_sound : B3_3_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U1_1_2D_sound) (w := B3_3_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U1_1_2ED : Ball := ⟨(12642478233154932529095142340777 / 100000000000000000000000000000000), (197982093 / 4000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2ED_sound : B3_3_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U1_1_2D_sound) B3_3_2U1_1_2EDLog_sound) (by decide +kernel)
def B3_3_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 240261, 125000⟩
def B3_3_2U1_1_2EOneDLog : Ball := ⟨(-198675427100083019722202722521 / 5000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2EOneDLog_sound : B3_3_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U1_1_2OneD_sound) (w := B3_3_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U1_1_2EOneD : Ball := ⟨(3818716543239443712118091865249 / 100000000000000000000000000000000), (2543862287 / 6250000000000000000000000000000)⟩
lemma B3_3_2U1_1_2EOneD_sound : B3_3_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U1_1_2OneD_sound) B3_3_2U1_1_2EOneDLog_sound) (by decide +kernel)
def B3_3_2U1_1_2BinaryEntropy : Ball := ⟨(3832283786596739837715800582899 / 20000000000000000000000000000000), (47301199693 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2BinaryEntropy_sound : B3_3_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U1_1_2EOneD_sound B3_3_2U1_1_2ED_sound)
    (Ball.mul_sound B3_3_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U1_1_2Leaf : Ball := ⟨(15780892807757089675042853684627 / 5000000000000000000000000000000), (124580165937 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2Leaf_sound : B3_3_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (490261 / 250000)).Encloses (2 - (binaryParameter (shape 3 3 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 3 3 2) (shape 1 1 2) = (9739 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((490261 / 250000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_3_2U1_1_2Mass : Ball := ⟨(897878186940305685491830221689 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_1_2Mass_sound : B3_3_2U1_1_2Mass.Encloses (littleMass (shape 3 3 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 1 1 2))) (by decide +kernel)
def B3_3_2U1_2_1D : Ball := .exact (1219 / 250000)
lemma B3_3_2U1_2_1D_sound : B3_3_2U1_2_1D.Encloses (binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U1_2_1OneD : Ball := .exact (248781 / 250000)
lemma B3_3_2U1_2_1OneD_sound : B3_3_2U1_2_1OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 1 2 1) = (1219 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((248781 / 250000) : ℚ) using 1 <;> norm_num [B3_3_2U1_2_1OneD, Ball.exact]
def B3_3_2U1_2_1EDLogWitness : LogWitness := ⟨-8, 19504, 15625⟩
def B3_3_2U1_2_1EDLog : Ball := ⟨(-133085751684077799008056524667789 / 25000000000000000000000000000000), (190582413147 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1EDLog_sound : B3_3_2U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U1_2_1D_sound) (w := B3_3_2U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U1_2_1ED : Ball := ⟨(2595704500846253391853134457121 / 100000000000000000000000000000000), (929279847 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1ED_sound : B3_3_2U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U1_2_1D_sound) B3_3_2U1_2_1EDLog_sound) (by decide +kernel)
def B3_3_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 248781, 125000⟩
def B3_3_2U1_2_1EOneDLog : Ball := ⟨(-244396323639087523862893819551 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1EOneDLog_sound : B3_3_2U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U1_2_1OneD_sound) (w := B3_3_2U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U1_2_1EOneD : Ball := ⟨(243204647165023333096538349287 / 50000000000000000000000000000000), (21072570367 / 50000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1EOneD_sound : B3_3_2U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U1_2_1OneD_sound) B3_3_2U1_2_1EOneDLog_sound) (by decide +kernel)
def B3_3_2U1_2_1BinaryEntropy : Ball := ⟨(213755772526083086932378340313 / 6250000000000000000000000000000), (21640463607 / 50000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1BinaryEntropy_sound : B3_3_2U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U1_2_1EOneD_sound B3_3_2U1_2_1ED_sound)
    (Ball.mul_sound B3_3_2U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U1_2_1Leaf : Ball := ⟨(160551410280358603788748230099313 / 50000000000000000000000000000000), (2534903643 / 2000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1Leaf_sound : B3_3_2U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (498781 / 250000)).Encloses (2 - (binaryParameter (shape 3 3 2) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 3 3 2) (shape 1 2 1) = (1219 / 250000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((498781 / 250000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_3_2U1_2_1Mass : Ball := ⟨(6962742902874551343715804077263 / 100000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
lemma B3_3_2U1_2_1Mass_sound : B3_3_2U1_2_1Mass.Encloses (littleMass (shape 3 3 2) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 1 2 1))) (by decide +kernel)
def B3_3_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_3_2U1_3_0Leaf_sound : B3_3_2U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_3_2U1_3_0Mass : Ball := ⟨(257347875542098689266630589041 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B3_3_2U1_3_0Mass_sound : B3_3_2U1_3_0Mass.Encloses (littleMass (shape 3 3 2) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 1 3 0))) (by decide +kernel)
def B3_3_2U2_0_2D : Ball := .exact (20479 / 200000)
lemma B3_3_2U2_0_2D_sound : B3_3_2U2_0_2D.Encloses (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U2_0_2OneD : Ball := .exact (179521 / 200000)
lemma B3_3_2U2_0_2OneD_sound : B3_3_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 2 0 2) = (20479 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((179521 / 200000) : ℚ) using 1 <;> norm_num [B3_3_2U2_0_2OneD, Ball.exact]
def B3_3_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 20479, 12500⟩
def B3_3_2U2_0_2EDLog : Ball := ⟨(-45578347913877226878717459404093 / 20000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2EDLog_sound : B3_3_2U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_0_2D_sound) (w := B3_3_2U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_0_2ED : Ball := ⟨(23334974673207293231231371278411 / 100000000000000000000000000000000), (10841492331 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2ED_sound : B3_3_2U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_0_2D_sound) B3_3_2U2_0_2EDLog_sound) (by decide +kernel)
def B3_3_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 179521, 100000⟩
def B3_3_2U2_0_2EOneDLog : Ball := ⟨(-10802517381923768407763481952009 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2EOneDLog_sound : B3_3_2U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_0_2OneD_sound) (w := B3_3_2U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_0_2EOneD : Ball := ⟨(9696393614601684141650540217533 / 100000000000000000000000000000000), (19007525217 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2EOneD_sound : B3_3_2U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_0_2OneD_sound) B3_3_2U2_0_2EOneDLog_sound) (by decide +kernel)
def B3_3_2U2_0_2BinaryEntropy : Ball := ⟨(40128848843152537368659657848333 / 100000000000000000000000000000000), (26596569849 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2BinaryEntropy_sound : B3_3_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U2_0_2EOneD_sound B3_3_2U2_0_2ED_sound)
    (Ball.mul_sound B3_3_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U2_0_2Leaf : Ball := ⟨(82264188080308667679340626386903 / 25000000000000000000000000000000), (167238291001 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2Leaf_sound : B3_3_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_3_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B3_3_2U2_0_2Mass : Ball := ⟨(257347875542098689266630589041 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B3_3_2U2_0_2Mass_sound : B3_3_2U2_0_2Mass.Encloses (littleMass (shape 3 3 2) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 2 0 2))) (by decide +kernel)
def B3_3_2U2_1_1D : Ball := .exact (21083 / 500000)
lemma B3_3_2U2_1_1D_sound : B3_3_2U2_1_1D.Encloses (binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U2_1_1OneD : Ball := .exact (478917 / 500000)
lemma B3_3_2U2_1_1OneD_sound : B3_3_2U2_1_1OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478917 / 500000) : ℚ) using 1 <;> norm_num [B3_3_2U2_1_1OneD, Ball.exact]
def B3_3_2U2_1_1EDLogWitness : LogWitness := ⟨-5, 21083, 15625⟩
def B3_3_2U2_1_1EDLog : Ball := ⟨(-63322821397686708031899813013369 / 20000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1EDLog_sound : B3_3_2U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_1_1D_sound) (w := B3_3_2U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_1_1ED : Ball := ⟨(13350350435274288654365437577609 / 100000000000000000000000000000000), (5357398689 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1ED_sound : B3_3_2U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_1_1D_sound) B3_3_2U2_1_1EDLog_sound) (by decide +kernel)
def B3_3_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 478917, 250000⟩
def B3_3_2U2_1_1EOneDLog : Ball := ⟨(-67313740136531887218517535329 / 1562500000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1EOneDLog_sound : B3_3_2U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_1_1OneD_sound) (w := B3_3_2U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_1_1EOneD : Ball := ⟨(1031606223518958138592984398949 / 25000000000000000000000000000000), (10141461951 / 25000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1EOneD_sound : B3_3_2U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_1_1OneD_sound) B3_3_2U2_1_1EOneDLog_sound) (by decide +kernel)
def B3_3_2U2_1_1BinaryEntropy : Ball := ⟨(4079899946179837320085215066313 / 20000000000000000000000000000000), (47709046057 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1BinaryEntropy_sound : B3_3_2U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U2_1_1EOneD_sound B3_3_2U2_1_1ED_sound)
    (Ball.mul_sound B3_3_2U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U2_1_1Leaf : Ball := ⟨(315101226585250447280610230069167 / 100000000000000000000000000000000), (62188121377 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1Leaf_sound : B3_3_2U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978917 / 500000)).Encloses (2 - (binaryParameter (shape 3 3 2) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 3 3 2) (shape 2 1 1) = (21083 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978917 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B3_3_2U2_1_1Mass : Ball := ⟨(6962742902874551343715804077263 / 100000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_1_1Mass_sound : B3_3_2U2_1_1Mass.Encloses (littleMass (shape 3 3 2) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 2 1 1))) (by decide +kernel)
def B3_3_2U2_2_0D : Ball := .exact (27517 / 250000)
lemma B3_3_2U2_2_0D_sound : B3_3_2U2_2_0D.Encloses (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B3_3_2U2_2_0OneD : Ball := .exact (222483 / 250000)
lemma B3_3_2U2_2_0OneD_sound : B3_3_2U2_2_0OneD.Encloses (1 - (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 3 3 2) (shape 2 2 0) = (27517 / 250000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((222483 / 250000) : ℚ) using 1 <;> norm_num [B3_3_2U2_2_0OneD, Ball.exact]
def B3_3_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 27517, 15625⟩
def B3_3_2U2_2_0EDLog : Ball := ⟨(-220665692236720985729493316733689 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0EDLog_sound : B3_3_2U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_2_0D_sound) (w := B3_3_2U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_2_0ED : Ball := ⟨(6072057853277851364318467596561 / 25000000000000000000000000000000), (11653902807 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0ED_sound : B3_3_2U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_2_0D_sound) B3_3_2U2_2_0EDLog_sound) (by decide +kernel)
def B3_3_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 222483, 125000⟩
def B3_3_2U2_2_0EOneDLog : Ball := ⟨(-5830511183465280787305887930417 / 50000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0EOneDLog_sound : B3_3_2U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B3_3_2U2_2_0OneD_sound) (w := B3_3_2U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B3_3_2U2_2_0EOneD : Ball := ⟨(1297189619630906065402175864423 / 12500000000000000000000000000000), (9422521561 / 25000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0EOneD_sound : B3_3_2U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 3 3 2) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B3_3_2U2_2_0OneD_sound) B3_3_2U2_2_0EOneDLog_sound) (by decide +kernel)
def B3_3_2U2_2_0BinaryEntropy : Ball := ⟨(10573770189286465003046216428573 / 25000000000000000000000000000000), (27002775087 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0BinaryEntropy_sound : B3_3_2U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 3 3 2) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B3_3_2U2_2_0EOneD_sound B3_3_2U2_2_0ED_sound)
    (Ball.mul_sound B3_3_2U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B3_3_2U2_2_0Leaf : Ball := ⟨(2054707130092541393287658679543 / 625000000000000000000000000000), (83537904453 / 50000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0Leaf_sound : B3_3_2U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B3_3_2U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B3_3_2U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B3_3_2U2_2_0Mass : Ball := ⟨(897878186940305685491830221689 / 25000000000000000000000000000000), (47 / 100000000000000000000000000000000)⟩
lemma B3_3_2U2_2_0Mass_sound : B3_3_2U2_2_0Mass.Encloses (littleMass (shape 3 3 2) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 2 2 0))) (by decide +kernel)
def B3_3_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_3_2U3_0_1Leaf_sound : B3_3_2U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_3_2U3_0_1Mass : Ball := ⟨(7163443911078640424744493343 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B3_3_2U3_0_1Mass_sound : B3_3_2U3_0_1Mass.Encloses (littleMass (shape 3 3 2) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 3 0 1))) (by decide +kernel)
def B3_3_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B3_3_2U3_1_0Leaf_sound : B3_3_2U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B3_3_2U3_1_0Mass : Ball := ⟨(257837301312875337408670808073 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B3_3_2U3_1_0Mass_sound : B3_3_2U3_1_0Mass.Encloses (littleMass (shape 3 3 2) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_3_3_2))
    (B3_3_2Law_sound (shape 3 1 0))) (by decide +kernel)
def B3_3_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2Leaf
  | 0, 3, 1 => B3_3_2U0_3_1Leaf
  | 1, 1, 2 => B3_3_2U1_1_2Leaf
  | 1, 2, 1 => B3_3_2U1_2_1Leaf
  | 1, 3, 0 => B3_3_2U1_3_0Leaf
  | 2, 0, 2 => B3_3_2U2_0_2Leaf
  | 2, 1, 1 => B3_3_2U2_1_1Leaf
  | 2, 2, 0 => B3_3_2U2_2_0Leaf
  | 3, 0, 1 => B3_3_2U3_0_1Leaf
  | 3, 1, 0 => B3_3_2U3_1_0Leaf
  | _, _, _ => (.exact 0)
lemma B3_3_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    (B3_3_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 3 3 2) u) := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2U0_2_2Leaf_sound
  · exact B3_3_2U0_3_1Leaf_sound
  · exact B3_3_2U1_1_2Leaf_sound
  · exact B3_3_2U1_2_1Leaf_sound
  · exact B3_3_2U1_3_0Leaf_sound
  · exact B3_3_2U2_0_2Leaf_sound
  · exact B3_3_2U2_1_1Leaf_sound
  · exact B3_3_2U2_2_0Leaf_sound
  · exact B3_3_2U3_0_1Leaf_sound
  · exact B3_3_2U3_1_0Leaf_sound
def B3_3_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2Mass
  | 0, 3, 1 => B3_3_2U0_3_1Mass
  | 1, 1, 2 => B3_3_2U1_1_2Mass
  | 1, 2, 1 => B3_3_2U1_2_1Mass
  | 1, 3, 0 => B3_3_2U1_3_0Mass
  | 2, 0, 2 => B3_3_2U2_0_2Mass
  | 2, 1, 1 => B3_3_2U2_1_1Mass
  | 2, 2, 0 => B3_3_2U2_2_0Mass
  | 3, 0, 1 => B3_3_2U3_0_1Mass
  | 3, 1, 0 => B3_3_2U3_1_0Mass
  | _, _, _ => (.exact 0)
lemma B3_3_2Masses_sound (u : Shape) (hu : u ∈ below (shape 3 3 2)) :
    (B3_3_2Masses u).Encloses ((fun u => (littleMass (shape 3 3 2) u : ℝ)) u) := by
  rw [B3_3_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B3_3_2U0_2_2Mass_sound
  · exact B3_3_2U0_3_1Mass_sound
  · exact B3_3_2U1_1_2Mass_sound
  · exact B3_3_2U1_2_1Mass_sound
  · exact B3_3_2U1_3_0Mass_sound
  · exact B3_3_2U2_0_2Mass_sound
  · exact B3_3_2U2_1_1Mass_sound
  · exact B3_3_2U2_2_0Mass_sound
  · exact B3_3_2U3_0_1Mass_sound
  · exact B3_3_2U3_1_0Mass_sound
def B3_3_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B3_3_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B3_3_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B3_3_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B3_3_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B3_3_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B3_3_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B3_3_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 3 3 2)).filter positive) :
    (B3_3_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 3 3 2) u)) u) := by
  have hl : (below (shape 3 3 2)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B3_3_2U1_1_2BinaryEntropy_sound
  · exact B3_3_2U1_2_1BinaryEntropy_sound
  · exact B3_3_2U2_1_1BinaryEntropy_sound
def B3_3_2S2 : Ball := ⟨(70486191644416634713605546718153 / 100000000000000000000000000000000), (14659169619 / 50000000000000000000000000000000)⟩
lemma B3_3_2S2_sound : B3_3_2S2.Encloses
    (((below (shape 3 3 2)).map fun u => (littleMass (shape 3 3 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 3 3 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 3 3 2))
    (fun u => .mul (B3_3_2Masses u) (B3_3_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B3_3_2Masses_sound u hu) (B3_3_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
