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
lemma B2_2_4_below : below (shape 2 2 4) = [
  (shape 0 0 4),
  (shape 0 1 3),
  (shape 0 2 2),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0)] := by decide +kernel
def B2_2_4Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(3985809275202830388494116183 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(658685387040686388916222849389 / 2500000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨1, 0⟩
  | 1, 2, 1 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(658685387040686388916222849389 / 2500000000000000000000000000000), (67 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(1687715475618203929478025269739 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(3985809275202830388494116183 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_2_4Raw_0_0_4 : (B2_2_4Raw (shape 0 0 4)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 0 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 0 0 4)
    (-6669) (-6669) (-64938) w153 w153 w16
    (by decide +kernel) w153_sound w153_sound w16_sound) (by decide +kernel)
lemma B2_2_4Raw_0_1_3 : (B2_2_4Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 0 1 3)
    (-6669) (0) (-20286) w153 w195 w85
    (by decide +kernel) w153_sound w195_sound w85_sound) (by decide +kernel)
lemma B2_2_4Raw_0_2_2 : (B2_2_4Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 0 2 2)
    (-6669) (-6669) (0) w153 w153 w195
    (by decide +kernel) w153_sound w153_sound w195_sound) (by decide +kernel)
lemma B2_2_4Raw_1_0_3 : (B2_2_4Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 1 0 3)
    (0) (-6669) (-20286) w195 w153 w85
    (by decide +kernel) w195_sound w153_sound w85_sound) (by decide +kernel)
lemma B2_2_4Raw_1_1_2 : (B2_2_4Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 1 1 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_2_4Raw_1_2_1 : (B2_2_4Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 1 2 1)
    (0) (-6669) (-20286) w195 w153 w85
    (by decide +kernel) w195_sound w153_sound w85_sound) (by decide +kernel)
lemma B2_2_4Raw_2_0_2 : (B2_2_4Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 2 0 2)
    (-6669) (-6669) (0) w153 w153 w195
    (by decide +kernel) w153_sound w153_sound w195_sound) (by decide +kernel)
lemma B2_2_4Raw_2_1_1 : (B2_2_4Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 2 1 1)
    (-6669) (0) (-20286) w153 w195 w85
    (by decide +kernel) w153_sound w195_sound w85_sound) (by decide +kernel)
lemma B2_2_4Raw_2_2_0 : (B2_2_4Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 2 4) (shape 2 2 0)
    (-6669) (-6669) (-64938) w153 w153 w16
    (by decide +kernel) w153_sound w153_sound w16_sound) (by decide +kernel)
lemma B2_2_4Raw_sound (u : Shape) (hu : u ∈ below (shape 2 2 4)) :
    (B2_2_4Raw u).Encloses (splitWeight positiveSecond tablep (shape 2 2 4) u : ℝ) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_2_4Raw_0_0_4
  · exact B2_2_4Raw_0_1_3
  · exact B2_2_4Raw_0_2_2
  · exact B2_2_4Raw_1_0_3
  · exact B2_2_4Raw_1_1_2
  · exact B2_2_4Raw_1_2_1
  · exact B2_2_4Raw_2_0_2
  · exact B2_2_4Raw_2_1_1
  · exact B2_2_4Raw_2_2_0
def B2_2_4Den : Ball := ⟨(44944498689662557648179028647651 / 25000000000000000000000000000000), (49 / 25000000000000000000000000000000)⟩
lemma B2_2_4Den_sound : B2_2_4Den.Encloses (((below (shape 2 2 4)).map (splitWeight positiveSecond tablep (shape 2 2 4))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 2 4)) B2_2_4Raw (splitWeight positiveSecond tablep (shape 2 2 4)) B2_2_4Raw_sound) (by decide +kernel)
lemma B2_2_4Den_positive : 0 < B2_2_4Den.lower := by decide +kernel
def B2_2_4Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 3 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(7327764312033444386854140531431 / 50000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(6953020038287276387329040621707 / 12500000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(7327764312033444386854140531431 / 50000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(1877555123344146106224953559491 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_2_4Law (u : Shape) : Ball := if u ∈ below (shape 2 2 4) then B2_2_4Table u else .exact 0
lemma B2_2_4Law_check_0_0_4 : contains (.mul (B2_2_4Raw (shape 0 0 4)) (.inv B2_2_4Den)) (B2_2_4Table (shape 0 0 4)) = true := by decide +kernel
lemma B2_2_4Law_check_0_1_3 : contains (.mul (B2_2_4Raw (shape 0 1 3)) (.inv B2_2_4Den)) (B2_2_4Table (shape 0 1 3)) = true := by decide +kernel
lemma B2_2_4Law_check_0_2_2 : contains (.mul (B2_2_4Raw (shape 0 2 2)) (.inv B2_2_4Den)) (B2_2_4Table (shape 0 2 2)) = true := by decide +kernel
lemma B2_2_4Law_check_1_0_3 : contains (.mul (B2_2_4Raw (shape 1 0 3)) (.inv B2_2_4Den)) (B2_2_4Table (shape 1 0 3)) = true := by decide +kernel
lemma B2_2_4Law_check_1_1_2 : contains (.mul (B2_2_4Raw (shape 1 1 2)) (.inv B2_2_4Den)) (B2_2_4Table (shape 1 1 2)) = true := by decide +kernel
lemma B2_2_4Law_check_1_2_1 : contains (.mul (B2_2_4Raw (shape 1 2 1)) (.inv B2_2_4Den)) (B2_2_4Table (shape 1 2 1)) = true := by decide +kernel
lemma B2_2_4Law_check_2_0_2 : contains (.mul (B2_2_4Raw (shape 2 0 2)) (.inv B2_2_4Den)) (B2_2_4Table (shape 2 0 2)) = true := by decide +kernel
lemma B2_2_4Law_check_2_1_1 : contains (.mul (B2_2_4Raw (shape 2 1 1)) (.inv B2_2_4Den)) (B2_2_4Table (shape 2 1 1)) = true := by decide +kernel
lemma B2_2_4Law_check_2_2_0 : contains (.mul (B2_2_4Raw (shape 2 2 0)) (.inv B2_2_4Den)) (B2_2_4Table (shape 2 2 0)) = true := by decide +kernel
lemma B2_2_4Law_check (u : Shape) (hu : u ∈ below (shape 2 2 4)) :
    contains (.mul (B2_2_4Raw u) (.inv B2_2_4Den)) (B2_2_4Table u) = true := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_2_4Law_check_0_0_4
  · exact B2_2_4Law_check_0_1_3
  · exact B2_2_4Law_check_0_2_2
  · exact B2_2_4Law_check_1_0_3
  · exact B2_2_4Law_check_1_1_2
  · exact B2_2_4Law_check_1_2_1
  · exact B2_2_4Law_check_2_0_2
  · exact B2_2_4Law_check_2_1_1
  · exact B2_2_4Law_check_2_2_0
lemma B2_2_4Law_sound (u : Shape) :
    (B2_2_4Law u).Encloses (stageBLaw (shape 2 2 4) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 2 4)
  · have h := contains_sound (Ball.mul_sound (B2_2_4Raw_sound u hu)
      (Ball.inv_sound B2_2_4Den_sound B2_2_4Den_positive)) (B2_2_4Law_check u hu)
    simpa only [B2_2_4Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B2_2_4Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B2_2_4Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (51781 / 500000)
  | 1, 1, 2 => (9039 / 1000000)
  | 1, 2, 1 => (42157 / 1000000)
  | 2, 0, 2 => (103577 / 1000000)
  | 2, 1, 1 => (8433 / 200000)
  | 2, 2, 0 => (31791 / 500000)
  | _, _, _ => 0
lemma B2_2_4Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 2 2 4) u = B2_2_4Binary u := by
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
def B2_2_4LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_2_4Binary u else if i = 3 then B2_2_4Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_2_4Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_2_4LittleRat u w i)
  else .exact (littleLaw (shape 2 2 4) u w i)

lemma B2_2_4Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B2_2_4Little u w i).Encloses (littleLaw (shape 2 2 4) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B2_2_4Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B2_2_4LittleRat, littleLaw, B2_2_4Binary_eq u hu]
  · simp only [B2_2_4Little, hu, ite_false]
    exact Ball.exact_sound _
def B2_2_4Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(8377545014499415800266058795763 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(335543914232754127540362560533 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(8377545014499415800266058795763 / 50000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(335543914232754127540362560533 / 20000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(16755339902810166110201422814999 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(209683712169054516004063447399 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(3156719039983739776176606960581 / 5000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(16755339902810166110201422814999 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(209683712169054516004063447399 / 12500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 5, 0 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 1 => ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 2, 2 => ⟨(1563542695666112973568998103859 / 2000000000000000000000000000000), (149 / 100000000000000000000000000000000)⟩
  | 2, 2, 3 => ⟨(3219564442457119163781284689913 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 3, 2 => ⟨(3219564442457119163781284689913 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(79738471553025410009103131651 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 4 => ⟨(1877555123344146106224953559491 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 0, 5 => ⟨(22170729407421252075742212347 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_2_4Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((0 : Fin 6),j)) (B2_2_4Half 0 (0,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((1 : Fin 6),j)) (B2_2_4Half 0 (1,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((2 : Fin 6),j)) (B2_2_4Half 0 (2,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((3 : Fin 6),j)) (B2_2_4Half 0 (3,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((4 : Fin 6),j)) (B2_2_4Half 0 (4,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 0) ((5 : Fin 6),j)) (B2_2_4Half 0 (5,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((0 : Fin 6),j)) (B2_2_4Half 1 (0,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((1 : Fin 6),j)) (B2_2_4Half 1 (1,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((2 : Fin 6),j)) (B2_2_4Half 1 (2,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((3 : Fin 6),j)) (B2_2_4Half 1 (3,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((4 : Fin 6),j)) (B2_2_4Half 1 (4,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 1) ((5 : Fin 6),j)) (B2_2_4Half 1 (5,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((0 : Fin 6),j)) (B2_2_4Half 2 (0,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((1 : Fin 6),j)) (B2_2_4Half 2 (1,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((2 : Fin 6),j)) (B2_2_4Half 2 (2,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((3 : Fin 6),j)) (B2_2_4Half 2 (3,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((4 : Fin 6),j)) (B2_2_4Half 2 (4,j)) = true := by
  decide +kernel
lemma B2_2_4Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u 2) ((5 : Fin 6),j)) (B2_2_4Half 2 (5,j)) = true := by
  decide +kernel
lemma B2_2_4Half_sound (w : Fin 3) (ij : PairSlot) :
    (B2_2_4Half w ij).Encloses (halfLaw (shape 2 2 4) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 2 2 4)) (shape 2 2 4) B2_2_4Law
      (fun u => B2_2_4Little u w) ij) (B2_2_4Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B2_2_4Half_check_0_0 j) (B2_2_4Half_check_0_1 j) (B2_2_4Half_check_0_2 j) (B2_2_4Half_check_0_3 j) (B2_2_4Half_check_0_4 j) (B2_2_4Half_check_0_5 j)
    · exact forall_fin6 (B2_2_4Half_check_1_0 j) (B2_2_4Half_check_1_1 j) (B2_2_4Half_check_1_2 j) (B2_2_4Half_check_1_3 j) (B2_2_4Half_check_1_4 j) (B2_2_4Half_check_1_5 j)
    · exact forall_fin6 (B2_2_4Half_check_2_0 j) (B2_2_4Half_check_2_1 j) (B2_2_4Half_check_2_2 j) (B2_2_4Half_check_2_3 j) (B2_2_4Half_check_2_4 j) (B2_2_4Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 2 2 4)) (shape 2 2 4)
    B2_2_4Law (fun u => (stageBLaw (shape 2 2 4) u : ℝ))
    (fun u => B2_2_4Little u w) (fun u i => (littleLaw (shape 2 2 4) u w i : ℝ))
    (fun u _ => B2_2_4Law_sound u) (fun u i => B2_2_4Little_sound u w i) ij) hcheck
  have hp : positive (shape 2 2 4) = true := by decide +kernel
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
def B2_2_4U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B2_2_4U0_0_4Leaf_sound : B2_2_4U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B2_2_4U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B2_2_4U0_0_4Mass : Ball := ⟨(459983845027779558302590723 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B2_2_4U0_0_4Mass_sound : B2_2_4U0_0_4Mass.Encloses (littleMass (shape 2 2 4) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 0 0 4))) (by decide +kernel)
def B2_2_4U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_2_4U0_1_3Leaf_sound : B2_2_4U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_2_4U0_1_3Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma B2_2_4U0_1_3Mass_sound : B2_2_4U0_1_3Mass.Encloses (littleMass (shape 2 2 4) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 0 1 3))) (by decide +kernel)
def B2_2_4U0_2_2D : Ball := .exact (51781 / 500000)
lemma B2_2_4U0_2_2D_sound : B2_2_4U0_2_2D.Encloses (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U0_2_2OneD : Ball := .exact (448219 / 500000)
lemma B2_2_4U0_2_2OneD_sound : B2_2_4U0_2_2OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 0 2 2) = (51781 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((448219 / 500000) : ℚ) using 1 <;> norm_num [B2_2_4U0_2_2OneD, Ball.exact]
def B2_2_4U0_2_2EDLogWitness : LogWitness := ⟨-4, 51781, 31250⟩
def B2_2_4U0_2_2EDLog : Ball := ⟨(-226758481180942422019326103547823 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2EDLog_sound : B2_2_4U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U0_2_2D_sound) (w := B2_2_4U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U0_2_2ED : Ball := ⟨(1174178091403037955458272496781 / 5000000000000000000000000000000), (5482526631 / 50000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2ED_sound : B2_2_4U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U0_2_2D_sound) B2_2_4U0_2_2EDLog_sound) (by decide +kernel)
def B2_2_4U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 448219, 250000⟩
def B2_2_4U0_2_2EOneDLog : Ball := ⟨(-2186522923289837780427151140763 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2EOneDLog_sound : B2_2_4U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U0_2_2OneD_sound) (w := B2_2_4U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U0_2_2EOneD : Ball := ⟨(9800411181540478001052772571617 / 100000000000000000000000000000000), (18982813031 / 50000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2EOneD_sound : B2_2_4U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U0_2_2OneD_sound) B2_2_4U0_2_2EOneDLog_sound) (by decide +kernel)
def B2_2_4U0_2_2BinaryEntropy : Ball := ⟨(8092468768183228544720991965183 / 20000000000000000000000000000000), (53316700629 / 100000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2BinaryEntropy_sound : B2_2_4U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U0_2_2EOneD_sound B2_2_4U0_2_2ED_sound)
    (Ball.mul_sound B2_2_4U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U0_2_2Leaf : Ball := ⟨(82253651127559039261218997596489 / 25000000000000000000000000000000), (83606789407 / 50000000000000000000000000000000)⟩
lemma B2_2_4U0_2_2Leaf_sound : B2_2_4U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_2_4U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_2_4U0_2_2Mass : Ball := ⟨(973002741917034495619167964551 / 10000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
lemma B2_2_4U0_2_2Mass_sound : B2_2_4U0_2_2Mass.Encloses (littleMass (shape 2 2 4) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 0 2 2))) (by decide +kernel)
def B2_2_4U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_2_4U1_0_3Leaf_sound : B2_2_4U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_2_4U1_0_3Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma B2_2_4U1_0_3Mass_sound : B2_2_4U1_0_3Mass.Encloses (littleMass (shape 2 2 4) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 1 0 3))) (by decide +kernel)
def B2_2_4U1_1_2D : Ball := .exact (9039 / 1000000)
lemma B2_2_4U1_1_2D_sound : B2_2_4U1_1_2D.Encloses (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U1_1_2OneD : Ball := .exact (990961 / 1000000)
lemma B2_2_4U1_1_2OneD_sound : B2_2_4U1_1_2OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 1 1 2) = (9039 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((990961 / 1000000) : ℚ) using 1 <;> norm_num [B2_2_4U1_1_2OneD, Ball.exact]
def B2_2_4U1_1_2EDLogWitness : LogWitness := ⟨-7, 18078, 15625⟩
def B2_2_4U1_1_2EDLog : Ball := ⟨(-23531033650829315888782626557599 / 5000000000000000000000000000000), (169406589463 / 100000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2EDLog_sound : B2_2_4U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U1_1_2D_sound) (w := B2_2_4U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U1_1_2ED : Ball := ⟨(4253940263396923726374123229083 / 100000000000000000000000000000000), (1531266163 / 100000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2ED_sound : B2_2_4U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U1_1_2D_sound) B2_2_4U1_1_2EDLog_sound) (by decide +kernel)
def B2_2_4U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 990961, 500000⟩
def B2_2_4U1_1_2EOneDLog : Ball := ⟨(-56750622588966416224534897681 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2EOneDLog_sound : B2_2_4U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U1_1_2OneD_sound) (w := B2_2_4U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U1_1_2EOneD : Ball := ⟨(449901229691077990306250613927 / 50000000000000000000000000000000), (20984415413 / 50000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2EOneD_sound : B2_2_4U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U1_1_2OneD_sound) B2_2_4U1_1_2EOneDLog_sound) (by decide +kernel)
def B2_2_4U1_1_2BinaryEntropy : Ball := ⟨(5780278459287214272168860398919 / 100000000000000000000000000000000), (4388291353 / 10000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2BinaryEntropy_sound : B2_2_4U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U1_1_2EOneD_sound B2_2_4U1_1_2ED_sound)
    (Ball.mul_sound B2_2_4U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U1_1_2Leaf : Ball := ⟨(320432811557770891591550164247193 / 100000000000000000000000000000000), (15810089661 / 12500000000000000000000000000000)⟩
lemma B2_2_4U1_1_2Leaf_sound : B2_2_4U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1990961 / 1000000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 1 1 2) = (9039 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1990961 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_2_4U1_1_2Mass : Ball := ⟨(18464861242187634366717571822117 / 50000000000000000000000000000000), (97 / 25000000000000000000000000000000)⟩
lemma B2_2_4U1_1_2Mass_sound : B2_2_4U1_1_2Mass.Encloses (littleMass (shape 2 2 4) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 1 1 2))) (by decide +kernel)
def B2_2_4U1_2_1D : Ball := .exact (42157 / 1000000)
lemma B2_2_4U1_2_1D_sound : B2_2_4U1_2_1D.Encloses (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U1_2_1OneD : Ball := .exact (957843 / 1000000)
lemma B2_2_4U1_2_1OneD_sound : B2_2_4U1_2_1OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 1 2 1) = (42157 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((957843 / 1000000) : ℚ) using 1 <;> norm_num [B2_2_4U1_2_1OneD, Ball.exact]
def B2_2_4U1_2_1EDLogWitness : LogWitness := ⟨-5, 42157, 31250⟩
def B2_2_4U1_2_1EDLog : Ball := ⟨(-316635453477610100398073168374679 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1EDLog_sound : B2_2_4U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U1_2_1D_sound) (w := B2_2_4U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U1_2_1ED : Ball := ⟨(13348400812255609002481570559171 / 100000000000000000000000000000000), (1071251039 / 20000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1ED_sound : B2_2_4U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U1_2_1D_sound) B2_2_4U1_2_1EDLog_sound) (by decide +kernel)
def B2_2_4U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 957843, 500000⟩
def B2_2_4U1_2_1EOneDLog : Ball := ⟨(-2153569876567388580629376620277 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1EOneDLog_sound : B2_2_4U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U1_2_1OneD_sound) (w := B2_2_4U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U1_2_1EOneD : Ball := ⟨(128923864455058573764736499381 / 3125000000000000000000000000000), (40566228969 / 100000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1EOneD_sound : B2_2_4U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U1_2_1OneD_sound) B2_2_4U1_2_1EOneDLog_sound) (by decide +kernel)
def B2_2_4U1_2_1BinaryEntropy : Ball := ⟨(10198032521952022401931681594393 / 50000000000000000000000000000000), (47707902563 / 100000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1BinaryEntropy_sound : B2_2_4U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U1_2_1EOneD_sound B2_2_4U1_2_1ED_sound)
    (Ball.mul_sound B2_2_4U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U1_2_1Leaf : Ball := ⟨(315102675079371637970947370752223 / 100000000000000000000000000000000), (62188407251 / 50000000000000000000000000000000)⟩
lemma B2_2_4U1_2_1Leaf_sound : B2_2_4U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1957843 / 1000000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 1 2 1) = (42157 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1957843 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_2_4U1_2_1Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma B2_2_4U1_2_1Mass_sound : B2_2_4U1_2_1Mass.Encloses (littleMass (shape 2 2 4) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 1 2 1))) (by decide +kernel)
def B2_2_4U2_0_2D : Ball := .exact (103577 / 1000000)
lemma B2_2_4U2_0_2D_sound : B2_2_4U2_0_2D.Encloses (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U2_0_2OneD : Ball := .exact (896423 / 1000000)
lemma B2_2_4U2_0_2OneD_sound : B2_2_4U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 2 0 2) = (103577 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((896423 / 1000000) : ℚ) using 1 <;> norm_num [B2_2_4U2_0_2OneD, Ball.exact]
def B2_2_4U2_0_2EDLogWitness : LogWitness := ⟨-4, 103577, 62500⟩
def B2_2_4U2_0_2EDLog : Ball := ⟨(-2834299976907655511632457381399 / 1250000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_0_2EDLog_sound : B2_2_4U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_0_2D_sound) (w := B2_2_4U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_0_2ED : Ball := ⟨(23485463096653138794268403055453 / 100000000000000000000000000000000), (10966641449 / 100000000000000000000000000000000)⟩
lemma B2_2_4U2_0_2ED_sound : B2_2_4U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_0_2D_sound) B2_2_4U2_0_2EDLog_sound) (by decide +kernel)
def B2_2_4U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 896423, 500000⟩
def B2_2_4U2_0_2EOneDLog : Ball := ⟨(-2733571979905550299613262420469 / 25000000000000000000000000000000), (8470329473 / 20000000000000000000000000000000)⟩
lemma B2_2_4U2_0_2EOneDLog_sound : B2_2_4U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_0_2OneD_sound) (w := B2_2_4U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_0_2EOneD : Ball := ⟨(306304599367859139528777442343 / 3125000000000000000000000000000), (37964990787 / 100000000000000000000000000000000)⟩
lemma B2_2_4U2_0_2EOneD_sound : B2_2_4U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_0_2OneD_sound) B2_2_4U2_0_2EOneDLog_sound) (by decide +kernel)
def B2_2_4U2_0_2BinaryEntropy : Ball := ⟨(40466620828510376790540144377003 / 100000000000000000000000000000000), (3332393051 / 6250000000000000000000000000000)⟩
lemma B2_2_4U2_0_2BinaryEntropy_sound : B2_2_4U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U2_0_2EOneD_sound B2_2_4U2_0_2ED_sound)
    (Ball.mul_sound B2_2_4U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U2_0_2Leaf : Ball := ⟨(32901405318409308881068737266019 / 10000000000000000000000000000000), (167213261177 / 100000000000000000000000000000000)⟩
lemma B2_2_4U2_0_2Leaf_sound : B2_2_4U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_2_4U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_2_4U2_0_2Mass : Ball := ⟨(973002741917034495619167964551 / 10000000000000000000000000000000), (1 / 781250000000000000000000000000)⟩
lemma B2_2_4U2_0_2Mass_sound : B2_2_4U2_0_2Mass.Encloses (littleMass (shape 2 2 4) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 2 0 2))) (by decide +kernel)
def B2_2_4U2_1_1D : Ball := .exact (8433 / 200000)
lemma B2_2_4U2_1_1D_sound : B2_2_4U2_1_1D.Encloses (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U2_1_1OneD : Ball := .exact (191567 / 200000)
lemma B2_2_4U2_1_1OneD_sound : B2_2_4U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 2 1 1) = (8433 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((191567 / 200000) : ℚ) using 1 <;> norm_num [B2_2_4U2_1_1OneD, Ball.exact]
def B2_2_4U2_1_1EDLogWitness : LogWitness := ⟨-5, 8433, 6250⟩
def B2_2_4U2_1_1EDLog : Ball := ⟨(-316616478595553215892035736909523 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1EDLog_sound : B2_2_4U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_1_1D_sound) (w := B2_2_4U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_1_1ED : Ball := ⟨(1335013381998150134808768684679 / 10000000000000000000000000000000), (2678635817 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1ED_sound : B2_2_4U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_1_1D_sound) B2_2_4U2_1_1EDLog_sound) (by decide +kernel)
def B2_2_4U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 191567, 100000⟩
def B2_2_4U2_1_1EOneDLog : Ball := ⟨(-4307974966568354882089913298341 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1EOneDLog_sound : B2_2_4U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_1_1OneD_sound) (w := B2_2_4U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_1_1EOneD : Ball := ⟨(1031582300525750049621648026029 / 25000000000000000000000000000000), (10141472539 / 25000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1EOneD_sound : B2_2_4U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_1_1OneD_sound) B2_2_4U2_1_1EOneDLog_sound) (by decide +kernel)
def B2_2_4U2_1_1BinaryEntropy : Ball := ⟨(20399118108915510943732037385873 / 100000000000000000000000000000000), (23854459501 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1BinaryEntropy_sound : B2_2_4U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U2_1_1EOneD_sound B2_2_4U2_1_1ED_sound)
    (Ball.mul_sound B2_2_4U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U2_1_1Leaf : Ball := ⟨(157550693764520845345323845072531 / 50000000000000000000000000000000), (62188153141 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_1_1Leaf_sound : B2_2_4U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (391567 / 200000)).Encloses (2 - (binaryParameter (shape 2 2 4) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 2 4) (shape 2 1 1) = (8433 / 200000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((391567 / 200000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_2_4U2_1_1Mass : Ball := ⟨(1246537282943313726061518292613 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
lemma B2_2_4U2_1_1Mass_sound : B2_2_4U2_1_1Mass.Encloses (littleMass (shape 2 2 4) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 2 1 1))) (by decide +kernel)
def B2_2_4U2_2_0D : Ball := .exact (31791 / 500000)
lemma B2_2_4U2_2_0D_sound : B2_2_4U2_2_0D.Encloses (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_2_4U2_2_0OneD : Ball := .exact (468209 / 500000)
lemma B2_2_4U2_2_0OneD_sound : B2_2_4U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 2 4) (shape 2 2 0) = (31791 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((468209 / 500000) : ℚ) using 1 <;> norm_num [B2_2_4U2_2_0OneD, Ball.exact]
def B2_2_4U2_2_0EDLogWitness : LogWitness := ⟨-4, 31791, 31250⟩
def B2_2_4U2_2_0EDLog : Ball := ⟨(-8610702711129322182939633075951 / 3125000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0EDLog_sound : B2_2_4U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_2_0D_sound) (w := B2_2_4U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_2_0ED : Ball := ⟨(4379885598232196504285342001881 / 25000000000000000000000000000000), (1683001527 / 25000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0ED_sound : B2_2_4U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_2_0D_sound) B2_2_4U2_2_0EDLog_sound) (by decide +kernel)
def B2_2_4U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 468209, 250000⟩
def B2_2_4U2_2_0EOneDLog : Ball := ⟨(-1642333024891709491091130987267 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0EOneDLog_sound : B2_2_4U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_2_4U2_2_0OneD_sound) (w := B2_2_4U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_2_4U2_2_0EOneD : Ball := ⟨(3075820413006089636457149393669 / 50000000000000000000000000000000), (9914711231 / 25000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0EOneD_sound : B2_2_4U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 2 4) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_2_4U2_2_0OneD_sound) B2_2_4U2_2_0EOneDLog_sound) (by decide +kernel)
def B2_2_4U2_2_0BinaryEntropy : Ball := ⟨(7019587905594302389098077713847 / 25000000000000000000000000000000), (1963346139 / 4000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0BinaryEntropy_sound : B2_2_4U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 2 4) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_2_4U2_2_0EOneD_sound B2_2_4U2_2_0ED_sound)
    (Ball.mul_sound B2_2_4U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B2_2_4U2_2_0Leaf : Ball := ⟨(82374919459880072618242752497539 / 25000000000000000000000000000000), (33612037649 / 20000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0Leaf_sound : B2_2_4U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_2_4U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_2_4U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B2_2_4U2_2_0Mass : Ball := ⟨(459983845027779558302590723 / 3125000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B2_2_4U2_2_0Mass_sound : B2_2_4U2_2_0Mass.Encloses (littleMass (shape 2 2 4) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_2_4))
    (B2_2_4Law_sound (shape 2 2 0))) (by decide +kernel)
def B2_2_4Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_2_4U0_0_4Leaf
  | 0, 1, 3 => B2_2_4U0_1_3Leaf
  | 0, 2, 2 => B2_2_4U0_2_2Leaf
  | 1, 0, 3 => B2_2_4U1_0_3Leaf
  | 1, 1, 2 => B2_2_4U1_1_2Leaf
  | 1, 2, 1 => B2_2_4U1_2_1Leaf
  | 2, 0, 2 => B2_2_4U2_0_2Leaf
  | 2, 1, 1 => B2_2_4U2_1_1Leaf
  | 2, 2, 0 => B2_2_4U2_2_0Leaf
  | _, _, _ => (.exact 0)
lemma B2_2_4Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 2 4)) :
    (B2_2_4Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 2 4) u) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_2_4U0_0_4Leaf_sound
  · exact B2_2_4U0_1_3Leaf_sound
  · exact B2_2_4U0_2_2Leaf_sound
  · exact B2_2_4U1_0_3Leaf_sound
  · exact B2_2_4U1_1_2Leaf_sound
  · exact B2_2_4U1_2_1Leaf_sound
  · exact B2_2_4U2_0_2Leaf_sound
  · exact B2_2_4U2_1_1Leaf_sound
  · exact B2_2_4U2_2_0Leaf_sound
def B2_2_4Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B2_2_4U0_0_4Mass
  | 0, 1, 3 => B2_2_4U0_1_3Mass
  | 0, 2, 2 => B2_2_4U0_2_2Mass
  | 1, 0, 3 => B2_2_4U1_0_3Mass
  | 1, 1, 2 => B2_2_4U1_1_2Mass
  | 1, 2, 1 => B2_2_4U1_2_1Mass
  | 2, 0, 2 => B2_2_4U2_0_2Mass
  | 2, 1, 1 => B2_2_4U2_1_1Mass
  | 2, 2, 0 => B2_2_4U2_2_0Mass
  | _, _, _ => (.exact 0)
lemma B2_2_4Masses_sound (u : Shape) (hu : u ∈ below (shape 2 2 4)) :
    (B2_2_4Masses u).Encloses ((fun u => (littleMass (shape 2 2 4) u : ℝ)) u) := by
  rw [B2_2_4_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_2_4U0_0_4Mass_sound
  · exact B2_2_4U0_1_3Mass_sound
  · exact B2_2_4U0_2_2Mass_sound
  · exact B2_2_4U1_0_3Mass_sound
  · exact B2_2_4U1_1_2Mass_sound
  · exact B2_2_4U1_2_1Mass_sound
  · exact B2_2_4U2_0_2Mass_sound
  · exact B2_2_4U2_1_1Mass_sound
  · exact B2_2_4U2_2_0Mass_sound
def B2_2_4Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_2_4U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_2_4U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_2_4U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_2_4U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_2_4U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_2_4U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B2_2_4Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 2 4)).filter positive) :
    (B2_2_4Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 2 4) u)) u) := by
  have hl : (below (shape 2 2 4)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B2_2_4U1_1_2BinaryEntropy_sound
  · exact B2_2_4U1_2_1BinaryEntropy_sound
  · exact B2_2_4U2_1_1BinaryEntropy_sound
def B2_2_4S2 : Ball := ⟨(2096023073863630218761879684683 / 1000000000000000000000000000000), (89698574533 / 100000000000000000000000000000000)⟩
lemma B2_2_4S2_sound : B2_2_4S2.Encloses
    (((below (shape 2 2 4)).map fun u => (littleMass (shape 2 2 4) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 2 4) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 2 4))
    (fun u => .mul (B2_2_4Masses u) (B2_2_4Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_2_4Masses_sound u hu) (B2_2_4Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
