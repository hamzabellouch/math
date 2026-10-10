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
lemma B2_4_2_below : below (shape 2 4 2) = [
  (shape 0 2 2),
  (shape 0 3 1),
  (shape 0 4 0),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 1 3 0),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0)] := by decide +kernel
def B2_4_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(131106254622443168152919965261 / 500000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(887034541322513256023482129547 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(59473180615091031899554539751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1420107074792739577725554863013 / 20000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨1, 0⟩
  | 1, 3, 0 => ⟨(1420107074792739577725554863013 / 20000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(59473180615091031899554539751 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(887034541322513256023482129547 / 12500000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(131106254622443168152919965261 / 500000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_4_2Raw_0_2_2 : (B2_4_2Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 0 2 2)
    (-6696) (0) (-6690) w150 w195 w152
    (by decide +kernel) w150_sound w195_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_0_3_1 : (B2_4_2Raw (shape 0 3 1)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 0 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 0 3 1)
    (-6696) (-19760) (0) w150 w87 w195
    (by decide +kernel) w150_sound w87_sound w195_sound) (by decide +kernel)
lemma B2_4_2Raw_0_4_0 : (B2_4_2Raw (shape 0 4 0)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 0 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 0 4 0)
    (-6696) (-60888) (-6690) w150 w20 w152
    (by decide +kernel) w150_sound w20_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_1_1_2 : (B2_4_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 1 1 2)
    (0) (-19760) (-6690) w195 w87 w152
    (by decide +kernel) w195_sound w87_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_1_2_1 : (B2_4_2Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 1 2 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B2_4_2Raw_1_3_0 : (B2_4_2Raw (shape 1 3 0)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 1 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 1 3 0)
    (0) (-19760) (-6690) w195 w87 w152
    (by decide +kernel) w195_sound w87_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_2_0_2 : (B2_4_2Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 2 0 2)
    (-6696) (-60888) (-6690) w150 w20 w152
    (by decide +kernel) w150_sound w20_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_2_1_1 : (B2_4_2Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 2 1 1)
    (-6696) (-19760) (0) w150 w87 w195
    (by decide +kernel) w150_sound w87_sound w195_sound) (by decide +kernel)
lemma B2_4_2Raw_2_2_0 : (B2_4_2Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 2 4 2) (shape 2 2 0)
    (-6696) (0) (-6690) w150 w195 w152
    (by decide +kernel) w150_sound w195_sound w152_sound) (by decide +kernel)
lemma B2_4_2Raw_sound (u : Shape) (hu : u ∈ below (shape 2 4 2)) :
    (B2_4_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 2 4 2) u : ℝ) := by
  rw [B2_4_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_4_2Raw_0_2_2
  · exact B2_4_2Raw_0_3_1
  · exact B2_4_2Raw_0_4_0
  · exact B2_4_2Raw_1_1_2
  · exact B2_4_2Raw_1_2_1
  · exact B2_4_2Raw_1_3_0
  · exact B2_4_2Raw_2_0_2
  · exact B2_4_2Raw_2_1_1
  · exact B2_4_2Raw_2_2_0
def B2_4_2Den : Ball := ⟨(2827422994051485268728099341981 / 1562500000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
lemma B2_4_2Den_sound : B2_4_2Den.Encloses (((below (shape 2 4 2)).map (splitWeight positiveSecond tablep (shape 2 4 2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 4 2)) B2_4_2Raw (splitWeight positiveSecond tablep (shape 2 4 2)) B2_4_2Raw_sound) (by decide +kernel)
lemma B2_4_2Den_positive : 0 < B2_4_2Den.lower := by decide +kernel
def B2_4_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(14490475834606388578250612343089 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 0, 3, 1 => ⟨(3921568081556569782136761397233 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 4, 0 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3923921728428956034133711412569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(6907792021600978205615474676497 / 12500000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(3923921728428956034133711412569 / 100000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(3921568081556569782136761397233 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(14490475834606388578250612343089 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B2_4_2Law (u : Shape) : Ball := if u ∈ below (shape 2 4 2) then B2_4_2Table u else .exact 0
lemma B2_4_2Law_check_0_2_2 : contains (.mul (B2_4_2Raw (shape 0 2 2)) (.inv B2_4_2Den)) (B2_4_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B2_4_2Law_check_0_3_1 : contains (.mul (B2_4_2Raw (shape 0 3 1)) (.inv B2_4_2Den)) (B2_4_2Table (shape 0 3 1)) = true := by decide +kernel
lemma B2_4_2Law_check_0_4_0 : contains (.mul (B2_4_2Raw (shape 0 4 0)) (.inv B2_4_2Den)) (B2_4_2Table (shape 0 4 0)) = true := by decide +kernel
lemma B2_4_2Law_check_1_1_2 : contains (.mul (B2_4_2Raw (shape 1 1 2)) (.inv B2_4_2Den)) (B2_4_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B2_4_2Law_check_1_2_1 : contains (.mul (B2_4_2Raw (shape 1 2 1)) (.inv B2_4_2Den)) (B2_4_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B2_4_2Law_check_1_3_0 : contains (.mul (B2_4_2Raw (shape 1 3 0)) (.inv B2_4_2Den)) (B2_4_2Table (shape 1 3 0)) = true := by decide +kernel
lemma B2_4_2Law_check_2_0_2 : contains (.mul (B2_4_2Raw (shape 2 0 2)) (.inv B2_4_2Den)) (B2_4_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B2_4_2Law_check_2_1_1 : contains (.mul (B2_4_2Raw (shape 2 1 1)) (.inv B2_4_2Den)) (B2_4_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B2_4_2Law_check_2_2_0 : contains (.mul (B2_4_2Raw (shape 2 2 0)) (.inv B2_4_2Den)) (B2_4_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B2_4_2Law_check (u : Shape) (hu : u ∈ below (shape 2 4 2)) :
    contains (.mul (B2_4_2Raw u) (.inv B2_4_2Den)) (B2_4_2Table u) = true := by
  rw [B2_4_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_4_2Law_check_0_2_2
  · exact B2_4_2Law_check_0_3_1
  · exact B2_4_2Law_check_0_4_0
  · exact B2_4_2Law_check_1_1_2
  · exact B2_4_2Law_check_1_2_1
  · exact B2_4_2Law_check_1_3_0
  · exact B2_4_2Law_check_2_0_2
  · exact B2_4_2Law_check_2_1_1
  · exact B2_4_2Law_check_2_2_0
lemma B2_4_2Law_sound (u : Shape) :
    (B2_4_2Law u).Encloses (stageBLaw (shape 2 4 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 4 2)
  · have h := contains_sound (Ball.mul_sound (B2_4_2Raw_sound u hu)
      (Ball.inv_sound B2_4_2Den_sound B2_4_2Den_positive)) (B2_4_2Law_check u hu)
    simpa only [B2_4_2Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B2_4_2Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B2_4_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (104793 / 1000000)
  | 1, 1, 2 => (21063 / 500000)
  | 1, 2, 1 => (5907 / 500000)
  | 2, 0, 2 => (31669 / 500000)
  | 2, 1, 1 => (8433 / 200000)
  | 2, 2, 0 => (3277 / 31250)
  | _, _, _ => 0
lemma B2_4_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 2 4 2) u = B2_4_2Binary u := by
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
def B2_4_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B2_4_2Binary u else if i = 3 then B2_4_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B2_4_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B2_4_2LittleRat u w i)
  else .exact (littleLaw (shape 2 4 2) u w i)

lemma B2_4_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B2_4_2Little u w i).Encloses (littleLaw (shape 2 4 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B2_4_2Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B2_4_2LittleRat, littleLaw, B2_4_2Binary_eq u hu]
  · simp only [B2_4_2Little, hu, ite_false]
    exact Ball.exact_sound _
def B2_4_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 2 => ⟨(16757946325341947750940189356037 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 0, 3 => ⟨(843481929912591696232100262703 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 1, 1 => ⟨(31555089814832868856595610118557 / 50000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 0, 2, 0 => ⟨(16757946325341947750940189356037 / 100000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 0, 3, 0 => ⟨(843481929912591696232100262703 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 2, 2 => ⟨(38593837517531901492832074284017 / 50000000000000000000000000000000), (73 / 50000000000000000000000000000000)⟩
  | 1, 2, 3 => ⟨(84117846883879413836036378887 / 2500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 2 => ⟨(84117846883879413836036378887 / 2500000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 3 => ⟨(8154626406161167721949080479 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 4, 1 => ⟨(3922744904992762908135236404901 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 5, 0 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 4 => ⟨(3922744904992762908135236404901 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 0, 5 => ⟨(32866269004172783017016141121 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(16761382587425625619496074982197 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(842940622306945887952632457291 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(31552736167960482604598660103221 / 50000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(16761382587425625619496074982197 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(842940622306945887952632457291 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B2_4_2Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((0 : Fin 6),j)) (B2_4_2Half 0 (0,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((1 : Fin 6),j)) (B2_4_2Half 0 (1,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((2 : Fin 6),j)) (B2_4_2Half 0 (2,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((3 : Fin 6),j)) (B2_4_2Half 0 (3,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((4 : Fin 6),j)) (B2_4_2Half 0 (4,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 0) ((5 : Fin 6),j)) (B2_4_2Half 0 (5,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((0 : Fin 6),j)) (B2_4_2Half 1 (0,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((1 : Fin 6),j)) (B2_4_2Half 1 (1,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((2 : Fin 6),j)) (B2_4_2Half 1 (2,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((3 : Fin 6),j)) (B2_4_2Half 1 (3,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((4 : Fin 6),j)) (B2_4_2Half 1 (4,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 1) ((5 : Fin 6),j)) (B2_4_2Half 1 (5,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((0 : Fin 6),j)) (B2_4_2Half 2 (0,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((1 : Fin 6),j)) (B2_4_2Half 2 (1,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((2 : Fin 6),j)) (B2_4_2Half 2 (2,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((3 : Fin 6),j)) (B2_4_2Half 2 (3,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((4 : Fin 6),j)) (B2_4_2Half 2 (4,j)) = true := by
  decide +kernel
lemma B2_4_2Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u 2) ((5 : Fin 6),j)) (B2_4_2Half 2 (5,j)) = true := by
  decide +kernel
lemma B2_4_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (B2_4_2Half w ij).Encloses (halfLaw (shape 2 4 2) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 2 4 2)) (shape 2 4 2) B2_4_2Law
      (fun u => B2_4_2Little u w) ij) (B2_4_2Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B2_4_2Half_check_0_0 j) (B2_4_2Half_check_0_1 j) (B2_4_2Half_check_0_2 j) (B2_4_2Half_check_0_3 j) (B2_4_2Half_check_0_4 j) (B2_4_2Half_check_0_5 j)
    · exact forall_fin6 (B2_4_2Half_check_1_0 j) (B2_4_2Half_check_1_1 j) (B2_4_2Half_check_1_2 j) (B2_4_2Half_check_1_3 j) (B2_4_2Half_check_1_4 j) (B2_4_2Half_check_1_5 j)
    · exact forall_fin6 (B2_4_2Half_check_2_0 j) (B2_4_2Half_check_2_1 j) (B2_4_2Half_check_2_2 j) (B2_4_2Half_check_2_3 j) (B2_4_2Half_check_2_4 j) (B2_4_2Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 2 4 2)) (shape 2 4 2)
    B2_4_2Law (fun u => (stageBLaw (shape 2 4 2) u : ℝ))
    (fun u => B2_4_2Little u w) (fun u i => (littleLaw (shape 2 4 2) u w i : ℝ))
    (fun u _ => B2_4_2Law_sound u) (fun u i => B2_4_2Little_sound u w i) ij) hcheck
  have hp : positive (shape 2 4 2) = true := by decide +kernel
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
def B2_4_2U0_2_2D : Ball := .exact (104793 / 1000000)
lemma B2_4_2U0_2_2D_sound : B2_4_2U0_2_2D.Encloses (binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U0_2_2OneD : Ball := .exact (895207 / 1000000)
lemma B2_4_2U0_2_2OneD_sound : B2_4_2U0_2_2OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 0 2 2) = (104793 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((895207 / 1000000) : ℚ) using 1 <;> norm_num [B2_4_2U0_2_2OneD, Ball.exact]
def B2_4_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 104793, 62500⟩
def B2_4_2U0_2_2EDLog : Ball := ⟨(-22557683032191364513180248834139 / 10000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_4_2U0_2_2EDLog_sound : B2_4_2U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U0_2_2D_sound) (w := B2_4_2U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U0_2_2ED : Ball := ⟨(23638872779924296614296978160759 / 100000000000000000000000000000000), (11095390457 / 100000000000000000000000000000000)⟩
lemma B2_4_2U0_2_2ED_sound : B2_4_2U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U0_2_2D_sound) B2_4_2U0_2_2EDLog_sound) (by decide +kernel)
def B2_4_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 895207, 500000⟩
def B2_4_2U0_2_2EOneDLog : Ball := ⟨(-22140060506662698219615744903 / 200000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U0_2_2EOneDLog_sound : B2_4_2U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U0_2_2OneD_sound) (w := B2_4_2U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U0_2_2EOneD : Ball := ⟨(990996857299399704254377607369 / 10000000000000000000000000000000), (2369593199 / 6250000000000000000000000000000)⟩
lemma B2_4_2U0_2_2EOneD_sound : B2_4_2U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U0_2_2OneD_sound) B2_4_2U0_2_2EOneDLog_sound) (by decide +kernel)
def B2_4_2U0_2_2BinaryEntropy : Ball := ⟨(10203134650540032134454188200943 / 25000000000000000000000000000000), (417554983 / 781250000000000000000000000000)⟩
lemma B2_4_2U0_2_2BinaryEntropy_sound : B2_4_2U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U0_2_2EOneD_sound B2_4_2U0_2_2ED_sound)
    (Ball.mul_sound B2_4_2U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U0_2_2Leaf : Ball := ⟨(328968555657438867346861076509999 / 100000000000000000000000000000000), (1337500091 / 800000000000000000000000000000)⟩
lemma B2_4_2U0_2_2Leaf_sound : B2_4_2U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_4_2U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_4_2U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_4_2U0_2_2Mass : Ball := ⟨(2052429189538757016962171971651 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
lemma B2_4_2U0_2_2Mass_sound : B2_4_2U0_2_2Mass.Encloses (littleMass (shape 2 4 2) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 0 2 2))) (by decide +kernel)
def B2_4_2U0_3_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_4_2U0_3_1Leaf_sound : B2_4_2U0_3_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 0 3 1)) := by
  have hh : shapeMax (shape 0 3 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_4_2U0_3_1Mass : Ball := ⟨(27772520692964670763404186047 / 5000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B2_4_2U0_3_1Mass_sound : B2_4_2U0_3_1Mass.Encloses (littleMass (shape 2 4 2) (shape 0 3 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 0 3 1))) (by decide +kernel)
def B2_4_2U0_4_0Leaf : Ball := ⟨0, 0⟩
lemma B2_4_2U0_4_0Leaf_sound : B2_4_2U0_4_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 0 4 0)) := by
  have hh : shapeMax (shape 0 4 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B2_4_2U0_4_0Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B2_4_2U0_4_0Mass : Ball := ⟨(2327587120855560415853758489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_4_2U0_4_0Mass_sound : B2_4_2U0_4_0Mass.Encloses (littleMass (shape 2 4 2) (shape 0 4 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 0 4 0))) (by decide +kernel)
def B2_4_2U1_1_2D : Ball := .exact (21063 / 500000)
lemma B2_4_2U1_1_2D_sound : B2_4_2U1_1_2D.Encloses (binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U1_1_2OneD : Ball := .exact (478937 / 500000)
lemma B2_4_2U1_1_2OneD_sound : B2_4_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 1 1 2) = (21063 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478937 / 500000) : ℚ) using 1 <;> norm_num [B2_4_2U1_1_2OneD, Ball.exact]
def B2_4_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 21063, 15625⟩
def B2_4_2U1_1_2EDLog : Ball := ⟨(-316709015171897026732453267991509 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2EDLog_sound : B2_4_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U1_1_2D_sound) (w := B2_4_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U1_1_2ED : Ball := ⟨(1334168397313133414813132636741 / 10000000000000000000000000000000), (1338079123 / 25000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2ED_sound : B2_4_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U1_1_2D_sound) B2_4_2U1_1_2EDLog_sound) (by decide +kernel)
def B2_4_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 478937, 250000⟩
def B2_4_2U1_1_2EOneDLog : Ball := ⟨(-2151951683483404577051660903857 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2EOneDLog_sound : B2_4_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U1_1_2OneD_sound) (w := B2_4_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U1_1_2EOneD : Ball := ⟨(2061298566864982675838782636621 / 50000000000000000000000000000000), (4056754187 / 10000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2EOneD_sound : B2_4_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U1_1_2OneD_sound) B2_4_2U1_1_2EOneDLog_sound) (by decide +kernel)
def B2_4_2U1_1_2BinaryEntropy : Ball := ⟨(2038423291968812511025992287109 / 10000000000000000000000000000000), (2385198193 / 5000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2BinaryEntropy_sound : B2_4_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U1_1_2EOneD_sound B2_4_2U1_1_2ED_sound)
    (Ball.mul_sound B2_4_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U1_1_2Leaf : Ball := ⟨(78776916084225045920527158276243 / 25000000000000000000000000000000), (124378783853 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2Leaf_sound : B2_4_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978937 / 500000)).Encloses (2 - (binaryParameter (shape 2 4 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 2 4 2) (shape 1 1 2) = (21063 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978937 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_4_2U1_1_2Mass : Ball := ⟨(111156756821736540136239317403 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_1_2Mass_sound : B2_4_2U1_1_2Mass.Encloses (littleMass (shape 2 4 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 1 1 2))) (by decide +kernel)
def B2_4_2U1_2_1D : Ball := .exact (5907 / 500000)
lemma B2_4_2U1_2_1D_sound : B2_4_2U1_2_1D.Encloses (binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U1_2_1OneD : Ball := .exact (494093 / 500000)
lemma B2_4_2U1_2_1OneD_sound : B2_4_2U1_2_1OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 1 2 1) = (5907 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((494093 / 500000) : ℚ) using 1 <;> norm_num [B2_4_2U1_2_1OneD, Ball.exact]
def B2_4_2U1_2_1EDLogWitness : LogWitness := ⟨-7, 23628, 15625⟩
def B2_4_2U1_2_1EDLog : Ball := ⟨(-443847001009709356305572202505481 / 100000000000000000000000000000000), (21175823683 / 12500000000000000000000000000000)⟩
lemma B2_4_2U1_2_1EDLog_sound : B2_4_2U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U1_2_1D_sound) (w := B2_4_2U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U1_2_1ED : Ball := ⟨(13109021174821765838485075001 / 250000000000000000000000000000), (2001369449 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1ED_sound : B2_4_2U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U1_2_1D_sound) B2_4_2U1_2_1EDLog_sound) (by decide +kernel)
def B2_4_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 494093, 250000⟩
def B2_4_2U1_2_1EOneDLog : Ball := ⟨(-594216992173993420750540540271 / 50000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1EOneDLog_sound : B2_4_2U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U1_2_1OneD_sound) (w := B2_4_2U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U1_2_1EOneD : Ball := ⟨(73399614078556232809724206791 / 6250000000000000000000000000000), (8370261001 / 20000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1EOneD_sound : B2_4_2U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U1_2_1OneD_sound) B2_4_2U1_2_1EOneDLog_sound) (by decide +kernel)
def B2_4_2U1_2_1BinaryEntropy : Ball := ⟨(7236886374299125448895135111753 / 100000000000000000000000000000000), (44353016817 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1BinaryEntropy_sound : B2_4_2U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U1_2_1EOneD_sound B2_4_2U1_2_1ED_sound)
    (Ball.mul_sound B2_4_2U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U1_2_1Leaf : Ball := ⟨(319986192537070428737598453638203 / 100000000000000000000000000000000), (31576107139 / 25000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1Leaf_sound : B2_4_2U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (994093 / 500000)).Encloses (2 - (binaryParameter (shape 2 4 2) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 2 4 2) (shape 1 2 1) = (5907 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((994093 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_4_2U1_2_1Mass : Ball := ⟨(7827350401585707164473237434991 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_2_1Mass_sound : B2_4_2U1_2_1Mass.Encloses (littleMass (shape 2 4 2) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 1 2 1))) (by decide +kernel)
def B2_4_2U1_3_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B2_4_2U1_3_0Leaf_sound : B2_4_2U1_3_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 1 3 0)) := by
  have hh : shapeMax (shape 1 3 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B2_4_2U1_3_0Mass : Ball := ⟨(111156756821736540136239317403 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B2_4_2U1_3_0Mass_sound : B2_4_2U1_3_0Mass.Encloses (littleMass (shape 2 4 2) (shape 1 3 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 1 3 0))) (by decide +kernel)
def B2_4_2U2_0_2D : Ball := .exact (31669 / 500000)
lemma B2_4_2U2_0_2D_sound : B2_4_2U2_0_2D.Encloses (binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U2_0_2OneD : Ball := .exact (468331 / 500000)
lemma B2_4_2U2_0_2OneD_sound : B2_4_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 2 0 2) = (31669 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((468331 / 500000) : ℚ) using 1 <;> norm_num [B2_4_2U2_0_2OneD, Ball.exact]
def B2_4_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 31669, 31250⟩
def B2_4_2U2_0_2EDLog : Ball := ⟨(-275926981399378237867248750022457 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2EDLog_sound : B2_4_2U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_0_2D_sound) (w := B2_4_2U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_0_2ED : Ball := ⟨(8738331573936909415017900664461 / 50000000000000000000000000000000), (6706171603 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2ED_sound : B2_4_2U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_0_2D_sound) B2_4_2U2_0_2EDLog_sound) (by decide +kernel)
def B2_4_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 468331, 250000⟩
def B2_4_2U2_0_2EOneDLog : Ball := ⟨(-817909844265902747909981412881 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2EOneDLog_sound : B2_4_2U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_0_2OneD_sound) (w := B2_4_2U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_0_2EOneD : Ball := ⟨(95763133818723624957857376269 / 1562500000000000000000000000000), (19834589363 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2EOneD_sound : B2_4_2U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_0_2OneD_sound) B2_4_2U2_0_2EOneDLog_sound) (by decide +kernel)
def B2_4_2U2_0_2BinaryEntropy : Ball := ⟨(699893983112567810703138425289 / 2500000000000000000000000000000), (49057818971 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2BinaryEntropy_sound : B2_4_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U2_0_2EOneD_sound B2_4_2U2_0_2ED_sound)
    (Ball.mul_sound B2_4_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U2_0_2Leaf : Ball := ⟨(20593476631985786090186547073947 / 6250000000000000000000000000000), (168065355147 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2Leaf_sound : B2_4_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_4_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_4_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B2_4_2U2_0_2Mass : Ball := ⟨(2327587120855560415853758489 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_0_2Mass_sound : B2_4_2U2_0_2Mass.Encloses (littleMass (shape 2 4 2) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 2 0 2))) (by decide +kernel)
def B2_4_2U2_1_1D : Ball := .exact (8433 / 200000)
lemma B2_4_2U2_1_1D_sound : B2_4_2U2_1_1D.Encloses (binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U2_1_1OneD : Ball := .exact (191567 / 200000)
lemma B2_4_2U2_1_1OneD_sound : B2_4_2U2_1_1OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 2 1 1) = (8433 / 200000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((191567 / 200000) : ℚ) using 1 <;> norm_num [B2_4_2U2_1_1OneD, Ball.exact]
def B2_4_2U2_1_1EDLogWitness : LogWitness := ⟨-5, 8433, 6250⟩
def B2_4_2U2_1_1EDLog : Ball := ⟨(-316616478595553215892035736909523 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1EDLog_sound : B2_4_2U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_1_1D_sound) (w := B2_4_2U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_1_1ED : Ball := ⟨(1335013381998150134808768684679 / 10000000000000000000000000000000), (2678635817 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1ED_sound : B2_4_2U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_1_1D_sound) B2_4_2U2_1_1EDLog_sound) (by decide +kernel)
def B2_4_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 191567, 100000⟩
def B2_4_2U2_1_1EOneDLog : Ball := ⟨(-4307974966568354882089913298341 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1EOneDLog_sound : B2_4_2U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_1_1OneD_sound) (w := B2_4_2U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_1_1EOneD : Ball := ⟨(1031582300525750049621648026029 / 25000000000000000000000000000000), (10141472539 / 25000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1EOneD_sound : B2_4_2U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_1_1OneD_sound) B2_4_2U2_1_1EOneDLog_sound) (by decide +kernel)
def B2_4_2U2_1_1BinaryEntropy : Ball := ⟨(20399118108915510943732037385873 / 100000000000000000000000000000000), (23854459501 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1BinaryEntropy_sound : B2_4_2U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U2_1_1EOneD_sound B2_4_2U2_1_1ED_sound)
    (Ball.mul_sound B2_4_2U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U2_1_1Leaf : Ball := ⟨(157550693764520845345323845072531 / 50000000000000000000000000000000), (62188153141 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1Leaf_sound : B2_4_2U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (391567 / 200000)).Encloses (2 - (binaryParameter (shape 2 4 2) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 2 4 2) (shape 2 1 1) = (8433 / 200000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((391567 / 200000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B2_4_2U2_1_1Mass : Ball := ⟨(27772520692964670763404186047 / 5000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_1_1Mass_sound : B2_4_2U2_1_1Mass.Encloses (littleMass (shape 2 4 2) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 2 1 1))) (by decide +kernel)
def B2_4_2U2_2_0D : Ball := .exact (3277 / 31250)
lemma B2_4_2U2_2_0D_sound : B2_4_2U2_2_0D.Encloses (binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B2_4_2U2_2_0OneD : Ball := .exact (27973 / 31250)
lemma B2_4_2U2_2_0OneD_sound : B2_4_2U2_2_0OneD.Encloses (1 - (binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 2 4 2) (shape 2 2 0) = (3277 / 31250) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((27973 / 31250) : ℚ) using 1 <;> norm_num [B2_4_2U2_2_0OneD, Ball.exact]
def B2_4_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 26216, 15625⟩
def B2_4_2U2_2_0EDLog : Ball := ⟨(-56377275161643324031409595775453 / 25000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0EDLog_sound : B2_4_2U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_2_0D_sound) (w := B2_4_2U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_2_0ED : Ball := ⟨(5911946582550565531229735851397 / 25000000000000000000000000000000), (5551453937 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0ED_sound : B2_4_2U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_2_0D_sound) B2_4_2U2_2_0EDLog_sound) (by decide +kernel)
def B2_4_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 27973, 15625⟩
def B2_4_2U2_2_0EOneDLog : Ball := ⟨(-2769490423601434424009732717579 / 25000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0EOneDLog_sound : B2_4_2U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B2_4_2U2_2_0OneD_sound) (w := B2_4_2U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B2_4_2U2_2_0EOneD : Ball := ⟨(9916282319283574418281504423531 / 100000000000000000000000000000000), (37910484217 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0EOneD_sound : B2_4_2U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 2 4 2) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B2_4_2U2_2_0OneD_sound) B2_4_2U2_2_0EOneDLog_sound) (by decide +kernel)
def B2_4_2U2_2_0BinaryEntropy : Ball := ⟨(40832687243709647035873308745149 / 100000000000000000000000000000000), (53454555241 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0BinaryEntropy_sound : B2_4_2U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 2 4 2) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B2_4_2U2_2_0EOneD_sound B2_4_2U2_2_0ED_sound)
    (Ball.mul_sound B2_4_2U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B2_4_2U2_2_0Leaf : Ball := ⟨(82241462570157955404899575418567 / 25000000000000000000000000000000), (41796501973 / 25000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0Leaf_sound : B2_4_2U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B2_4_2U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B2_4_2U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B2_4_2U2_2_0Mass : Ball := ⟨(2052429189538757016962171971651 / 100000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
lemma B2_4_2U2_2_0Mass_sound : B2_4_2U2_2_0Mass.Encloses (littleMass (shape 2 4 2) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_2_4_2))
    (B2_4_2Law_sound (shape 2 2 0))) (by decide +kernel)
def B2_4_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2Leaf
  | 0, 3, 1 => B2_4_2U0_3_1Leaf
  | 0, 4, 0 => B2_4_2U0_4_0Leaf
  | 1, 1, 2 => B2_4_2U1_1_2Leaf
  | 1, 2, 1 => B2_4_2U1_2_1Leaf
  | 1, 3, 0 => B2_4_2U1_3_0Leaf
  | 2, 0, 2 => B2_4_2U2_0_2Leaf
  | 2, 1, 1 => B2_4_2U2_1_1Leaf
  | 2, 2, 0 => B2_4_2U2_2_0Leaf
  | _, _, _ => (.exact 0)
lemma B2_4_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 2 4 2)) :
    (B2_4_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 2 4 2) u) := by
  rw [B2_4_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_4_2U0_2_2Leaf_sound
  · exact B2_4_2U0_3_1Leaf_sound
  · exact B2_4_2U0_4_0Leaf_sound
  · exact B2_4_2U1_1_2Leaf_sound
  · exact B2_4_2U1_2_1Leaf_sound
  · exact B2_4_2U1_3_0Leaf_sound
  · exact B2_4_2U2_0_2Leaf_sound
  · exact B2_4_2U2_1_1Leaf_sound
  · exact B2_4_2U2_2_0Leaf_sound
def B2_4_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2Mass
  | 0, 3, 1 => B2_4_2U0_3_1Mass
  | 0, 4, 0 => B2_4_2U0_4_0Mass
  | 1, 1, 2 => B2_4_2U1_1_2Mass
  | 1, 2, 1 => B2_4_2U1_2_1Mass
  | 1, 3, 0 => B2_4_2U1_3_0Mass
  | 2, 0, 2 => B2_4_2U2_0_2Mass
  | 2, 1, 1 => B2_4_2U2_1_1Mass
  | 2, 2, 0 => B2_4_2U2_2_0Mass
  | _, _, _ => (.exact 0)
lemma B2_4_2Masses_sound (u : Shape) (hu : u ∈ below (shape 2 4 2)) :
    (B2_4_2Masses u).Encloses ((fun u => (littleMass (shape 2 4 2) u : ℝ)) u) := by
  rw [B2_4_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B2_4_2U0_2_2Mass_sound
  · exact B2_4_2U0_3_1Mass_sound
  · exact B2_4_2U0_4_0Mass_sound
  · exact B2_4_2U1_1_2Mass_sound
  · exact B2_4_2U1_2_1Mass_sound
  · exact B2_4_2U1_3_0Mass_sound
  · exact B2_4_2U2_0_2Mass_sound
  · exact B2_4_2U2_1_1Mass_sound
  · exact B2_4_2U2_2_0Mass_sound
def B2_4_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B2_4_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B2_4_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B2_4_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B2_4_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B2_4_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B2_4_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B2_4_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 2 4 2)).filter positive) :
    (B2_4_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 2 4 2) u)) u) := by
  have hl : (below (shape 2 4 2)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B2_4_2U1_1_2BinaryEntropy_sound
  · exact B2_4_2U1_2_1BinaryEntropy_sound
  · exact B2_4_2U2_1_1BinaryEntropy_sound
def B2_4_2S2 : Ball := ⟨(44625677478615700179775906702917 / 100000000000000000000000000000000), (19080272089 / 100000000000000000000000000000000)⟩
lemma B2_4_2S2_sound : B2_4_2S2.Encloses
    (((below (shape 2 4 2)).map fun u => (littleMass (shape 2 4 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 2 4 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 2 4 2))
    (fun u => .mul (B2_4_2Masses u) (B2_4_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B2_4_2Masses_sound u hu) (B2_4_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
