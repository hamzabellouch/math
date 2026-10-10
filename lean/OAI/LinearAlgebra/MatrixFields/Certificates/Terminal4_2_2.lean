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
lemma B4_2_2_below : below (shape 4 2 2) = [
  (shape 0 2 2),
  (shape 1 1 2),
  (shape 1 2 1),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 2 2 0),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B4_2_2Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(59580328744584746699210039469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3551332927065966816059043009887 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(7099825355927794995680046054547 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(26216007198693794473744704647899 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 2, 2, 0 => ⟨(26216007198693794473744704647899 / 100000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(7099825355927794995680046054547 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3551332927065966816059043009887 / 50000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(59580328744584746699210039469 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_2_2Raw_0_2_2 : (B4_2_2Raw (shape 0 2 2)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 0 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 0 2 2)
    (-60868) (-6696) (-6692) w21 w150 w151
    (by decide +kernel) w21_sound w150_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_1_1_2 : (B4_2_2Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 1 1 2)
    (-19755) (0) (-6692) w88 w195 w151
    (by decide +kernel) w88_sound w195_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_1_2_1 : (B4_2_2Raw (shape 1 2 1)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 1 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 1 2 1)
    (-19755) (-6696) (0) w88 w150 w195
    (by decide +kernel) w88_sound w150_sound w195_sound) (by decide +kernel)
lemma B4_2_2Raw_2_0_2 : (B4_2_2Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 2 0 2)
    (0) (-6696) (-6692) w195 w150 w151
    (by decide +kernel) w195_sound w150_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_2_1_1 : (B4_2_2Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_2_2Raw_2_2_0 : (B4_2_2Raw (shape 2 2 0)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 2 2 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 2 2 0)
    (0) (-6696) (-6692) w195 w150 w151
    (by decide +kernel) w195_sound w150_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_3_0_1 : (B4_2_2Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 3 0 1)
    (-19755) (-6696) (0) w88 w150 w195
    (by decide +kernel) w88_sound w150_sound w195_sound) (by decide +kernel)
lemma B4_2_2Raw_3_1_0 : (B4_2_2Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 3 1 0)
    (-19755) (0) (-6692) w88 w195 w151
    (by decide +kernel) w88_sound w195_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_4_0_0 : (B4_2_2Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 2 2) (shape 4 0 0)
    (-60868) (-6696) (-6692) w21 w150 w151
    (by decide +kernel) w21_sound w150_sound w151_sound) (by decide +kernel)
lemma B4_2_2Raw_sound (u : Shape) (hu : u ∈ below (shape 4 2 2)) :
    (B4_2_2Raw u).Encloses (splitWeight positiveSecond tablep (shape 4 2 2) u : ℝ) := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_2_2Raw_0_2_2
  · exact B4_2_2Raw_1_1_2
  · exact B4_2_2Raw_1_2_1
  · exact B4_2_2Raw_2_0_2
  · exact B4_2_2Raw_2_1_1
  · exact B4_2_2Raw_2_2_0
  · exact B4_2_2Raw_3_0_1
  · exact B4_2_2Raw_3_1_0
  · exact B4_2_2Raw_4_0_0
def B4_2_2Den : Ball := ⟨(90478078737498107848242046761689 / 50000000000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
lemma B4_2_2Den_sound : B4_2_2Den.Encloses (((below (shape 4 2 2)).map (splitWeight positiveSecond tablep (shape 4 2 2))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 2 2)) B4_2_2Raw (splitWeight positiveSecond tablep (shape 4 2 2)) B4_2_2Raw_sound) (by decide +kernel)
lemma B4_2_2Den_positive : 0 < B4_2_2Den.lower := by decide +kernel
def B4_2_2Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(1962537764185601435248786401077 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 1, 2, 1 => ⟨(980876453031008343288822515281 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(7243745547126854607846925140589 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(11052400912504742196751447679061 / 20000000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(7243745547126854607846925140589 / 50000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(980876453031008343288822515281 / 25000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(1962537764185601435248786401077 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_2_2Law (u : Shape) : Ball := if u ∈ below (shape 4 2 2) then B4_2_2Table u else .exact 0
lemma B4_2_2Law_check_0_2_2 : contains (.mul (B4_2_2Raw (shape 0 2 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 0 2 2)) = true := by decide +kernel
lemma B4_2_2Law_check_1_1_2 : contains (.mul (B4_2_2Raw (shape 1 1 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 1 1 2)) = true := by decide +kernel
lemma B4_2_2Law_check_1_2_1 : contains (.mul (B4_2_2Raw (shape 1 2 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 1 2 1)) = true := by decide +kernel
lemma B4_2_2Law_check_2_0_2 : contains (.mul (B4_2_2Raw (shape 2 0 2)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 0 2)) = true := by decide +kernel
lemma B4_2_2Law_check_2_1_1 : contains (.mul (B4_2_2Raw (shape 2 1 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_2_2Law_check_2_2_0 : contains (.mul (B4_2_2Raw (shape 2 2 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 2 2 0)) = true := by decide +kernel
lemma B4_2_2Law_check_3_0_1 : contains (.mul (B4_2_2Raw (shape 3 0 1)) (.inv B4_2_2Den)) (B4_2_2Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_2_2Law_check_3_1_0 : contains (.mul (B4_2_2Raw (shape 3 1 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_2_2Law_check_4_0_0 : contains (.mul (B4_2_2Raw (shape 4 0 0)) (.inv B4_2_2Den)) (B4_2_2Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_2_2Law_check (u : Shape) (hu : u ∈ below (shape 4 2 2)) :
    contains (.mul (B4_2_2Raw u) (.inv B4_2_2Den)) (B4_2_2Table u) = true := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_2_2Law_check_0_2_2
  · exact B4_2_2Law_check_1_1_2
  · exact B4_2_2Law_check_1_2_1
  · exact B4_2_2Law_check_2_0_2
  · exact B4_2_2Law_check_2_1_1
  · exact B4_2_2Law_check_2_2_0
  · exact B4_2_2Law_check_3_0_1
  · exact B4_2_2Law_check_3_1_0
  · exact B4_2_2Law_check_4_0_0
lemma B4_2_2Law_sound (u : Shape) :
    (B4_2_2Law u).Encloses (stageBLaw (shape 4 2 2) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 2 2)
  · have h := contains_sound (Ball.mul_sound (B4_2_2Raw_sound u hu)
      (Ball.inv_sound B4_2_2Den_sound B4_2_2Den_positive)) (B4_2_2Law_check u hu)
    simpa only [B4_2_2Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_2_2Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B4_2_2Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 0, 2, 2 => (63321 / 1000000)
  | 1, 1, 2 => (1051 / 25000)
  | 1, 2, 1 => (21087 / 500000)
  | 2, 0, 2 => (52331 / 500000)
  | 2, 1, 1 => (593 / 50000)
  | 2, 2, 0 => (52451 / 500000)
  | _, _, _ => 0
lemma B4_2_2Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 4 2 2) u = B4_2_2Binary u := by
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
def B4_2_2LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_2_2Binary u else if i = 3 then B4_2_2Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_2_2Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_2_2LittleRat u w i)
  else .exact (littleLaw (shape 4 2 2) u w i)

lemma B4_2_2Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B4_2_2Little u w i).Encloses (littleLaw (shape 4 2 2) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B4_2_2Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B4_2_2LittleRat, littleLaw, B4_2_2Binary_eq u hu]
  · simp only [B4_2_2Little, hu, ite_false]
    exact Ball.exact_sound _
def B4_2_2Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(77179955630623675545342364672979 / 100000000000000000000000000000000), (147 / 100000000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(3365567162619738339457547396989 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(3365567162619738339457547396989 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(20368549697998574430467468169 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(3924290670247618121826431431639 / 50000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(32925283989199048774667657891 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 0 => ⟨(8378300301784769988516089892097 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 1, 3, 0 => ⟨(1687321586797401660591628215999 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 1, 1 => ⟨(63112155619266116724752383999613 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 1, 0, 2 => ⟨(8378300301784769988516089892097 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(1687321586797401660591628215999 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 2, 0 => ⟨(8381053538293561989694981145863 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 3, 0 => ⟨(1683384830026987155576128449497 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(63109016186771777730067818517553 / 100000000000000000000000000000000), (93 / 100000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(8381053538293561989694981145863 / 50000000000000000000000000000000), (1 / 1562500000000000000000000000000)⟩
  | 2, 0, 3 => ⟨(1683384830026987155576128449497 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_2_2Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((0 : Fin 6),j)) (B4_2_2Half 0 (0,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((1 : Fin 6),j)) (B4_2_2Half 0 (1,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((2 : Fin 6),j)) (B4_2_2Half 0 (2,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((3 : Fin 6),j)) (B4_2_2Half 0 (3,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((4 : Fin 6),j)) (B4_2_2Half 0 (4,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 0) ((5 : Fin 6),j)) (B4_2_2Half 0 (5,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((0 : Fin 6),j)) (B4_2_2Half 1 (0,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((1 : Fin 6),j)) (B4_2_2Half 1 (1,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((2 : Fin 6),j)) (B4_2_2Half 1 (2,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((3 : Fin 6),j)) (B4_2_2Half 1 (3,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((4 : Fin 6),j)) (B4_2_2Half 1 (4,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 1) ((5 : Fin 6),j)) (B4_2_2Half 1 (5,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((0 : Fin 6),j)) (B4_2_2Half 2 (0,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((1 : Fin 6),j)) (B4_2_2Half 2 (1,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((2 : Fin 6),j)) (B4_2_2Half 2 (2,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((3 : Fin 6),j)) (B4_2_2Half 2 (3,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((4 : Fin 6),j)) (B4_2_2Half 2 (4,j)) = true := by
  decide +kernel
lemma B4_2_2Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u 2) ((5 : Fin 6),j)) (B4_2_2Half 2 (5,j)) = true := by
  decide +kernel
lemma B4_2_2Half_sound (w : Fin 3) (ij : PairSlot) :
    (B4_2_2Half w ij).Encloses (halfLaw (shape 4 2 2) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 4 2 2)) (shape 4 2 2) B4_2_2Law
      (fun u => B4_2_2Little u w) ij) (B4_2_2Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B4_2_2Half_check_0_0 j) (B4_2_2Half_check_0_1 j) (B4_2_2Half_check_0_2 j) (B4_2_2Half_check_0_3 j) (B4_2_2Half_check_0_4 j) (B4_2_2Half_check_0_5 j)
    · exact forall_fin6 (B4_2_2Half_check_1_0 j) (B4_2_2Half_check_1_1 j) (B4_2_2Half_check_1_2 j) (B4_2_2Half_check_1_3 j) (B4_2_2Half_check_1_4 j) (B4_2_2Half_check_1_5 j)
    · exact forall_fin6 (B4_2_2Half_check_2_0 j) (B4_2_2Half_check_2_1 j) (B4_2_2Half_check_2_2 j) (B4_2_2Half_check_2_3 j) (B4_2_2Half_check_2_4 j) (B4_2_2Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 4 2 2)) (shape 4 2 2)
    B4_2_2Law (fun u => (stageBLaw (shape 4 2 2) u : ℝ))
    (fun u => B4_2_2Little u w) (fun u i => (littleLaw (shape 4 2 2) u w i : ℝ))
    (fun u _ => B4_2_2Law_sound u) (fun u i => B4_2_2Little_sound u w i) ij) hcheck
  have hp : positive (shape 4 2 2) = true := by decide +kernel
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
def B4_2_2U0_2_2D : Ball := .exact (63321 / 1000000)
lemma B4_2_2U0_2_2D_sound : B4_2_2U0_2_2D.Encloses (binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U0_2_2OneD : Ball := .exact (936679 / 1000000)
lemma B4_2_2U0_2_2OneD_sound : B4_2_2U0_2_2OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 0 2 2) = (63321 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((936679 / 1000000) : ℚ) using 1 <;> norm_num [B4_2_2U0_2_2OneD, Ball.exact]
def B4_2_2U0_2_2EDLogWitness : LogWitness := ⟨-4, 63321, 62500⟩
def B4_2_2U0_2_2EDLog : Ball := ⟨(-275953825129554669064816416181401 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2EDLog_sound : B4_2_2U0_2_2EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U0_2_2D_sound) (w := B4_2_2U0_2_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U0_2_2ED : Ball := ⟨(8736836080514265599926620144511 / 50000000000000000000000000000000), (3352185829 / 50000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2ED_sound : B4_2_2U0_2_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U0_2_2D_sound) B4_2_2U0_2_2EDLog_sound) (by decide +kernel)
def B4_2_2U0_2_2EOneDLogWitness : LogWitness := ⟨-1, 936679, 500000⟩
def B4_2_2U0_2_2EOneDLog : Ball := ⟨(-6541463814935642164057959379121 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2EOneDLog_sound : B4_2_2U0_2_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U0_2_2OneD_sound) (w := B4_2_2U0_2_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U0_2_2EOneD : Ball := ⟨(1531812946177525591646911333319 / 25000000000000000000000000000000), (2479368669 / 6250000000000000000000000000000)⟩
lemma B4_2_2U0_2_2EOneD_sound : B4_2_2U0_2_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 0 2 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U0_2_2OneD_sound) B4_2_2U0_2_2EOneDLog_sound) (by decide +kernel)
def B4_2_2U0_2_2BinaryEntropy : Ball := ⟨(13995000603881131630100869964719 / 50000000000000000000000000000000), (1962240761 / 4000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2BinaryEntropy_sound : B4_2_2U0_2_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 0 2 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U0_2_2EOneD_sound B4_2_2U0_2_2ED_sound)
    (Ball.mul_sound B4_2_2U0_2_2D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U0_2_2Leaf : Ball := ⟨(41186917510491800527041824835183 / 12500000000000000000000000000000), (33613143027 / 20000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2Leaf_sound : B4_2_2U0_2_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 0 2 2)) := by
  have hh : shapeMax (shape 0 2 2) = 2 := by decide +kernel
  have hp : positive (shape 0 2 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B4_2_2U0_2_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B4_2_2U0_2_2OneD_sound) logN5_sound)) (by decide +kernel)
def B4_2_2U0_2_2Mass : Ball := ⟨(491331029136091495330612073 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_2_2U0_2_2Mass_sound : B4_2_2U0_2_2Mass.Encloses (littleMass (shape 4 2 2) (shape 0 2 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 0 2 2))) (by decide +kernel)
def B4_2_2U1_1_2D : Ball := .exact (1051 / 25000)
lemma B4_2_2U1_1_2D_sound : B4_2_2U1_1_2D.Encloses (binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U1_1_2OneD : Ball := .exact (23949 / 25000)
lemma B4_2_2U1_1_2OneD_sound : B4_2_2U1_1_2OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 1 1 2) = (1051 / 25000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((23949 / 25000) : ℚ) using 1 <;> norm_num [B4_2_2U1_1_2OneD, Ball.exact]
def B4_2_2U1_1_2EDLogWitness : LogWitness := ⟨-5, 4204, 3125⟩
def B4_2_2U1_1_2EDLog : Ball := ⟨(-7922834332433466689101770028001 / 2500000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B4_2_2U1_1_2EDLog_sound : B4_2_2U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U1_1_2D_sound) (w := B4_2_2U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U1_1_2ED : Ball := ⟨(6661519106710058792196768239543 / 50000000000000000000000000000000), (5341389767 / 100000000000000000000000000000000)⟩
lemma B4_2_2U1_1_2ED_sound : B4_2_2U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U1_1_2D_sound) B4_2_2U1_1_2EDLog_sound) (by decide +kernel)
def B4_2_2U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 23949, 12500⟩
def B4_2_2U1_1_2EOneDLog : Ball := ⟨(-4294925553642923666670848622939 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U1_1_2EOneDLog_sound : B4_2_2U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U1_1_2OneD_sound) (w := B4_2_2U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U1_1_2EOneD : Ball := ⟨(4114366883367775155724006146831 / 100000000000000000000000000000000), (2535699007 / 6250000000000000000000000000000)⟩
lemma B4_2_2U1_1_2EOneD_sound : B4_2_2U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U1_1_2OneD_sound) B4_2_2U1_1_2EOneDLog_sound) (by decide +kernel)
def B4_2_2U1_1_2BinaryEntropy : Ball := ⟨(20351395843861902820907585661753 / 100000000000000000000000000000000), (9538607427 / 20000000000000000000000000000000)⟩
lemma B4_2_2U1_1_2BinaryEntropy_sound : B4_2_2U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U1_1_2EOneD_sound B4_2_2U1_1_2ED_sound)
    (Ball.mul_sound B4_2_2U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U1_1_2Leaf : Ball := ⟨(157560752751473558472665099815977 / 50000000000000000000000000000000), (7774015451 / 6250000000000000000000000000000)⟩
lemma B4_2_2U1_1_2Leaf_sound : B4_2_2U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (48949 / 25000)).Encloses (2 - (binaryParameter (shape 4 2 2) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 4 2 2) (shape 1 1 2) = (1051 / 25000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((48949 / 25000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_2_2U1_1_2Mass : Ball := ⟨(58572354286272772622701551241 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B4_2_2U1_1_2Mass_sound : B4_2_2U1_1_2Mass.Encloses (littleMass (shape 4 2 2) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 1 1 2))) (by decide +kernel)
def B4_2_2U1_2_1D : Ball := .exact (21087 / 500000)
lemma B4_2_2U1_2_1D_sound : B4_2_2U1_2_1D.Encloses (binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U1_2_1OneD : Ball := .exact (478913 / 500000)
lemma B4_2_2U1_2_1OneD_sound : B4_2_2U1_2_1OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 1 2 1) = (21087 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((478913 / 500000) : ℚ) using 1 <;> norm_num [B4_2_2U1_2_1OneD, Ball.exact]
def B4_2_2U1_2_1EDLogWitness : LogWitness := ⟨-5, 21087, 15625⟩
def B4_2_2U1_2_1EDLog : Ball := ⟨(-316595136156031375511358183062789 / 100000000000000000000000000000000), (63527471049 / 50000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1EDLog_sound : B4_2_2U1_2_1EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U1_2_1D_sound) (w := B4_2_2U1_2_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U1_2_1ED : Ball := ⟨(1335208327224446723081602001249 / 10000000000000000000000000000000), (5358415129 / 100000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1ED_sound : B4_2_2U1_2_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U1_2_1D_sound) B4_2_2U1_2_1EDLog_sound) (by decide +kernel)
def B4_2_2U1_2_1EOneDLogWitness : LogWitness := ⟨-1, 478913, 250000⟩
def B4_2_2U1_2_1EOneDLog : Ball := ⟨(-861782918003896777682762665419 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1EOneDLog_sound : B4_2_2U1_2_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U1_2_1OneD_sound) (w := B4_2_2U1_2_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U1_2_1EOneD : Ball := ⟨(2063595213050001087451924581919 / 50000000000000000000000000000000), (40565508991 / 100000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1EOneD_sound : B4_2_2U1_2_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U1_2_1OneD_sound) B4_2_2U1_2_1EOneDLog_sound) (by decide +kernel)
def B4_2_2U1_2_1BinaryEntropy : Ball := ⟨(20402552617637982753656103120033 / 100000000000000000000000000000000), (47710062497 / 100000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1BinaryEntropy_sound : B4_2_2U1_2_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 1 2 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U1_2_1EOneD_sound B4_2_2U1_2_1ED_sound)
    (Ball.mul_sound B4_2_2U1_2_1D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U1_2_1Leaf : Ball := ⟨(157549969517460250000155274731003 / 50000000000000000000000000000000), (24875146907 / 20000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1Leaf_sound : B4_2_2U1_2_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 1 2 1)) := by
  have hh : shapeMax (shape 1 2 1) = 2 := by decide +kernel
  have hp : positive (shape 1 2 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (978913 / 500000)).Encloses (2 - (binaryParameter (shape 4 2 2) (shape 1 2 1) : ℝ)) := by
    have he : binaryParameter (shape 4 2 2) (shape 1 2 1) = (21087 / 500000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((978913 / 500000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_2_2U1_2_1Mass : Ball := ⟨(58548930029721897108600768513 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B4_2_2U1_2_1Mass_sound : B4_2_2U1_2_1Mass.Encloses (littleMass (shape 4 2 2) (shape 1 2 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 1 2 1))) (by decide +kernel)
def B4_2_2U2_0_2D : Ball := .exact (52331 / 500000)
lemma B4_2_2U2_0_2D_sound : B4_2_2U2_0_2D.Encloses (binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U2_0_2OneD : Ball := .exact (447669 / 500000)
lemma B4_2_2U2_0_2OneD_sound : B4_2_2U2_0_2OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 2 0 2) = (52331 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((447669 / 500000) : ℚ) using 1 <;> norm_num [B4_2_2U2_0_2OneD, Ball.exact]
def B4_2_2U2_0_2EDLogWitness : LogWitness := ⟨-4, 52331, 31250⟩
def B4_2_2U2_0_2EDLog : Ball := ⟨(-14106369804520244990198383124901 / 6250000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B4_2_2U2_0_2EDLog_sound : B4_2_2U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_0_2D_sound) (w := B4_2_2U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_0_2ED : Ball := ⟨(11811207011845583049313145396947 / 50000000000000000000000000000000), (2770380073 / 25000000000000000000000000000000)⟩
lemma B4_2_2U2_0_2ED_sound : B4_2_2U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_0_2D_sound) B4_2_2U2_0_2EDLog_sound) (by decide +kernel)
def B4_2_2U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 447669, 250000⟩
def B4_2_2U2_0_2EOneDLog : Ball := ⟨(-11055397836918052136994139561117 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U2_0_2EOneDLog_sound : B4_2_2U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_0_2OneD_sound) (w := B4_2_2U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_0_2EOneD : Ball := ⟨(9898317788510534964232058926371 / 100000000000000000000000000000000), (151676157 / 400000000000000000000000000000)⟩
lemma B4_2_2U2_0_2EOneD_sound : B4_2_2U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_0_2OneD_sound) B4_2_2U2_0_2EOneDLog_sound) (by decide +kernel)
def B4_2_2U2_0_2BinaryEntropy : Ball := ⟨(40775348833378200660280982551299 / 100000000000000000000000000000000), (53433167659 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_0_2BinaryEntropy_sound : B4_2_2U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U2_0_2EOneD_sound B4_2_2U2_0_2ED_sound)
    (Ball.mul_sound B4_2_2U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U2_0_2Leaf : Ball := ⟨(328973533161962712899139846142051 / 100000000000000000000000000000000), (5224696419 / 3125000000000000000000000000000)⟩
lemma B4_2_2U2_0_2Leaf_sound : B4_2_2U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B4_2_2U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B4_2_2U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B4_2_2U2_0_2Mass : Ball := ⟨(86476446627153830691567188243 / 10000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
lemma B4_2_2U2_0_2Mass_sound : B4_2_2U2_0_2Mass.Encloses (littleMass (shape 4 2 2) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 2 0 2))) (by decide +kernel)
def B4_2_2U2_1_1D : Ball := .exact (593 / 50000)
lemma B4_2_2U2_1_1D_sound : B4_2_2U2_1_1D.Encloses (binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U2_1_1OneD : Ball := .exact (49407 / 50000)
lemma B4_2_2U2_1_1OneD_sound : B4_2_2U2_1_1OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 2 1 1) = (593 / 50000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((49407 / 50000) : ℚ) using 1 <;> norm_num [B4_2_2U2_1_1OneD, Ball.exact]
def B4_2_2U2_1_1EDLogWitness : LogWitness := ⟨-7, 4744, 3125⟩
def B4_2_2U2_1_1EDLog : Ball := ⟨(-55432298567656970726576300895367 / 12500000000000000000000000000000), (169406589463 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1EDLog_sound : B4_2_2U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_1_1D_sound) (w := B4_2_2U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_1_1ED : Ball := ⟨(657427061012411672817194928619 / 12500000000000000000000000000000), (251145269 / 12500000000000000000000000000000)⟩
lemma B4_2_2U2_1_1ED_sound : B4_2_2U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_1_1D_sound) B4_2_2U2_1_1EDLog_sound) (by decide +kernel)
def B4_2_2U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 49407, 25000⟩
def B4_2_2U2_1_1EOneDLog : Ball := ⟨(-149136135849562572644784501963 / 12500000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1EOneDLog_sound : B4_2_2U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_1_1OneD_sound) (w := B4_2_2U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_1_1EOneD : Ball := ⟨(589469525113547042132869431079 / 50000000000000000000000000000000), (41849356829 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1EOneD_sound : B4_2_2U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_1_1OneD_sound) B4_2_2U2_1_1EOneDLog_sound) (by decide +kernel)
def B4_2_2U2_1_1BinaryEntropy : Ball := ⟨(7260428094470482603772135360687 / 100000000000000000000000000000000), (44360809519 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1BinaryEntropy_sound : B4_2_2U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U2_1_1EOneD_sound B4_2_2U2_1_1ED_sound)
    (Ball.mul_sound B4_2_2U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U2_1_1Leaf : Ball := ⟨(319978789122673231875875290147027 / 100000000000000000000000000000000), (31575376573 / 25000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1Leaf_sound : B4_2_2U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (99407 / 50000)).Encloses (2 - (binaryParameter (shape 4 2 2) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 4 2 2) (shape 2 1 1) = (593 / 50000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((99407 / 50000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_2_2U2_1_1Mass : Ball := ⟨(3298612407745390627125647993311 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
lemma B4_2_2U2_1_1Mass_sound : B4_2_2U2_1_1Mass.Encloses (littleMass (shape 4 2 2) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 2 1 1))) (by decide +kernel)
def B4_2_2U2_2_0D : Ball := .exact (52451 / 500000)
lemma B4_2_2U2_2_0D_sound : B4_2_2U2_2_0D.Encloses (binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_2_2U2_2_0OneD : Ball := .exact (447549 / 500000)
lemma B4_2_2U2_2_0OneD_sound : B4_2_2U2_2_0OneD.Encloses (1 - (binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ)) := by
  have he : binaryParameter (shape 4 2 2) (shape 2 2 0) = (52451 / 500000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((447549 / 500000) : ℚ) using 1 <;> norm_num [B4_2_2U2_2_0OneD, Ball.exact]
def B4_2_2U2_2_0EDLogWitness : LogWitness := ⟨-4, 52451, 31250⟩
def B4_2_2U2_2_0EDLog : Ball := ⟨(-225472869798470476592187191794959 / 100000000000000000000000000000000), (52939559207 / 50000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0EDLog_sound : B4_2_2U2_2_0EDLog.Encloses (Real.log ((binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_2_0D_sound) (w := B4_2_2U2_2_0EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_2_0ED : Ball := ⟨(946102199503965997418944831747 / 4000000000000000000000000000000), (11106931281 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0ED_sound : B4_2_2U2_2_0ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_2_0D_sound) B4_2_2U2_2_0EDLog_sound) (by decide +kernel)
def B4_2_2U2_2_0EOneDLogWitness : LogWitness := ⟨-1, 447549, 250000⟩
def B4_2_2U2_2_0EOneDLog : Ball := ⟨(-692637934343495837134511622293 / 6250000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0EOneDLog_sound : B4_2_2U2_2_0EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_2_2U2_2_0OneD_sound) (w := B4_2_2U2_2_0EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_2_2U2_2_0EOneD : Ball := ⟨(495983063803995549461941667273 / 5000000000000000000000000000000), (7581774971 / 20000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0EOneD_sound : B4_2_2U2_2_0EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 2 2) (shape 2 2 0) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_2_2U2_2_0OneD_sound) B4_2_2U2_2_0EOneDLog_sound) (by decide +kernel)
def B4_2_2U2_2_0BinaryEntropy : Ball := ⟨(40843468817188999209561100536501 / 100000000000000000000000000000000), (53458578649 / 100000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0BinaryEntropy_sound : B4_2_2U2_2_0BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 2 2) (shape 2 2 0))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_2_2U2_2_0EOneD_sound B4_2_2U2_2_0ED_sound)
    (Ball.mul_sound B4_2_2U2_2_0D_sound logN2_sound)) (by decide +kernel)
def B4_2_2U2_2_0Leaf : Ball := ⟨(32896440012597667463043912769759 / 10000000000000000000000000000000), (41796300803 / 25000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0Leaf_sound : B4_2_2U2_2_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 2 2 0)) := by
  have hh : shapeMax (shape 2 2 0) = 2 := by decide +kernel
  have hp : positive (shape 2 2 0) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B4_2_2U2_2_0BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B4_2_2U2_2_0OneD_sound) logN5_sound)) (by decide +kernel)
def B4_2_2U2_2_0Mass : Ball := ⟨(86476446627153830691567188243 / 10000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
lemma B4_2_2U2_2_0Mass_sound : B4_2_2U2_2_0Mass.Encloses (littleMass (shape 4 2 2) (shape 2 2 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 2 2 0))) (by decide +kernel)
def B4_2_2U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_2_2U3_0_1Leaf_sound : B4_2_2U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_2_2U3_0_1Mass : Ball := ⟨(58548930029721897108600768513 / 25000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B4_2_2U3_0_1Mass_sound : B4_2_2U3_0_1Mass.Encloses (littleMass (shape 4 2 2) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 3 0 1))) (by decide +kernel)
def B4_2_2U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_2_2U3_1_0Leaf_sound : B4_2_2U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_2_2U3_1_0Mass : Ball := ⟨(58572354286272772622701551241 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
lemma B4_2_2U3_1_0Mass_sound : B4_2_2U3_1_0Mass.Encloses (littleMass (shape 4 2 2) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 3 1 0))) (by decide +kernel)
def B4_2_2U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B4_2_2U4_0_0Leaf_sound : B4_2_2U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  change (Ball.exact 0).Encloses 0
  simpa only [Rat.cast_zero] using Ball.exact_sound 0
def B4_2_2U4_0_0Mass : Ball := ⟨(491331029136091495330612073 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_2_2U4_0_0Mass_sound : B4_2_2U4_0_0Mass.Encloses (littleMass (shape 4 2 2) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_2_2))
    (B4_2_2Law_sound (shape 4 0 0))) (by decide +kernel)
def B4_2_2Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2Leaf
  | 1, 1, 2 => B4_2_2U1_1_2Leaf
  | 1, 2, 1 => B4_2_2U1_2_1Leaf
  | 2, 0, 2 => B4_2_2U2_0_2Leaf
  | 2, 1, 1 => B4_2_2U2_1_1Leaf
  | 2, 2, 0 => B4_2_2U2_2_0Leaf
  | 3, 0, 1 => B4_2_2U3_0_1Leaf
  | 3, 1, 0 => B4_2_2U3_1_0Leaf
  | 4, 0, 0 => B4_2_2U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B4_2_2Leaves_sound (u : Shape) (hu : u ∈ below (shape 4 2 2)) :
    (B4_2_2Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 2 2) u) := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_2_2U0_2_2Leaf_sound
  · exact B4_2_2U1_1_2Leaf_sound
  · exact B4_2_2U1_2_1Leaf_sound
  · exact B4_2_2U2_0_2Leaf_sound
  · exact B4_2_2U2_1_1Leaf_sound
  · exact B4_2_2U2_2_0Leaf_sound
  · exact B4_2_2U3_0_1Leaf_sound
  · exact B4_2_2U3_1_0Leaf_sound
  · exact B4_2_2U4_0_0Leaf_sound
def B4_2_2Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2Mass
  | 1, 1, 2 => B4_2_2U1_1_2Mass
  | 1, 2, 1 => B4_2_2U1_2_1Mass
  | 2, 0, 2 => B4_2_2U2_0_2Mass
  | 2, 1, 1 => B4_2_2U2_1_1Mass
  | 2, 2, 0 => B4_2_2U2_2_0Mass
  | 3, 0, 1 => B4_2_2U3_0_1Mass
  | 3, 1, 0 => B4_2_2U3_1_0Mass
  | 4, 0, 0 => B4_2_2U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B4_2_2Masses_sound (u : Shape) (hu : u ∈ below (shape 4 2 2)) :
    (B4_2_2Masses u).Encloses ((fun u => (littleMass (shape 4 2 2) u : ℝ)) u) := by
  rw [B4_2_2_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_2_2U0_2_2Mass_sound
  · exact B4_2_2U1_1_2Mass_sound
  · exact B4_2_2U1_2_1Mass_sound
  · exact B4_2_2U2_0_2Mass_sound
  · exact B4_2_2U2_1_1Mass_sound
  · exact B4_2_2U2_2_0Mass_sound
  · exact B4_2_2U3_0_1Mass_sound
  · exact B4_2_2U3_1_0Mass_sound
  · exact B4_2_2U4_0_0Mass_sound
def B4_2_2Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 2 => B4_2_2U0_2_2BinaryEntropy
  | 1, 1, 2 => B4_2_2U1_1_2BinaryEntropy
  | 1, 2, 1 => B4_2_2U1_2_1BinaryEntropy
  | 2, 0, 2 => B4_2_2U2_0_2BinaryEntropy
  | 2, 1, 1 => B4_2_2U2_1_1BinaryEntropy
  | 2, 2, 0 => B4_2_2U2_2_0BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B4_2_2Binaries_sound (u : Shape) (hu : u ∈ (below (shape 4 2 2)).filter positive) :
    (B4_2_2Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 4 2 2) u)) u) := by
  have hl : (below (shape 4 2 2)).filter positive = [(shape 1 1 2), (shape 1 2 1), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact B4_2_2U1_1_2BinaryEntropy_sound
  · exact B4_2_2U1_2_1BinaryEntropy_sound
  · exact B4_2_2U2_1_1BinaryEntropy_sound
def B4_2_2S2 : Ball := ⟨(18805922951942961214562949931267 / 100000000000000000000000000000000), (402029251 / 5000000000000000000000000000000)⟩
lemma B4_2_2S2_sound : B4_2_2S2.Encloses
    (((below (shape 4 2 2)).map fun u => (littleMass (shape 4 2 2) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 4 2 2) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 4 2 2))
    (fun u => .mul (B4_2_2Masses u) (B4_2_2Leaves u)) _
    (fun u hu => Ball.mul_sound (B4_2_2Masses_sound u hu) (B4_2_2Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
