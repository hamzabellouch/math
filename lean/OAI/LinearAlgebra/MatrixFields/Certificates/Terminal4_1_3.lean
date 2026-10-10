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
lemma B4_1_3_below : below (shape 4 1 3) = [
  (shape 0 1 3),
  (shape 1 0 3),
  (shape 1 1 2),
  (shape 2 0 2),
  (shape 2 1 1),
  (shape 3 0 1),
  (shape 3 1 0),
  (shape 4 0 0)] := by decide +kernel
def B4_1_3Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(1986046562779191655644056193 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(3067522357202958037026075746671 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(15612473623271752962591099629173 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨1, 0⟩
  | 2, 1, 1 => ⟨1, 0⟩
  | 3, 0, 1 => ⟨(15612473623271752962591099629173 / 100000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(3067522357202958037026075746671 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(1986046562779191655644056193 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_1_3Raw_0_1_3 : (B4_1_3Raw (shape 0 1 3)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 0 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 0 1 3)
    (-55107) (0) (-16272) w31 w195 w105
    (by decide +kernel) w31_sound w195_sound w105_sound) (by decide +kernel)
lemma B4_1_3Raw_1_0_3 : (B4_1_3Raw (shape 1 0 3)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 1 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 1 0 3)
    (-18571) (0) (-16272) w93 w195 w105
    (by decide +kernel) w93_sound w195_sound w105_sound) (by decide +kernel)
lemma B4_1_3Raw_1_1_2 : (B4_1_3Raw (shape 1 1 2)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 1 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 1 1 2)
    (-18571) (0) (0) w93 w195 w195
    (by decide +kernel) w93_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_1_3Raw_2_0_2 : (B4_1_3Raw (shape 2 0 2)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 2 0 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 2 0 2)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_1_3Raw_2_1_1 : (B4_1_3Raw (shape 2 1 1)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 2 1 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 2 1 1)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_1_3Raw_3_0_1 : (B4_1_3Raw (shape 3 0 1)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 3 0 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 3 0 1)
    (-18571) (0) (0) w93 w195 w195
    (by decide +kernel) w93_sound w195_sound w195_sound) (by decide +kernel)
lemma B4_1_3Raw_3_1_0 : (B4_1_3Raw (shape 3 1 0)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 3 1 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 3 1 0)
    (-18571) (0) (-16272) w93 w195 w105
    (by decide +kernel) w93_sound w195_sound w105_sound) (by decide +kernel)
lemma B4_1_3Raw_4_0_0 : (B4_1_3Raw (shape 4 0 0)).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) (shape 4 0 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveSecond tablep (shape 4 1 3) (shape 4 0 0)
    (-55107) (0) (-16272) w31 w195 w105
    (by decide +kernel) w31_sound w195_sound w105_sound) (by decide +kernel)
lemma B4_1_3Raw_sound (u : Shape) (hu : u ∈ below (shape 4 1 3)) :
    (B4_1_3Raw u).Encloses (splitWeight positiveSecond tablep (shape 4 1 3) u : ℝ) := by
  rw [B4_1_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_1_3Raw_0_1_3
  · exact B4_1_3Raw_1_0_3
  · exact B4_1_3Raw_1_1_2
  · exact B4_1_3Raw_2_0_2
  · exact B4_1_3Raw_2_1_1
  · exact B4_1_3Raw_3_0_1
  · exact B4_1_3Raw_3_1_0
  · exact B4_1_3Raw_4_0_0
def B4_1_3Den : Ball := ⟨(29689859460746469666460734405891 / 12500000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
lemma B4_1_3Den_sound : B4_1_3Den.Encloses (((below (shape 4 1 3)).map (splitWeight positiveSecond tablep (shape 4 1 3))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 1 3)) B4_1_3Raw (splitWeight positiveSecond tablep (shape 4 1 3)) B4_1_3Raw_sound) (by decide +kernel)
lemma B4_1_3Den_positive : 0 < B4_1_3Den.lower := by decide +kernel
def B4_1_3Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 3 => ⟨(2066377148910784129369940729 / 160000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 2 => ⟨(3286575346523891131058813407701 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 0, 2 => ⟨(2631369815114502473693307033871 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 1, 1 => ⟨(2631369815114502473693307033871 / 6250000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 0, 1 => ⟨(3286575346523891131058813407701 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 1, 0 => ⟨(2066377148910784129369940729 / 160000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 0, 0 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def B4_1_3Law (u : Shape) : Ball := if u ∈ below (shape 4 1 3) then B4_1_3Table u else .exact 0
lemma B4_1_3Law_check_0_1_3 : contains (.mul (B4_1_3Raw (shape 0 1 3)) (.inv B4_1_3Den)) (B4_1_3Table (shape 0 1 3)) = true := by decide +kernel
lemma B4_1_3Law_check_1_0_3 : contains (.mul (B4_1_3Raw (shape 1 0 3)) (.inv B4_1_3Den)) (B4_1_3Table (shape 1 0 3)) = true := by decide +kernel
lemma B4_1_3Law_check_1_1_2 : contains (.mul (B4_1_3Raw (shape 1 1 2)) (.inv B4_1_3Den)) (B4_1_3Table (shape 1 1 2)) = true := by decide +kernel
lemma B4_1_3Law_check_2_0_2 : contains (.mul (B4_1_3Raw (shape 2 0 2)) (.inv B4_1_3Den)) (B4_1_3Table (shape 2 0 2)) = true := by decide +kernel
lemma B4_1_3Law_check_2_1_1 : contains (.mul (B4_1_3Raw (shape 2 1 1)) (.inv B4_1_3Den)) (B4_1_3Table (shape 2 1 1)) = true := by decide +kernel
lemma B4_1_3Law_check_3_0_1 : contains (.mul (B4_1_3Raw (shape 3 0 1)) (.inv B4_1_3Den)) (B4_1_3Table (shape 3 0 1)) = true := by decide +kernel
lemma B4_1_3Law_check_3_1_0 : contains (.mul (B4_1_3Raw (shape 3 1 0)) (.inv B4_1_3Den)) (B4_1_3Table (shape 3 1 0)) = true := by decide +kernel
lemma B4_1_3Law_check_4_0_0 : contains (.mul (B4_1_3Raw (shape 4 0 0)) (.inv B4_1_3Den)) (B4_1_3Table (shape 4 0 0)) = true := by decide +kernel
lemma B4_1_3Law_check (u : Shape) (hu : u ∈ below (shape 4 1 3)) :
    contains (.mul (B4_1_3Raw u) (.inv B4_1_3Den)) (B4_1_3Table u) = true := by
  rw [B4_1_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_1_3Law_check_0_1_3
  · exact B4_1_3Law_check_1_0_3
  · exact B4_1_3Law_check_1_1_2
  · exact B4_1_3Law_check_2_0_2
  · exact B4_1_3Law_check_2_1_1
  · exact B4_1_3Law_check_3_0_1
  · exact B4_1_3Law_check_3_1_0
  · exact B4_1_3Law_check_4_0_0
lemma B4_1_3Law_sound (u : Shape) :
    (B4_1_3Law u).Encloses (stageBLaw (shape 4 1 3) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 1 3)
  · have h := contains_sound (Ball.mul_sound (B4_1_3Raw_sound u hu)
      (Ball.inv_sound B4_1_3Den_sound B4_1_3Den_positive)) (B4_1_3Law_check u hu)
    simpa only [B4_1_3Law, hu, ite_true, stageBLaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [B4_1_3Law, hu, ite_false, stageBLaw, splitLaw, Rat.cast_zero]
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
def B4_1_3Binary (u : Shape) : ℚ :=
  match u 0, u 1, u 2 with
  | 1, 1, 2 => (41863 / 1000000)
  | 2, 0, 2 => (95723 / 1000000)
  | 2, 1, 1 => (3031 / 1000000)
  | _, _, _ => 0
lemma B4_1_3Binary_eq (u : Shape) (hu : u ∈ shapes 4) :
    binaryParameter (shape 4 1 3) u = B4_1_3Binary u := by
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
def B4_1_3LittleRat (u : Shape) (w : Fin 3) (i : Fin 6) : ℚ :=
  if u w = 2 then
    if i = 2 then 1 - B4_1_3Binary u else if i = 3 then B4_1_3Binary u else 0
  else if i = singletonSlot (u w) then 1 else 0

def B4_1_3Little (u : Shape) (w : Fin 3) (i : Fin 6) : Ball :=
  if u ∈ shapes 4 then .exact (B4_1_3LittleRat u w i)
  else .exact (littleLaw (shape 4 1 3) u w i)

lemma B4_1_3Little_sound (u : Shape) (w : Fin 3) (i : Fin 6) :
    (B4_1_3Little u w i).Encloses (littleLaw (shape 4 1 3) u w i : ℝ) := by
  by_cases hu : u ∈ shapes 4
  · simp only [B4_1_3Little, hu, ite_true]
    apply exact_rat_enclosed
    simp only [B4_1_3LittleRat, littleLaw, B4_1_3Binary_eq u hu]
  · simp only [B4_1_3Little, hu, ite_false]
    exact Ball.exact_sound _
def B4_1_3Half (w : Fin 3) (ij : PairSlot) : Ball :=
  match w.val, ij.1.val, ij.2.val with
  | 0, 0, 5 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 4 => ⟨(7864636411117022342973839771027 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 2, 2 => ⟨(75912799250947798122822246208417 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 0, 2, 3 => ⟨(4133302117167199798769837390289 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 2 => ⟨(4133302117167199798769837390289 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 3 => ⟨(24430598381881437823904094877 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 1 => ⟨(7864636411117022342973839771027 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 5, 0 => ⟨(33446547050938077933247687037 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 0 => ⟨(1 / 2), (13 / 50000000000000000000000000000000)⟩
  | 1, 0, 1 => ⟨(1 / 2), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 0 => ⟨(662466132560089079394730321331 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 1 => ⟨(44369774122421474207741998278713 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 3, 1 => ⟨(34442348899666781067748328629 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 2 => ⟨(44369774122421474207741998278713 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 2, 1, 3 => ⟨(34442348899666781067748328629 / 800000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 4 => ⟨(662466132560089079394730321331 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma B4_1_3Half_check_0_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((0 : Fin 6),j)) (B4_1_3Half 0 (0,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_0_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((1 : Fin 6),j)) (B4_1_3Half 0 (1,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_0_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((2 : Fin 6),j)) (B4_1_3Half 0 (2,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_0_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((3 : Fin 6),j)) (B4_1_3Half 0 (3,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_0_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((4 : Fin 6),j)) (B4_1_3Half 0 (4,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_0_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 0) ((5 : Fin 6),j)) (B4_1_3Half 0 (5,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((0 : Fin 6),j)) (B4_1_3Half 1 (0,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((1 : Fin 6),j)) (B4_1_3Half 1 (1,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((2 : Fin 6),j)) (B4_1_3Half 1 (2,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((3 : Fin 6),j)) (B4_1_3Half 1 (3,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((4 : Fin 6),j)) (B4_1_3Half 1 (4,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_1_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 1) ((5 : Fin 6),j)) (B4_1_3Half 1 (5,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_0 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((0 : Fin 6),j)) (B4_1_3Half 2 (0,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_1 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((1 : Fin 6),j)) (B4_1_3Half 2 (1,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_2 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((2 : Fin 6),j)) (B4_1_3Half 2 (2,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_3 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((3 : Fin 6),j)) (B4_1_3Half 2 (3,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_4 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((4 : Fin 6),j)) (B4_1_3Half 2 (4,j)) = true := by
  decide +kernel
lemma B4_1_3Half_check_2_5 : ∀ j : Fin 6,
    contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u 2) ((5 : Fin 6),j)) (B4_1_3Half 2 (5,j)) = true := by
  decide +kernel
lemma B4_1_3Half_sound (w : Fin 3) (ij : PairSlot) :
    (B4_1_3Half w ij).Encloses (halfLaw (shape 4 1 3) w ij : ℝ) := by
  have hcheck : contains (pairLawBall (below (shape 4 1 3)) (shape 4 1 3) B4_1_3Law
      (fun u => B4_1_3Little u w) ij) (B4_1_3Half w ij) = true := by
    rcases ij with ⟨i,j⟩
    revert i w
    apply forall_fin3
    · exact forall_fin6 (B4_1_3Half_check_0_0 j) (B4_1_3Half_check_0_1 j) (B4_1_3Half_check_0_2 j) (B4_1_3Half_check_0_3 j) (B4_1_3Half_check_0_4 j) (B4_1_3Half_check_0_5 j)
    · exact forall_fin6 (B4_1_3Half_check_1_0 j) (B4_1_3Half_check_1_1 j) (B4_1_3Half_check_1_2 j) (B4_1_3Half_check_1_3 j) (B4_1_3Half_check_1_4 j) (B4_1_3Half_check_1_5 j)
    · exact forall_fin6 (B4_1_3Half_check_2_0 j) (B4_1_3Half_check_2_1 j) (B4_1_3Half_check_2_2 j) (B4_1_3Half_check_2_3 j) (B4_1_3Half_check_2_4 j) (B4_1_3Half_check_2_5 j)
  have h := contains_sound (pairLawBall_sound (below (shape 4 1 3)) (shape 4 1 3)
    B4_1_3Law (fun u => (stageBLaw (shape 4 1 3) u : ℝ))
    (fun u => B4_1_3Little u w) (fun u i => (littleLaw (shape 4 1 3) u w i : ℝ))
    (fun u _ => B4_1_3Law_sound u) (fun u i => B4_1_3Little_sound u w i) ij) hcheck
  have hp : positive (shape 4 1 3) = true := by decide +kernel
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
def B4_1_3U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_1_3U0_1_3Leaf_sound : B4_1_3U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_1_3U0_1_3Mass : Ball := ⟨(1534436237026567284168100653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_1_3U0_1_3Mass_sound : B4_1_3U0_1_3Mass.Encloses (littleMass (shape 4 1 3) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 0 1 3))) (by decide +kernel)
def B4_1_3U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_1_3U1_0_3Leaf_sound : B4_1_3U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_1_3U1_0_3Mass : Ball := ⟨(59249837730323733309452320717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B4_1_3U1_0_3Mass_sound : B4_1_3U1_0_3Mass.Encloses (littleMass (shape 4 1 3) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 1 0 3))) (by decide +kernel)
def B4_1_3U1_1_2D : Ball := .exact (41863 / 1000000)
lemma B4_1_3U1_1_2D_sound : B4_1_3U1_1_2D.Encloses (binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_1_3U1_1_2OneD : Ball := .exact (958137 / 1000000)
lemma B4_1_3U1_1_2OneD_sound : B4_1_3U1_1_2OneD.Encloses (1 - (binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 4 1 3) (shape 1 1 2) = (41863 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((958137 / 1000000) : ℚ) using 1 <;> norm_num [B4_1_3U1_1_2OneD, Ball.exact]
def B4_1_3U1_1_2EDLogWitness : LogWitness := ⟨-5, 41863, 31250⟩
def B4_1_3U1_1_2EDLog : Ball := ⟨(-317335289706930149883438220903761 / 100000000000000000000000000000000), (127054942097 / 100000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2EDLog_sound : B4_1_3U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U1_1_2D_sound) (w := B4_1_3U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U1_1_2ED : Ball := ⟨(6642303616500608432285187120847 / 50000000000000000000000000000000), (2659450521 / 50000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2ED_sound : B4_1_3U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U1_1_2D_sound) B4_1_3U1_1_2EDLog_sound) (by decide +kernel)
def B4_1_3U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 958137, 500000⟩
def B4_1_3U1_1_2EOneDLog : Ball := ⟨(-855290099452987341985735013837 / 20000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2EOneDLog_sound : B4_1_3U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U1_1_2OneD_sound) (w := B4_1_3U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U1_1_2EOneD : Ball := ⟨(1024356362524483666110232736191 / 25000000000000000000000000000000), (40578680353 / 100000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2EOneD_sound : B4_1_3U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U1_1_2OneD_sound) B4_1_3U1_1_2EOneDLog_sound) (by decide +kernel)
def B4_1_3U1_1_2BinaryEntropy : Ball := ⟨(5070938681269312644456165804281 / 25000000000000000000000000000000), (47670548409 / 100000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2BinaryEntropy_sound : B4_1_3U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 1 3) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_1_3U1_1_2EOneD_sound B4_1_3U1_1_2ED_sound)
    (Ball.mul_sound B4_1_3U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B4_1_3U1_1_2Leaf : Ball := ⟨(19696874534624825032622539566587 / 6250000000000000000000000000000), (62197745789 / 50000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2Leaf_sound : B4_1_3U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1958137 / 1000000)).Encloses (2 - (binaryParameter (shape 4 1 3) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 4 1 3) (shape 1 1 2) = (41863 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1958137 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_1_3U1_1_2Mass : Ball := ⟨(301558202689444043590391085003 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B4_1_3U1_1_2Mass_sound : B4_1_3U1_1_2Mass.Encloses (littleMass (shape 4 1 3) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 1 1 2))) (by decide +kernel)
def B4_1_3U2_0_2D : Ball := .exact (95723 / 1000000)
lemma B4_1_3U2_0_2D_sound : B4_1_3U2_0_2D.Encloses (binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_1_3U2_0_2OneD : Ball := .exact (904277 / 1000000)
lemma B4_1_3U2_0_2OneD_sound : B4_1_3U2_0_2OneD.Encloses (1 - (binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ)) := by
  have he : binaryParameter (shape 4 1 3) (shape 2 0 2) = (95723 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((904277 / 1000000) : ℚ) using 1 <;> norm_num [B4_1_3U2_0_2OneD, Ball.exact]
def B4_1_3U2_0_2EDLogWitness : LogWitness := ⟨-4, 95723, 62500⟩
def B4_1_3U2_0_2EDLog : Ball := ⟨(-234629667502064329567169639454029 / 100000000000000000000000000000000), (21175823683 / 20000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2EDLog_sound : B4_1_3U2_0_2EDLog.Encloses (Real.log ((binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U2_0_2D_sound) (w := B4_1_3U2_0_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U2_0_2ED : Ball := ⟨(11229727831150051909579089698729 / 50000000000000000000000000000000), (10135066853 / 100000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2ED_sound : B4_1_3U2_0_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U2_0_2D_sound) B4_1_3U2_0_2EDLog_sound) (by decide +kernel)
def B4_1_3U2_0_2EOneDLogWitness : LogWitness := ⟨-1, 904277, 500000⟩
def B4_1_3U2_0_2EOneDLog : Ball := ⟨(-10061954959653018265030300181801 / 100000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2EOneDLog_sound : B4_1_3U2_0_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U2_0_2OneD_sound) (w := B4_1_3U2_0_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U2_0_2EOneD : Ball := ⟨(4549397222525076198823402378749 / 50000000000000000000000000000000), (19148810313 / 50000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2EOneD_sound : B4_1_3U2_0_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 1 3) (shape 2 0 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U2_0_2OneD_sound) B4_1_3U2_0_2EOneDLog_sound) (by decide +kernel)
def B4_1_3U2_0_2BinaryEntropy : Ball := ⟨(38193262863824220702139553363313 / 100000000000000000000000000000000), (2624335711 / 5000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2BinaryEntropy_sound : B4_1_3U2_0_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 1 3) (shape 2 0 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_1_3U2_0_2EOneD_sound B4_1_3U2_0_2ED_sound)
    (Ball.mul_sound B4_1_3U2_0_2D_sound logN2_sound)) (by decide +kernel)
def B4_1_3U2_0_2Leaf : Ball := ⟨(82317200073064604397677413451807 / 25000000000000000000000000000000), (5230611753 / 3125000000000000000000000000000)⟩
lemma B4_1_3U2_0_2Leaf_sound : B4_1_3U2_0_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 2 0 2)) := by
  have hh : shapeMax (shape 2 0 2) = 2 := by decide +kernel
  have hp : positive (shape 2 0 2) = false := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_false,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false, ite_true]
  exact contains_sound (Ball.add_sound B4_1_3U2_0_2BinaryEntropy_sound
    (Ball.mul_sound (Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      B4_1_3U2_0_2OneD_sound) logN5_sound)) (by decide +kernel)
def B4_1_3U2_0_2Mass : Ball := ⟨(965760487306589437428352637319 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
lemma B4_1_3U2_0_2Mass_sound : B4_1_3U2_0_2Mass.Encloses (littleMass (shape 4 1 3) (shape 2 0 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 2 0 2))) (by decide +kernel)
def B4_1_3U2_1_1D : Ball := .exact (3031 / 1000000)
lemma B4_1_3U2_1_1D_sound : B4_1_3U2_1_1D.Encloses (binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B4_1_3U2_1_1OneD : Ball := .exact (996969 / 1000000)
lemma B4_1_3U2_1_1OneD_sound : B4_1_3U2_1_1OneD.Encloses (1 - (binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ)) := by
  have he : binaryParameter (shape 4 1 3) (shape 2 1 1) = (3031 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((996969 / 1000000) : ℚ) using 1 <;> norm_num [B4_1_3U2_1_1OneD, Ball.exact]
def B4_1_3U2_1_1EDLogWitness : LogWitness := ⟨-9, 24248, 15625⟩
def B4_1_3U2_1_1EDLog : Ball := ⟨(-579886268090647095228230969209657 / 100000000000000000000000000000000), (21175823683 / 10000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1EDLog_sound : B4_1_3U2_1_1EDLog.Encloses (Real.log ((binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U2_1_1D_sound) (w := B4_1_3U2_1_1EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U2_1_1ED : Ball := ⟨(878817639291375672818384033837 / 50000000000000000000000000000000), (641839217 / 100000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1ED_sound : B4_1_3U2_1_1ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U2_1_1D_sound) B4_1_3U2_1_1EDLog_sound) (by decide +kernel)
def B4_1_3U2_1_1EOneDLogWitness : LogWitness := ⟨-1, 996969, 500000⟩
def B4_1_3U2_1_1EOneDLog : Ball := ⟨(-2371564674643973779035589817 / 781250000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1EOneDLog_sound : B4_1_3U2_1_1EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B4_1_3U2_1_1OneD_sound) (w := B4_1_3U2_1_1EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B4_1_3U2_1_1EOneD : Ball := ⟨(151320093575368185248725308433 / 50000000000000000000000000000000), (42223279523 / 100000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1EOneD_sound : B4_1_3U2_1_1EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B4_1_3U2_1_1OneD_sound) B4_1_3U2_1_1EOneDLog_sound) (by decide +kernel)
def B4_1_3U2_1_1BinaryEntropy : Ball := ⟨(567592094040301784854645420669 / 25000000000000000000000000000000), (5374185823 / 12500000000000000000000000000000)⟩
lemma B4_1_3U2_1_1BinaryEntropy_sound : B4_1_3U2_1_1BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 4 1 3) (shape 2 1 1))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B4_1_3U2_1_1EOneD_sound B4_1_3U2_1_1ED_sound)
    (Ball.mul_sound B4_1_3U2_1_1D_sound logN2_sound)) (by decide +kernel)
def B4_1_3U2_1_1Leaf : Ball := ⟨(40174970231945162387076287528143 / 12500000000000000000000000000000), (63431195167 / 50000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1Leaf_sound : B4_1_3U2_1_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 2 1 1)) := by
  have hh : shapeMax (shape 2 1 1) = 2 := by decide +kernel
  have hp : positive (shape 2 1 1) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1996969 / 1000000)).Encloses (2 - (binaryParameter (shape 4 1 3) (shape 2 1 1) : ℝ)) := by
    have he : binaryParameter (shape 4 1 3) (shape 2 1 1) = (3031 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1996969 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B4_1_3U2_1_1Mass : Ball := ⟨(965760487306589437428352637319 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
lemma B4_1_3U2_1_1Mass_sound : B4_1_3U2_1_1Mass.Encloses (littleMass (shape 4 1 3) (shape 2 1 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 2 1 1))) (by decide +kernel)
def B4_1_3U3_0_1Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_1_3U3_0_1Leaf_sound : B4_1_3U3_0_1Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 3 0 1)) := by
  have hh : shapeMax (shape 3 0 1) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_1_3U3_0_1Mass : Ball := ⟨(301558202689444043590391085003 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
lemma B4_1_3U3_0_1Mass_sound : B4_1_3U3_0_1Mass.Encloses (littleMass (shape 4 1 3) (shape 3 0 1) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 3 0 1))) (by decide +kernel)
def B4_1_3U3_1_0Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B4_1_3U3_1_0Leaf_sound : B4_1_3U3_1_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 3 1 0)) := by
  have hh : shapeMax (shape 3 1 0) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B4_1_3U3_1_0Mass : Ball := ⟨(59249837730323733309452320717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
lemma B4_1_3U3_1_0Mass_sound : B4_1_3U3_1_0Mass.Encloses (littleMass (shape 4 1 3) (shape 3 1 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 3 1 0))) (by decide +kernel)
def B4_1_3U4_0_0Leaf : Ball := ⟨0, 0⟩
lemma B4_1_3U4_0_0Leaf_sound : B4_1_3U4_0_0Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) (shape 4 0 0)) := by
  have hh : shapeMax (shape 4 0 0) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [Rat.cast_zero, B4_1_3U4_0_0Leaf, Ball.exact] using Ball.exact_sound 0
def B4_1_3U4_0_0Mass : Ball := ⟨(1534436237026567284168100653 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B4_1_3U4_0_0Mass_sound : B4_1_3U4_0_0Mass.Encloses (littleMass (shape 4 1 3) (shape 4 0 0) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_4_1_3))
    (B4_1_3Law_sound (shape 4 0 0))) (by decide +kernel)
def B4_1_3Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B4_1_3U0_1_3Leaf
  | 1, 0, 3 => B4_1_3U1_0_3Leaf
  | 1, 1, 2 => B4_1_3U1_1_2Leaf
  | 2, 0, 2 => B4_1_3U2_0_2Leaf
  | 2, 1, 1 => B4_1_3U2_1_1Leaf
  | 3, 0, 1 => B4_1_3U3_0_1Leaf
  | 3, 1, 0 => B4_1_3U3_1_0Leaf
  | 4, 0, 0 => B4_1_3U4_0_0Leaf
  | _, _, _ => (.exact 0)
lemma B4_1_3Leaves_sound (u : Shape) (hu : u ∈ below (shape 4 1 3)) :
    (B4_1_3Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 4 1 3) u) := by
  rw [B4_1_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_1_3U0_1_3Leaf_sound
  · exact B4_1_3U1_0_3Leaf_sound
  · exact B4_1_3U1_1_2Leaf_sound
  · exact B4_1_3U2_0_2Leaf_sound
  · exact B4_1_3U2_1_1Leaf_sound
  · exact B4_1_3U3_0_1Leaf_sound
  · exact B4_1_3U3_1_0Leaf_sound
  · exact B4_1_3U4_0_0Leaf_sound
def B4_1_3Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 3 => B4_1_3U0_1_3Mass
  | 1, 0, 3 => B4_1_3U1_0_3Mass
  | 1, 1, 2 => B4_1_3U1_1_2Mass
  | 2, 0, 2 => B4_1_3U2_0_2Mass
  | 2, 1, 1 => B4_1_3U2_1_1Mass
  | 3, 0, 1 => B4_1_3U3_0_1Mass
  | 3, 1, 0 => B4_1_3U3_1_0Mass
  | 4, 0, 0 => B4_1_3U4_0_0Mass
  | _, _, _ => (.exact 0)
lemma B4_1_3Masses_sound (u : Shape) (hu : u ∈ below (shape 4 1 3)) :
    (B4_1_3Masses u).Encloses ((fun u => (littleMass (shape 4 1 3) u : ℝ)) u) := by
  rw [B4_1_3_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact B4_1_3U0_1_3Mass_sound
  · exact B4_1_3U1_0_3Mass_sound
  · exact B4_1_3U1_1_2Mass_sound
  · exact B4_1_3U2_0_2Mass_sound
  · exact B4_1_3U2_1_1Mass_sound
  · exact B4_1_3U3_0_1Mass_sound
  · exact B4_1_3U3_1_0Mass_sound
  · exact B4_1_3U4_0_0Mass_sound
def B4_1_3Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B4_1_3U1_1_2BinaryEntropy
  | 2, 0, 2 => B4_1_3U2_0_2BinaryEntropy
  | 2, 1, 1 => B4_1_3U2_1_1BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B4_1_3Binaries_sound (u : Shape) (hu : u ∈ (below (shape 4 1 3)).filter positive) :
    (B4_1_3Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 4 1 3) u)) u) := by
  have hl : (below (shape 4 1 3)).filter positive = [(shape 1 1 2), (shape 2 1 1)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact B4_1_3U1_1_2BinaryEntropy_sound
  · exact B4_1_3U2_1_1BinaryEntropy_sound
def B4_1_3S2 : Ball := ⟨(14488912584849512791622540958653 / 100000000000000000000000000000000), (6415572889 / 100000000000000000000000000000000)⟩
lemma B4_1_3S2_sound : B4_1_3S2.Encloses
    (((below (shape 4 1 3)).map fun u => (littleMass (shape 4 1 3) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 4 1 3) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 4 1 3))
    (fun u => .mul (B4_1_3Masses u) (B4_1_3Leaves u)) _
    (fun u hu => Ball.mul_sound (B4_1_3Masses_sound u hu) (B4_1_3Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
