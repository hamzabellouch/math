import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_3_12

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_4_11_below : below (shape 1 4 11) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3)] := by decide +kernel
def A1_4_11Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(188090920380700586676163797639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(7347227310806514247293732489647 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨1, 0⟩
  | 0, 3, 5 => ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(9124564624877481324080557406303 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9124564624877481324080557406303 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1185052529893235166451447015261 / 1562500000000000000000000000000), (1 / 1000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(7347227310806514247293732489647 / 50000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(188090920380700586676163797639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A1_4_11Raw_0_0_8 : (A1_4_11Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 0 8)
    (0) (-7530) (-55230) w195 w142 w28
    (by decide +kernel) w195_sound w142_sound w28_sound) (by decide +kernel)
lemma A1_4_11Raw_0_1_7 : (A1_4_11Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 1 7)
    (0) (-2765) (-16412) w195 w186 w104
    (by decide +kernel) w195_sound w186_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_0_2_6 : (A1_4_11Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 2 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_0_3_5 : (A1_4_11Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 3 5)
    (0) (-2765) (0) w195 w186 w195
    (by decide +kernel) w195_sound w186_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_0_4_4 : (A1_4_11Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 0 4 4)
    (0) (-7530) (-16412) w195 w142 w104
    (by decide +kernel) w195_sound w142_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_0_7 : (A1_4_11Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 0 7)
    (0) (-7530) (-16412) w195 w142 w104
    (by decide +kernel) w195_sound w142_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_1_6 : (A1_4_11Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 1 6)
    (0) (-2765) (0) w195 w186 w195
    (by decide +kernel) w195_sound w186_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_1_2_5 : (A1_4_11Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_4_11Raw_1_3_4 : (A1_4_11Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 3 4)
    (0) (-2765) (-16412) w195 w186 w104
    (by decide +kernel) w195_sound w186_sound w104_sound) (by decide +kernel)
lemma A1_4_11Raw_1_4_3 : (A1_4_11Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 4 11) (shape 1 4 3)
    (0) (-7530) (-55230) w195 w142 w28
    (by decide +kernel) w195_sound w142_sound w28_sound) (by decide +kernel)
lemma A1_4_11Raw_sound (u : Shape) (hu : u ∈ below (shape 1 4 11)) :
    (A1_4_11Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 4 11) u : ℝ) := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_4_11Raw_0_0_8
  · exact A1_4_11Raw_0_1_7
  · exact A1_4_11Raw_0_2_6
  · exact A1_4_11Raw_0_3_5
  · exact A1_4_11Raw_0_4_4
  · exact A1_4_11Raw_1_0_7
  · exact A1_4_11Raw_1_1_6
  · exact A1_4_11Raw_1_2_5
  · exact A1_4_11Raw_1_3_4
  · exact A1_4_11Raw_1_4_3
def A1_4_11Den : Ball := ⟨(9992523604001913052911839757997 / 2500000000000000000000000000000), (163 / 50000000000000000000000000000000)⟩
lemma A1_4_11Den_sound : A1_4_11Den.Encloses (((below (shape 1 4 11)).map (splitWeight positiveInitial tableP (shape 1 4 11))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 4 11)) A1_4_11Raw (splitWeight positiveInitial tableP (shape 1 4 11)) A1_4_11Raw_sound) (by decide +kernel)
lemma A1_4_11Den_positive : 0 < A1_4_11Den.lower := by decide +kernel
def A1_4_11Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(47057912454010095367492939241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(4595452811755191797013350101 / 125000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5003740994914984598991554798533 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(3795005391970877478082437264067 / 20000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2282847903712526081651866666959 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(2282847903712526081651866666959 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(3795005391970877478082437264067 / 20000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5003740994914984598991554798533 / 20000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(4595452811755191797013350101 / 125000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(47057912454010095367492939241 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_4_11Law (u : Shape) : Ball := if u ∈ below (shape 1 4 11) then A1_4_11Table u else .exact 0
lemma A1_4_11Law_check_0_0_8 : contains (.mul (A1_4_11Raw (shape 0 0 8)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_4_11Law_check_0_1_7 : contains (.mul (A1_4_11Raw (shape 0 1 7)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_4_11Law_check_0_2_6 : contains (.mul (A1_4_11Raw (shape 0 2 6)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_4_11Law_check_0_3_5 : contains (.mul (A1_4_11Raw (shape 0 3 5)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_4_11Law_check_0_4_4 : contains (.mul (A1_4_11Raw (shape 0 4 4)) (.inv A1_4_11Den)) (A1_4_11Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_4_11Law_check_1_0_7 : contains (.mul (A1_4_11Raw (shape 1 0 7)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_4_11Law_check_1_1_6 : contains (.mul (A1_4_11Raw (shape 1 1 6)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_4_11Law_check_1_2_5 : contains (.mul (A1_4_11Raw (shape 1 2 5)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_4_11Law_check_1_3_4 : contains (.mul (A1_4_11Raw (shape 1 3 4)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_4_11Law_check_1_4_3 : contains (.mul (A1_4_11Raw (shape 1 4 3)) (.inv A1_4_11Den)) (A1_4_11Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_4_11Law_check (u : Shape) (hu : u ∈ below (shape 1 4 11)) :
    contains (.mul (A1_4_11Raw u) (.inv A1_4_11Den)) (A1_4_11Table u) = true := by
  rw [A1_4_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_4_11Law_check_0_0_8
  · exact A1_4_11Law_check_0_1_7
  · exact A1_4_11Law_check_0_2_6
  · exact A1_4_11Law_check_0_3_5
  · exact A1_4_11Law_check_0_4_4
  · exact A1_4_11Law_check_1_0_7
  · exact A1_4_11Law_check_1_1_6
  · exact A1_4_11Law_check_1_2_5
  · exact A1_4_11Law_check_1_3_4
  · exact A1_4_11Law_check_1_4_3
lemma A1_4_11Law_sound (u : Shape) :
    (A1_4_11Law u).Encloses (stageALaw (shape 1 4 11) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 4 11)
  · have h := contains_sound (Ball.mul_sound (A1_4_11Raw_sound u hu)
      (Ball.inv_sound A1_4_11Den_sound A1_4_11Den_positive)) (A1_4_11Law_check u hu)
    simpa only [A1_4_11Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_4_11Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
