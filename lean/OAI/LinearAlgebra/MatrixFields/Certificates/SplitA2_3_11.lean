import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB1_1_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A2_3_11_below : below (shape 2 3 11) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3)] := by decide +kernel
def A2_3_11Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(186089076496629284671636655033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(3883263175820951434259740591633 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(72108374302660701632463080306707 / 100000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(7622712470039063487610425167721 / 20000000000000000000000000000000), (97 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1423229584278735571932633776199 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(1423229584278735571932633776199 / 12500000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(7622712470039063487610425167721 / 20000000000000000000000000000000), (97 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(72108374302660701632463080306707 / 100000000000000000000000000000000), (11 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(3883263175820951434259740591633 / 25000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(186089076496629284671636655033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_3_11Raw_0_0_8 : (A2_3_11Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 0 8)
    (-3270) (-6376) (-53221) w184 w157 w33
    (by decide +kernel) w184_sound w157_sound w33_sound) (by decide +kernel)
lemma A2_3_11Raw_0_1_7 : (A2_3_11Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 1 7)
    (-3270) (0) (-15352) w184 w195 w112
    (by decide +kernel) w184_sound w195_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_0_2_6 : (A2_3_11Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 2 6)
    (-3270) (0) (0) w184 w195 w195
    (by decide +kernel) w184_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_0_3_5 : (A2_3_11Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 0 3 5)
    (-3270) (-6376) (0) w184 w157 w195
    (by decide +kernel) w184_sound w157_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_0_7 : (A2_3_11Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 0 7)
    (0) (-6376) (-15352) w195 w157 w112
    (by decide +kernel) w195_sound w157_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_1_1_6 : (A2_3_11Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_2_5 : (A2_3_11Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_1_3_4 : (A2_3_11Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 1 3 4)
    (0) (-6376) (-15352) w195 w157 w112
    (by decide +kernel) w195_sound w157_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_2_0_6 : (A2_3_11Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 0 6)
    (-3270) (-6376) (0) w184 w157 w195
    (by decide +kernel) w184_sound w157_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_2_1_5 : (A2_3_11Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 1 5)
    (-3270) (0) (0) w184 w195 w195
    (by decide +kernel) w184_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_3_11Raw_2_2_4 : (A2_3_11Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 2 4)
    (-3270) (0) (-15352) w184 w195 w112
    (by decide +kernel) w184_sound w195_sound w112_sound) (by decide +kernel)
lemma A2_3_11Raw_2_3_3 : (A2_3_11Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 3 11) (shape 2 3 3)
    (-3270) (-6376) (-53221) w184 w157 w33
    (by decide +kernel) w184_sound w157_sound w33_sound) (by decide +kernel)
lemma A2_3_11Raw_sound (u : Shape) (hu : u ∈ below (shape 2 3 11)) :
    (A2_3_11Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 3 11) u : ℝ) := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_3_11Raw_0_0_8
  · exact A2_3_11Raw_0_1_7
  · exact A2_3_11Raw_0_2_6
  · exact A2_3_11Raw_0_3_5
  · exact A2_3_11Raw_1_0_7
  · exact A2_3_11Raw_1_1_6
  · exact A2_3_11Raw_1_2_5
  · exact A2_3_11Raw_1_3_4
  · exact A2_3_11Raw_2_0_6
  · exact A2_3_11Raw_2_1_5
  · exact A2_3_11Raw_2_2_4
  · exact A2_3_11Raw_2_3_3
def A2_3_11Den : Ball := ⟨(237326915106866338667686875376469 / 50000000000000000000000000000000), (263 / 50000000000000000000000000000000)⟩
lemma A2_3_11Den_sound : A2_3_11Den.Encloses (((below (shape 2 3 11)).map (splitWeight positiveInitial tableP (shape 2 3 11))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 3 11)) A2_3_11Raw (splitWeight positiveInitial tableP (shape 2 3 11)) A2_3_11Raw_sound) (by decide +kernel)
lemma A2_3_11Den_positive : 0 < A2_3_11Den.lower := by decide +kernel
def A2_3_11Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1636250643578437060137490917283 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(3038356364687540796048396518993 / 20000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2007439944866403842027423610433 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1199383208295499995255418131323 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(21067985473744271817281816227921 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(1199383208295499995255418131323 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2007439944866403842027423610433 / 25000000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3038356364687540796048396518993 / 20000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1636250643578437060137490917283 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(3920521960453472358068863817 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_3_11Law (u : Shape) : Ball := if u ∈ below (shape 2 3 11) then A2_3_11Table u else .exact 0
lemma A2_3_11Law_check_0_0_8 : contains (.mul (A2_3_11Raw (shape 0 0 8)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_3_11Law_check_0_1_7 : contains (.mul (A2_3_11Raw (shape 0 1 7)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_3_11Law_check_0_2_6 : contains (.mul (A2_3_11Raw (shape 0 2 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_3_11Law_check_0_3_5 : contains (.mul (A2_3_11Raw (shape 0 3 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_3_11Law_check_1_0_7 : contains (.mul (A2_3_11Raw (shape 1 0 7)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_3_11Law_check_1_1_6 : contains (.mul (A2_3_11Raw (shape 1 1 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_3_11Law_check_1_2_5 : contains (.mul (A2_3_11Raw (shape 1 2 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_3_11Law_check_1_3_4 : contains (.mul (A2_3_11Raw (shape 1 3 4)) (.inv A2_3_11Den)) (A2_3_11Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_3_11Law_check_2_0_6 : contains (.mul (A2_3_11Raw (shape 2 0 6)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_3_11Law_check_2_1_5 : contains (.mul (A2_3_11Raw (shape 2 1 5)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_3_11Law_check_2_2_4 : contains (.mul (A2_3_11Raw (shape 2 2 4)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_3_11Law_check_2_3_3 : contains (.mul (A2_3_11Raw (shape 2 3 3)) (.inv A2_3_11Den)) (A2_3_11Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_3_11Law_check (u : Shape) (hu : u ∈ below (shape 2 3 11)) :
    contains (.mul (A2_3_11Raw u) (.inv A2_3_11Den)) (A2_3_11Table u) = true := by
  rw [A2_3_11_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_3_11Law_check_0_0_8
  · exact A2_3_11Law_check_0_1_7
  · exact A2_3_11Law_check_0_2_6
  · exact A2_3_11Law_check_0_3_5
  · exact A2_3_11Law_check_1_0_7
  · exact A2_3_11Law_check_1_1_6
  · exact A2_3_11Law_check_1_2_5
  · exact A2_3_11Law_check_1_3_4
  · exact A2_3_11Law_check_2_0_6
  · exact A2_3_11Law_check_2_1_5
  · exact A2_3_11Law_check_2_2_4
  · exact A2_3_11Law_check_2_3_3
lemma A2_3_11Law_sound (u : Shape) :
    (A2_3_11Law u).Encloses (stageALaw (shape 2 3 11) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 3 11)
  · have h := contains_sound (Ball.mul_sound (A2_3_11Raw_sound u hu)
      (Ball.inv_sound A2_3_11Den_sound A2_3_11Den_positive)) (A2_3_11Law_check u hu)
    simpa only [A2_3_11Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_3_11Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
