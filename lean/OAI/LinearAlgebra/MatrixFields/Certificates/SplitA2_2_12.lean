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
lemma A2_2_12_below : below (shape 2 2 12) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4)] := by decide +kernel
def A2_2_12Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1869311508851834494291415094233 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(7549884563595081968144199084631 / 20000000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(30069849903795798682001150038067 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(3769284113062302699382690041033 / 10000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨1, 0⟩
  | 1, 2, 5 => ⟨(3769284113062302699382690041033 / 10000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(30069849903795798682001150038067 / 50000000000000000000000000000000), (19 / 12500000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7549884563595081968144199084631 / 20000000000000000000000000000000), (49 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1869311508851834494291415094233 / 100000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_2_12Raw_0_0_8 : (A2_2_12Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 0 8)
    (-2535) (-2550) (-34711) w188 w187 w53
    (by decide +kernel) w188_sound w187_sound w53_sound) (by decide +kernel)
lemma A2_2_12Raw_0_1_7 : (A2_2_12Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 1 7)
    (-2535) (0) (-7207) w188 w195 w147
    (by decide +kernel) w188_sound w195_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_0_2_6 : (A2_2_12Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 0 2 6)
    (-2535) (-2550) (0) w188 w187 w195
    (by decide +kernel) w188_sound w187_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_1_0_7 : (A2_2_12Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 0 7)
    (0) (-2550) (-7207) w195 w187 w147
    (by decide +kernel) w195_sound w187_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_1_1_6 : (A2_2_12Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 1 6)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_1_2_5 : (A2_2_12Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 1 2 5)
    (0) (-2550) (-7207) w195 w187 w147
    (by decide +kernel) w195_sound w187_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_2_0_6 : (A2_2_12Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 0 6)
    (-2535) (-2550) (0) w188 w187 w195
    (by decide +kernel) w188_sound w187_sound w195_sound) (by decide +kernel)
lemma A2_2_12Raw_2_1_5 : (A2_2_12Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 1 5)
    (-2535) (0) (-7207) w188 w195 w147
    (by decide +kernel) w188_sound w195_sound w147_sound) (by decide +kernel)
lemma A2_2_12Raw_2_2_4 : (A2_2_12Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 2 12) (shape 2 2 4)
    (-2535) (-2550) (-34711) w188 w187 w53
    (by decide +kernel) w188_sound w187_sound w53_sound) (by decide +kernel)
lemma A2_2_12Raw_sound (u : Shape) (hu : u ∈ below (shape 2 2 12)) :
    (A2_2_12Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 2 12) u : ℝ) := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_2_12Raw_0_0_8
  · exact A2_2_12Raw_0_1_7
  · exact A2_2_12Raw_0_2_6
  · exact A2_2_12Raw_1_0_7
  · exact A2_2_12Raw_1_1_6
  · exact A2_2_12Raw_1_2_5
  · exact A2_2_12Raw_2_0_6
  · exact A2_2_12Raw_2_1_5
  · exact A2_2_12Raw_2_2_4
def A2_2_12Den : Ball := ⟨(46862818816260467173210402750963 / 12500000000000000000000000000000), (353 / 50000000000000000000000000000000)⟩
lemma A2_2_12Den_sound : A2_2_12Den.Encloses (((below (shape 2 2 12)).map (splitWeight positiveInitial tableP (shape 2 2 12))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 2 12)) A2_2_12Raw (splitWeight positiveInitial tableP (shape 2 2 12)) A2_2_12Raw_sound) (by decide +kernel)
lemma A2_2_12Den_positive : 0 < A2_2_12Den.lower := by decide +kernel
def A2_2_12Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(498612641127346285354984562323 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(629320585519500210170837921791 / 6250000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(16041421890184163505612052300387 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(5027018498184156379482942970689 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(13336799104008174087333670447257 / 50000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5027018498184156379482942970689 / 50000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(16041421890184163505612052300387 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(629320585519500210170837921791 / 6250000000000000000000000000000), (23 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(498612641127346285354984562323 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_2_12Law (u : Shape) : Ball := if u ∈ below (shape 2 2 12) then A2_2_12Table u else .exact 0
lemma A2_2_12Law_check_0_0_8 : contains (.mul (A2_2_12Raw (shape 0 0 8)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_2_12Law_check_0_1_7 : contains (.mul (A2_2_12Raw (shape 0 1 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_2_12Law_check_0_2_6 : contains (.mul (A2_2_12Raw (shape 0 2 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_0_7 : contains (.mul (A2_2_12Raw (shape 1 0 7)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_2_12Law_check_1_1_6 : contains (.mul (A2_2_12Raw (shape 1 1 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_2_12Law_check_1_2_5 : contains (.mul (A2_2_12Raw (shape 1 2 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_0_6 : contains (.mul (A2_2_12Raw (shape 2 0 6)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_2_12Law_check_2_1_5 : contains (.mul (A2_2_12Raw (shape 2 1 5)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_2_12Law_check_2_2_4 : contains (.mul (A2_2_12Raw (shape 2 2 4)) (.inv A2_2_12Den)) (A2_2_12Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_2_12Law_check (u : Shape) (hu : u ∈ below (shape 2 2 12)) :
    contains (.mul (A2_2_12Raw u) (.inv A2_2_12Den)) (A2_2_12Table u) = true := by
  rw [A2_2_12_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_2_12Law_check_0_0_8
  · exact A2_2_12Law_check_0_1_7
  · exact A2_2_12Law_check_0_2_6
  · exact A2_2_12Law_check_1_0_7
  · exact A2_2_12Law_check_1_1_6
  · exact A2_2_12Law_check_1_2_5
  · exact A2_2_12Law_check_2_0_6
  · exact A2_2_12Law_check_2_1_5
  · exact A2_2_12Law_check_2_2_4
lemma A2_2_12Law_sound (u : Shape) :
    (A2_2_12Law u).Encloses (stageALaw (shape 2 2 12) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 2 12)
  · have h := contains_sound (Ball.mul_sound (A2_2_12Raw_sound u hu)
      (Ball.inv_sound A2_2_12Den_sound A2_2_12Den_positive)) (A2_2_12Law_check u hu)
    simpa only [A2_2_12Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_2_12Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
