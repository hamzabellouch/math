import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.Zero0_1_7

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_1_14_below : below (shape 1 1 14) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 1 0 7),
  (shape 1 1 6)] := by decide +kernel
def A1_1_14Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(36782530045362665672288806008641 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨1, 0⟩
  | 1, 0, 7 => ⟨1, 0⟩
  | 1, 1, 6 => ⟨(36782530045362665672288806008641 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A1_1_14Raw_0_0_8 : (A1_1_14Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 0 0 8)
    (0) (0) (-3070) w195 w195 w185
    (by decide +kernel) w195_sound w195_sound w185_sound) (by decide +kernel)
lemma A1_1_14Raw_0_1_7 : (A1_1_14Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 0 1 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_1_14Raw_1_0_7 : (A1_1_14Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 1 0 7)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_1_14Raw_1_1_6 : (A1_1_14Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 1 14) (shape 1 1 6)
    (0) (0) (-3070) w195 w195 w185
    (by decide +kernel) w195_sound w195_sound w185_sound) (by decide +kernel)
lemma A1_1_14Raw_sound (u : Shape) (hu : u ∈ below (shape 1 1 14)) :
    (A1_1_14Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 1 14) u : ℝ) := by
  rw [A1_1_14_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact A1_1_14Raw_0_0_8
  · exact A1_1_14Raw_0_1_7
  · exact A1_1_14Raw_1_0_7
  · exact A1_1_14Raw_1_1_6
def A1_1_14Den : Ball := ⟨(86782530045362665672288806008641 / 25000000000000000000000000000000), (39 / 25000000000000000000000000000000)⟩
lemma A1_1_14Den_sound : A1_1_14Den.Encloses (((below (shape 1 1 14)).map (splitWeight positiveInitial tableP (shape 1 1 14))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 1 14)) A1_1_14Raw (splitWeight positiveInitial tableP (shape 1 1 14)) A1_1_14Raw_sound) (by decide +kernel)
lemma A1_1_14Den_positive : 0 < A1_1_14Den.lower := by decide +kernel
def A1_1_14Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(211923586614355608536476757861 / 1000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(288076413385644391463523242139 / 1000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(288076413385644391463523242139 / 1000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(211923586614355608536476757861 / 1000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_1_14Law (u : Shape) : Ball := if u ∈ below (shape 1 1 14) then A1_1_14Table u else .exact 0
lemma A1_1_14Law_check_0_0_8 : contains (.mul (A1_1_14Raw (shape 0 0 8)) (.inv A1_1_14Den)) (A1_1_14Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_1_14Law_check_0_1_7 : contains (.mul (A1_1_14Raw (shape 0 1 7)) (.inv A1_1_14Den)) (A1_1_14Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_1_14Law_check_1_0_7 : contains (.mul (A1_1_14Raw (shape 1 0 7)) (.inv A1_1_14Den)) (A1_1_14Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_1_14Law_check_1_1_6 : contains (.mul (A1_1_14Raw (shape 1 1 6)) (.inv A1_1_14Den)) (A1_1_14Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_1_14Law_check (u : Shape) (hu : u ∈ below (shape 1 1 14)) :
    contains (.mul (A1_1_14Raw u) (.inv A1_1_14Den)) (A1_1_14Table u) = true := by
  rw [A1_1_14_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact A1_1_14Law_check_0_0_8
  · exact A1_1_14Law_check_0_1_7
  · exact A1_1_14Law_check_1_0_7
  · exact A1_1_14Law_check_1_1_6
lemma A1_1_14Law_sound (u : Shape) :
    (A1_1_14Law u).Encloses (stageALaw (shape 1 1 14) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 1 14)
  · have h := contains_sound (Ball.mul_sound (A1_1_14Raw_sound u hu)
      (Ball.inv_sound A1_1_14Den_sound A1_1_14Den_positive)) (A1_1_14Law_check u hu)
    simpa only [A1_1_14Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_1_14Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
