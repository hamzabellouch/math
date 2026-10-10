import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitB1_3_4

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A1_7_8_below : below (shape 1 7 8) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 1 7 0)] := by decide +kernel
def A1_7_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(64668921862685299795581911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(8061327816168650758772421803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(53906227585276956042284318339 / 2500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(10604472274941479671393272450057 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨1, 0⟩
  | 0, 5, 3 => ⟨(5174982216910474785081875841 / 32000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(230783094467553527628691159093 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(1820161921466848777911127321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1820161921466848777911127321 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(230783094467553527628691159093 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(5174982216910474785081875841 / 32000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(10604472274941479671393272450057 / 25000000000000000000000000000000), (3 / 6250000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(53906227585276956042284318339 / 2500000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(8061327816168650758772421803 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(64668921862685299795581911 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A1_7_8Raw_0_0_8 : (A1_7_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 0 8)
    (0) (-46871) (-95643) w195 w38 w5
    (by decide +kernel) w195_sound w38_sound w5_sound) (by decide +kernel)
lemma A1_7_8Raw_0_1_7 : (A1_7_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 1 7)
    (0) (-25058) (-62269) w195 w80 w19
    (by decide +kernel) w195_sound w80_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_0_2_6 : (A1_7_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 2 6)
    (0) (-9643) (-28725) w195 w135 w69
    (by decide +kernel) w195_sound w135_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_0_3_5 : (A1_7_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 3 5)
    (0) (0) (-8576) w195 w195 w138
    (by decide +kernel) w195_sound w195_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_0_4_4 : (A1_7_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 4 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_7_8Raw_0_5_3 : (A1_7_8Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 5 3)
    (0) (-9643) (-8576) w195 w135 w138
    (by decide +kernel) w195_sound w135_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_0_6_2 : (A1_7_8Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 6 2)
    (0) (-25058) (-28725) w195 w80 w69
    (by decide +kernel) w195_sound w80_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_0_7_1 : (A1_7_8Raw (shape 0 7 1)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 0 7 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 0 7 1)
    (0) (-46871) (-62269) w195 w38 w19
    (by decide +kernel) w195_sound w38_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_0_7 : (A1_7_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 0 7)
    (0) (-46871) (-62269) w195 w38 w19
    (by decide +kernel) w195_sound w38_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_1_6 : (A1_7_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 1 6)
    (0) (-25058) (-28725) w195 w80 w69
    (by decide +kernel) w195_sound w80_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_1_2_5 : (A1_7_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 2 5)
    (0) (-9643) (-8576) w195 w135 w138
    (by decide +kernel) w195_sound w135_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_1_3_4 : (A1_7_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A1_7_8Raw_1_4_3 : (A1_7_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 4 3)
    (0) (0) (-8576) w195 w195 w138
    (by decide +kernel) w195_sound w195_sound w138_sound) (by decide +kernel)
lemma A1_7_8Raw_1_5_2 : (A1_7_8Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 5 2)
    (0) (-9643) (-28725) w195 w135 w69
    (by decide +kernel) w195_sound w135_sound w69_sound) (by decide +kernel)
lemma A1_7_8Raw_1_6_1 : (A1_7_8Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 6 1)
    (0) (-25058) (-62269) w195 w80 w19
    (by decide +kernel) w195_sound w80_sound w19_sound) (by decide +kernel)
lemma A1_7_8Raw_1_7_0 : (A1_7_8Raw (shape 1 7 0)).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) (shape 1 7 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 1 7 8) (shape 1 7 0)
    (0) (-46871) (-95643) w195 w38 w5
    (by decide +kernel) w195_sound w38_sound w5_sound) (by decide +kernel)
lemma A1_7_8Raw_sound (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
    (A1_7_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 1 7 8) u : ℝ) := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_7_8Raw_0_0_8
  · exact A1_7_8Raw_0_1_7
  · exact A1_7_8Raw_0_2_6
  · exact A1_7_8Raw_0_3_5
  · exact A1_7_8Raw_0_4_4
  · exact A1_7_8Raw_0_5_3
  · exact A1_7_8Raw_0_6_2
  · exact A1_7_8Raw_0_7_1
  · exact A1_7_8Raw_1_0_7
  · exact A1_7_8Raw_1_1_6
  · exact A1_7_8Raw_1_2_5
  · exact A1_7_8Raw_1_3_4
  · exact A1_7_8Raw_1_4_3
  · exact A1_7_8Raw_1_5_2
  · exact A1_7_8Raw_1_6_1
  · exact A1_7_8Raw_1_7_0
def A1_7_8Den : Ball := ⟨(161225531306433004521497958407937 / 50000000000000000000000000000000), (51 / 25000000000000000000000000000000)⟩
lemma A1_7_8Den_sound : A1_7_8Den.Encloses (((below (shape 1 7 8)).map (splitWeight positiveInitial tableP (shape 1 7 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 1 7 8)) A1_7_8Raw (splitWeight positiveInitial tableP (shape 1 7 8)) A1_7_8Raw_sound) (by decide +kernel)
lemma A1_7_8Den_positive : 0 < A1_7_8Den.lower := by decide +kernel
def A1_7_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(13154829993750939206545618238241 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(71571509982781843275618258667 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(35279809335985405792837309 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(71571509982781843275618258667 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(626909836209048342179201955027 / 12500000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(49619932619696659353487069911 / 160000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(13154829993750939206545618238241 / 100000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(167176461285217244558128668051 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(500003178829468586018862723 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(20055422158842954722213457 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A1_7_8Law (u : Shape) : Ball := if u ∈ below (shape 1 7 8) then A1_7_8Table u else .exact 0
lemma A1_7_8Law_check_0_0_8 : contains (.mul (A1_7_8Raw (shape 0 0 8)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A1_7_8Law_check_0_1_7 : contains (.mul (A1_7_8Raw (shape 0 1 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A1_7_8Law_check_0_2_6 : contains (.mul (A1_7_8Raw (shape 0 2 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A1_7_8Law_check_0_3_5 : contains (.mul (A1_7_8Raw (shape 0 3 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A1_7_8Law_check_0_4_4 : contains (.mul (A1_7_8Raw (shape 0 4 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A1_7_8Law_check_0_5_3 : contains (.mul (A1_7_8Raw (shape 0 5 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 5 3)) = true := by decide +kernel
lemma A1_7_8Law_check_0_6_2 : contains (.mul (A1_7_8Raw (shape 0 6 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 6 2)) = true := by decide +kernel
lemma A1_7_8Law_check_0_7_1 : contains (.mul (A1_7_8Raw (shape 0 7 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 0 7 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_0_7 : contains (.mul (A1_7_8Raw (shape 1 0 7)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A1_7_8Law_check_1_1_6 : contains (.mul (A1_7_8Raw (shape 1 1 6)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A1_7_8Law_check_1_2_5 : contains (.mul (A1_7_8Raw (shape 1 2 5)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A1_7_8Law_check_1_3_4 : contains (.mul (A1_7_8Raw (shape 1 3 4)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A1_7_8Law_check_1_4_3 : contains (.mul (A1_7_8Raw (shape 1 4 3)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A1_7_8Law_check_1_5_2 : contains (.mul (A1_7_8Raw (shape 1 5 2)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 5 2)) = true := by decide +kernel
lemma A1_7_8Law_check_1_6_1 : contains (.mul (A1_7_8Raw (shape 1 6 1)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 6 1)) = true := by decide +kernel
lemma A1_7_8Law_check_1_7_0 : contains (.mul (A1_7_8Raw (shape 1 7 0)) (.inv A1_7_8Den)) (A1_7_8Table (shape 1 7 0)) = true := by decide +kernel
lemma A1_7_8Law_check (u : Shape) (hu : u ∈ below (shape 1 7 8)) :
    contains (.mul (A1_7_8Raw u) (.inv A1_7_8Den)) (A1_7_8Table u) = true := by
  rw [A1_7_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_7_8Law_check_0_0_8
  · exact A1_7_8Law_check_0_1_7
  · exact A1_7_8Law_check_0_2_6
  · exact A1_7_8Law_check_0_3_5
  · exact A1_7_8Law_check_0_4_4
  · exact A1_7_8Law_check_0_5_3
  · exact A1_7_8Law_check_0_6_2
  · exact A1_7_8Law_check_0_7_1
  · exact A1_7_8Law_check_1_0_7
  · exact A1_7_8Law_check_1_1_6
  · exact A1_7_8Law_check_1_2_5
  · exact A1_7_8Law_check_1_3_4
  · exact A1_7_8Law_check_1_4_3
  · exact A1_7_8Law_check_1_5_2
  · exact A1_7_8Law_check_1_6_1
  · exact A1_7_8Law_check_1_7_0
lemma A1_7_8Law_sound (u : Shape) :
    (A1_7_8Law u).Encloses (stageALaw (shape 1 7 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 1 7 8)
  · have h := contains_sound (Ball.mul_sound (A1_7_8Raw_sound u hu)
      (Ball.inv_sound A1_7_8Den_sound A1_7_8Den_positive)) (A1_7_8Law_check u hu)
    simpa only [A1_7_8Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A1_7_8Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
