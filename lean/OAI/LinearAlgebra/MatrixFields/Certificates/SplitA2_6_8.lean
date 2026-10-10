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
lemma A2_6_8_below : below (shape 2 6 8) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 2 6 0)] := by decide +kernel
def A2_6_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(21466224447373239265811841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(4164228830985898487035268579 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(236816107750252950992530912187 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(26588271193898263795134550700049 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(42109365988791183706790041939433 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(3497925876037468983918864089217 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(43048417256949502222394857087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(152992977510149012892744533 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(591892757125928317262835160377 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(11311535044206459420578689801861 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(11311535044206459420578689801861 / 50000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(591892757125928317262835160377 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(152992977510149012892744533 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(43048417256949502222394857087 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3497925876037468983918864089217 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(42109365988791183706790041939433 / 100000000000000000000000000000000), (103 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(26588271193898263795134550700049 / 100000000000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(236816107750252950992530912187 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(4164228830985898487035268579 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(21466224447373239265811841 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_6_8Raw_0_0_8 : (A2_6_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 0 8)
    (-3517) (-42976) (-107049) w182 w41 w2
    (by decide +kernel) w182_sound w41_sound w2_sound) (by decide +kernel)
lemma A2_6_8Raw_0_1_7 : (A2_6_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 1 7)
    (-3517) (-20283) (-63201) w182 w86 w17
    (by decide +kernel) w182_sound w86_sound w17_sound) (by decide +kernel)
lemma A2_6_8Raw_0_2_6 : (A2_6_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 2 6)
    (-3517) (-5132) (-31013) w182 w171 w67
    (by decide +kernel) w182_sound w171_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_0_3_5 : (A2_6_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 3 5)
    (-3517) (0) (-9730) w182 w195 w133
    (by decide +kernel) w182_sound w195_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_0_4_4 : (A2_6_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 4 4)
    (-3517) (-5132) (0) w182 w171 w195
    (by decide +kernel) w182_sound w171_sound w195_sound) (by decide +kernel)
lemma A2_6_8Raw_0_5_3 : (A2_6_8Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 5 3)
    (-3517) (-20283) (-9730) w182 w86 w133
    (by decide +kernel) w182_sound w86_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_0_6_2 : (A2_6_8Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 0 6 2)
    (-3517) (-42976) (-31013) w182 w41 w67
    (by decide +kernel) w182_sound w41_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_1_0_7 : (A2_6_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 0 7)
    (0) (-42976) (-63201) w195 w41 w17
    (by decide +kernel) w195_sound w41_sound w17_sound) (by decide +kernel)
lemma A2_6_8Raw_1_1_6 : (A2_6_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 1 6)
    (0) (-20283) (-31013) w195 w86 w67
    (by decide +kernel) w195_sound w86_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_1_2_5 : (A2_6_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 2 5)
    (0) (-5132) (-9730) w195 w171 w133
    (by decide +kernel) w195_sound w171_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_1_3_4 : (A2_6_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_6_8Raw_1_4_3 : (A2_6_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 4 3)
    (0) (-5132) (-9730) w195 w171 w133
    (by decide +kernel) w195_sound w171_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_1_5_2 : (A2_6_8Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 5 2)
    (0) (-20283) (-31013) w195 w86 w67
    (by decide +kernel) w195_sound w86_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_1_6_1 : (A2_6_8Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 1 6 1)
    (0) (-42976) (-63201) w195 w41 w17
    (by decide +kernel) w195_sound w41_sound w17_sound) (by decide +kernel)
lemma A2_6_8Raw_2_0_6 : (A2_6_8Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 0 6)
    (-3517) (-42976) (-31013) w182 w41 w67
    (by decide +kernel) w182_sound w41_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_2_1_5 : (A2_6_8Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 1 5)
    (-3517) (-20283) (-9730) w182 w86 w133
    (by decide +kernel) w182_sound w86_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_2_2_4 : (A2_6_8Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 2 4)
    (-3517) (-5132) (0) w182 w171 w195
    (by decide +kernel) w182_sound w171_sound w195_sound) (by decide +kernel)
lemma A2_6_8Raw_2_3_3 : (A2_6_8Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 3 3)
    (-3517) (0) (-9730) w182 w195 w133
    (by decide +kernel) w182_sound w195_sound w133_sound) (by decide +kernel)
lemma A2_6_8Raw_2_4_2 : (A2_6_8Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 4 2)
    (-3517) (-5132) (-31013) w182 w171 w67
    (by decide +kernel) w182_sound w171_sound w67_sound) (by decide +kernel)
lemma A2_6_8Raw_2_5_1 : (A2_6_8Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 5 1)
    (-3517) (-20283) (-63201) w182 w86 w17
    (by decide +kernel) w182_sound w86_sound w17_sound) (by decide +kernel)
lemma A2_6_8Raw_2_6_0 : (A2_6_8Raw (shape 2 6 0)).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) (shape 2 6 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 6 8) (shape 2 6 0)
    (-3517) (-42976) (-107049) w182 w41 w2
    (by decide +kernel) w182_sound w41_sound w2_sound) (by decide +kernel)
lemma A2_6_8Raw_sound (u : Shape) (hu : u ∈ below (shape 2 6 8)) :
    (A2_6_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 6 8) u : ℝ) := by
  rw [A2_6_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_6_8Raw_0_0_8
  · exact A2_6_8Raw_0_1_7
  · exact A2_6_8Raw_0_2_6
  · exact A2_6_8Raw_0_3_5
  · exact A2_6_8Raw_0_4_4
  · exact A2_6_8Raw_0_5_3
  · exact A2_6_8Raw_0_6_2
  · exact A2_6_8Raw_1_0_7
  · exact A2_6_8Raw_1_1_6
  · exact A2_6_8Raw_1_2_5
  · exact A2_6_8Raw_1_3_4
  · exact A2_6_8Raw_1_4_3
  · exact A2_6_8Raw_1_5_2
  · exact A2_6_8Raw_1_6_1
  · exact A2_6_8Raw_2_0_6
  · exact A2_6_8Raw_2_1_5
  · exact A2_6_8Raw_2_2_4
  · exact A2_6_8Raw_2_3_3
  · exact A2_6_8Raw_2_4_2
  · exact A2_6_8Raw_2_5_1
  · exact A2_6_8Raw_2_6_0
def A2_6_8Den : Ball := ⟨(73683614726356645052910002223033 / 25000000000000000000000000000000), (263 / 50000000000000000000000000000000)⟩
lemma A2_6_8Den_sound : A2_6_8Den.Encloses (((below (shape 2 6 8)).map (splitWeight positiveInitial tableP (shape 2 6 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 6 8)) A2_6_8Raw (splitWeight positiveInitial tableP (shape 2 6 8)) A2_6_8Raw_sound) (by decide +kernel)
lemma A2_6_8Den_positive : 0 < A2_6_8Den.lower := by decide +kernel
def A2_6_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(5651499110692180694905247591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(642791775701372526766325518709 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(9021093526912582843203331566559 / 100000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(14287221842052441515014217084377 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(29670146892799120299239106787 / 2500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(182572888731864977572933803 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(830540022111175778026502387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(200822380702981496437118097259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1918936639817210417915987511527 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(33928845772352553367922348016919 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1918936639817210417915987511527 / 25000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(200822380702981496437118097259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(830540022111175778026502387 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(182572888731864977572933803 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(29670146892799120299239106787 / 2500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(14287221842052441515014217084377 / 100000000000000000000000000000000), (61 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(9021093526912582843203331566559 / 100000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(642791775701372526766325518709 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(5651499110692180694905247591 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(7283242185896305552952829 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_6_8Law (u : Shape) : Ball := if u ∈ below (shape 2 6 8) then A2_6_8Table u else .exact 0
lemma A2_6_8Law_check_0_0_8 : contains (.mul (A2_6_8Raw (shape 0 0 8)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_6_8Law_check_0_1_7 : contains (.mul (A2_6_8Raw (shape 0 1 7)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_6_8Law_check_0_2_6 : contains (.mul (A2_6_8Raw (shape 0 2 6)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_6_8Law_check_0_3_5 : contains (.mul (A2_6_8Raw (shape 0 3 5)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_6_8Law_check_0_4_4 : contains (.mul (A2_6_8Raw (shape 0 4 4)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_6_8Law_check_0_5_3 : contains (.mul (A2_6_8Raw (shape 0 5 3)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 5 3)) = true := by decide +kernel
lemma A2_6_8Law_check_0_6_2 : contains (.mul (A2_6_8Raw (shape 0 6 2)) (.inv A2_6_8Den)) (A2_6_8Table (shape 0 6 2)) = true := by decide +kernel
lemma A2_6_8Law_check_1_0_7 : contains (.mul (A2_6_8Raw (shape 1 0 7)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_6_8Law_check_1_1_6 : contains (.mul (A2_6_8Raw (shape 1 1 6)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_6_8Law_check_1_2_5 : contains (.mul (A2_6_8Raw (shape 1 2 5)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_6_8Law_check_1_3_4 : contains (.mul (A2_6_8Raw (shape 1 3 4)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_6_8Law_check_1_4_3 : contains (.mul (A2_6_8Raw (shape 1 4 3)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_6_8Law_check_1_5_2 : contains (.mul (A2_6_8Raw (shape 1 5 2)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 5 2)) = true := by decide +kernel
lemma A2_6_8Law_check_1_6_1 : contains (.mul (A2_6_8Raw (shape 1 6 1)) (.inv A2_6_8Den)) (A2_6_8Table (shape 1 6 1)) = true := by decide +kernel
lemma A2_6_8Law_check_2_0_6 : contains (.mul (A2_6_8Raw (shape 2 0 6)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_6_8Law_check_2_1_5 : contains (.mul (A2_6_8Raw (shape 2 1 5)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_6_8Law_check_2_2_4 : contains (.mul (A2_6_8Raw (shape 2 2 4)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_6_8Law_check_2_3_3 : contains (.mul (A2_6_8Raw (shape 2 3 3)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_6_8Law_check_2_4_2 : contains (.mul (A2_6_8Raw (shape 2 4 2)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_6_8Law_check_2_5_1 : contains (.mul (A2_6_8Raw (shape 2 5 1)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 5 1)) = true := by decide +kernel
lemma A2_6_8Law_check_2_6_0 : contains (.mul (A2_6_8Raw (shape 2 6 0)) (.inv A2_6_8Den)) (A2_6_8Table (shape 2 6 0)) = true := by decide +kernel
lemma A2_6_8Law_check (u : Shape) (hu : u ∈ below (shape 2 6 8)) :
    contains (.mul (A2_6_8Raw u) (.inv A2_6_8Den)) (A2_6_8Table u) = true := by
  rw [A2_6_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_6_8Law_check_0_0_8
  · exact A2_6_8Law_check_0_1_7
  · exact A2_6_8Law_check_0_2_6
  · exact A2_6_8Law_check_0_3_5
  · exact A2_6_8Law_check_0_4_4
  · exact A2_6_8Law_check_0_5_3
  · exact A2_6_8Law_check_0_6_2
  · exact A2_6_8Law_check_1_0_7
  · exact A2_6_8Law_check_1_1_6
  · exact A2_6_8Law_check_1_2_5
  · exact A2_6_8Law_check_1_3_4
  · exact A2_6_8Law_check_1_4_3
  · exact A2_6_8Law_check_1_5_2
  · exact A2_6_8Law_check_1_6_1
  · exact A2_6_8Law_check_2_0_6
  · exact A2_6_8Law_check_2_1_5
  · exact A2_6_8Law_check_2_2_4
  · exact A2_6_8Law_check_2_3_3
  · exact A2_6_8Law_check_2_4_2
  · exact A2_6_8Law_check_2_5_1
  · exact A2_6_8Law_check_2_6_0
lemma A2_6_8Law_sound (u : Shape) :
    (A2_6_8Law u).Encloses (stageALaw (shape 2 6 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 6 8)
  · have h := contains_sound (Ball.mul_sound (A2_6_8Raw_sound u hu)
      (Ball.inv_sound A2_6_8Den_sound A2_6_8Den_positive)) (A2_6_8Law_check u hu)
    simpa only [A2_6_8Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_6_8Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
