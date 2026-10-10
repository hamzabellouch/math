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
lemma A2_5_9_below : below (shape 2 5 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1)] := by decide +kernel
def A2_5_9Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(273399354531404847951902717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(68946518086100053614010604923 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5026696090772982390642513919 / 39062500000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(34960645180196030788867851759237 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(14646816460940129823291825517243 / 50000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(549758056631767773116973570093 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(20110279532265531872236546511 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(481900057386660180442774113293 / 6250000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(481900057386660180442774113293 / 6250000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(20110279532265531872236546511 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(549758056631767773116973570093 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(14646816460940129823291825517243 / 50000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(34960645180196030788867851759237 / 50000000000000000000000000000000), (21 / 25000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(5026696090772982390642513919 / 39062500000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(68946518086100053614010604923 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(273399354531404847951902717 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_5_9Raw_0_0_8 : (A2_5_9Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 0 8)
    (-3578) (-24599) (-92989) w181 w82 w6
    (by decide +kernel) w181_sound w82_sound w6_sound) (by decide +kernel)
lemma A2_5_9Raw_0_1_7 : (A2_5_9Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 1 7)
    (-3578) (-8700) (-46655) w181 w137 w39
    (by decide +kernel) w181_sound w137_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_0_2_6 : (A2_5_9Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 2 6)
    (-3578) (0) (-16926) w181 w195 w101
    (by decide +kernel) w181_sound w195_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_0_3_5 : (A2_5_9Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 3 5)
    (-3578) (0) (0) w181 w195 w195
    (by decide +kernel) w181_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_0_4_4 : (A2_5_9Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 4 4)
    (-3578) (-8700) (0) w181 w137 w195
    (by decide +kernel) w181_sound w137_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_0_5_3 : (A2_5_9Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 0 5 3)
    (-3578) (-24599) (-16926) w181 w82 w101
    (by decide +kernel) w181_sound w82_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_0_7 : (A2_5_9Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 0 7)
    (0) (-24599) (-46655) w195 w82 w39
    (by decide +kernel) w195_sound w82_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_1_1_6 : (A2_5_9Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 1 6)
    (0) (-8700) (-16926) w195 w137 w101
    (by decide +kernel) w195_sound w137_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_2_5 : (A2_5_9Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_1_3_4 : (A2_5_9Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_1_4_3 : (A2_5_9Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 4 3)
    (0) (-8700) (-16926) w195 w137 w101
    (by decide +kernel) w195_sound w137_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_1_5_2 : (A2_5_9Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 1 5 2)
    (0) (-24599) (-46655) w195 w82 w39
    (by decide +kernel) w195_sound w82_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_2_0_6 : (A2_5_9Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 0 6)
    (-3578) (-24599) (-16926) w181 w82 w101
    (by decide +kernel) w181_sound w82_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_2_1_5 : (A2_5_9Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 1 5)
    (-3578) (-8700) (0) w181 w137 w195
    (by decide +kernel) w181_sound w137_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_2_2_4 : (A2_5_9Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 2 4)
    (-3578) (0) (0) w181 w195 w195
    (by decide +kernel) w181_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_5_9Raw_2_3_3 : (A2_5_9Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 3 3)
    (-3578) (0) (-16926) w181 w195 w101
    (by decide +kernel) w181_sound w195_sound w101_sound) (by decide +kernel)
lemma A2_5_9Raw_2_4_2 : (A2_5_9Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 4 2)
    (-3578) (-8700) (-46655) w181 w137 w39
    (by decide +kernel) w181_sound w137_sound w39_sound) (by decide +kernel)
lemma A2_5_9Raw_2_5_1 : (A2_5_9Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 5 9) (shape 2 5 1)
    (-3578) (-24599) (-92989) w181 w82 w6
    (by decide +kernel) w181_sound w82_sound w6_sound) (by decide +kernel)
lemma A2_5_9Raw_sound (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
    (A2_5_9Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 5 9) u : ℝ) := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_5_9Raw_0_0_8
  · exact A2_5_9Raw_0_1_7
  · exact A2_5_9Raw_0_2_6
  · exact A2_5_9Raw_0_3_5
  · exact A2_5_9Raw_0_4_4
  · exact A2_5_9Raw_0_5_3
  · exact A2_5_9Raw_1_0_7
  · exact A2_5_9Raw_1_1_6
  · exact A2_5_9Raw_1_2_5
  · exact A2_5_9Raw_1_3_4
  · exact A2_5_9Raw_1_4_3
  · exact A2_5_9Raw_1_5_2
  · exact A2_5_9Raw_2_0_6
  · exact A2_5_9Raw_2_1_5
  · exact A2_5_9Raw_2_2_4
  · exact A2_5_9Raw_2_3_3
  · exact A2_5_9Raw_2_4_2
  · exact A2_5_9Raw_2_5_1
def A2_5_9Den : Ball := ⟨(55312489073820944932330853887411 / 12500000000000000000000000000000), (11 / 2500000000000000000000000000000)⟩
lemma A2_5_9Den_sound : A2_5_9Den.Encloses (((below (shape 2 5 9)).map (splitWeight positiveInitial tableP (shape 2 5 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 5 9)) A2_5_9Raw (splitWeight positiveInitial tableP (shape 2 5 9)) A2_5_9Raw_sound) (by decide +kernel)
lemma A2_5_9Den_positive : 0 < A2_5_9Den.lower := by decide +kernel
def A2_5_9Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(4942814165649309970823409 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(62324548434335428709365572507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(116324018389450319333620372957 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(1580142467171247110537433641061 / 10000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3310015673266902490136717119167 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(248478266769938591622945895033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9089393674467454662811780111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(54451994641697075498935578049 / 3125000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(706214828767994042269955497393 / 3125000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(706214828767994042269955497393 / 3125000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(54451994641697075498935578049 / 3125000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(9089393674467454662811780111 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(248478266769938591622945895033 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3310015673266902490136717119167 / 50000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1580142467171247110537433641061 / 10000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(116324018389450319333620372957 / 4000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(62324548434335428709365572507 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(4942814165649309970823409 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_5_9Law (u : Shape) : Ball := if u ∈ below (shape 2 5 9) then A2_5_9Table u else .exact 0
lemma A2_5_9Law_check_0_0_8 : contains (.mul (A2_5_9Raw (shape 0 0 8)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_5_9Law_check_0_1_7 : contains (.mul (A2_5_9Raw (shape 0 1 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_5_9Law_check_0_2_6 : contains (.mul (A2_5_9Raw (shape 0 2 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_5_9Law_check_0_3_5 : contains (.mul (A2_5_9Raw (shape 0 3 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_5_9Law_check_0_4_4 : contains (.mul (A2_5_9Raw (shape 0 4 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_5_9Law_check_0_5_3 : contains (.mul (A2_5_9Raw (shape 0 5 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 0 5 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_0_7 : contains (.mul (A2_5_9Raw (shape 1 0 7)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_5_9Law_check_1_1_6 : contains (.mul (A2_5_9Raw (shape 1 1 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_5_9Law_check_1_2_5 : contains (.mul (A2_5_9Raw (shape 1 2 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_5_9Law_check_1_3_4 : contains (.mul (A2_5_9Raw (shape 1 3 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_5_9Law_check_1_4_3 : contains (.mul (A2_5_9Raw (shape 1 4 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_5_9Law_check_1_5_2 : contains (.mul (A2_5_9Raw (shape 1 5 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 1 5 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_0_6 : contains (.mul (A2_5_9Raw (shape 2 0 6)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_5_9Law_check_2_1_5 : contains (.mul (A2_5_9Raw (shape 2 1 5)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_5_9Law_check_2_2_4 : contains (.mul (A2_5_9Raw (shape 2 2 4)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_5_9Law_check_2_3_3 : contains (.mul (A2_5_9Raw (shape 2 3 3)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_5_9Law_check_2_4_2 : contains (.mul (A2_5_9Raw (shape 2 4 2)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_5_9Law_check_2_5_1 : contains (.mul (A2_5_9Raw (shape 2 5 1)) (.inv A2_5_9Den)) (A2_5_9Table (shape 2 5 1)) = true := by decide +kernel
lemma A2_5_9Law_check (u : Shape) (hu : u ∈ below (shape 2 5 9)) :
    contains (.mul (A2_5_9Raw u) (.inv A2_5_9Den)) (A2_5_9Table u) = true := by
  rw [A2_5_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_5_9Law_check_0_0_8
  · exact A2_5_9Law_check_0_1_7
  · exact A2_5_9Law_check_0_2_6
  · exact A2_5_9Law_check_0_3_5
  · exact A2_5_9Law_check_0_4_4
  · exact A2_5_9Law_check_0_5_3
  · exact A2_5_9Law_check_1_0_7
  · exact A2_5_9Law_check_1_1_6
  · exact A2_5_9Law_check_1_2_5
  · exact A2_5_9Law_check_1_3_4
  · exact A2_5_9Law_check_1_4_3
  · exact A2_5_9Law_check_1_5_2
  · exact A2_5_9Law_check_2_0_6
  · exact A2_5_9Law_check_2_1_5
  · exact A2_5_9Law_check_2_2_4
  · exact A2_5_9Law_check_2_3_3
  · exact A2_5_9Law_check_2_4_2
  · exact A2_5_9Law_check_2_5_1
lemma A2_5_9Law_sound (u : Shape) :
    (A2_5_9Law u).Encloses (stageALaw (shape 2 5 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 5 9)
  · have h := contains_sound (Ball.mul_sound (A2_5_9Raw_sound u hu)
      (Ball.inv_sound A2_5_9Den_sound A2_5_9Den_positive)) (A2_5_9Law_check u hu)
    simpa only [A2_5_9Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_5_9Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
