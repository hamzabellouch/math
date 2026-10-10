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
lemma A3_4_9_below : below (shape 3 4 9) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1)] := by decide +kernel
def A3_4_9Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(52604183508248426299746893 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(107048101953376826039075703437 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(7949191186854819609435816255409 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(29617641665026676343636152910233 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2097142753831614220150564409891 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(25538511110736612768307319049 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1305033413039090422171216880161 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(31184557034256196846304679690331 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1478492526375484315026102985421 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(1478492526375484315026102985421 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(31184557034256196846304679690331 / 50000000000000000000000000000000), (39 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(1305033413039090422171216880161 / 12500000000000000000000000000000), (3 / 10000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(25538511110736612768307319049 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(2097142753831614220150564409891 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(29617641665026676343636152910233 / 100000000000000000000000000000000), (19 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(7949191186854819609435816255409 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(107048101953376826039075703437 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(52604183508248426299746893 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A3_4_9Raw_0_0_8 : (A3_4_9Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 0 8)
    (-7447) (-17336) (-96770) w144 w97 w3
    (by decide +kernel) w144_sound w97_sound w3_sound) (by decide +kernel)
lemma A3_4_9Raw_0_1_7 : (A3_4_9Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 1 7)
    (-7447) (-4721) (-49297) w144 w173 w36
    (by decide +kernel) w144_sound w173_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_0_2_6 : (A3_4_9Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 2 6)
    (-7447) (0) (-17874) w144 w195 w95
    (by decide +kernel) w144_sound w195_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_0_3_5 : (A3_4_9Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 3 5)
    (-7447) (-4721) (0) w144 w173 w195
    (by decide +kernel) w144_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_0_4_4 : (A3_4_9Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 0 4 4)
    (-7447) (-17336) (0) w144 w97 w195
    (by decide +kernel) w144_sound w97_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_0_7 : (A3_4_9Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 0 7)
    (0) (-17336) (-49297) w195 w97 w36
    (by decide +kernel) w195_sound w97_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_1_1_6 : (A3_4_9Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 1 6)
    (0) (-4721) (-17874) w195 w173 w95
    (by decide +kernel) w195_sound w173_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_1_2_5 : (A3_4_9Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_3_4 : (A3_4_9Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 3 4)
    (0) (-4721) (0) w195 w173 w195
    (by decide +kernel) w195_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_1_4_3 : (A3_4_9Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 1 4 3)
    (0) (-17336) (-17874) w195 w97 w95
    (by decide +kernel) w195_sound w97_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_0_6 : (A3_4_9Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 0 6)
    (0) (-17336) (-17874) w195 w97 w95
    (by decide +kernel) w195_sound w97_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_1_5 : (A3_4_9Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 1 5)
    (0) (-4721) (0) w195 w173 w195
    (by decide +kernel) w195_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_2_2_4 : (A3_4_9Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_2_3_3 : (A3_4_9Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 3 3)
    (0) (-4721) (-17874) w195 w173 w95
    (by decide +kernel) w195_sound w173_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_2_4_2 : (A3_4_9Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 2 4 2)
    (0) (-17336) (-49297) w195 w97 w36
    (by decide +kernel) w195_sound w97_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_3_0_5 : (A3_4_9Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 0 5)
    (-7447) (-17336) (0) w144 w97 w195
    (by decide +kernel) w144_sound w97_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_3_1_4 : (A3_4_9Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 1 4)
    (-7447) (-4721) (0) w144 w173 w195
    (by decide +kernel) w144_sound w173_sound w195_sound) (by decide +kernel)
lemma A3_4_9Raw_3_2_3 : (A3_4_9Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 2 3)
    (-7447) (0) (-17874) w144 w195 w95
    (by decide +kernel) w144_sound w195_sound w95_sound) (by decide +kernel)
lemma A3_4_9Raw_3_3_2 : (A3_4_9Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 3 2)
    (-7447) (-4721) (-49297) w144 w173 w36
    (by decide +kernel) w144_sound w173_sound w36_sound) (by decide +kernel)
lemma A3_4_9Raw_3_4_1 : (A3_4_9Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 4 9) (shape 3 4 1)
    (-7447) (-17336) (-96770) w144 w97 w3
    (by decide +kernel) w144_sound w97_sound w3_sound) (by decide +kernel)
lemma A3_4_9Raw_sound (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
    (A3_4_9Raw u).Encloses (splitWeight positiveInitial tableP (shape 3 4 9) u : ℝ) := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_4_9Raw_0_0_8
  · exact A3_4_9Raw_0_1_7
  · exact A3_4_9Raw_0_2_6
  · exact A3_4_9Raw_0_3_5
  · exact A3_4_9Raw_0_4_4
  · exact A3_4_9Raw_1_0_7
  · exact A3_4_9Raw_1_1_6
  · exact A3_4_9Raw_1_2_5
  · exact A3_4_9Raw_1_3_4
  · exact A3_4_9Raw_1_4_3
  · exact A3_4_9Raw_2_0_6
  · exact A3_4_9Raw_2_1_5
  · exact A3_4_9Raw_2_2_4
  · exact A3_4_9Raw_2_3_3
  · exact A3_4_9Raw_2_4_2
  · exact A3_4_9Raw_3_0_5
  · exact A3_4_9Raw_3_1_4
  · exact A3_4_9Raw_3_2_3
  · exact A3_4_9Raw_3_3_2
  · exact A3_4_9Raw_3_4_1
def A3_4_9Den : Ball := ⟨(222064085094079557733888212669047 / 50000000000000000000000000000000), (241 / 50000000000000000000000000000000)⟩
lemma A3_4_9Den_sound : A3_4_9Den.Encloses (((below (shape 3 4 9)).map (splitWeight positiveInitial tableP (shape 3 4 9))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 4 9)) A3_4_9Raw (splitWeight positiveInitial tableP (shape 3 4 9)) A3_4_9Raw_sound) (by decide +kernel)
lemma A3_4_9Den_positive : 0 < A3_4_9Den.lower := by decide +kernel
def A3_4_9Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(12051487514068842044483780559 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1789841698959800118150495751873 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(6668714946065880326404692767049 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(944386280628468031665627187853 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(28751284904892409882235281843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22516022786312800353724657277333 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(14043043935287673024483191909343 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(665795428265271676282857013551 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(665795428265271676282857013551 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(14043043935287673024483191909343 / 100000000000000000000000000000000), (17 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(22516022786312800353724657277333 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(1175366482595508974701704124553 / 50000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(28751284904892409882235281843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(944386280628468031665627187853 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(6668714946065880326404692767049 / 100000000000000000000000000000000), (1 / 4000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1789841698959800118150495751873 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(12051487514068842044483780559 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2961092486317753981806299 / 2500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_4_9Law (u : Shape) : Ball := if u ∈ below (shape 3 4 9) then A3_4_9Table u else .exact 0
lemma A3_4_9Law_check_0_0_8 : contains (.mul (A3_4_9Raw (shape 0 0 8)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 0 8)) = true := by decide +kernel
lemma A3_4_9Law_check_0_1_7 : contains (.mul (A3_4_9Raw (shape 0 1 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_4_9Law_check_0_2_6 : contains (.mul (A3_4_9Raw (shape 0 2 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_4_9Law_check_0_3_5 : contains (.mul (A3_4_9Raw (shape 0 3 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_4_9Law_check_0_4_4 : contains (.mul (A3_4_9Raw (shape 0 4 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 0 4 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_0_7 : contains (.mul (A3_4_9Raw (shape 1 0 7)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_4_9Law_check_1_1_6 : contains (.mul (A3_4_9Raw (shape 1 1 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_4_9Law_check_1_2_5 : contains (.mul (A3_4_9Raw (shape 1 2 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_4_9Law_check_1_3_4 : contains (.mul (A3_4_9Raw (shape 1 3 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_4_9Law_check_1_4_3 : contains (.mul (A3_4_9Raw (shape 1 4 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 1 4 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_0_6 : contains (.mul (A3_4_9Raw (shape 2 0 6)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_4_9Law_check_2_1_5 : contains (.mul (A3_4_9Raw (shape 2 1 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_4_9Law_check_2_2_4 : contains (.mul (A3_4_9Raw (shape 2 2 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_4_9Law_check_2_3_3 : contains (.mul (A3_4_9Raw (shape 2 3 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_4_9Law_check_2_4_2 : contains (.mul (A3_4_9Raw (shape 2 4 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 2 4 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_0_5 : contains (.mul (A3_4_9Raw (shape 3 0 5)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_4_9Law_check_3_1_4 : contains (.mul (A3_4_9Raw (shape 3 1 4)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_4_9Law_check_3_2_3 : contains (.mul (A3_4_9Raw (shape 3 2 3)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_4_9Law_check_3_3_2 : contains (.mul (A3_4_9Raw (shape 3 3 2)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_4_9Law_check_3_4_1 : contains (.mul (A3_4_9Raw (shape 3 4 1)) (.inv A3_4_9Den)) (A3_4_9Table (shape 3 4 1)) = true := by decide +kernel
lemma A3_4_9Law_check (u : Shape) (hu : u ∈ below (shape 3 4 9)) :
    contains (.mul (A3_4_9Raw u) (.inv A3_4_9Den)) (A3_4_9Table u) = true := by
  rw [A3_4_9_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_4_9Law_check_0_0_8
  · exact A3_4_9Law_check_0_1_7
  · exact A3_4_9Law_check_0_2_6
  · exact A3_4_9Law_check_0_3_5
  · exact A3_4_9Law_check_0_4_4
  · exact A3_4_9Law_check_1_0_7
  · exact A3_4_9Law_check_1_1_6
  · exact A3_4_9Law_check_1_2_5
  · exact A3_4_9Law_check_1_3_4
  · exact A3_4_9Law_check_1_4_3
  · exact A3_4_9Law_check_2_0_6
  · exact A3_4_9Law_check_2_1_5
  · exact A3_4_9Law_check_2_2_4
  · exact A3_4_9Law_check_2_3_3
  · exact A3_4_9Law_check_2_4_2
  · exact A3_4_9Law_check_3_0_5
  · exact A3_4_9Law_check_3_1_4
  · exact A3_4_9Law_check_3_2_3
  · exact A3_4_9Law_check_3_3_2
  · exact A3_4_9Law_check_3_4_1
lemma A3_4_9Law_sound (u : Shape) :
    (A3_4_9Law u).Encloses (stageALaw (shape 3 4 9) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 4 9)
  · have h := contains_sound (Ball.mul_sound (A3_4_9Raw_sound u hu)
      (Ball.inv_sound A3_4_9Den_sound A3_4_9Den_positive)) (A3_4_9Law_check u hu)
    simpa only [A3_4_9Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_4_9Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
