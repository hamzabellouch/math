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
lemma A3_5_8_below : below (shape 3 5 8) = [
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
  (shape 2 5 1),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 3 5 0)] := by decide +kernel
def A3_5_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(328669583149386781185709 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(19209894118417149770024794673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1723177871786636609721592861297 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(17261354968926351667760393882717 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(445432629432246067049549352859 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(855619240745488096141205264161 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(66803408806529843382445509 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(640582734291565687942242590477 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(35260740785769191116135010727999 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(6416822165959928926276575414637 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(174482677080586900029834379827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(174482677080586900029834379827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(6416822165959928926276575414637 / 50000000000000000000000000000000), (33 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(35260740785769191116135010727999 / 100000000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(640582734291565687942242590477 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(66803408806529843382445509 / 1250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(855619240745488096141205264161 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(445432629432246067049549352859 / 2500000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(17261354968926351667760393882717 / 100000000000000000000000000000000), (1 / 2500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(1723177871786636609721592861297 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(19209894118417149770024794673 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(328669583149386781185709 / 1562500000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A3_5_8Raw_0_0_8 : (A3_5_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 0 8)
    (-7143) (-30044) (-116558) w148 w68 w1
    (by decide +kernel) w148_sound w68_sound w1_sound) (by decide +kernel)
lemma A3_5_8Raw_0_1_7 : (A3_5_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 1 7)
    (-7143) (-10107) (-68325) w148 w128 w14
    (by decide +kernel) w148_sound w128_sound w14_sound) (by decide +kernel)
lemma A3_5_8Raw_0_2_6 : (A3_5_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 2 6)
    (-7143) (0) (-33467) w148 w195 w57
    (by decide +kernel) w148_sound w195_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_0_3_5 : (A3_5_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 3 5)
    (-7143) (0) (-10424) w148 w195 w127
    (by decide +kernel) w148_sound w195_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_0_4_4 : (A3_5_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 4 4)
    (-7143) (-10107) (0) w148 w128 w195
    (by decide +kernel) w148_sound w128_sound w195_sound) (by decide +kernel)
lemma A3_5_8Raw_0_5_3 : (A3_5_8Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 0 5 3)
    (-7143) (-30044) (-10424) w148 w68 w127
    (by decide +kernel) w148_sound w68_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_1_0_7 : (A3_5_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 0 7)
    (0) (-30044) (-68325) w195 w68 w14
    (by decide +kernel) w195_sound w68_sound w14_sound) (by decide +kernel)
lemma A3_5_8Raw_1_1_6 : (A3_5_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 1 6)
    (0) (-10107) (-33467) w195 w128 w57
    (by decide +kernel) w195_sound w128_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_1_2_5 : (A3_5_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 2 5)
    (0) (0) (-10424) w195 w195 w127
    (by decide +kernel) w195_sound w195_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_1_3_4 : (A3_5_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_5_8Raw_1_4_3 : (A3_5_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 4 3)
    (0) (-10107) (-10424) w195 w128 w127
    (by decide +kernel) w195_sound w128_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_1_5_2 : (A3_5_8Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 1 5 2)
    (0) (-30044) (-33467) w195 w68 w57
    (by decide +kernel) w195_sound w68_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_2_0_6 : (A3_5_8Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 0 6)
    (0) (-30044) (-33467) w195 w68 w57
    (by decide +kernel) w195_sound w68_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_2_1_5 : (A3_5_8Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 1 5)
    (0) (-10107) (-10424) w195 w128 w127
    (by decide +kernel) w195_sound w128_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_2_2_4 : (A3_5_8Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_5_8Raw_2_3_3 : (A3_5_8Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 3 3)
    (0) (0) (-10424) w195 w195 w127
    (by decide +kernel) w195_sound w195_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_2_4_2 : (A3_5_8Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 4 2)
    (0) (-10107) (-33467) w195 w128 w57
    (by decide +kernel) w195_sound w128_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_2_5_1 : (A3_5_8Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 2 5 1)
    (0) (-30044) (-68325) w195 w68 w14
    (by decide +kernel) w195_sound w68_sound w14_sound) (by decide +kernel)
lemma A3_5_8Raw_3_0_5 : (A3_5_8Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 0 5)
    (-7143) (-30044) (-10424) w148 w68 w127
    (by decide +kernel) w148_sound w68_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_3_1_4 : (A3_5_8Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 1 4)
    (-7143) (-10107) (0) w148 w128 w195
    (by decide +kernel) w148_sound w128_sound w195_sound) (by decide +kernel)
lemma A3_5_8Raw_3_2_3 : (A3_5_8Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 2 3)
    (-7143) (0) (-10424) w148 w195 w127
    (by decide +kernel) w148_sound w195_sound w127_sound) (by decide +kernel)
lemma A3_5_8Raw_3_3_2 : (A3_5_8Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 3 2)
    (-7143) (0) (-33467) w148 w195 w57
    (by decide +kernel) w148_sound w195_sound w57_sound) (by decide +kernel)
lemma A3_5_8Raw_3_4_1 : (A3_5_8Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 4 1)
    (-7143) (-10107) (-68325) w148 w128 w14
    (by decide +kernel) w148_sound w128_sound w14_sound) (by decide +kernel)
lemma A3_5_8Raw_3_5_0 : (A3_5_8Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 5 8) (shape 3 5 0)
    (-7143) (-30044) (-116558) w148 w68 w1
    (by decide +kernel) w148_sound w68_sound w1_sound) (by decide +kernel)
lemma A3_5_8Raw_sound (u : Shape) (hu : u ∈ below (shape 3 5 8)) :
    (A3_5_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 3 5 8) u : ℝ) := by
  rw [A3_5_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_5_8Raw_0_0_8
  · exact A3_5_8Raw_0_1_7
  · exact A3_5_8Raw_0_2_6
  · exact A3_5_8Raw_0_3_5
  · exact A3_5_8Raw_0_4_4
  · exact A3_5_8Raw_0_5_3
  · exact A3_5_8Raw_1_0_7
  · exact A3_5_8Raw_1_1_6
  · exact A3_5_8Raw_1_2_5
  · exact A3_5_8Raw_1_3_4
  · exact A3_5_8Raw_1_4_3
  · exact A3_5_8Raw_1_5_2
  · exact A3_5_8Raw_2_0_6
  · exact A3_5_8Raw_2_1_5
  · exact A3_5_8Raw_2_2_4
  · exact A3_5_8Raw_2_3_3
  · exact A3_5_8Raw_2_4_2
  · exact A3_5_8Raw_2_5_1
  · exact A3_5_8Raw_3_0_5
  · exact A3_5_8Raw_3_1_4
  · exact A3_5_8Raw_3_2_3
  · exact A3_5_8Raw_3_3_2
  · exact A3_5_8Raw_3_4_1
  · exact A3_5_8Raw_3_5_0
def A3_5_8Den : Ball := ⟨(93616032861888673699101131780679 / 25000000000000000000000000000000), (89 / 25000000000000000000000000000000)⟩
lemma A3_5_8Den_sound : A3_5_8Den.Encloses (((below (shape 3 5 8)).map (splitWeight positiveInitial tableP (shape 3 5 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 5 8)) A3_5_8Raw (splitWeight positiveInitial tableP (shape 3 5 8)) A3_5_8Raw_sound) (by decide +kernel)
lemma A3_5_8Den_positive : 0 < A3_5_8Den.lower := by decide +kernel
def A3_5_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(2564984534587871162395170351 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(14380364892404713617013575761 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2304807526184103743816886449421 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(951616119194862462941861582207 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(228491641492590121381678806719 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(1427178801842300281575260073 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(9416319968874671475112547173063 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(26704827405880776123709349345923 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1713601284361899518761493331217 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(46595297767531026173741859253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(46595297767531026173741859253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1713601284361899518761493331217 / 50000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(26704827405880776123709349345923 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(9416319968874671475112547173063 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(342133027168868932426842786183 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(1427178801842300281575260073 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(228491641492590121381678806719 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(951616119194862462941861582207 / 20000000000000000000000000000000), (17 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(2304807526184103743816886449421 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(14380364892404713617013575761 / 3125000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2564984534587871162395170351 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(5617321274602978972531421 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_5_8Law (u : Shape) : Ball := if u ∈ below (shape 3 5 8) then A3_5_8Table u else .exact 0
lemma A3_5_8Law_check_0_0_8 : contains (.mul (A3_5_8Raw (shape 0 0 8)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A3_5_8Law_check_0_1_7 : contains (.mul (A3_5_8Raw (shape 0 1 7)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_5_8Law_check_0_2_6 : contains (.mul (A3_5_8Raw (shape 0 2 6)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_5_8Law_check_0_3_5 : contains (.mul (A3_5_8Raw (shape 0 3 5)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_5_8Law_check_0_4_4 : contains (.mul (A3_5_8Raw (shape 0 4 4)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A3_5_8Law_check_0_5_3 : contains (.mul (A3_5_8Raw (shape 0 5 3)) (.inv A3_5_8Den)) (A3_5_8Table (shape 0 5 3)) = true := by decide +kernel
lemma A3_5_8Law_check_1_0_7 : contains (.mul (A3_5_8Raw (shape 1 0 7)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_5_8Law_check_1_1_6 : contains (.mul (A3_5_8Raw (shape 1 1 6)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_5_8Law_check_1_2_5 : contains (.mul (A3_5_8Raw (shape 1 2 5)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_5_8Law_check_1_3_4 : contains (.mul (A3_5_8Raw (shape 1 3 4)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_5_8Law_check_1_4_3 : contains (.mul (A3_5_8Raw (shape 1 4 3)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A3_5_8Law_check_1_5_2 : contains (.mul (A3_5_8Raw (shape 1 5 2)) (.inv A3_5_8Den)) (A3_5_8Table (shape 1 5 2)) = true := by decide +kernel
lemma A3_5_8Law_check_2_0_6 : contains (.mul (A3_5_8Raw (shape 2 0 6)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_5_8Law_check_2_1_5 : contains (.mul (A3_5_8Raw (shape 2 1 5)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_5_8Law_check_2_2_4 : contains (.mul (A3_5_8Raw (shape 2 2 4)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_5_8Law_check_2_3_3 : contains (.mul (A3_5_8Raw (shape 2 3 3)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_5_8Law_check_2_4_2 : contains (.mul (A3_5_8Raw (shape 2 4 2)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 4 2)) = true := by decide +kernel
lemma A3_5_8Law_check_2_5_1 : contains (.mul (A3_5_8Raw (shape 2 5 1)) (.inv A3_5_8Den)) (A3_5_8Table (shape 2 5 1)) = true := by decide +kernel
lemma A3_5_8Law_check_3_0_5 : contains (.mul (A3_5_8Raw (shape 3 0 5)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_5_8Law_check_3_1_4 : contains (.mul (A3_5_8Raw (shape 3 1 4)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_5_8Law_check_3_2_3 : contains (.mul (A3_5_8Raw (shape 3 2 3)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_5_8Law_check_3_3_2 : contains (.mul (A3_5_8Raw (shape 3 3 2)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_5_8Law_check_3_4_1 : contains (.mul (A3_5_8Raw (shape 3 4 1)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 4 1)) = true := by decide +kernel
lemma A3_5_8Law_check_3_5_0 : contains (.mul (A3_5_8Raw (shape 3 5 0)) (.inv A3_5_8Den)) (A3_5_8Table (shape 3 5 0)) = true := by decide +kernel
lemma A3_5_8Law_check (u : Shape) (hu : u ∈ below (shape 3 5 8)) :
    contains (.mul (A3_5_8Raw u) (.inv A3_5_8Den)) (A3_5_8Table u) = true := by
  rw [A3_5_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_5_8Law_check_0_0_8
  · exact A3_5_8Law_check_0_1_7
  · exact A3_5_8Law_check_0_2_6
  · exact A3_5_8Law_check_0_3_5
  · exact A3_5_8Law_check_0_4_4
  · exact A3_5_8Law_check_0_5_3
  · exact A3_5_8Law_check_1_0_7
  · exact A3_5_8Law_check_1_1_6
  · exact A3_5_8Law_check_1_2_5
  · exact A3_5_8Law_check_1_3_4
  · exact A3_5_8Law_check_1_4_3
  · exact A3_5_8Law_check_1_5_2
  · exact A3_5_8Law_check_2_0_6
  · exact A3_5_8Law_check_2_1_5
  · exact A3_5_8Law_check_2_2_4
  · exact A3_5_8Law_check_2_3_3
  · exact A3_5_8Law_check_2_4_2
  · exact A3_5_8Law_check_2_5_1
  · exact A3_5_8Law_check_3_0_5
  · exact A3_5_8Law_check_3_1_4
  · exact A3_5_8Law_check_3_2_3
  · exact A3_5_8Law_check_3_3_2
  · exact A3_5_8Law_check_3_4_1
  · exact A3_5_8Law_check_3_5_0
lemma A3_5_8Law_sound (u : Shape) :
    (A3_5_8Law u).Encloses (stageALaw (shape 3 5 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 5 8)
  · have h := contains_sound (Ball.mul_sound (A3_5_8Raw_sound u hu)
      (Ball.inv_sound A3_5_8Den_sound A3_5_8Den_positive)) (A3_5_8Law_check u hu)
    simpa only [A3_5_8Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_5_8Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
