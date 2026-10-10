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
lemma A2_7_7_below : below (shape 2 7 7) = [
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
  (shape 1 7 0),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 2 6 0)] := by decide +kernel
def A2_7_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(997980326700703990907442669 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(110767244555364068131295527073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(17036705883006141337553720298693 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(69038904979943881194700567488221 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(17481972130738693443717668197977 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(60056388144364868734784399473 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(2064990167644092904399448839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(756166967065100758247607 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(71473408038032577228923343497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(3124339826741735799459034189257 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨1, 0⟩
  | 1, 5, 2 => ⟨(3124339826741735799459034189257 / 50000000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(71473408038032577228923343497 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(756166967065100758247607 / 625000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2064990167644092904399448839 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(60056388144364868734784399473 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(17481972130738693443717668197977 / 100000000000000000000000000000000), (11 / 25000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(69038904979943881194700567488221 / 100000000000000000000000000000000), (87 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(17036705883006141337553720298693 / 100000000000000000000000000000000), (43 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(110767244555364068131295527073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(997980326700703990907442669 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_7_7Raw_0_1_7 : (A2_7_7Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 1 7)
    (-3705) (-35684) (-68829) w179 w52 w13
    (by decide +kernel) w179_sound w52_sound w13_sound) (by decide +kernel)
lemma A2_7_7Raw_0_2_6 : (A2_7_7Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 2 6)
    (-3705) (-13735) (-36752) w179 w119 w48
    (by decide +kernel) w179_sound w119_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_0_3_5 : (A2_7_7Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 3 5)
    (-3705) (0) (-13993) w179 w195 w118
    (by decide +kernel) w179_sound w195_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_0_4_4 : (A2_7_7Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 4 4)
    (-3705) (0) (0) w179 w195 w195
    (by decide +kernel) w179_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_0_5_3 : (A2_7_7Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 5 3)
    (-3705) (-13735) (0) w179 w119 w195
    (by decide +kernel) w179_sound w119_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_0_6_2 : (A2_7_7Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 6 2)
    (-3705) (-35684) (-13993) w179 w52 w118
    (by decide +kernel) w179_sound w52_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_0_7_1 : (A2_7_7Raw (shape 0 7 1)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 0 7 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 0 7 1)
    (-3705) (-67421) (-36752) w179 w15 w48
    (by decide +kernel) w179_sound w15_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_1_0_7 : (A2_7_7Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 0 7)
    (0) (-67421) (-68829) w195 w15 w13
    (by decide +kernel) w195_sound w15_sound w13_sound) (by decide +kernel)
lemma A2_7_7Raw_1_1_6 : (A2_7_7Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 1 6)
    (0) (-35684) (-36752) w195 w52 w48
    (by decide +kernel) w195_sound w52_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_1_2_5 : (A2_7_7Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 2 5)
    (0) (-13735) (-13993) w195 w119 w118
    (by decide +kernel) w195_sound w119_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_1_3_4 : (A2_7_7Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_1_4_3 : (A2_7_7Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 4 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_1_5_2 : (A2_7_7Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 5 2)
    (0) (-13735) (-13993) w195 w119 w118
    (by decide +kernel) w195_sound w119_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_1_6_1 : (A2_7_7Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 6 1)
    (0) (-35684) (-36752) w195 w52 w48
    (by decide +kernel) w195_sound w52_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_1_7_0 : (A2_7_7Raw (shape 1 7 0)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 1 7 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 1 7 0)
    (0) (-67421) (-68829) w195 w15 w13
    (by decide +kernel) w195_sound w15_sound w13_sound) (by decide +kernel)
lemma A2_7_7Raw_2_0_6 : (A2_7_7Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 0 6)
    (-3705) (-67421) (-36752) w179 w15 w48
    (by decide +kernel) w179_sound w15_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_2_1_5 : (A2_7_7Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 1 5)
    (-3705) (-35684) (-13993) w179 w52 w118
    (by decide +kernel) w179_sound w52_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_2_2_4 : (A2_7_7Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 2 4)
    (-3705) (-13735) (0) w179 w119 w195
    (by decide +kernel) w179_sound w119_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_2_3_3 : (A2_7_7Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 3 3)
    (-3705) (0) (0) w179 w195 w195
    (by decide +kernel) w179_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_7_7Raw_2_4_2 : (A2_7_7Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 4 2)
    (-3705) (0) (-13993) w179 w195 w118
    (by decide +kernel) w179_sound w195_sound w118_sound) (by decide +kernel)
lemma A2_7_7Raw_2_5_1 : (A2_7_7Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 5 1)
    (-3705) (-13735) (-36752) w179 w119 w48
    (by decide +kernel) w179_sound w119_sound w48_sound) (by decide +kernel)
lemma A2_7_7Raw_2_6_0 : (A2_7_7Raw (shape 2 6 0)).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) (shape 2 6 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 7 7) (shape 2 6 0)
    (-3705) (-35684) (-68829) w179 w52 w13
    (by decide +kernel) w179_sound w52_sound w13_sound) (by decide +kernel)
lemma A2_7_7Raw_sound (u : Shape) (hu : u ∈ below (shape 2 7 7)) :
    (A2_7_7Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 7 7) u : ℝ) := by
  rw [A2_7_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_7_7Raw_0_1_7
  · exact A2_7_7Raw_0_2_6
  · exact A2_7_7Raw_0_3_5
  · exact A2_7_7Raw_0_4_4
  · exact A2_7_7Raw_0_5_3
  · exact A2_7_7Raw_0_6_2
  · exact A2_7_7Raw_0_7_1
  · exact A2_7_7Raw_1_0_7
  · exact A2_7_7Raw_1_1_6
  · exact A2_7_7Raw_1_2_5
  · exact A2_7_7Raw_1_3_4
  · exact A2_7_7Raw_1_4_3
  · exact A2_7_7Raw_1_5_2
  · exact A2_7_7Raw_1_6_1
  · exact A2_7_7Raw_1_7_0
  · exact A2_7_7Raw_2_0_6
  · exact A2_7_7Raw_2_1_5
  · exact A2_7_7Raw_2_2_4
  · exact A2_7_7Raw_2_3_3
  · exact A2_7_7Raw_2_4_2
  · exact A2_7_7Raw_2_5_1
  · exact A2_7_7Raw_2_6_0
def A2_7_7Den : Ball := ⟨(8432217523044894851661197558491 / 2000000000000000000000000000000), (199 / 50000000000000000000000000000000)⟩
lemma A2_7_7Den_sound : A2_7_7Den.Encloses (((below (shape 2 7 7)).map (splitWeight positiveInitial tableP (shape 2 7 7))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 7 7)) A2_7_7Raw (splitWeight positiveInitial tableP (shape 2 7 7)) A2_7_7Raw_sound) (by decide +kernel)
lemma A2_7_7Den_positive : 0 < A2_7_7Den.lower := by decide +kernel
def A2_7_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(236706494815454143359971229 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(6568096959823549410460354727 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(4040860150119596109248067465019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(4093757353345277543101032118639 / 25000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(2073235431007466414784974589209 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(113956051024980402388261306291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(28696298310560545365494143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1482096408544038066251740184659 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(23718553210161909988480210591893 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(23718553210161909988480210591893 / 100000000000000000000000000000000), (23 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(1482096408544038066251740184659 / 100000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(8476229158308448226948659597 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(28696298310560545365494143 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(61223223962159475536795967 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(113956051024980402388261306291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(2073235431007466414784974589209 / 50000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(4093757353345277543101032118639 / 25000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(4040860150119596109248067465019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(6568096959823549410460354727 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(236706494815454143359971229 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_7_7Law (u : Shape) : Ball := if u ∈ below (shape 2 7 7) then A2_7_7Table u else .exact 0
lemma A2_7_7Law_check_0_1_7 : contains (.mul (A2_7_7Raw (shape 0 1 7)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_7_7Law_check_0_2_6 : contains (.mul (A2_7_7Raw (shape 0 2 6)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_7_7Law_check_0_3_5 : contains (.mul (A2_7_7Raw (shape 0 3 5)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_7_7Law_check_0_4_4 : contains (.mul (A2_7_7Raw (shape 0 4 4)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_7_7Law_check_0_5_3 : contains (.mul (A2_7_7Raw (shape 0 5 3)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 5 3)) = true := by decide +kernel
lemma A2_7_7Law_check_0_6_2 : contains (.mul (A2_7_7Raw (shape 0 6 2)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 6 2)) = true := by decide +kernel
lemma A2_7_7Law_check_0_7_1 : contains (.mul (A2_7_7Raw (shape 0 7 1)) (.inv A2_7_7Den)) (A2_7_7Table (shape 0 7 1)) = true := by decide +kernel
lemma A2_7_7Law_check_1_0_7 : contains (.mul (A2_7_7Raw (shape 1 0 7)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_7_7Law_check_1_1_6 : contains (.mul (A2_7_7Raw (shape 1 1 6)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_7_7Law_check_1_2_5 : contains (.mul (A2_7_7Raw (shape 1 2 5)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_7_7Law_check_1_3_4 : contains (.mul (A2_7_7Raw (shape 1 3 4)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_7_7Law_check_1_4_3 : contains (.mul (A2_7_7Raw (shape 1 4 3)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_7_7Law_check_1_5_2 : contains (.mul (A2_7_7Raw (shape 1 5 2)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 5 2)) = true := by decide +kernel
lemma A2_7_7Law_check_1_6_1 : contains (.mul (A2_7_7Raw (shape 1 6 1)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 6 1)) = true := by decide +kernel
lemma A2_7_7Law_check_1_7_0 : contains (.mul (A2_7_7Raw (shape 1 7 0)) (.inv A2_7_7Den)) (A2_7_7Table (shape 1 7 0)) = true := by decide +kernel
lemma A2_7_7Law_check_2_0_6 : contains (.mul (A2_7_7Raw (shape 2 0 6)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_7_7Law_check_2_1_5 : contains (.mul (A2_7_7Raw (shape 2 1 5)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_7_7Law_check_2_2_4 : contains (.mul (A2_7_7Raw (shape 2 2 4)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_7_7Law_check_2_3_3 : contains (.mul (A2_7_7Raw (shape 2 3 3)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_7_7Law_check_2_4_2 : contains (.mul (A2_7_7Raw (shape 2 4 2)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_7_7Law_check_2_5_1 : contains (.mul (A2_7_7Raw (shape 2 5 1)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 5 1)) = true := by decide +kernel
lemma A2_7_7Law_check_2_6_0 : contains (.mul (A2_7_7Raw (shape 2 6 0)) (.inv A2_7_7Den)) (A2_7_7Table (shape 2 6 0)) = true := by decide +kernel
lemma A2_7_7Law_check (u : Shape) (hu : u ∈ below (shape 2 7 7)) :
    contains (.mul (A2_7_7Raw u) (.inv A2_7_7Den)) (A2_7_7Table u) = true := by
  rw [A2_7_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_7_7Law_check_0_1_7
  · exact A2_7_7Law_check_0_2_6
  · exact A2_7_7Law_check_0_3_5
  · exact A2_7_7Law_check_0_4_4
  · exact A2_7_7Law_check_0_5_3
  · exact A2_7_7Law_check_0_6_2
  · exact A2_7_7Law_check_0_7_1
  · exact A2_7_7Law_check_1_0_7
  · exact A2_7_7Law_check_1_1_6
  · exact A2_7_7Law_check_1_2_5
  · exact A2_7_7Law_check_1_3_4
  · exact A2_7_7Law_check_1_4_3
  · exact A2_7_7Law_check_1_5_2
  · exact A2_7_7Law_check_1_6_1
  · exact A2_7_7Law_check_1_7_0
  · exact A2_7_7Law_check_2_0_6
  · exact A2_7_7Law_check_2_1_5
  · exact A2_7_7Law_check_2_2_4
  · exact A2_7_7Law_check_2_3_3
  · exact A2_7_7Law_check_2_4_2
  · exact A2_7_7Law_check_2_5_1
  · exact A2_7_7Law_check_2_6_0
lemma A2_7_7Law_sound (u : Shape) :
    (A2_7_7Law u).Encloses (stageALaw (shape 2 7 7) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 7 7)
  · have h := contains_sound (Ball.mul_sound (A2_7_7Raw_sound u hu)
      (Ball.inv_sound A2_7_7Den_sound A2_7_7Den_positive)) (A2_7_7Law_check u hu)
    simpa only [A2_7_7Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_7_7Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
