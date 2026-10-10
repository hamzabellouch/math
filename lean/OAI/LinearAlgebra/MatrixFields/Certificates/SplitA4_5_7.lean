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
lemma A4_5_7_below : below (shape 4 5 7) = [
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
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0)] := by decide +kernel
def A4_5_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(320070995306194163489326983 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(111908131966907707297208391469 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(924572162836136938580133522067 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(1712194403755276647553732402859 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(86252921110897044875603592223 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(563000628202886554057056869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(17983177592845578600362644283 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(258269201999648166411752129327 / 2000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(32476703126909447167938135835733 / 50000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(1494634153844948446443758553957 / 6250000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(47901191170901796701943780139 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2789428518380002493238768961 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7319706166566425133179750241413 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(7319706166566425133179750241413 / 100000000000000000000000000000000), (11 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(2789428518380002493238768961 / 6250000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(47901191170901796701943780139 / 10000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(1494634153844948446443758553957 / 6250000000000000000000000000000), (63 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(32476703126909447167938135835733 / 50000000000000000000000000000000), (1 / 1250000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(258269201999648166411752129327 / 2000000000000000000000000000000), (9 / 25000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(17983177592845578600362644283 / 6250000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(563000628202886554057056869 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(86252921110897044875603592223 / 12500000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1712194403755276647553732402859 / 25000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(924572162836136938580133522067 / 25000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(111908131966907707297208391469 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(320070995306194163489326983 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A4_5_7Raw_0_1_7 : (A4_5_7Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 0 1 7)
    (-16819) (-9992) (-83616) w102 w129 w7
    (by decide +kernel) w102_sound w129_sound w7_sound) (by decide +kernel)
lemma A4_5_7Raw_0_2_6 : (A4_5_7Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 0 2 6)
    (-16819) (0) (-44202) w102 w195 w40
    (by decide +kernel) w102_sound w195_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_0_3_5 : (A4_5_7Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 0 3 5)
    (-16819) (0) (-16154) w102 w195 w109
    (by decide +kernel) w102_sound w195_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_0_4_4 : (A4_5_7Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 0 4 4)
    (-16819) (-9992) (0) w102 w129 w195
    (by decide +kernel) w102_sound w129_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_0_5_3 : (A4_5_7Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 0 5 3)
    (-16819) (-32943) (0) w102 w60 w195
    (by decide +kernel) w102_sound w60_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_1_0_7 : (A4_5_7Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 0 7)
    (-4315) (-32943) (-83616) w177 w60 w7
    (by decide +kernel) w177_sound w60_sound w7_sound) (by decide +kernel)
lemma A4_5_7Raw_1_1_6 : (A4_5_7Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 1 6)
    (-4315) (-9992) (-44202) w177 w129 w40
    (by decide +kernel) w177_sound w129_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_1_2_5 : (A4_5_7Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 2 5)
    (-4315) (0) (-16154) w177 w195 w109
    (by decide +kernel) w177_sound w195_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_1_3_4 : (A4_5_7Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 3 4)
    (-4315) (0) (0) w177 w195 w195
    (by decide +kernel) w177_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_1_4_3 : (A4_5_7Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 4 3)
    (-4315) (-9992) (0) w177 w129 w195
    (by decide +kernel) w177_sound w129_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_1_5_2 : (A4_5_7Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 1 5 2)
    (-4315) (-32943) (-16154) w177 w60 w109
    (by decide +kernel) w177_sound w60_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_2_0_6 : (A4_5_7Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 0 6)
    (0) (-32943) (-44202) w195 w60 w40
    (by decide +kernel) w195_sound w60_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_2_1_5 : (A4_5_7Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 1 5)
    (0) (-9992) (-16154) w195 w129 w109
    (by decide +kernel) w195_sound w129_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_2_2_4 : (A4_5_7Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_2_3_3 : (A4_5_7Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 3 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_2_4_2 : (A4_5_7Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 4 2)
    (0) (-9992) (-16154) w195 w129 w109
    (by decide +kernel) w195_sound w129_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_2_5_1 : (A4_5_7Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 2 5 1)
    (0) (-32943) (-44202) w195 w60 w40
    (by decide +kernel) w195_sound w60_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_3_0_5 : (A4_5_7Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 0 5)
    (-4315) (-32943) (-16154) w177 w60 w109
    (by decide +kernel) w177_sound w60_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_3_1_4 : (A4_5_7Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 1 4)
    (-4315) (-9992) (0) w177 w129 w195
    (by decide +kernel) w177_sound w129_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_3_2_3 : (A4_5_7Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 2 3)
    (-4315) (0) (0) w177 w195 w195
    (by decide +kernel) w177_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_3_3_2 : (A4_5_7Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 3 2)
    (-4315) (0) (-16154) w177 w195 w109
    (by decide +kernel) w177_sound w195_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_3_4_1 : (A4_5_7Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 4 1)
    (-4315) (-9992) (-44202) w177 w129 w40
    (by decide +kernel) w177_sound w129_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_3_5_0 : (A4_5_7Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 3 5 0)
    (-4315) (-32943) (-83616) w177 w60 w7
    (by decide +kernel) w177_sound w60_sound w7_sound) (by decide +kernel)
lemma A4_5_7Raw_4_0_4 : (A4_5_7Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 4 0 4)
    (-16819) (-32943) (0) w102 w60 w195
    (by decide +kernel) w102_sound w60_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_4_1_3 : (A4_5_7Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 4 1 3)
    (-16819) (-9992) (0) w102 w129 w195
    (by decide +kernel) w102_sound w129_sound w195_sound) (by decide +kernel)
lemma A4_5_7Raw_4_2_2 : (A4_5_7Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 4 2 2)
    (-16819) (0) (-16154) w102 w195 w109
    (by decide +kernel) w102_sound w195_sound w109_sound) (by decide +kernel)
lemma A4_5_7Raw_4_3_1 : (A4_5_7Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 4 3 1)
    (-16819) (0) (-44202) w102 w195 w40
    (by decide +kernel) w102_sound w195_sound w40_sound) (by decide +kernel)
lemma A4_5_7Raw_4_4_0 : (A4_5_7Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 5 7) (shape 4 4 0)
    (-16819) (-9992) (-83616) w102 w129 w7
    (by decide +kernel) w102_sound w129_sound w7_sound) (by decide +kernel)
lemma A4_5_7Raw_sound (u : Shape) (hu : u ∈ below (shape 4 5 7)) :
    (A4_5_7Raw u).Encloses (splitWeight positiveInitial tableP (shape 4 5 7) u : ℝ) := by
  rw [A4_5_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_5_7Raw_0_1_7
  · exact A4_5_7Raw_0_2_6
  · exact A4_5_7Raw_0_3_5
  · exact A4_5_7Raw_0_4_4
  · exact A4_5_7Raw_0_5_3
  · exact A4_5_7Raw_1_0_7
  · exact A4_5_7Raw_1_1_6
  · exact A4_5_7Raw_1_2_5
  · exact A4_5_7Raw_1_3_4
  · exact A4_5_7Raw_1_4_3
  · exact A4_5_7Raw_1_5_2
  · exact A4_5_7Raw_2_0_6
  · exact A4_5_7Raw_2_1_5
  · exact A4_5_7Raw_2_2_4
  · exact A4_5_7Raw_2_3_3
  · exact A4_5_7Raw_2_4_2
  · exact A4_5_7Raw_2_5_1
  · exact A4_5_7Raw_3_0_5
  · exact A4_5_7Raw_3_1_4
  · exact A4_5_7Raw_3_2_3
  · exact A4_5_7Raw_3_3_2
  · exact A4_5_7Raw_3_4_1
  · exact A4_5_7Raw_3_5_0
  · exact A4_5_7Raw_4_0_4
  · exact A4_5_7Raw_4_1_3
  · exact A4_5_7Raw_4_2_2
  · exact A4_5_7Raw_4_3_1
  · exact A4_5_7Raw_4_4_0
def A4_5_7Den : Ball := ⟨(44275032369233382034553407713609 / 10000000000000000000000000000000), (247 / 50000000000000000000000000000000)⟩
lemma A4_5_7Den_sound : A4_5_7Den.Encloses (((below (shape 4 5 7)).map (splitWeight positiveInitial tableP (shape 4 5 7))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 5 7)) A4_5_7Raw (splitWeight positiveInitial tableP (shape 4 5 7)) A4_5_7Raw_sound) (by decide +kernel)
lemma A4_5_7Den_positive : 0 < A4_5_7Den.lower := by decide +kernel
def A4_5_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(72291532762065411961625181 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(50551349588474794800387489967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(835298915312477561452360781693 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(1546871283549937362097791005049 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(155849320025945821317144591277 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(127159845645672388759135689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(2916646111580472154804741948879 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(14670436762674140168945445265753 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(5401271367141237916102377734777 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(108190076003621906016955145267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(1008036672268904292945876487 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(413308911076758019532532898899 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11293046515025223285749624084633 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(11293046515025223285749624084633 / 50000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(413308911076758019532532898899 / 25000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(1008036672268904292945876487 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(108190076003621906016955145267 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(5401271367141237916102377734777 / 100000000000000000000000000000000), (21 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(14670436762674140168945445265753 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(2916646111580472154804741948879 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(16246788883517155613847561503 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(127159845645672388759135689 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(155849320025945821317144591277 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1546871283549937362097791005049 / 100000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(835298915312477561452360781693 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(50551349588474794800387489967 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(72291532762065411961625181 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_5_7Law (u : Shape) : Ball := if u ∈ below (shape 4 5 7) then A4_5_7Table u else .exact 0
lemma A4_5_7Law_check_0_1_7 : contains (.mul (A4_5_7Raw (shape 0 1 7)) (.inv A4_5_7Den)) (A4_5_7Table (shape 0 1 7)) = true := by decide +kernel
lemma A4_5_7Law_check_0_2_6 : contains (.mul (A4_5_7Raw (shape 0 2 6)) (.inv A4_5_7Den)) (A4_5_7Table (shape 0 2 6)) = true := by decide +kernel
lemma A4_5_7Law_check_0_3_5 : contains (.mul (A4_5_7Raw (shape 0 3 5)) (.inv A4_5_7Den)) (A4_5_7Table (shape 0 3 5)) = true := by decide +kernel
lemma A4_5_7Law_check_0_4_4 : contains (.mul (A4_5_7Raw (shape 0 4 4)) (.inv A4_5_7Den)) (A4_5_7Table (shape 0 4 4)) = true := by decide +kernel
lemma A4_5_7Law_check_0_5_3 : contains (.mul (A4_5_7Raw (shape 0 5 3)) (.inv A4_5_7Den)) (A4_5_7Table (shape 0 5 3)) = true := by decide +kernel
lemma A4_5_7Law_check_1_0_7 : contains (.mul (A4_5_7Raw (shape 1 0 7)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 0 7)) = true := by decide +kernel
lemma A4_5_7Law_check_1_1_6 : contains (.mul (A4_5_7Raw (shape 1 1 6)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 1 6)) = true := by decide +kernel
lemma A4_5_7Law_check_1_2_5 : contains (.mul (A4_5_7Raw (shape 1 2 5)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 2 5)) = true := by decide +kernel
lemma A4_5_7Law_check_1_3_4 : contains (.mul (A4_5_7Raw (shape 1 3 4)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 3 4)) = true := by decide +kernel
lemma A4_5_7Law_check_1_4_3 : contains (.mul (A4_5_7Raw (shape 1 4 3)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 4 3)) = true := by decide +kernel
lemma A4_5_7Law_check_1_5_2 : contains (.mul (A4_5_7Raw (shape 1 5 2)) (.inv A4_5_7Den)) (A4_5_7Table (shape 1 5 2)) = true := by decide +kernel
lemma A4_5_7Law_check_2_0_6 : contains (.mul (A4_5_7Raw (shape 2 0 6)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 0 6)) = true := by decide +kernel
lemma A4_5_7Law_check_2_1_5 : contains (.mul (A4_5_7Raw (shape 2 1 5)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 1 5)) = true := by decide +kernel
lemma A4_5_7Law_check_2_2_4 : contains (.mul (A4_5_7Raw (shape 2 2 4)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 2 4)) = true := by decide +kernel
lemma A4_5_7Law_check_2_3_3 : contains (.mul (A4_5_7Raw (shape 2 3 3)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 3 3)) = true := by decide +kernel
lemma A4_5_7Law_check_2_4_2 : contains (.mul (A4_5_7Raw (shape 2 4 2)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 4 2)) = true := by decide +kernel
lemma A4_5_7Law_check_2_5_1 : contains (.mul (A4_5_7Raw (shape 2 5 1)) (.inv A4_5_7Den)) (A4_5_7Table (shape 2 5 1)) = true := by decide +kernel
lemma A4_5_7Law_check_3_0_5 : contains (.mul (A4_5_7Raw (shape 3 0 5)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 0 5)) = true := by decide +kernel
lemma A4_5_7Law_check_3_1_4 : contains (.mul (A4_5_7Raw (shape 3 1 4)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 1 4)) = true := by decide +kernel
lemma A4_5_7Law_check_3_2_3 : contains (.mul (A4_5_7Raw (shape 3 2 3)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 2 3)) = true := by decide +kernel
lemma A4_5_7Law_check_3_3_2 : contains (.mul (A4_5_7Raw (shape 3 3 2)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 3 2)) = true := by decide +kernel
lemma A4_5_7Law_check_3_4_1 : contains (.mul (A4_5_7Raw (shape 3 4 1)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 4 1)) = true := by decide +kernel
lemma A4_5_7Law_check_3_5_0 : contains (.mul (A4_5_7Raw (shape 3 5 0)) (.inv A4_5_7Den)) (A4_5_7Table (shape 3 5 0)) = true := by decide +kernel
lemma A4_5_7Law_check_4_0_4 : contains (.mul (A4_5_7Raw (shape 4 0 4)) (.inv A4_5_7Den)) (A4_5_7Table (shape 4 0 4)) = true := by decide +kernel
lemma A4_5_7Law_check_4_1_3 : contains (.mul (A4_5_7Raw (shape 4 1 3)) (.inv A4_5_7Den)) (A4_5_7Table (shape 4 1 3)) = true := by decide +kernel
lemma A4_5_7Law_check_4_2_2 : contains (.mul (A4_5_7Raw (shape 4 2 2)) (.inv A4_5_7Den)) (A4_5_7Table (shape 4 2 2)) = true := by decide +kernel
lemma A4_5_7Law_check_4_3_1 : contains (.mul (A4_5_7Raw (shape 4 3 1)) (.inv A4_5_7Den)) (A4_5_7Table (shape 4 3 1)) = true := by decide +kernel
lemma A4_5_7Law_check_4_4_0 : contains (.mul (A4_5_7Raw (shape 4 4 0)) (.inv A4_5_7Den)) (A4_5_7Table (shape 4 4 0)) = true := by decide +kernel
lemma A4_5_7Law_check (u : Shape) (hu : u ∈ below (shape 4 5 7)) :
    contains (.mul (A4_5_7Raw u) (.inv A4_5_7Den)) (A4_5_7Table u) = true := by
  rw [A4_5_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_5_7Law_check_0_1_7
  · exact A4_5_7Law_check_0_2_6
  · exact A4_5_7Law_check_0_3_5
  · exact A4_5_7Law_check_0_4_4
  · exact A4_5_7Law_check_0_5_3
  · exact A4_5_7Law_check_1_0_7
  · exact A4_5_7Law_check_1_1_6
  · exact A4_5_7Law_check_1_2_5
  · exact A4_5_7Law_check_1_3_4
  · exact A4_5_7Law_check_1_4_3
  · exact A4_5_7Law_check_1_5_2
  · exact A4_5_7Law_check_2_0_6
  · exact A4_5_7Law_check_2_1_5
  · exact A4_5_7Law_check_2_2_4
  · exact A4_5_7Law_check_2_3_3
  · exact A4_5_7Law_check_2_4_2
  · exact A4_5_7Law_check_2_5_1
  · exact A4_5_7Law_check_3_0_5
  · exact A4_5_7Law_check_3_1_4
  · exact A4_5_7Law_check_3_2_3
  · exact A4_5_7Law_check_3_3_2
  · exact A4_5_7Law_check_3_4_1
  · exact A4_5_7Law_check_3_5_0
  · exact A4_5_7Law_check_4_0_4
  · exact A4_5_7Law_check_4_1_3
  · exact A4_5_7Law_check_4_2_2
  · exact A4_5_7Law_check_4_3_1
  · exact A4_5_7Law_check_4_4_0
lemma A4_5_7Law_sound (u : Shape) :
    (A4_5_7Law u).Encloses (stageALaw (shape 4 5 7) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 5 7)
  · have h := contains_sound (Ball.mul_sound (A4_5_7Raw_sound u hu)
      (Ball.inv_sound A4_5_7Den_sound A4_5_7Den_positive)) (A4_5_7Law_check u hu)
    simpa only [A4_5_7Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A4_5_7Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
