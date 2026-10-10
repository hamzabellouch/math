import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.InitialProbabilities
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_1_14
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_4_11
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA1_7_8
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_2_12
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_3_11
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_4_10
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_5_9
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_6_8
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA2_7_7
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_3_10
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_4_9
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_5_8
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA3_6_7
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA4_5_7
import OAI.LinearAlgebra.MatrixFields.Certificates.SplitA4_6_6

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A4_4_8_below : below (shape 4 4 8) = [
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
  (shape 3 4 1),
  (shape 4 0 4),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 4 4 0)] := by decide +kernel
def A4_4_8Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(18292309835383748212700097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(9679647302864801584009674223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(115294249586007915494116430803 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(49998791258020844658220845781 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(25723673806193141051082939537 / 800000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(9822006849405278656185245843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(678835129521870795795191707909 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22454031748889508411675041798339 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(41895154924763898251935527356047 / 100000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(253670642551677628600159805953 / 6250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(146442242833390519127469727577 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1124274470428081998513583312611 / 5000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨1, 0⟩
  | 2, 3, 3 => ⟨(1124274470428081998513583312611 / 5000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(146442242833390519127469727577 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(253670642551677628600159805953 / 6250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(41895154924763898251935527356047 / 100000000000000000000000000000000), (19 / 20000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(22454031748889508411675041798339 / 100000000000000000000000000000000), (13 / 25000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(678835129521870795795191707909 / 50000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(9822006849405278656185245843 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(25723673806193141051082939537 / 800000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(49998791258020844658220845781 / 1250000000000000000000000000000), (1 / 6250000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(115294249586007915494116430803 / 20000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(9679647302864801584009674223 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(18292309835383748212700097 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A4_4_8Raw_0_0_8 : (A4_4_8Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 0 8)
    (-17266) (-17106) (-120770) w98 w99 w0
    (by decide +kernel) w98_sound w99_sound w0_sound) (by decide +kernel)
lemma A4_4_8Raw_0_1_7 : (A4_4_8Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 1 7)
    (-17266) (-4343) (-70820) w98 w176 w12
    (by decide +kernel) w98_sound w176_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_0_2_6 : (A4_4_8Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 2 6)
    (-17266) (0) (-34294) w98 w195 w55
    (by decide +kernel) w98_sound w195_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_0_3_5 : (A4_4_8Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 3 5)
    (-17266) (-4343) (-10580) w98 w176 w126
    (by decide +kernel) w98_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_0_4_4 : (A4_4_8Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 0 4 4)
    (-17266) (-17106) (0) w98 w99 w195
    (by decide +kernel) w98_sound w99_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_1_0_7 : (A4_4_8Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 0 7)
    (-4357) (-17106) (-70820) w175 w99 w12
    (by decide +kernel) w175_sound w99_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_1_1_6 : (A4_4_8Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 1 6)
    (-4357) (-4343) (-34294) w175 w176 w55
    (by decide +kernel) w175_sound w176_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_1_2_5 : (A4_4_8Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 2 5)
    (-4357) (0) (-10580) w175 w195 w126
    (by decide +kernel) w175_sound w195_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_1_3_4 : (A4_4_8Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 3 4)
    (-4357) (-4343) (0) w175 w176 w195
    (by decide +kernel) w175_sound w176_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_1_4_3 : (A4_4_8Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 1 4 3)
    (-4357) (-17106) (-10580) w175 w99 w126
    (by decide +kernel) w175_sound w99_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_0_6 : (A4_4_8Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 0 6)
    (0) (-17106) (-34294) w195 w99 w55
    (by decide +kernel) w195_sound w99_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_2_1_5 : (A4_4_8Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 1 5)
    (0) (-4343) (-10580) w195 w176 w126
    (by decide +kernel) w195_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_2_4 : (A4_4_8Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 2 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_2_3_3 : (A4_4_8Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 3 3)
    (0) (-4343) (-10580) w195 w176 w126
    (by decide +kernel) w195_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_2_4_2 : (A4_4_8Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 2 4 2)
    (0) (-17106) (-34294) w195 w99 w55
    (by decide +kernel) w195_sound w99_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_3_0_5 : (A4_4_8Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 0 5)
    (-4357) (-17106) (-10580) w175 w99 w126
    (by decide +kernel) w175_sound w99_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_3_1_4 : (A4_4_8Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 1 4)
    (-4357) (-4343) (0) w175 w176 w195
    (by decide +kernel) w175_sound w176_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_3_2_3 : (A4_4_8Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 2 3)
    (-4357) (0) (-10580) w175 w195 w126
    (by decide +kernel) w175_sound w195_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_3_3_2 : (A4_4_8Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 3 2)
    (-4357) (-4343) (-34294) w175 w176 w55
    (by decide +kernel) w175_sound w176_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_3_4_1 : (A4_4_8Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 3 4 1)
    (-4357) (-17106) (-70820) w175 w99 w12
    (by decide +kernel) w175_sound w99_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_4_0_4 : (A4_4_8Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 0 4)
    (-17266) (-17106) (0) w98 w99 w195
    (by decide +kernel) w98_sound w99_sound w195_sound) (by decide +kernel)
lemma A4_4_8Raw_4_1_3 : (A4_4_8Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 1 3)
    (-17266) (-4343) (-10580) w98 w176 w126
    (by decide +kernel) w98_sound w176_sound w126_sound) (by decide +kernel)
lemma A4_4_8Raw_4_2_2 : (A4_4_8Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 2 2)
    (-17266) (0) (-34294) w98 w195 w55
    (by decide +kernel) w98_sound w195_sound w55_sound) (by decide +kernel)
lemma A4_4_8Raw_4_3_1 : (A4_4_8Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 3 1)
    (-17266) (-4343) (-70820) w98 w176 w12
    (by decide +kernel) w98_sound w176_sound w12_sound) (by decide +kernel)
lemma A4_4_8Raw_4_4_0 : (A4_4_8Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 4 8) (shape 4 4 0)
    (-17266) (-17106) (-120770) w98 w99 w0
    (by decide +kernel) w98_sound w99_sound w0_sound) (by decide +kernel)
lemma A4_4_8Raw_sound (u : Shape) (hu : u ∈ below (shape 4 4 8)) :
    (A4_4_8Raw u).Encloses (splitWeight positiveInitial tableP (shape 4 4 8) u : ℝ) := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_4_8Raw_0_0_8
  · exact A4_4_8Raw_0_1_7
  · exact A4_4_8Raw_0_2_6
  · exact A4_4_8Raw_0_3_5
  · exact A4_4_8Raw_0_4_4
  · exact A4_4_8Raw_1_0_7
  · exact A4_4_8Raw_1_1_6
  · exact A4_4_8Raw_1_2_5
  · exact A4_4_8Raw_1_3_4
  · exact A4_4_8Raw_1_4_3
  · exact A4_4_8Raw_2_0_6
  · exact A4_4_8Raw_2_1_5
  · exact A4_4_8Raw_2_2_4
  · exact A4_4_8Raw_2_3_3
  · exact A4_4_8Raw_2_4_2
  · exact A4_4_8Raw_3_0_5
  · exact A4_4_8Raw_3_1_4
  · exact A4_4_8Raw_3_2_3
  · exact A4_4_8Raw_3_3_2
  · exact A4_4_8Raw_3_4_1
  · exact A4_4_8Raw_4_0_4
  · exact A4_4_8Raw_4_1_3
  · exact A4_4_8Raw_4_2_2
  · exact A4_4_8Raw_4_3_1
  · exact A4_4_8Raw_4_4_0
def A4_4_8Den : Ball := ⟨(150648199314227147605087079506763 / 50000000000000000000000000000000), (129 / 25000000000000000000000000000000)⟩
lemma A4_4_8Den_sound : A4_4_8Den.Encloses (((below (shape 4 4 8)).map (splitWeight positiveInitial tableP (shape 4 4 8))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 4 8)) A4_4_8Raw (splitWeight positiveInitial tableP (shape 4 4 8)) A4_4_8Raw_sound) (by decide +kernel)
lemma A4_4_8Den_positive : 0 < A4_4_8Den.lower := by decide +kernel
def A4_4_8Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(100395816077291183265741961 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(95665140797271696018077340381 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(1327564258600440675632668642677 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(266801996340761781073908742717 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(407489389771853581693404047 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(225304760565353108107595575157 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(1863118166289372952288716397111 / 25000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(869060232620536432990705106057 / 6250000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(53883555187553276131757505307 / 4000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(194416187515041316719536553259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(7462913433721381544107457287859 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(16594954412866328459781726401447 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(7462913433721381544107457287859 / 100000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(194416187515041316719536553259 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(53883555187553276131757505307 / 4000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(869060232620536432990705106057 / 6250000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1863118166289372952288716397111 / 25000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(225304760565353108107595575157 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(407489389771853581693404047 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(266801996340761781073908742717 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1327564258600440675632668642677 / 100000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(95665140797271696018077340381 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(100395816077291183265741961 / 3125000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(3035600478242196747209827 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_4_8Law (u : Shape) : Ball := if u ∈ below (shape 4 4 8) then A4_4_8Table u else .exact 0
lemma A4_4_8Law_check_0_0_8 : contains (.mul (A4_4_8Raw (shape 0 0 8)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 0 8)) = true := by decide +kernel
lemma A4_4_8Law_check_0_1_7 : contains (.mul (A4_4_8Raw (shape 0 1 7)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 1 7)) = true := by decide +kernel
lemma A4_4_8Law_check_0_2_6 : contains (.mul (A4_4_8Raw (shape 0 2 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 2 6)) = true := by decide +kernel
lemma A4_4_8Law_check_0_3_5 : contains (.mul (A4_4_8Raw (shape 0 3 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 3 5)) = true := by decide +kernel
lemma A4_4_8Law_check_0_4_4 : contains (.mul (A4_4_8Raw (shape 0 4 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 0 4 4)) = true := by decide +kernel
lemma A4_4_8Law_check_1_0_7 : contains (.mul (A4_4_8Raw (shape 1 0 7)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 0 7)) = true := by decide +kernel
lemma A4_4_8Law_check_1_1_6 : contains (.mul (A4_4_8Raw (shape 1 1 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 1 6)) = true := by decide +kernel
lemma A4_4_8Law_check_1_2_5 : contains (.mul (A4_4_8Raw (shape 1 2 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 2 5)) = true := by decide +kernel
lemma A4_4_8Law_check_1_3_4 : contains (.mul (A4_4_8Raw (shape 1 3 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 3 4)) = true := by decide +kernel
lemma A4_4_8Law_check_1_4_3 : contains (.mul (A4_4_8Raw (shape 1 4 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 1 4 3)) = true := by decide +kernel
lemma A4_4_8Law_check_2_0_6 : contains (.mul (A4_4_8Raw (shape 2 0 6)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 0 6)) = true := by decide +kernel
lemma A4_4_8Law_check_2_1_5 : contains (.mul (A4_4_8Raw (shape 2 1 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 1 5)) = true := by decide +kernel
lemma A4_4_8Law_check_2_2_4 : contains (.mul (A4_4_8Raw (shape 2 2 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 2 4)) = true := by decide +kernel
lemma A4_4_8Law_check_2_3_3 : contains (.mul (A4_4_8Raw (shape 2 3 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 3 3)) = true := by decide +kernel
lemma A4_4_8Law_check_2_4_2 : contains (.mul (A4_4_8Raw (shape 2 4 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 2 4 2)) = true := by decide +kernel
lemma A4_4_8Law_check_3_0_5 : contains (.mul (A4_4_8Raw (shape 3 0 5)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 0 5)) = true := by decide +kernel
lemma A4_4_8Law_check_3_1_4 : contains (.mul (A4_4_8Raw (shape 3 1 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 1 4)) = true := by decide +kernel
lemma A4_4_8Law_check_3_2_3 : contains (.mul (A4_4_8Raw (shape 3 2 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 2 3)) = true := by decide +kernel
lemma A4_4_8Law_check_3_3_2 : contains (.mul (A4_4_8Raw (shape 3 3 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 3 2)) = true := by decide +kernel
lemma A4_4_8Law_check_3_4_1 : contains (.mul (A4_4_8Raw (shape 3 4 1)) (.inv A4_4_8Den)) (A4_4_8Table (shape 3 4 1)) = true := by decide +kernel
lemma A4_4_8Law_check_4_0_4 : contains (.mul (A4_4_8Raw (shape 4 0 4)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 0 4)) = true := by decide +kernel
lemma A4_4_8Law_check_4_1_3 : contains (.mul (A4_4_8Raw (shape 4 1 3)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 1 3)) = true := by decide +kernel
lemma A4_4_8Law_check_4_2_2 : contains (.mul (A4_4_8Raw (shape 4 2 2)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 2 2)) = true := by decide +kernel
lemma A4_4_8Law_check_4_3_1 : contains (.mul (A4_4_8Raw (shape 4 3 1)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 3 1)) = true := by decide +kernel
lemma A4_4_8Law_check_4_4_0 : contains (.mul (A4_4_8Raw (shape 4 4 0)) (.inv A4_4_8Den)) (A4_4_8Table (shape 4 4 0)) = true := by decide +kernel
lemma A4_4_8Law_check (u : Shape) (hu : u ∈ below (shape 4 4 8)) :
    contains (.mul (A4_4_8Raw u) (.inv A4_4_8Den)) (A4_4_8Table u) = true := by
  rw [A4_4_8_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_4_8Law_check_0_0_8
  · exact A4_4_8Law_check_0_1_7
  · exact A4_4_8Law_check_0_2_6
  · exact A4_4_8Law_check_0_3_5
  · exact A4_4_8Law_check_0_4_4
  · exact A4_4_8Law_check_1_0_7
  · exact A4_4_8Law_check_1_1_6
  · exact A4_4_8Law_check_1_2_5
  · exact A4_4_8Law_check_1_3_4
  · exact A4_4_8Law_check_1_4_3
  · exact A4_4_8Law_check_2_0_6
  · exact A4_4_8Law_check_2_1_5
  · exact A4_4_8Law_check_2_2_4
  · exact A4_4_8Law_check_2_3_3
  · exact A4_4_8Law_check_2_4_2
  · exact A4_4_8Law_check_3_0_5
  · exact A4_4_8Law_check_3_1_4
  · exact A4_4_8Law_check_3_2_3
  · exact A4_4_8Law_check_3_3_2
  · exact A4_4_8Law_check_3_4_1
  · exact A4_4_8Law_check_4_0_4
  · exact A4_4_8Law_check_4_1_3
  · exact A4_4_8Law_check_4_2_2
  · exact A4_4_8Law_check_4_3_1
  · exact A4_4_8Law_check_4_4_0
lemma A4_4_8Law_sound (u : Shape) :
    (A4_4_8Law u).Encloses (stageALaw (shape 4 4 8) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 4 8)
  · have h := contains_sound (Ball.mul_sound (A4_4_8Raw_sound u hu)
      (Ball.inv_sound A4_4_8Den_sound A4_4_8Den_positive)) (A4_4_8Law_check u hu)
    simpa only [A4_4_8Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A4_4_8Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma A5_5_6_below : below (shape 5 5 6) = [
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
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
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 5 3 0)] := by decide +kernel
def A5_5_6Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(598393443808798963104497811 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(269057595129013954010741499 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(195357478600075867932284843153 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(67997999417353477070680589579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(11231598536934101059647265467 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(339979024578301882451997256747 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(425430866772270433481086062941 / 2000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(13773826846282937567353855599691 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(394207840594426910088570909701 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(6044678416630759639672068403 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(1361548977162547525623139130929 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(5734984758757153909776083780903 / 10000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(4259416902451820897167775843919 / 20000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(6794721161026753944048082769 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(6794721161026753944048082769 / 2500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(4259416902451820897167775843919 / 20000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨1, 0⟩
  | 3, 3, 2 => ⟨(5734984758757153909776083780903 / 10000000000000000000000000000000), (73 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(1361548977162547525623139130929 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(6044678416630759639672068403 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(394207840594426910088570909701 / 50000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(13773826846282937567353855599691 / 100000000000000000000000000000000), (19 / 50000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(425430866772270433481086062941 / 2000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(339979024578301882451997256747 / 12500000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(11231598536934101059647265467 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(67997999417353477070680589579 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(195357478600075867932284843153 / 25000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(269057595129013954010741499 / 100000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(598393443808798963104497811 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A5_5_6Raw_0_2_6 : (A5_5_6Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 0 2 6)
    (-33052) (0) (-57255) w58 w195 w23
    (by decide +kernel) w58_sound w195_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_0_3_5 : (A5_5_6Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 0 3 5)
    (-33052) (0) (-26128) w58 w195 w77
    (by decide +kernel) w58_sound w195_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_0_4_4 : (A5_5_6Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 0 4 4)
    (-33052) (-9906) (-5560) w58 w131 w168
    (by decide +kernel) w58_sound w131_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_0_5_3 : (A5_5_6Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 0 5 3)
    (-33052) (-32951) (0) w58 w59 w195
    (by decide +kernel) w58_sound w59_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_1_1_6 : (A5_5_6Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 1 1 6)
    (-9918) (-9906) (-57255) w130 w131 w23
    (by decide +kernel) w130_sound w131_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_1_2_5 : (A5_5_6Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 1 2 5)
    (-9918) (0) (-26128) w130 w195 w77
    (by decide +kernel) w130_sound w195_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_1_3_4 : (A5_5_6Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 1 3 4)
    (-9918) (0) (-5560) w130 w195 w168
    (by decide +kernel) w130_sound w195_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_1_4_3 : (A5_5_6Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 1 4 3)
    (-9918) (-9906) (0) w130 w131 w195
    (by decide +kernel) w130_sound w131_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_1_5_2 : (A5_5_6Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 1 5 2)
    (-9918) (-32951) (-5560) w130 w59 w168
    (by decide +kernel) w130_sound w59_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_2_0_6 : (A5_5_6Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 0 6)
    (0) (-32951) (-57255) w195 w59 w23
    (by decide +kernel) w195_sound w59_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_2_1_5 : (A5_5_6Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 1 5)
    (0) (-9906) (-26128) w195 w131 w77
    (by decide +kernel) w195_sound w131_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_2_2_4 : (A5_5_6Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 2 4)
    (0) (0) (-5560) w195 w195 w168
    (by decide +kernel) w195_sound w195_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_2_3_3 : (A5_5_6Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 3 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_2_4_2 : (A5_5_6Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 4 2)
    (0) (-9906) (-5560) w195 w131 w168
    (by decide +kernel) w195_sound w131_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_2_5_1 : (A5_5_6Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 2 5 1)
    (0) (-32951) (-26128) w195 w59 w77
    (by decide +kernel) w195_sound w59_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_3_0_5 : (A5_5_6Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 0 5)
    (0) (-32951) (-26128) w195 w59 w77
    (by decide +kernel) w195_sound w59_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_3_1_4 : (A5_5_6Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 1 4)
    (0) (-9906) (-5560) w195 w131 w168
    (by decide +kernel) w195_sound w131_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_3_2_3 : (A5_5_6Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 2 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_3_3_2 : (A5_5_6Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 3 2)
    (0) (0) (-5560) w195 w195 w168
    (by decide +kernel) w195_sound w195_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_3_4_1 : (A5_5_6Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 4 1)
    (0) (-9906) (-26128) w195 w131 w77
    (by decide +kernel) w195_sound w131_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_3_5_0 : (A5_5_6Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 3 5 0)
    (0) (-32951) (-57255) w195 w59 w23
    (by decide +kernel) w195_sound w59_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_4_0_4 : (A5_5_6Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 4 0 4)
    (-9918) (-32951) (-5560) w130 w59 w168
    (by decide +kernel) w130_sound w59_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_4_1_3 : (A5_5_6Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 4 1 3)
    (-9918) (-9906) (0) w130 w131 w195
    (by decide +kernel) w130_sound w131_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_4_2_2 : (A5_5_6Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 4 2 2)
    (-9918) (0) (-5560) w130 w195 w168
    (by decide +kernel) w130_sound w195_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_4_3_1 : (A5_5_6Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 4 3 1)
    (-9918) (0) (-26128) w130 w195 w77
    (by decide +kernel) w130_sound w195_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_4_4_0 : (A5_5_6Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 4 4 0)
    (-9918) (-9906) (-57255) w130 w131 w23
    (by decide +kernel) w130_sound w131_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_5_0_3 : (A5_5_6Raw (shape 5 0 3)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 5 0 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 5 0 3)
    (-33052) (-32951) (0) w58 w59 w195
    (by decide +kernel) w58_sound w59_sound w195_sound) (by decide +kernel)
lemma A5_5_6Raw_5_1_2 : (A5_5_6Raw (shape 5 1 2)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 5 1 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 5 1 2)
    (-33052) (-9906) (-5560) w58 w131 w168
    (by decide +kernel) w58_sound w131_sound w168_sound) (by decide +kernel)
lemma A5_5_6Raw_5_2_1 : (A5_5_6Raw (shape 5 2 1)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 5 2 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 5 2 1)
    (-33052) (0) (-26128) w58 w195 w77
    (by decide +kernel) w58_sound w195_sound w77_sound) (by decide +kernel)
lemma A5_5_6Raw_5_3_0 : (A5_5_6Raw (shape 5 3 0)).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) (shape 5 3 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 5 5 6) (shape 5 3 0)
    (-33052) (0) (-57255) w58 w195 w23
    (by decide +kernel) w58_sound w195_sound w23_sound) (by decide +kernel)
lemma A5_5_6Raw_sound (u : Shape) (hu : u ∈ below (shape 5 5 6)) :
    (A5_5_6Raw u).Encloses (splitWeight positiveInitial tableP (shape 5 5 6) u : ℝ) := by
  rw [A5_5_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A5_5_6Raw_0_2_6
  · exact A5_5_6Raw_0_3_5
  · exact A5_5_6Raw_0_4_4
  · exact A5_5_6Raw_0_5_3
  · exact A5_5_6Raw_1_1_6
  · exact A5_5_6Raw_1_2_5
  · exact A5_5_6Raw_1_3_4
  · exact A5_5_6Raw_1_4_3
  · exact A5_5_6Raw_1_5_2
  · exact A5_5_6Raw_2_0_6
  · exact A5_5_6Raw_2_1_5
  · exact A5_5_6Raw_2_2_4
  · exact A5_5_6Raw_2_3_3
  · exact A5_5_6Raw_2_4_2
  · exact A5_5_6Raw_2_5_1
  · exact A5_5_6Raw_3_0_5
  · exact A5_5_6Raw_3_1_4
  · exact A5_5_6Raw_3_2_3
  · exact A5_5_6Raw_3_3_2
  · exact A5_5_6Raw_3_4_1
  · exact A5_5_6Raw_3_5_0
  · exact A5_5_6Raw_4_0_4
  · exact A5_5_6Raw_4_1_3
  · exact A5_5_6Raw_4_2_2
  · exact A5_5_6Raw_4_3_1
  · exact A5_5_6Raw_4_4_0
  · exact A5_5_6Raw_5_0_3
  · exact A5_5_6Raw_5_1_2
  · exact A5_5_6Raw_5_2_1
  · exact A5_5_6Raw_5_3_0
def A5_5_6Den : Ball := ⟨(110725452045764867598235231213513 / 25000000000000000000000000000000), (1 / 195312500000000000000000000000)⟩
lemma A5_5_6Den_sound : A5_5_6Den.Encloses (((below (shape 5 5 6)).map (splitWeight positiveInitial tableP (shape 5 5 6))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 5 5 6)) A5_5_6Raw (splitWeight positiveInitial tableP (shape 5 5 6)) A5_5_6Raw_sound) (by decide +kernel)
lemma A5_5_6Den_positive : 0 < A5_5_6Den.lower := by decide +kernel
def A5_5_6Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(675537368275398796035425779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(12149762776213706359494656353 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(176434121505623680657566151503 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(30705677042189293652050887643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(614093721537090303603790920153 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(4802767328017229778204193388411 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(621981061797334608261562972731 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(89005696818355176566211545587 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(272957947109232969209465951 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(614831076327326380909751491957 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(6474329809449298000655312889227 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(22578367970597256891228418236613 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(2404267054093469337759843178867 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(30682742926253173520153038357 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(30682742926253173520153038357 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(2404267054093469337759843178867 / 50000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(22578367970597256891228418236613 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(6474329809449298000655312889227 / 50000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(614831076327326380909751491957 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(272957947109232969209465951 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(89005696818355176566211545587 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(621981061797334608261562972731 / 20000000000000000000000000000000), (13 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(4802767328017229778204193388411 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(614093721537090303603790920153 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(10143646586596796759663111597 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(30705677042189293652050887643 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(176434121505623680657566151503 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(12149762776213706359494656353 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(675537368275398796035425779 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A5_5_6Law (u : Shape) : Ball := if u ∈ below (shape 5 5 6) then A5_5_6Table u else .exact 0
lemma A5_5_6Law_check_0_2_6 : contains (.mul (A5_5_6Raw (shape 0 2 6)) (.inv A5_5_6Den)) (A5_5_6Table (shape 0 2 6)) = true := by decide +kernel
lemma A5_5_6Law_check_0_3_5 : contains (.mul (A5_5_6Raw (shape 0 3 5)) (.inv A5_5_6Den)) (A5_5_6Table (shape 0 3 5)) = true := by decide +kernel
lemma A5_5_6Law_check_0_4_4 : contains (.mul (A5_5_6Raw (shape 0 4 4)) (.inv A5_5_6Den)) (A5_5_6Table (shape 0 4 4)) = true := by decide +kernel
lemma A5_5_6Law_check_0_5_3 : contains (.mul (A5_5_6Raw (shape 0 5 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 0 5 3)) = true := by decide +kernel
lemma A5_5_6Law_check_1_1_6 : contains (.mul (A5_5_6Raw (shape 1 1 6)) (.inv A5_5_6Den)) (A5_5_6Table (shape 1 1 6)) = true := by decide +kernel
lemma A5_5_6Law_check_1_2_5 : contains (.mul (A5_5_6Raw (shape 1 2 5)) (.inv A5_5_6Den)) (A5_5_6Table (shape 1 2 5)) = true := by decide +kernel
lemma A5_5_6Law_check_1_3_4 : contains (.mul (A5_5_6Raw (shape 1 3 4)) (.inv A5_5_6Den)) (A5_5_6Table (shape 1 3 4)) = true := by decide +kernel
lemma A5_5_6Law_check_1_4_3 : contains (.mul (A5_5_6Raw (shape 1 4 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 1 4 3)) = true := by decide +kernel
lemma A5_5_6Law_check_1_5_2 : contains (.mul (A5_5_6Raw (shape 1 5 2)) (.inv A5_5_6Den)) (A5_5_6Table (shape 1 5 2)) = true := by decide +kernel
lemma A5_5_6Law_check_2_0_6 : contains (.mul (A5_5_6Raw (shape 2 0 6)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 0 6)) = true := by decide +kernel
lemma A5_5_6Law_check_2_1_5 : contains (.mul (A5_5_6Raw (shape 2 1 5)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 1 5)) = true := by decide +kernel
lemma A5_5_6Law_check_2_2_4 : contains (.mul (A5_5_6Raw (shape 2 2 4)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 2 4)) = true := by decide +kernel
lemma A5_5_6Law_check_2_3_3 : contains (.mul (A5_5_6Raw (shape 2 3 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 3 3)) = true := by decide +kernel
lemma A5_5_6Law_check_2_4_2 : contains (.mul (A5_5_6Raw (shape 2 4 2)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 4 2)) = true := by decide +kernel
lemma A5_5_6Law_check_2_5_1 : contains (.mul (A5_5_6Raw (shape 2 5 1)) (.inv A5_5_6Den)) (A5_5_6Table (shape 2 5 1)) = true := by decide +kernel
lemma A5_5_6Law_check_3_0_5 : contains (.mul (A5_5_6Raw (shape 3 0 5)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 0 5)) = true := by decide +kernel
lemma A5_5_6Law_check_3_1_4 : contains (.mul (A5_5_6Raw (shape 3 1 4)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 1 4)) = true := by decide +kernel
lemma A5_5_6Law_check_3_2_3 : contains (.mul (A5_5_6Raw (shape 3 2 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 2 3)) = true := by decide +kernel
lemma A5_5_6Law_check_3_3_2 : contains (.mul (A5_5_6Raw (shape 3 3 2)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 3 2)) = true := by decide +kernel
lemma A5_5_6Law_check_3_4_1 : contains (.mul (A5_5_6Raw (shape 3 4 1)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 4 1)) = true := by decide +kernel
lemma A5_5_6Law_check_3_5_0 : contains (.mul (A5_5_6Raw (shape 3 5 0)) (.inv A5_5_6Den)) (A5_5_6Table (shape 3 5 0)) = true := by decide +kernel
lemma A5_5_6Law_check_4_0_4 : contains (.mul (A5_5_6Raw (shape 4 0 4)) (.inv A5_5_6Den)) (A5_5_6Table (shape 4 0 4)) = true := by decide +kernel
lemma A5_5_6Law_check_4_1_3 : contains (.mul (A5_5_6Raw (shape 4 1 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 4 1 3)) = true := by decide +kernel
lemma A5_5_6Law_check_4_2_2 : contains (.mul (A5_5_6Raw (shape 4 2 2)) (.inv A5_5_6Den)) (A5_5_6Table (shape 4 2 2)) = true := by decide +kernel
lemma A5_5_6Law_check_4_3_1 : contains (.mul (A5_5_6Raw (shape 4 3 1)) (.inv A5_5_6Den)) (A5_5_6Table (shape 4 3 1)) = true := by decide +kernel
lemma A5_5_6Law_check_4_4_0 : contains (.mul (A5_5_6Raw (shape 4 4 0)) (.inv A5_5_6Den)) (A5_5_6Table (shape 4 4 0)) = true := by decide +kernel
lemma A5_5_6Law_check_5_0_3 : contains (.mul (A5_5_6Raw (shape 5 0 3)) (.inv A5_5_6Den)) (A5_5_6Table (shape 5 0 3)) = true := by decide +kernel
lemma A5_5_6Law_check_5_1_2 : contains (.mul (A5_5_6Raw (shape 5 1 2)) (.inv A5_5_6Den)) (A5_5_6Table (shape 5 1 2)) = true := by decide +kernel
lemma A5_5_6Law_check_5_2_1 : contains (.mul (A5_5_6Raw (shape 5 2 1)) (.inv A5_5_6Den)) (A5_5_6Table (shape 5 2 1)) = true := by decide +kernel
lemma A5_5_6Law_check_5_3_0 : contains (.mul (A5_5_6Raw (shape 5 3 0)) (.inv A5_5_6Den)) (A5_5_6Table (shape 5 3 0)) = true := by decide +kernel
lemma A5_5_6Law_check (u : Shape) (hu : u ∈ below (shape 5 5 6)) :
    contains (.mul (A5_5_6Raw u) (.inv A5_5_6Den)) (A5_5_6Table u) = true := by
  rw [A5_5_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A5_5_6Law_check_0_2_6
  · exact A5_5_6Law_check_0_3_5
  · exact A5_5_6Law_check_0_4_4
  · exact A5_5_6Law_check_0_5_3
  · exact A5_5_6Law_check_1_1_6
  · exact A5_5_6Law_check_1_2_5
  · exact A5_5_6Law_check_1_3_4
  · exact A5_5_6Law_check_1_4_3
  · exact A5_5_6Law_check_1_5_2
  · exact A5_5_6Law_check_2_0_6
  · exact A5_5_6Law_check_2_1_5
  · exact A5_5_6Law_check_2_2_4
  · exact A5_5_6Law_check_2_3_3
  · exact A5_5_6Law_check_2_4_2
  · exact A5_5_6Law_check_2_5_1
  · exact A5_5_6Law_check_3_0_5
  · exact A5_5_6Law_check_3_1_4
  · exact A5_5_6Law_check_3_2_3
  · exact A5_5_6Law_check_3_3_2
  · exact A5_5_6Law_check_3_4_1
  · exact A5_5_6Law_check_3_5_0
  · exact A5_5_6Law_check_4_0_4
  · exact A5_5_6Law_check_4_1_3
  · exact A5_5_6Law_check_4_2_2
  · exact A5_5_6Law_check_4_3_1
  · exact A5_5_6Law_check_4_4_0
  · exact A5_5_6Law_check_5_0_3
  · exact A5_5_6Law_check_5_1_2
  · exact A5_5_6Law_check_5_2_1
  · exact A5_5_6Law_check_5_3_0
lemma A5_5_6Law_sound (u : Shape) :
    (A5_5_6Law u).Encloses (stageALaw (shape 5 5 6) u : ℝ) := by
  by_cases hu : u ∈ below (shape 5 5 6)
  · have h := contains_sound (Ball.mul_sound (A5_5_6Raw_sound u hu)
      (Ball.inv_sound A5_5_6Den_sound A5_5_6Den_positive)) (A5_5_6Law_check u hu)
    simpa only [A5_5_6Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A5_5_6Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def AProbsTable (s u : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 14 => A1_1_14Law u
  | 1, 2, 13 => A1_2_13Law u
  | 1, 3, 12 => A1_3_12Law u
  | 1, 4, 11 => A1_4_11Law u
  | 1, 5, 10 => A1_5_10Law u
  | 1, 6, 9 => A1_6_9Law u
  | 1, 7, 8 => A1_7_8Law u
  | 2, 2, 12 => A2_2_12Law u
  | 2, 3, 11 => A2_3_11Law u
  | 2, 4, 10 => A2_4_10Law u
  | 2, 5, 9 => A2_5_9Law u
  | 2, 6, 8 => A2_6_8Law u
  | 2, 7, 7 => A2_7_7Law u
  | 3, 3, 10 => A3_3_10Law u
  | 3, 4, 9 => A3_4_9Law u
  | 3, 5, 8 => A3_5_8Law u
  | 3, 6, 7 => A3_6_7Law u
  | 4, 4, 8 => A4_4_8Law u
  | 4, 5, 7 => A4_5_7Law u
  | 4, 6, 6 => A4_6_6Law u
  | 5, 5, 6 => A5_5_6Law u
  | _, _, _ => (.exact 0)
lemma AProbsTable_sound (g : Shape) (hg : g ∈ positiveInitial) (u : Shape) :
    (AProbsTable g u).Encloses (stageALaw g u : ℝ) := by
  rw [positiveInitial_list] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A1_1_14Law_sound u
  · exact A1_2_13Law_sound u
  · exact A1_3_12Law_sound u
  · exact A1_4_11Law_sound u
  · exact A1_5_10Law_sound u
  · exact A1_6_9Law_sound u
  · exact A1_7_8Law_sound u
  · exact A2_2_12Law_sound u
  · exact A2_3_11Law_sound u
  · exact A2_4_10Law_sound u
  · exact A2_5_9Law_sound u
  · exact A2_6_8Law_sound u
  · exact A2_7_7Law_sound u
  · exact A3_3_10Law_sound u
  · exact A3_4_9Law_sound u
  · exact A3_5_8Law_sound u
  · exact A3_6_7Law_sound u
  · exact A4_4_8Law_sound u
  · exact A4_5_7Law_sound u
  · exact A4_6_6Law_sound u
  · exact A5_5_6Law_sound u
def secondProbs (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(69961933900937038973810717 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(12225475568090238873041151441 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(237411073357556581276502992929 / 50000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(4230776649784552867243147046861 / 100000000000000000000000000000000), (51 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3547397943227606492584968866981 / 50000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(479798427065252805047798804001 / 50000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(8873532193375516366129001309 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 7, 1 => ⟨(37761738676306841647289119 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 8, 0 => ⟨0, 0⟩
  | 1, 0, 7 => ⟨(6438692289104433119668731959 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(396449683591614668262742331113 / 100000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(7475754434060585075518103043991 / 100000000000000000000000000000000), (83 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(30737266894969885701115253765617 / 100000000000000000000000000000000), (59 / 20000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(14261596080166754120520730143589 / 100000000000000000000000000000000), (31 / 20000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(626067956486069015200470969959 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(3285158323719550978069819523 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 7, 0 => ⟨(975621486089752789548109 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(90413820613809065387009577181 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(168682821311829360842363366021 / 5000000000000000000000000000000), (41 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(16597878638086061586510503770607 / 50000000000000000000000000000000), (311 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(40531425822231342208196361227163 / 100000000000000000000000000000000), (363 / 100000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(7081993762541297835979778514079 / 100000000000000000000000000000000), (17 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(9821070435865618341900223303 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(40664393453437432199665563 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(66372901003719256392546735253 / 20000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(7458452229072232749356247455867 / 100000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(5834298510241192163399383030477 / 25000000000000000000000000000000), (229 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(11105258047046141314482148827847 / 100000000000000000000000000000000), (61 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(115877797524955486474569484493 / 20000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(1474745044110606848348633769 / 50000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(127180720981131837029517845441 / 50000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(229386345126997321904071678101 / 10000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(596904226304951333077005521279 / 20000000000000000000000000000000), (37 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(204433827117624377981263345963 / 50000000000000000000000000000000), (7 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(157961720646067031611604423 / 2000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 0, 3 => ⟨(1281566078537013099196608213 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 1, 2 => ⟨(9204811902836787308641159891 / 12500000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 5, 2, 1 => ⟨(3169349558485787912791048423 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 5, 3, 0 => ⟨(45111958926755639262102049 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 6, 0, 2 => ⟨0, 0⟩
  | 6, 1, 1 => ⟨0, 0⟩
  | 6, 2, 0 => ⟨0, 0⟩
  | 7, 0, 1 => ⟨0, 0⟩
  | 7, 1, 0 => ⟨0, 0⟩
  | 8, 0, 0 => ⟨0, 0⟩
  | _, _, _ => (.exact 0)
lemma second_0_0_8 : (secondProbs (shape 0 0 8)).Encloses (secondMass (shape 0 0 8) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 0 8))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 0 8))))
  · decide +kernel
lemma second_0_1_7 : (secondProbs (shape 0 1 7)).Encloses (secondMass (shape 0 1 7) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 1 7))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 1 7))))
  · decide +kernel
lemma second_0_2_6 : (secondProbs (shape 0 2 6)).Encloses (secondMass (shape 0 2 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 2 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 2 6))))
  · decide +kernel
lemma second_0_3_5 : (secondProbs (shape 0 3 5)).Encloses (secondMass (shape 0 3 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 3 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 3 5))))
  · decide +kernel
lemma second_0_4_4 : (secondProbs (shape 0 4 4)).Encloses (secondMass (shape 0 4 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 4 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 4 4))))
  · decide +kernel
lemma second_0_5_3 : (secondProbs (shape 0 5 3)).Encloses (secondMass (shape 0 5 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 5 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 5 3))))
  · decide +kernel
lemma second_0_6_2 : (secondProbs (shape 0 6 2)).Encloses (secondMass (shape 0 6 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 6 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 6 2))))
  · decide +kernel
lemma second_0_7_1 : (secondProbs (shape 0 7 1)).Encloses (secondMass (shape 0 7 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 7 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 7 1))))
  · decide +kernel
lemma second_0_8_0 : (secondProbs (shape 0 8 0)).Encloses (secondMass (shape 0 8 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 0 8 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 0 8 0))))
  · decide +kernel
lemma second_1_0_7 : (secondProbs (shape 1 0 7)).Encloses (secondMass (shape 1 0 7) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 0 7))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 0 7))))
  · decide +kernel
lemma second_1_1_6 : (secondProbs (shape 1 1 6)).Encloses (secondMass (shape 1 1 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 1 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 1 6))))
  · decide +kernel
lemma second_1_2_5 : (secondProbs (shape 1 2 5)).Encloses (secondMass (shape 1 2 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 2 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 2 5))))
  · decide +kernel
lemma second_1_3_4 : (secondProbs (shape 1 3 4)).Encloses (secondMass (shape 1 3 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 3 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 3 4))))
  · decide +kernel
lemma second_1_4_3 : (secondProbs (shape 1 4 3)).Encloses (secondMass (shape 1 4 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 4 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 4 3))))
  · decide +kernel
lemma second_1_5_2 : (secondProbs (shape 1 5 2)).Encloses (secondMass (shape 1 5 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 5 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 5 2))))
  · decide +kernel
lemma second_1_6_1 : (secondProbs (shape 1 6 1)).Encloses (secondMass (shape 1 6 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 6 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 6 1))))
  · decide +kernel
lemma second_1_7_0 : (secondProbs (shape 1 7 0)).Encloses (secondMass (shape 1 7 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 1 7 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 1 7 0))))
  · decide +kernel
lemma second_2_0_6 : (secondProbs (shape 2 0 6)).Encloses (secondMass (shape 2 0 6) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 0 6))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 0 6))))
  · decide +kernel
lemma second_2_1_5 : (secondProbs (shape 2 1 5)).Encloses (secondMass (shape 2 1 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 1 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 1 5))))
  · decide +kernel
lemma second_2_2_4 : (secondProbs (shape 2 2 4)).Encloses (secondMass (shape 2 2 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 2 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 2 4))))
  · decide +kernel
lemma second_2_3_3 : (secondProbs (shape 2 3 3)).Encloses (secondMass (shape 2 3 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 3 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 3 3))))
  · decide +kernel
lemma second_2_4_2 : (secondProbs (shape 2 4 2)).Encloses (secondMass (shape 2 4 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 4 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 4 2))))
  · decide +kernel
lemma second_2_5_1 : (secondProbs (shape 2 5 1)).Encloses (secondMass (shape 2 5 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 5 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 5 1))))
  · decide +kernel
lemma second_2_6_0 : (secondProbs (shape 2 6 0)).Encloses (secondMass (shape 2 6 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 2 6 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 2 6 0))))
  · decide +kernel
lemma second_3_0_5 : (secondProbs (shape 3 0 5)).Encloses (secondMass (shape 3 0 5) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 0 5))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 0 5))))
  · decide +kernel
lemma second_3_1_4 : (secondProbs (shape 3 1 4)).Encloses (secondMass (shape 3 1 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 1 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 1 4))))
  · decide +kernel
lemma second_3_2_3 : (secondProbs (shape 3 2 3)).Encloses (secondMass (shape 3 2 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 2 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 2 3))))
  · decide +kernel
lemma second_3_3_2 : (secondProbs (shape 3 3 2)).Encloses (secondMass (shape 3 3 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 3 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 3 2))))
  · decide +kernel
lemma second_3_4_1 : (secondProbs (shape 3 4 1)).Encloses (secondMass (shape 3 4 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 4 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 4 1))))
  · decide +kernel
lemma second_3_5_0 : (secondProbs (shape 3 5 0)).Encloses (secondMass (shape 3 5 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 3 5 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 3 5 0))))
  · decide +kernel
lemma second_4_0_4 : (secondProbs (shape 4 0 4)).Encloses (secondMass (shape 4 0 4) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 0 4))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 0 4))))
  · decide +kernel
lemma second_4_1_3 : (secondProbs (shape 4 1 3)).Encloses (secondMass (shape 4 1 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 1 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 1 3))))
  · decide +kernel
lemma second_4_2_2 : (secondProbs (shape 4 2 2)).Encloses (secondMass (shape 4 2 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 2 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 2 2))))
  · decide +kernel
lemma second_4_3_1 : (secondProbs (shape 4 3 1)).Encloses (secondMass (shape 4 3 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 3 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 3 1))))
  · decide +kernel
lemma second_4_4_0 : (secondProbs (shape 4 4 0)).Encloses (secondMass (shape 4 4 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 4 4 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 4 4 0))))
  · decide +kernel
lemma second_5_0_3 : (secondProbs (shape 5 0 3)).Encloses (secondMass (shape 5 0 3) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 0 3))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 0 3))))
  · decide +kernel
lemma second_5_1_2 : (secondProbs (shape 5 1 2)).Encloses (secondMass (shape 5 1 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 1 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 1 2))))
  · decide +kernel
lemma second_5_2_1 : (secondProbs (shape 5 2 1)).Encloses (secondMass (shape 5 2 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 2 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 2 1))))
  · decide +kernel
lemma second_5_3_0 : (secondProbs (shape 5 3 0)).Encloses (secondMass (shape 5 3 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 5 3 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 5 3 0))))
  · decide +kernel
lemma second_6_0_2 : (secondProbs (shape 6 0 2)).Encloses (secondMass (shape 6 0 2) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 0 2))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 0 2))))
  · decide +kernel
lemma second_6_1_1 : (secondProbs (shape 6 1 1)).Encloses (secondMass (shape 6 1 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 1 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 1 1))))
  · decide +kernel
lemma second_6_2_0 : (secondProbs (shape 6 2 0)).Encloses (secondMass (shape 6 2 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 6 2 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 6 2 0))))
  · decide +kernel
lemma second_7_0_1 : (secondProbs (shape 7 0 1)).Encloses (secondMass (shape 7 0 1) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 7 0 1))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 7 0 1))))
  · decide +kernel
lemma second_7_1_0 : (secondProbs (shape 7 1 0)).Encloses (secondMass (shape 7 1 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 7 1 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 7 1 0))))
  · decide +kernel
lemma second_8_0_0 : (secondProbs (shape 8 0 0)).Encloses (secondMass (shape 8 0 0) : ℝ) := by
  rw [secondMass_cast]
  apply contains_sound (a := (Ball.mul (.exact 2) (listSumBall positiveInitial (fun g => .mul (initialProbs g) (AProbsTable g (shape 8 0 0))))))
  · exact Ball.mul_sound (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2)
      (listSumBall_sound _ _ _ (fun g hg => Ball.mul_sound
        (initialProbs_sound g (List.mem_filter.mp hg).1) (AProbsTable_sound g hg (shape 8 0 0))))
  · decide +kernel
lemma secondProbs_sound (t : Shape) (ht : t ∈ shapes 8) :
    (secondProbs t).Encloses (secondMass t : ℝ) := by
  rw [allSecond_list] at ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact second_0_0_8
  · exact second_0_1_7
  · exact second_0_2_6
  · exact second_0_3_5
  · exact second_0_4_4
  · exact second_0_5_3
  · exact second_0_6_2
  · exact second_0_7_1
  · exact second_0_8_0
  · exact second_1_0_7
  · exact second_1_1_6
  · exact second_1_2_5
  · exact second_1_3_4
  · exact second_1_4_3
  · exact second_1_5_2
  · exact second_1_6_1
  · exact second_1_7_0
  · exact second_2_0_6
  · exact second_2_1_5
  · exact second_2_2_4
  · exact second_2_3_3
  · exact second_2_4_2
  · exact second_2_5_1
  · exact second_2_6_0
  · exact second_3_0_5
  · exact second_3_1_4
  · exact second_3_2_3
  · exact second_3_3_2
  · exact second_3_4_1
  · exact second_3_5_0
  · exact second_4_0_4
  · exact second_4_1_3
  · exact second_4_2_2
  · exact second_4_3_1
  · exact second_4_4_0
  · exact second_5_0_3
  · exact second_5_1_2
  · exact second_5_2_1
  · exact second_5_3_0
  · exact second_6_0_2
  · exact second_6_1_1
  · exact second_6_2_0
  · exact second_7_0_1
  · exact second_7_1_0
  · exact second_8_0_0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
def B1_1_6U0_0_4Leaf : Ball := ⟨0, 0⟩
lemma B1_1_6U0_0_4Leaf_sound : B1_1_6U0_0_4Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 1 6) (shape 0 0 4)) := by
  have hh : shapeMax (shape 0 0 4) = 4 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, ite_true]
  simpa only [B1_1_6U0_0_4Leaf, Ball.exact, Rat.cast_zero] using Ball.exact_sound 0
def B1_1_6U0_0_4Mass : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_1_6U0_0_4Mass_sound : B1_1_6U0_0_4Mass.Encloses (littleMass (shape 1 1 6) (shape 0 0 4) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_1_6))
    (B1_1_6Law_sound (shape 0 0 4))) (by decide +kernel)
def B1_1_6U0_1_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_1_6U0_1_3Leaf_sound : B1_1_6U0_1_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 1 6) (shape 0 1 3)) := by
  have hh : shapeMax (shape 0 1 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_1_6U0_1_3Mass : Ball := ⟨(389029125902587733647766048067 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma B1_1_6U0_1_3Mass_sound : B1_1_6U0_1_3Mass.Encloses (littleMass (shape 1 1 6) (shape 0 1 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_1_6))
    (B1_1_6Law_sound (shape 0 1 3))) (by decide +kernel)
def B1_1_6U1_0_3Leaf : Ball := ⟨(115129254649702284200899544090987 / 50000000000000000000000000000000), (21175823683 / 25000000000000000000000000000000)⟩
lemma B1_1_6U1_0_3Leaf_sound : B1_1_6U1_0_3Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 1 6) (shape 1 0 3)) := by
  have hh : shapeMax (shape 1 0 3) = 3 := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, show (3 : ℕ) ≠ 4 by decide, ite_false, ite_true]
  exact logN10_sound
def B1_1_6U1_0_3Mass : Ball := ⟨(389029125902587733647766048067 / 100000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
lemma B1_1_6U1_0_3Mass_sound : B1_1_6U1_0_3Mass.Encloses (littleMass (shape 1 1 6) (shape 1 0 3) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_1_6))
    (B1_1_6Law_sound (shape 1 0 3))) (by decide +kernel)
def B1_1_6U1_1_2D : Ball := .exact (63 / 1000000)
lemma B1_1_6U1_1_2D_sound : B1_1_6U1_1_2D.Encloses (binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ) := by
  apply exact_rat_enclosed
  decide +kernel
def B1_1_6U1_1_2OneD : Ball := .exact (999937 / 1000000)
lemma B1_1_6U1_1_2OneD_sound : B1_1_6U1_1_2OneD.Encloses (1 - (binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ)) := by
  have he : binaryParameter (shape 1 1 6) (shape 1 1 2) = (63 / 1000000) := by decide +kernel
  rw [he]
  convert Ball.exact_sound ((999937 / 1000000) : ℚ) using 1 <;> norm_num [B1_1_6U1_1_2OneD, Ball.exact]
def B1_1_6U1_1_2EDLogWitness : LogWitness := ⟨-14, 16128, 15625⟩
def B1_1_6U1_1_2EDLog : Ball := ⟨(-120904697894659267702651285468121 / 12500000000000000000000000000000), (79409338811 / 25000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2EDLog_sound : B1_1_6U1_1_2EDLog.Encloses (Real.log ((binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ))) := by
  exact checkLog_sound logTwoBall_sound (B1_1_6U1_1_2D_sound) (w := B1_1_6U1_1_2EDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_1_6U1_1_2ED : Ball := ⟨(15233991934727067730534061969 / 25000000000000000000000000000000), (10005577 / 50000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2ED_sound : B1_1_6U1_1_2ED.Encloses (Foundation.entropyTerm ((binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ))) := by
  exact contains_sound (entropyTerm_ball (B1_1_6U1_1_2D_sound) B1_1_6U1_1_2EDLog_sound) (by decide +kernel)
def B1_1_6U1_1_2EOneDLogWitness : LogWitness := ⟨-1, 999937, 500000⟩
def B1_1_6U1_1_2EOneDLog : Ball := ⟨(-126003969166705876877493883 / 2000000000000000000000000000000), (21175823683 / 50000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2EOneDLog_sound : B1_1_6U1_1_2EOneDLog.Encloses (Real.log ((1 - (binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ)))) := by
  exact checkLog_sound logTwoBall_sound (B1_1_6U1_1_2OneD_sound) (w := B1_1_6U1_1_2EOneDLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
def B1_1_6U1_1_2EOneD : Ball := ⟨(1574950386458104680090632511 / 25000000000000000000000000000000), (42348979213 / 100000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2EOneD_sound : B1_1_6U1_1_2EOneD.Encloses (Foundation.entropyTerm ((1 - (binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ)))) := by
  exact contains_sound (entropyTerm_ball (B1_1_6U1_1_2OneD_sound) B1_1_6U1_1_2EOneDLog_sound) (by decide +kernel)
def B1_1_6U1_1_2BinaryEntropy : Ball := ⟨(35801298261134172545913669541 / 50000000000000000000000000000000), (42371658521 / 100000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2BinaryEntropy_sound : B1_1_6U1_1_2BinaryEntropy.Encloses
    (binaryEntropyRate (binaryParameter (shape 1 1 6) (shape 1 1 2))) := by
  exact contains_sound (Ball.add_sound (Ball.add_sound B1_1_6U1_1_2EOneD_sound B1_1_6U1_1_2ED_sound)
    (Ball.mul_sound B1_1_6U1_1_2D_sound logN2_sound)) (by decide +kernel)
def B1_1_6U1_1_2Leaf : Ball := ⟨(64375488605594348017558361096379 / 20000000000000000000000000000000), (31762734967 / 25000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2Leaf_sound : B1_1_6U1_1_2Leaf.Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 1 6) (shape 1 1 2)) := by
  have hh : shapeMax (shape 1 1 2) = 2 := by decide +kernel
  have hp : positive (shape 1 1 2) = true := by decide +kernel
  simp only [AllFieldTerminalRates.secondLeafRate, hh, hp, Bool.not_true, Bool.false_eq_true,
    show (2 : ℕ) ≠ 4 by decide, show (2 : ℕ) ≠ 3 by decide, ite_false]
  have ht : (Ball.exact (1999937 / 1000000)).Encloses (2 - (binaryParameter (shape 1 1 6) (shape 1 1 2) : ℝ)) := by
    have he : binaryParameter (shape 1 1 6) (shape 1 1 2) = (63 / 1000000) := by decide +kernel
    rw [he]
    convert Ball.exact_sound ((1999937 / 1000000) : ℚ) using 1
    norm_num [Ball.exact]
  exact contains_sound (Ball.mul_sound ht logN5_sound) (by decide +kernel)
def B1_1_6U1_1_2Mass : Ball := ⟨(3710278844513467307488141523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
lemma B1_1_6U1_1_2Mass_sound : B1_1_6U1_1_2Mass.Encloses (littleMass (shape 1 1 6) (shape 1 1 2) : ℝ) := by
  rw [littleMass_cast]
  exact contains_sound (Ball.mul_sound (Ball.mul_sound
    (by simpa only [Rat.cast_ofNat] using Ball.exact_sound 2) (second_1_1_6))
    (B1_1_6Law_sound (shape 1 1 2))) (by decide +kernel)
def B1_1_6Leaves (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_1_6U0_0_4Leaf
  | 0, 1, 3 => B1_1_6U0_1_3Leaf
  | 1, 0, 3 => B1_1_6U1_0_3Leaf
  | 1, 1, 2 => B1_1_6U1_1_2Leaf
  | _, _, _ => (.exact 0)
lemma B1_1_6Leaves_sound (u : Shape) (hu : u ∈ below (shape 1 1 6)) :
    (B1_1_6Leaves u).Encloses (AllFieldTerminalRates.secondLeafRate (shape 1 1 6) u) := by
  rw [B1_1_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_1_6U0_0_4Leaf_sound
  · exact B1_1_6U0_1_3Leaf_sound
  · exact B1_1_6U1_0_3Leaf_sound
  · exact B1_1_6U1_1_2Leaf_sound
def B1_1_6Masses (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 4 => B1_1_6U0_0_4Mass
  | 0, 1, 3 => B1_1_6U0_1_3Mass
  | 1, 0, 3 => B1_1_6U1_0_3Mass
  | 1, 1, 2 => B1_1_6U1_1_2Mass
  | _, _, _ => (.exact 0)
lemma B1_1_6Masses_sound (u : Shape) (hu : u ∈ below (shape 1 1 6)) :
    (B1_1_6Masses u).Encloses ((fun u => (littleMass (shape 1 1 6) u : ℝ)) u) := by
  rw [B1_1_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact B1_1_6U0_0_4Mass_sound
  · exact B1_1_6U0_1_3Mass_sound
  · exact B1_1_6U1_0_3Mass_sound
  · exact B1_1_6U1_1_2Mass_sound
def B1_1_6Binaries (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 1, 1, 2 => B1_1_6U1_1_2BinaryEntropy
  | _, _, _ => (.exact 0)
lemma B1_1_6Binaries_sound (u : Shape) (hu : u ∈ (below (shape 1 1 6)).filter positive) :
    (B1_1_6Binaries u).Encloses ((fun u => binaryEntropyRate (binaryParameter (shape 1 1 6) u)) u) := by
  have hl : (below (shape 1 1 6)).filter positive = [(shape 1 1 2)] := by decide +kernel
  rw [hl] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl
  · exact B1_1_6U1_1_2BinaryEntropy_sound
def B1_1_6S2 : Ball := ⟨(113464402089716250899384401133 / 6250000000000000000000000000000), (668468917 / 100000000000000000000000000000000)⟩
lemma B1_1_6S2_sound : B1_1_6S2.Encloses
    (((below (shape 1 1 6)).map fun u => (littleMass (shape 1 1 6) u : ℝ) * AllFieldTerminalRates.secondLeafRate (shape 1 1 6) u).sum) := by
  exact contains_sound (listSumBall_sound (below (shape 1 1 6))
    (fun u => .mul (B1_1_6Masses u) (B1_1_6Leaves u)) _
    (fun u hu => Ball.mul_sound (B1_1_6Masses_sound u hu) (B1_1_6Leaves_sound u hu))) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
