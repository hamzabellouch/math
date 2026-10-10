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
lemma A4_6_6_below : below (shape 4 6 6) = [
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
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
  (shape 2 6 0),
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
def A4_6_6Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(37007680233059694261632513727 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(271425459907852890084474170757 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2973450328881290536063908848299 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(1344967952978413384079961640011 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(7218791470495623248351293593 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(17136753165425385847386480203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(2777830385098454704554116818579 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(37038954605575141351236241889301 / 100000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(2314240286611235203992770108591 / 6250000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(172110505220792807003863412141 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(16859688301886595155585889253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(9933044295486291664832751 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(557758160866722243028058363771 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(8218402317164102891027245622431 / 25000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(8218402317164102891027245622431 / 25000000000000000000000000000000), (43 / 50000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(557758160866722243028058363771 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(9933044295486291664832751 / 800000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(16859688301886595155585889253 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(172110505220792807003863412141 / 6250000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(2314240286611235203992770108591 / 6250000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(37038954605575141351236241889301 / 100000000000000000000000000000000), (47 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(2777830385098454704554116818579 / 100000000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(17136753165425385847386480203 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(7218791470495623248351293593 / 20000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(1344967952978413384079961640011 / 100000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(2973450328881290536063908848299 / 50000000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(271425459907852890084474170757 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(37007680233059694261632513727 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A4_6_6Raw_0_2_6 : (A4_6_6Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 2 6)
    (-17098) (-5564) (-56356) w100 w166 w25
    (by decide +kernel) w100_sound w166_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_0_3_5 : (A4_6_6Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 3 5)
    (-17098) (0) (-25900) w100 w195 w79
    (by decide +kernel) w100_sound w195_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_0_4_4 : (A4_6_6Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 4 4)
    (-17098) (-5564) (-5561) w100 w166 w167
    (by decide +kernel) w100_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_0_5_3 : (A4_6_6Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 5 3)
    (-17098) (-25990) (0) w100 w78 w195
    (by decide +kernel) w100_sound w78_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_0_6_2 : (A4_6_6Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 0 6 2)
    (-17098) (-56609) (-5561) w100 w24 w167
    (by decide +kernel) w100_sound w24_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_1_6 : (A4_6_6Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 1 6)
    (-4371) (-25990) (-56356) w174 w78 w25
    (by decide +kernel) w174_sound w78_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_1_2_5 : (A4_6_6Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 2 5)
    (-4371) (-5564) (-25900) w174 w166 w79
    (by decide +kernel) w174_sound w166_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_1_3_4 : (A4_6_6Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 3 4)
    (-4371) (0) (-5561) w174 w195 w167
    (by decide +kernel) w174_sound w195_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_4_3 : (A4_6_6Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 4 3)
    (-4371) (-5564) (0) w174 w166 w195
    (by decide +kernel) w174_sound w166_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_1_5_2 : (A4_6_6Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 5 2)
    (-4371) (-25990) (-5561) w174 w78 w167
    (by decide +kernel) w174_sound w78_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_1_6_1 : (A4_6_6Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 1 6 1)
    (-4371) (-56609) (-25900) w174 w24 w79
    (by decide +kernel) w174_sound w24_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_0_6 : (A4_6_6Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 0 6)
    (0) (-56609) (-56356) w195 w24 w25
    (by decide +kernel) w195_sound w24_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_2_1_5 : (A4_6_6Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 1 5)
    (0) (-25990) (-25900) w195 w78 w79
    (by decide +kernel) w195_sound w78_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_2_4 : (A4_6_6Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 2 4)
    (0) (-5564) (-5561) w195 w166 w167
    (by decide +kernel) w195_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_2_3_3 : (A4_6_6Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 3 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_2_4_2 : (A4_6_6Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 4 2)
    (0) (-5564) (-5561) w195 w166 w167
    (by decide +kernel) w195_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_2_5_1 : (A4_6_6Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 5 1)
    (0) (-25990) (-25900) w195 w78 w79
    (by decide +kernel) w195_sound w78_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_2_6_0 : (A4_6_6Raw (shape 2 6 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 2 6 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 2 6 0)
    (0) (-56609) (-56356) w195 w24 w25
    (by decide +kernel) w195_sound w24_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_3_0_5 : (A4_6_6Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 0 5)
    (-4371) (-56609) (-25900) w174 w24 w79
    (by decide +kernel) w174_sound w24_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_3_1_4 : (A4_6_6Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 1 4)
    (-4371) (-25990) (-5561) w174 w78 w167
    (by decide +kernel) w174_sound w78_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_3_2_3 : (A4_6_6Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 2 3)
    (-4371) (-5564) (0) w174 w166 w195
    (by decide +kernel) w174_sound w166_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_3_3_2 : (A4_6_6Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 3 2)
    (-4371) (0) (-5561) w174 w195 w167
    (by decide +kernel) w174_sound w195_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_3_4_1 : (A4_6_6Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 4 1)
    (-4371) (-5564) (-25900) w174 w166 w79
    (by decide +kernel) w174_sound w166_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_3_5_0 : (A4_6_6Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 3 5 0)
    (-4371) (-25990) (-56356) w174 w78 w25
    (by decide +kernel) w174_sound w78_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_4_0_4 : (A4_6_6Raw (shape 4 0 4)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 0 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 0 4)
    (-17098) (-56609) (-5561) w100 w24 w167
    (by decide +kernel) w100_sound w24_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_4_1_3 : (A4_6_6Raw (shape 4 1 3)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 1 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 1 3)
    (-17098) (-25990) (0) w100 w78 w195
    (by decide +kernel) w100_sound w78_sound w195_sound) (by decide +kernel)
lemma A4_6_6Raw_4_2_2 : (A4_6_6Raw (shape 4 2 2)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 2 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 2 2)
    (-17098) (-5564) (-5561) w100 w166 w167
    (by decide +kernel) w100_sound w166_sound w167_sound) (by decide +kernel)
lemma A4_6_6Raw_4_3_1 : (A4_6_6Raw (shape 4 3 1)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 3 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 3 1)
    (-17098) (0) (-25900) w100 w195 w79
    (by decide +kernel) w100_sound w195_sound w79_sound) (by decide +kernel)
lemma A4_6_6Raw_4_4_0 : (A4_6_6Raw (shape 4 4 0)).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) (shape 4 4 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 4 6 6) (shape 4 4 0)
    (-17098) (-5564) (-56356) w100 w166 w25
    (by decide +kernel) w100_sound w166_sound w25_sound) (by decide +kernel)
lemma A4_6_6Raw_sound (u : Shape) (hu : u ∈ below (shape 4 6 6)) :
    (A4_6_6Raw u).Encloses (splitWeight positiveInitial tableP (shape 4 6 6) u : ℝ) := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_6_6Raw_0_2_6
  · exact A4_6_6Raw_0_3_5
  · exact A4_6_6Raw_0_4_4
  · exact A4_6_6Raw_0_5_3
  · exact A4_6_6Raw_0_6_2
  · exact A4_6_6Raw_1_1_6
  · exact A4_6_6Raw_1_2_5
  · exact A4_6_6Raw_1_3_4
  · exact A4_6_6Raw_1_4_3
  · exact A4_6_6Raw_1_5_2
  · exact A4_6_6Raw_1_6_1
  · exact A4_6_6Raw_2_0_6
  · exact A4_6_6Raw_2_1_5
  · exact A4_6_6Raw_2_2_4
  · exact A4_6_6Raw_2_3_3
  · exact A4_6_6Raw_2_4_2
  · exact A4_6_6Raw_2_5_1
  · exact A4_6_6Raw_2_6_0
  · exact A4_6_6Raw_3_0_5
  · exact A4_6_6Raw_3_1_4
  · exact A4_6_6Raw_3_2_3
  · exact A4_6_6Raw_3_3_2
  · exact A4_6_6Raw_3_4_1
  · exact A4_6_6Raw_3_5_0
  · exact A4_6_6Raw_4_0_4
  · exact A4_6_6Raw_4_1_3
  · exact A4_6_6Raw_4_2_2
  · exact A4_6_6Raw_4_3_1
  · exact A4_6_6Raw_4_4_0
def A4_6_6Den : Ball := ⟨(21473387588672402815433518941063 / 6250000000000000000000000000000), (339 / 50000000000000000000000000000000)⟩
lemma A4_6_6Den_sound : A4_6_6Den.Encloses (((below (shape 4 6 6)).map (splitWeight positiveInitial tableP (shape 4 6 6))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 4 6 6)) A4_6_6Raw (splitWeight positiveInitial tableP (shape 4 6 6)) A4_6_6Raw_sound) (by decide +kernel)
lemma A4_6_6Den_positive : 0 < A4_6_6Den.lower := by decide +kernel
def A4_6_6Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 2, 6 => ⟨(10771379247987724786312094607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(395002678878428760271589624507 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(346178533382622745572856101671 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(97865901122995442910500291001 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(420217317871148638292284089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(4987788109427518371238771367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(202127398799710262270548863881 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(5390240951245195934807849697209 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(5388624121496410916877795150321 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(40075303561228547414201969063 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(4907146180436727877076230291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(361386428843779882083529413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(81169971226522625940938278493 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(9568125060877047586886196521351 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(14552897101566282733842513365051 / 50000000000000000000000000000000), (29 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(9568125060877047586886196521351 / 100000000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(81169971226522625940938278493 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(361386428843779882083529413 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(4907146180436727877076230291 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(40075303561228547414201969063 / 5000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(5388624121496410916877795150321 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(5390240951245195934807849697209 / 50000000000000000000000000000000), (49 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(202127398799710262270548863881 / 25000000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(4987788109427518371238771367 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 0, 4 => ⟨(420217317871148638292284089 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 4, 1, 3 => ⟨(97865901122995442910500291001 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 2, 2 => ⟨(346178533382622745572856101671 / 20000000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 4, 3, 1 => ⟨(395002678878428760271589624507 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 4, 4, 0 => ⟨(10771379247987724786312094607 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A4_6_6Law (u : Shape) : Ball := if u ∈ below (shape 4 6 6) then A4_6_6Table u else .exact 0
lemma A4_6_6Law_check_0_2_6 : contains (.mul (A4_6_6Raw (shape 0 2 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 2 6)) = true := by decide +kernel
lemma A4_6_6Law_check_0_3_5 : contains (.mul (A4_6_6Raw (shape 0 3 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 3 5)) = true := by decide +kernel
lemma A4_6_6Law_check_0_4_4 : contains (.mul (A4_6_6Raw (shape 0 4 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 4 4)) = true := by decide +kernel
lemma A4_6_6Law_check_0_5_3 : contains (.mul (A4_6_6Raw (shape 0 5 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 5 3)) = true := by decide +kernel
lemma A4_6_6Law_check_0_6_2 : contains (.mul (A4_6_6Raw (shape 0 6 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 0 6 2)) = true := by decide +kernel
lemma A4_6_6Law_check_1_1_6 : contains (.mul (A4_6_6Raw (shape 1 1 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 1 6)) = true := by decide +kernel
lemma A4_6_6Law_check_1_2_5 : contains (.mul (A4_6_6Raw (shape 1 2 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 2 5)) = true := by decide +kernel
lemma A4_6_6Law_check_1_3_4 : contains (.mul (A4_6_6Raw (shape 1 3 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 3 4)) = true := by decide +kernel
lemma A4_6_6Law_check_1_4_3 : contains (.mul (A4_6_6Raw (shape 1 4 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 4 3)) = true := by decide +kernel
lemma A4_6_6Law_check_1_5_2 : contains (.mul (A4_6_6Raw (shape 1 5 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 5 2)) = true := by decide +kernel
lemma A4_6_6Law_check_1_6_1 : contains (.mul (A4_6_6Raw (shape 1 6 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 1 6 1)) = true := by decide +kernel
lemma A4_6_6Law_check_2_0_6 : contains (.mul (A4_6_6Raw (shape 2 0 6)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 0 6)) = true := by decide +kernel
lemma A4_6_6Law_check_2_1_5 : contains (.mul (A4_6_6Raw (shape 2 1 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 1 5)) = true := by decide +kernel
lemma A4_6_6Law_check_2_2_4 : contains (.mul (A4_6_6Raw (shape 2 2 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 2 4)) = true := by decide +kernel
lemma A4_6_6Law_check_2_3_3 : contains (.mul (A4_6_6Raw (shape 2 3 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 3 3)) = true := by decide +kernel
lemma A4_6_6Law_check_2_4_2 : contains (.mul (A4_6_6Raw (shape 2 4 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 4 2)) = true := by decide +kernel
lemma A4_6_6Law_check_2_5_1 : contains (.mul (A4_6_6Raw (shape 2 5 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 5 1)) = true := by decide +kernel
lemma A4_6_6Law_check_2_6_0 : contains (.mul (A4_6_6Raw (shape 2 6 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 2 6 0)) = true := by decide +kernel
lemma A4_6_6Law_check_3_0_5 : contains (.mul (A4_6_6Raw (shape 3 0 5)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 0 5)) = true := by decide +kernel
lemma A4_6_6Law_check_3_1_4 : contains (.mul (A4_6_6Raw (shape 3 1 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 1 4)) = true := by decide +kernel
lemma A4_6_6Law_check_3_2_3 : contains (.mul (A4_6_6Raw (shape 3 2 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 2 3)) = true := by decide +kernel
lemma A4_6_6Law_check_3_3_2 : contains (.mul (A4_6_6Raw (shape 3 3 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 3 2)) = true := by decide +kernel
lemma A4_6_6Law_check_3_4_1 : contains (.mul (A4_6_6Raw (shape 3 4 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 4 1)) = true := by decide +kernel
lemma A4_6_6Law_check_3_5_0 : contains (.mul (A4_6_6Raw (shape 3 5 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 3 5 0)) = true := by decide +kernel
lemma A4_6_6Law_check_4_0_4 : contains (.mul (A4_6_6Raw (shape 4 0 4)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 0 4)) = true := by decide +kernel
lemma A4_6_6Law_check_4_1_3 : contains (.mul (A4_6_6Raw (shape 4 1 3)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 1 3)) = true := by decide +kernel
lemma A4_6_6Law_check_4_2_2 : contains (.mul (A4_6_6Raw (shape 4 2 2)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 2 2)) = true := by decide +kernel
lemma A4_6_6Law_check_4_3_1 : contains (.mul (A4_6_6Raw (shape 4 3 1)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 3 1)) = true := by decide +kernel
lemma A4_6_6Law_check_4_4_0 : contains (.mul (A4_6_6Raw (shape 4 4 0)) (.inv A4_6_6Den)) (A4_6_6Table (shape 4 4 0)) = true := by decide +kernel
lemma A4_6_6Law_check (u : Shape) (hu : u ∈ below (shape 4 6 6)) :
    contains (.mul (A4_6_6Raw u) (.inv A4_6_6Den)) (A4_6_6Table u) = true := by
  rw [A4_6_6_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A4_6_6Law_check_0_2_6
  · exact A4_6_6Law_check_0_3_5
  · exact A4_6_6Law_check_0_4_4
  · exact A4_6_6Law_check_0_5_3
  · exact A4_6_6Law_check_0_6_2
  · exact A4_6_6Law_check_1_1_6
  · exact A4_6_6Law_check_1_2_5
  · exact A4_6_6Law_check_1_3_4
  · exact A4_6_6Law_check_1_4_3
  · exact A4_6_6Law_check_1_5_2
  · exact A4_6_6Law_check_1_6_1
  · exact A4_6_6Law_check_2_0_6
  · exact A4_6_6Law_check_2_1_5
  · exact A4_6_6Law_check_2_2_4
  · exact A4_6_6Law_check_2_3_3
  · exact A4_6_6Law_check_2_4_2
  · exact A4_6_6Law_check_2_5_1
  · exact A4_6_6Law_check_2_6_0
  · exact A4_6_6Law_check_3_0_5
  · exact A4_6_6Law_check_3_1_4
  · exact A4_6_6Law_check_3_2_3
  · exact A4_6_6Law_check_3_3_2
  · exact A4_6_6Law_check_3_4_1
  · exact A4_6_6Law_check_3_5_0
  · exact A4_6_6Law_check_4_0_4
  · exact A4_6_6Law_check_4_1_3
  · exact A4_6_6Law_check_4_2_2
  · exact A4_6_6Law_check_4_3_1
  · exact A4_6_6Law_check_4_4_0
lemma A4_6_6Law_sound (u : Shape) :
    (A4_6_6Law u).Encloses (stageALaw (shape 4 6 6) u : ℝ) := by
  by_cases hu : u ∈ below (shape 4 6 6)
  · have h := contains_sound (Ball.mul_sound (A4_6_6Raw_sound u hu)
      (Ball.inv_sound A4_6_6Den_sound A4_6_6Den_positive)) (A4_6_6Law_check u hu)
    simpa only [A4_6_6Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A4_6_6Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
