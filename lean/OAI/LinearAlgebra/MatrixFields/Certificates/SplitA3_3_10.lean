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
lemma A3_3_10_below : below (shape 3 3 10) = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 1 0 7),
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 2 0 6),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 3 0 5),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2)] := by decide +kernel
def A3_3_10Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(10114049177547547375147291033 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(1631941133917831872522312559669 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(22342041798333750043260090322813 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(21775166867897778509284039754867 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(328746702339804911134262473157 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(48051347848878380719513662951177 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(22503484997364245598597737532479 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(22503484997364245598597737532479 / 100000000000000000000000000000000), (59 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨1, 0⟩
  | 2, 2, 4 => ⟨(48051347848878380719513662951177 / 100000000000000000000000000000000), (31 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(328746702339804911134262473157 / 20000000000000000000000000000000), (1 / 20000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(21775166867897778509284039754867 / 100000000000000000000000000000000), (53 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(22342041798333750043260090322813 / 100000000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(1631941133917831872522312559669 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(10114049177547547375147291033 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A3_3_10Raw_0_0_8 : (A3_3_10Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 0 0 8)
    (-7658) (-7586) (-76746) w140 w141 w9
    (by decide +kernel) w140_sound w141_sound w9_sound) (by decide +kernel)
lemma A3_3_10Raw_0_1_7 : (A3_3_10Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 0 1 7)
    (-7658) (0) (-33496) w140 w195 w56
    (by decide +kernel) w140_sound w195_sound w56_sound) (by decide +kernel)
lemma A3_3_10Raw_0_2_6 : (A3_3_10Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 0 2 6)
    (-7658) (0) (-7329) w140 w195 w145
    (by decide +kernel) w140_sound w195_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_0_3_5 : (A3_3_10Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 0 3 5)
    (-7658) (-7586) (0) w140 w141 w195
    (by decide +kernel) w140_sound w141_sound w195_sound) (by decide +kernel)
lemma A3_3_10Raw_1_0_7 : (A3_3_10Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 1 0 7)
    (0) (-7586) (-33496) w195 w141 w56
    (by decide +kernel) w195_sound w141_sound w56_sound) (by decide +kernel)
lemma A3_3_10Raw_1_1_6 : (A3_3_10Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 1 1 6)
    (0) (0) (-7329) w195 w195 w145
    (by decide +kernel) w195_sound w195_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_1_2_5 : (A3_3_10Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_3_10Raw_1_3_4 : (A3_3_10Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 1 3 4)
    (0) (-7586) (-7329) w195 w141 w145
    (by decide +kernel) w195_sound w141_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_2_0_6 : (A3_3_10Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 2 0 6)
    (0) (-7586) (-7329) w195 w141 w145
    (by decide +kernel) w195_sound w141_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_2_1_5 : (A3_3_10Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 2 1 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_3_10Raw_2_2_4 : (A3_3_10Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 2 2 4)
    (0) (0) (-7329) w195 w195 w145
    (by decide +kernel) w195_sound w195_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_2_3_3 : (A3_3_10Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 2 3 3)
    (0) (-7586) (-33496) w195 w141 w56
    (by decide +kernel) w195_sound w141_sound w56_sound) (by decide +kernel)
lemma A3_3_10Raw_3_0_5 : (A3_3_10Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 3 0 5)
    (-7658) (-7586) (0) w140 w141 w195
    (by decide +kernel) w140_sound w141_sound w195_sound) (by decide +kernel)
lemma A3_3_10Raw_3_1_4 : (A3_3_10Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 3 1 4)
    (-7658) (0) (-7329) w140 w195 w145
    (by decide +kernel) w140_sound w195_sound w145_sound) (by decide +kernel)
lemma A3_3_10Raw_3_2_3 : (A3_3_10Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 3 2 3)
    (-7658) (0) (-33496) w140 w195 w56
    (by decide +kernel) w140_sound w195_sound w56_sound) (by decide +kernel)
lemma A3_3_10Raw_3_3_2 : (A3_3_10Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 3 10) (shape 3 3 2)
    (-7658) (-7586) (-76746) w140 w141 w9
    (by decide +kernel) w140_sound w141_sound w9_sound) (by decide +kernel)
lemma A3_3_10Raw_sound (u : Shape) (hu : u ∈ below (shape 3 3 10)) :
    (A3_3_10Raw u).Encloses (splitWeight positiveInitial tableP (shape 3 3 10) u : ℝ) := by
  rw [A3_3_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_3_10Raw_0_0_8
  · exact A3_3_10Raw_0_1_7
  · exact A3_3_10Raw_0_2_6
  · exact A3_3_10Raw_0_3_5
  · exact A3_3_10Raw_1_0_7
  · exact A3_3_10Raw_1_1_6
  · exact A3_3_10Raw_1_2_5
  · exact A3_3_10Raw_1_3_4
  · exact A3_3_10Raw_2_0_6
  · exact A3_3_10Raw_2_1_5
  · exact A3_3_10Raw_2_2_4
  · exact A3_3_10Raw_2_3_3
  · exact A3_3_10Raw_3_0_5
  · exact A3_3_10Raw_3_1_4
  · exact A3_3_10Raw_3_2_3
  · exact A3_3_10Raw_3_3_2
def A3_3_10Den : Ball := ⟨(217957830207268558846224302777823 / 50000000000000000000000000000000), (119 / 25000000000000000000000000000000)⟩
lemma A3_3_10Den_sound : A3_3_10Den.Encloses (((below (shape 3 3 10)).map (splitWeight positiveInitial tableP (shape 3 3 10))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 3 10)) A3_3_10Raw (splitWeight positiveInitial tableP (shape 3 3 10)) A3_3_10Raw_sound) (by decide +kernel)
lemma A3_3_10Den_positive : 0 < A3_3_10Den.lower := by decide +kernel
def A3_3_10Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(374370843287879533686819841787 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(5125312950924365842644983492711 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2497635304864997016024994299279 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(377076040382652095214990170031 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(22940217358767125771206291343619 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(516234837169290854412959173031 / 10000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(516234837169290854412959173031 / 10000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(22940217358767125771206291343619 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11023083640349972174887924565559 / 100000000000000000000000000000000), (27 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(377076040382652095214990170031 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(2497635304864997016024994299279 / 50000000000000000000000000000000), (9 / 50000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(5125312950924365842644983492711 / 100000000000000000000000000000000), (19 / 100000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(374370843287879533686819841787 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(92807394604080247176410297 / 4000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_3_10Law (u : Shape) : Ball := if u ∈ below (shape 3 3 10) then A3_3_10Table u else .exact 0
lemma A3_3_10Law_check_0_0_8 : contains (.mul (A3_3_10Raw (shape 0 0 8)) (.inv A3_3_10Den)) (A3_3_10Table (shape 0 0 8)) = true := by decide +kernel
lemma A3_3_10Law_check_0_1_7 : contains (.mul (A3_3_10Raw (shape 0 1 7)) (.inv A3_3_10Den)) (A3_3_10Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_3_10Law_check_0_2_6 : contains (.mul (A3_3_10Raw (shape 0 2 6)) (.inv A3_3_10Den)) (A3_3_10Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_3_10Law_check_0_3_5 : contains (.mul (A3_3_10Raw (shape 0 3 5)) (.inv A3_3_10Den)) (A3_3_10Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_3_10Law_check_1_0_7 : contains (.mul (A3_3_10Raw (shape 1 0 7)) (.inv A3_3_10Den)) (A3_3_10Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_3_10Law_check_1_1_6 : contains (.mul (A3_3_10Raw (shape 1 1 6)) (.inv A3_3_10Den)) (A3_3_10Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_3_10Law_check_1_2_5 : contains (.mul (A3_3_10Raw (shape 1 2 5)) (.inv A3_3_10Den)) (A3_3_10Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_3_10Law_check_1_3_4 : contains (.mul (A3_3_10Raw (shape 1 3 4)) (.inv A3_3_10Den)) (A3_3_10Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_3_10Law_check_2_0_6 : contains (.mul (A3_3_10Raw (shape 2 0 6)) (.inv A3_3_10Den)) (A3_3_10Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_3_10Law_check_2_1_5 : contains (.mul (A3_3_10Raw (shape 2 1 5)) (.inv A3_3_10Den)) (A3_3_10Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_3_10Law_check_2_2_4 : contains (.mul (A3_3_10Raw (shape 2 2 4)) (.inv A3_3_10Den)) (A3_3_10Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_3_10Law_check_2_3_3 : contains (.mul (A3_3_10Raw (shape 2 3 3)) (.inv A3_3_10Den)) (A3_3_10Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_3_10Law_check_3_0_5 : contains (.mul (A3_3_10Raw (shape 3 0 5)) (.inv A3_3_10Den)) (A3_3_10Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_3_10Law_check_3_1_4 : contains (.mul (A3_3_10Raw (shape 3 1 4)) (.inv A3_3_10Den)) (A3_3_10Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_3_10Law_check_3_2_3 : contains (.mul (A3_3_10Raw (shape 3 2 3)) (.inv A3_3_10Den)) (A3_3_10Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_3_10Law_check_3_3_2 : contains (.mul (A3_3_10Raw (shape 3 3 2)) (.inv A3_3_10Den)) (A3_3_10Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_3_10Law_check (u : Shape) (hu : u ∈ below (shape 3 3 10)) :
    contains (.mul (A3_3_10Raw u) (.inv A3_3_10Den)) (A3_3_10Table u) = true := by
  rw [A3_3_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_3_10Law_check_0_0_8
  · exact A3_3_10Law_check_0_1_7
  · exact A3_3_10Law_check_0_2_6
  · exact A3_3_10Law_check_0_3_5
  · exact A3_3_10Law_check_1_0_7
  · exact A3_3_10Law_check_1_1_6
  · exact A3_3_10Law_check_1_2_5
  · exact A3_3_10Law_check_1_3_4
  · exact A3_3_10Law_check_2_0_6
  · exact A3_3_10Law_check_2_1_5
  · exact A3_3_10Law_check_2_2_4
  · exact A3_3_10Law_check_2_3_3
  · exact A3_3_10Law_check_3_0_5
  · exact A3_3_10Law_check_3_1_4
  · exact A3_3_10Law_check_3_2_3
  · exact A3_3_10Law_check_3_3_2
lemma A3_3_10Law_sound (u : Shape) :
    (A3_3_10Law u).Encloses (stageALaw (shape 3 3 10) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 3 10)
  · have h := contains_sound (Ball.mul_sound (A3_3_10Raw_sound u hu)
      (Ball.inv_sound A3_3_10Den_sound A3_3_10Den_positive)) (A3_3_10Law_check u hu)
    simpa only [A3_3_10Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_3_10Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
