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
lemma A2_4_10_below : below (shape 2 4 10) = [
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
  (shape 2 4 2)] := by decide +kernel
def A2_4_10Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(446772032626590449174459001 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(906397801707561174643203706603 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(6854684406764661394145666352671 / 20000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(46468291928546345537530836954281 / 100000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(3890053868306385356771126651001 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(221391162680060686462957026073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(7981096634328140896953939436857 / 25000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨1, 0⟩
  | 1, 3, 4 => ⟨(7981096634328140896953939436857 / 25000000000000000000000000000000), (81 / 100000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(221391162680060686462957026073 / 25000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(3890053868306385356771126651001 / 50000000000000000000000000000000), (31 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(46468291928546345537530836954281 / 100000000000000000000000000000000), (59 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(6854684406764661394145666352671 / 20000000000000000000000000000000), (89 / 100000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(906397801707561174643203706603 / 50000000000000000000000000000000), (1 / 12500000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(446772032626590449174459001 / 5000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A2_4_10Raw_0_0_8 : (A2_4_10Raw (shape 0 0 8)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 0 0 8) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 0 0 8)
    (-3477) (-14828) (-74924) w183 w114 w11
    (by decide +kernel) w183_sound w114_sound w11_sound) (by decide +kernel)
lemma A2_4_10Raw_0_1_7 : (A2_4_10Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 0 1 7)
    (-3477) (-4187) (-32439) w183 w178 w62
    (by decide +kernel) w183_sound w178_sound w62_sound) (by decide +kernel)
lemma A2_4_10Raw_0_2_6 : (A2_4_10Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 0 2 6)
    (-3477) (0) (-7231) w183 w195 w146
    (by decide +kernel) w183_sound w195_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_0_3_5 : (A2_4_10Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 0 3 5)
    (-3477) (-4187) (0) w183 w178 w195
    (by decide +kernel) w183_sound w178_sound w195_sound) (by decide +kernel)
lemma A2_4_10Raw_0_4_4 : (A2_4_10Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 0 4 4)
    (-3477) (-14828) (-7231) w183 w114 w146
    (by decide +kernel) w183_sound w114_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_1_0_7 : (A2_4_10Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 1 0 7)
    (0) (-14828) (-32439) w195 w114 w62
    (by decide +kernel) w195_sound w114_sound w62_sound) (by decide +kernel)
lemma A2_4_10Raw_1_1_6 : (A2_4_10Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 1 1 6)
    (0) (-4187) (-7231) w195 w178 w146
    (by decide +kernel) w195_sound w178_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_1_2_5 : (A2_4_10Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 1 2 5)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A2_4_10Raw_1_3_4 : (A2_4_10Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 1 3 4)
    (0) (-4187) (-7231) w195 w178 w146
    (by decide +kernel) w195_sound w178_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_1_4_3 : (A2_4_10Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 1 4 3)
    (0) (-14828) (-32439) w195 w114 w62
    (by decide +kernel) w195_sound w114_sound w62_sound) (by decide +kernel)
lemma A2_4_10Raw_2_0_6 : (A2_4_10Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 2 0 6)
    (-3477) (-14828) (-7231) w183 w114 w146
    (by decide +kernel) w183_sound w114_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_2_1_5 : (A2_4_10Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 2 1 5)
    (-3477) (-4187) (0) w183 w178 w195
    (by decide +kernel) w183_sound w178_sound w195_sound) (by decide +kernel)
lemma A2_4_10Raw_2_2_4 : (A2_4_10Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 2 2 4)
    (-3477) (0) (-7231) w183 w195 w146
    (by decide +kernel) w183_sound w195_sound w146_sound) (by decide +kernel)
lemma A2_4_10Raw_2_3_3 : (A2_4_10Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 2 3 3)
    (-3477) (-4187) (-32439) w183 w178 w62
    (by decide +kernel) w183_sound w178_sound w62_sound) (by decide +kernel)
lemma A2_4_10Raw_2_4_2 : (A2_4_10Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 2 4 10) (shape 2 4 2)
    (-3477) (-14828) (-74924) w183 w114 w11
    (by decide +kernel) w183_sound w114_sound w11_sound) (by decide +kernel)
lemma A2_4_10Raw_sound (u : Shape) (hu : u ∈ below (shape 2 4 10)) :
    (A2_4_10Raw u).Encloses (splitWeight positiveInitial tableP (shape 2 4 10) u : ℝ) := by
  rw [A2_4_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_4_10Raw_0_0_8
  · exact A2_4_10Raw_0_1_7
  · exact A2_4_10Raw_0_2_6
  · exact A2_4_10Raw_0_3_5
  · exact A2_4_10Raw_0_4_4
  · exact A2_4_10Raw_1_0_7
  · exact A2_4_10Raw_1_1_6
  · exact A2_4_10Raw_1_2_5
  · exact A2_4_10Raw_1_3_4
  · exact A2_4_10Raw_1_4_3
  · exact A2_4_10Raw_2_0_6
  · exact A2_4_10Raw_2_1_5
  · exact A2_4_10Raw_2_2_4
  · exact A2_4_10Raw_2_3_3
  · exact A2_4_10Raw_2_4_2
def A2_4_10Den : Ball := ⟨(21644187991385360464217363058073 / 6250000000000000000000000000000), (331 / 50000000000000000000000000000000)⟩
lemma A2_4_10Den_sound : A2_4_10Den.Encloses (((below (shape 2 4 10)).map (splitWeight positiveInitial tableP (shape 2 4 10))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 2 4 10)) A2_4_10Raw (splitWeight positiveInitial tableP (shape 2 4 10)) A2_4_10Raw_sound) (by decide +kernel)
lemma A2_4_10Den_positive : 0 < A2_4_10Den.lower := by decide +kernel
def A2_4_10Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 8 => ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 7 => ⟨(52346489163067591327869821847 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(1237103973342943767145037824953 / 12500000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(3354559023755106067899108779113 / 25000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(2246592636008493490381620329021 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(63929160442568044753234425373 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(288078801942145166747625960087 / 3125000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(14438056078813335419022981654143 / 50000000000000000000000000000000), (7 / 12500000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(288078801942145166747625960087 / 3125000000000000000000000000000), (21 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(63929160442568044753234425373 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2246592636008493490381620329021 / 100000000000000000000000000000000), (7 / 50000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(3354559023755106067899108779113 / 25000000000000000000000000000000), (3 / 5000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(1237103973342943767145037824953 / 12500000000000000000000000000000), (9 / 20000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(52346489163067591327869821847 / 10000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(1290103932301626811496829007 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A2_4_10Law (u : Shape) : Ball := if u ∈ below (shape 2 4 10) then A2_4_10Table u else .exact 0
lemma A2_4_10Law_check_0_0_8 : contains (.mul (A2_4_10Raw (shape 0 0 8)) (.inv A2_4_10Den)) (A2_4_10Table (shape 0 0 8)) = true := by decide +kernel
lemma A2_4_10Law_check_0_1_7 : contains (.mul (A2_4_10Raw (shape 0 1 7)) (.inv A2_4_10Den)) (A2_4_10Table (shape 0 1 7)) = true := by decide +kernel
lemma A2_4_10Law_check_0_2_6 : contains (.mul (A2_4_10Raw (shape 0 2 6)) (.inv A2_4_10Den)) (A2_4_10Table (shape 0 2 6)) = true := by decide +kernel
lemma A2_4_10Law_check_0_3_5 : contains (.mul (A2_4_10Raw (shape 0 3 5)) (.inv A2_4_10Den)) (A2_4_10Table (shape 0 3 5)) = true := by decide +kernel
lemma A2_4_10Law_check_0_4_4 : contains (.mul (A2_4_10Raw (shape 0 4 4)) (.inv A2_4_10Den)) (A2_4_10Table (shape 0 4 4)) = true := by decide +kernel
lemma A2_4_10Law_check_1_0_7 : contains (.mul (A2_4_10Raw (shape 1 0 7)) (.inv A2_4_10Den)) (A2_4_10Table (shape 1 0 7)) = true := by decide +kernel
lemma A2_4_10Law_check_1_1_6 : contains (.mul (A2_4_10Raw (shape 1 1 6)) (.inv A2_4_10Den)) (A2_4_10Table (shape 1 1 6)) = true := by decide +kernel
lemma A2_4_10Law_check_1_2_5 : contains (.mul (A2_4_10Raw (shape 1 2 5)) (.inv A2_4_10Den)) (A2_4_10Table (shape 1 2 5)) = true := by decide +kernel
lemma A2_4_10Law_check_1_3_4 : contains (.mul (A2_4_10Raw (shape 1 3 4)) (.inv A2_4_10Den)) (A2_4_10Table (shape 1 3 4)) = true := by decide +kernel
lemma A2_4_10Law_check_1_4_3 : contains (.mul (A2_4_10Raw (shape 1 4 3)) (.inv A2_4_10Den)) (A2_4_10Table (shape 1 4 3)) = true := by decide +kernel
lemma A2_4_10Law_check_2_0_6 : contains (.mul (A2_4_10Raw (shape 2 0 6)) (.inv A2_4_10Den)) (A2_4_10Table (shape 2 0 6)) = true := by decide +kernel
lemma A2_4_10Law_check_2_1_5 : contains (.mul (A2_4_10Raw (shape 2 1 5)) (.inv A2_4_10Den)) (A2_4_10Table (shape 2 1 5)) = true := by decide +kernel
lemma A2_4_10Law_check_2_2_4 : contains (.mul (A2_4_10Raw (shape 2 2 4)) (.inv A2_4_10Den)) (A2_4_10Table (shape 2 2 4)) = true := by decide +kernel
lemma A2_4_10Law_check_2_3_3 : contains (.mul (A2_4_10Raw (shape 2 3 3)) (.inv A2_4_10Den)) (A2_4_10Table (shape 2 3 3)) = true := by decide +kernel
lemma A2_4_10Law_check_2_4_2 : contains (.mul (A2_4_10Raw (shape 2 4 2)) (.inv A2_4_10Den)) (A2_4_10Table (shape 2 4 2)) = true := by decide +kernel
lemma A2_4_10Law_check (u : Shape) (hu : u ∈ below (shape 2 4 10)) :
    contains (.mul (A2_4_10Raw u) (.inv A2_4_10Den)) (A2_4_10Table u) = true := by
  rw [A2_4_10_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A2_4_10Law_check_0_0_8
  · exact A2_4_10Law_check_0_1_7
  · exact A2_4_10Law_check_0_2_6
  · exact A2_4_10Law_check_0_3_5
  · exact A2_4_10Law_check_0_4_4
  · exact A2_4_10Law_check_1_0_7
  · exact A2_4_10Law_check_1_1_6
  · exact A2_4_10Law_check_1_2_5
  · exact A2_4_10Law_check_1_3_4
  · exact A2_4_10Law_check_1_4_3
  · exact A2_4_10Law_check_2_0_6
  · exact A2_4_10Law_check_2_1_5
  · exact A2_4_10Law_check_2_2_4
  · exact A2_4_10Law_check_2_3_3
  · exact A2_4_10Law_check_2_4_2
lemma A2_4_10Law_sound (u : Shape) :
    (A2_4_10Law u).Encloses (stageALaw (shape 2 4 10) u : ℝ) := by
  by_cases hu : u ∈ below (shape 2 4 10)
  · have h := contains_sound (Ball.mul_sound (A2_4_10Raw_sound u hu)
      (Ball.inv_sound A2_4_10Den_sound A2_4_10Den_positive)) (A2_4_10Law_check u hu)
    simpa only [A2_4_10Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A2_4_10Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
