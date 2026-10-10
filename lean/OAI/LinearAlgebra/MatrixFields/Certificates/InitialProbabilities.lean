import Mathlib
import OAI.LinearAlgebra.MatrixFields.Certificates.SparseContraction

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

noncomputable section
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate
open scoped BigOperators
lemma sortedInitial_list : sortedInitial = [
  (shape 0 0 16),
  (shape 0 1 15),
  (shape 0 2 14),
  (shape 0 3 13),
  (shape 0 4 12),
  (shape 0 5 11),
  (shape 0 6 10),
  (shape 0 7 9),
  (shape 0 8 8),
  (shape 1 1 14),
  (shape 1 2 13),
  (shape 1 3 12),
  (shape 1 4 11),
  (shape 1 5 10),
  (shape 1 6 9),
  (shape 1 7 8),
  (shape 2 2 12),
  (shape 2 3 11),
  (shape 2 4 10),
  (shape 2 5 9),
  (shape 2 6 8),
  (shape 2 7 7),
  (shape 3 3 10),
  (shape 3 4 9),
  (shape 3 5 8),
  (shape 3 6 7),
  (shape 4 4 8),
  (shape 4 5 7),
  (shape 4 6 6),
  (shape 5 5 6)] := by decide +kernel
lemma positiveInitial_list : positiveInitial = [
  (shape 1 1 14),
  (shape 1 2 13),
  (shape 1 3 12),
  (shape 1 4 11),
  (shape 1 5 10),
  (shape 1 6 9),
  (shape 1 7 8),
  (shape 2 2 12),
  (shape 2 3 11),
  (shape 2 4 10),
  (shape 2 5 9),
  (shape 2 6 8),
  (shape 2 7 7),
  (shape 3 3 10),
  (shape 3 4 9),
  (shape 3 5 8),
  (shape 3 6 7),
  (shape 4 4 8),
  (shape 4 5 7),
  (shape 4 6 6),
  (shape 5 5 6)] := by decide +kernel
lemma positiveSecond_list : positiveSecond = [
  (shape 1 1 6),
  (shape 1 2 5),
  (shape 1 3 4),
  (shape 1 4 3),
  (shape 1 5 2),
  (shape 1 6 1),
  (shape 2 1 5),
  (shape 2 2 4),
  (shape 2 3 3),
  (shape 2 4 2),
  (shape 2 5 1),
  (shape 3 1 4),
  (shape 3 2 3),
  (shape 3 3 2),
  (shape 3 4 1),
  (shape 4 1 3),
  (shape 4 2 2),
  (shape 4 3 1),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 6 1 1)] := by decide +kernel
lemma zeroSecond_list : zeroSecond = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 0 8 0),
  (shape 1 0 7),
  (shape 1 7 0),
  (shape 2 0 6),
  (shape 2 6 0),
  (shape 3 0 5),
  (shape 3 5 0),
  (shape 4 0 4),
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 3 0),
  (shape 6 0 2),
  (shape 6 2 0),
  (shape 7 0 1),
  (shape 7 1 0),
  (shape 8 0 0)] := by decide +kernel
lemma allSecond_list : shapes 8 = [
  (shape 0 0 8),
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 0 7 1),
  (shape 0 8 0),
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
  (shape 4 4 0),
  (shape 5 0 3),
  (shape 5 1 2),
  (shape 5 2 1),
  (shape 5 3 0),
  (shape 6 0 2),
  (shape 6 1 1),
  (shape 6 2 0),
  (shape 7 0 1),
  (shape 7 1 0),
  (shape 8 0 0)] := by decide +kernel

def initialProbs (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 0, 16 => ⟨(13145890586460581196177 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 1, 15 => ⟨(42540492515727185225981 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 14 => ⟨(4900971162886037110823 / 2000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 13 => ⟨(14604082434529236400348639 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 4, 12 => ⟨(87208931167140990526853381 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 5, 11 => ⟨(566490078566605123939237597 / 12500000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 6, 10 => ⟨(15474579554896208143672879691 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 7, 9 => ⟨(21368287213656684042157621491 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 8, 8 => ⟨(42129637360788428263980836207 / 50000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 1, 14 => ⟨(135599977130724015865781 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 13 => ⟨(21858745833413986207356271 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 3, 12 => ⟨(65898522138499345540285359 / 10000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 4, 11 => ⟨(5367158627758357107638360451 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 5, 10 => ⟨(18883866194706956799381439539 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 1, 6, 9 => ⟨(440207333950294144127188221451 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 1, 7, 8 => ⟨(501647985135804550777153238571 / 50000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 2, 2, 12 => ⟨(445614366045202627519431351 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 3, 11 => ⟨(18322793467082776251620533929 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 4, 10 => ⟨(202076397116939330043327073307 / 100000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 2, 5, 9 => ⟨(60673895984904206933988362677 / 5000000000000000000000000000000), (1 / 10000000000000000000000000000000)⟩
  | 2, 6, 8 => ⟨(1867579803495739369034613847927 / 50000000000000000000000000000000), (7 / 25000000000000000000000000000000)⟩
  | 2, 7, 7 => ⟨(2698627660502582229985779719163 / 100000000000000000000000000000000), (1 / 5000000000000000000000000000000)⟩
  | 3, 3, 10 => ⟨(25504648673098899027157162387 / 20000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 4, 9 => ⟨(1920317525954107858922782450019 / 100000000000000000000000000000000), (3 / 20000000000000000000000000000000)⟩
  | 3, 5, 8 => ⟨(951656630773752719335842630811 / 12500000000000000000000000000000), (27 / 50000000000000000000000000000000)⟩
  | 3, 6, 7 => ⟨(7428644231760528410384248566849 / 50000000000000000000000000000000), (11 / 10000000000000000000000000000000)⟩
  | 4, 4, 8 => ⟨(4772848850473901186247710959367 / 100000000000000000000000000000000), (7 / 20000000000000000000000000000000)⟩
  | 4, 5, 7 => ⟨(23993682114587954796865544628907 / 100000000000000000000000000000000), (43 / 25000000000000000000000000000000)⟩
  | 4, 6, 6 => ⟨(1012633788103277317843835873381 / 6250000000000000000000000000000), (1 / 800000000000000000000000000000)⟩
  | 5, 5, 6 => ⟨(20868552691024433430449278430017 / 100000000000000000000000000000000), (153 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma initialProbs_0_0_16 : (initialProbs (shape 0 0 16)).Encloses (initialLaw (shape 0 0 16) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 0 16) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_1_15 : (initialProbs (shape 0 1 15)).Encloses (initialLaw (shape 0 1 15) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 1 15) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_2_14 : (initialProbs (shape 0 2 14)).Encloses (initialLaw (shape 0 2 14) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 2 14) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_3_13 : (initialProbs (shape 0 3 13)).Encloses (initialLaw (shape 0 3 13) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 3 13) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_4_12 : (initialProbs (shape 0 4 12)).Encloses (initialLaw (shape 0 4 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 4 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_5_11 : (initialProbs (shape 0 5 11)).Encloses (initialLaw (shape 0 5 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 5 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_6_10 : (initialProbs (shape 0 6 10)).Encloses (initialLaw (shape 0 6 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 6 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_7_9 : (initialProbs (shape 0 7 9)).Encloses (initialLaw (shape 0 7 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 7 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_0_8_8 : (initialProbs (shape 0 8 8)).Encloses (initialLaw (shape 0 8 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 0 8 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_1_14 : (initialProbs (shape 1 1 14)).Encloses (initialLaw (shape 1 1 14) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 1 14) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_2_13 : (initialProbs (shape 1 2 13)).Encloses (initialLaw (shape 1 2 13) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 2 13) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_3_12 : (initialProbs (shape 1 3 12)).Encloses (initialLaw (shape 1 3 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 3 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_4_11 : (initialProbs (shape 1 4 11)).Encloses (initialLaw (shape 1 4 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 4 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_5_10 : (initialProbs (shape 1 5 10)).Encloses (initialLaw (shape 1 5 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 5 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_6_9 : (initialProbs (shape 1 6 9)).Encloses (initialLaw (shape 1 6 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 6 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_1_7_8 : (initialProbs (shape 1 7 8)).Encloses (initialLaw (shape 1 7 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 1 7 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_2_12 : (initialProbs (shape 2 2 12)).Encloses (initialLaw (shape 2 2 12) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 2 12) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_3_11 : (initialProbs (shape 2 3 11)).Encloses (initialLaw (shape 2 3 11) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 3 11) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_4_10 : (initialProbs (shape 2 4 10)).Encloses (initialLaw (shape 2 4 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 4 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_5_9 : (initialProbs (shape 2 5 9)).Encloses (initialLaw (shape 2 5 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 5 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_6_8 : (initialProbs (shape 2 6 8)).Encloses (initialLaw (shape 2 6 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 6 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_2_7_7 : (initialProbs (shape 2 7 7)).Encloses (initialLaw (shape 2 7 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 2 7 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_3_10 : (initialProbs (shape 3 3 10)).Encloses (initialLaw (shape 3 3 10) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 3 10) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_4_9 : (initialProbs (shape 3 4 9)).Encloses (initialLaw (shape 3 4 9) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 4 9) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_5_8 : (initialProbs (shape 3 5 8)).Encloses (initialLaw (shape 3 5 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 5 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_3_6_7 : (initialProbs (shape 3 6 7)).Encloses (initialLaw (shape 3 6 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 3 6 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_4_8 : (initialProbs (shape 4 4 8)).Encloses (initialLaw (shape 4 4 8) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 4 8) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_5_7 : (initialProbs (shape 4 5 7)).Encloses (initialLaw (shape 4 5 7) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 5 7) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_4_6_6 : (initialProbs (shape 4 6 6)).Encloses (initialLaw (shape 4 6 6) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 4 6 6) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_5_5_6 : (initialProbs (shape 5 5 6)).Encloses (initialLaw (shape 5 5 6) : ℝ) := by
  exact contains_sound (initialLawBall_sound (shape 5 5 6) (by decide +kernel)) (by decide +kernel)
lemma initialProbs_sound (g : Shape) (hg : g ∈ sortedInitial) :
    (initialProbs g).Encloses (initialLaw g : ℝ) := by
  rw [sortedInitial_list] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact initialProbs_0_0_16
  · exact initialProbs_0_1_15
  · exact initialProbs_0_2_14
  · exact initialProbs_0_3_13
  · exact initialProbs_0_4_12
  · exact initialProbs_0_5_11
  · exact initialProbs_0_6_10
  · exact initialProbs_0_7_9
  · exact initialProbs_0_8_8
  · exact initialProbs_1_1_14
  · exact initialProbs_1_2_13
  · exact initialProbs_1_3_12
  · exact initialProbs_1_4_11
  · exact initialProbs_1_5_10
  · exact initialProbs_1_6_9
  · exact initialProbs_1_7_8
  · exact initialProbs_2_2_12
  · exact initialProbs_2_3_11
  · exact initialProbs_2_4_10
  · exact initialProbs_2_5_9
  · exact initialProbs_2_6_8
  · exact initialProbs_2_7_7
  · exact initialProbs_3_3_10
  · exact initialProbs_3_4_9
  · exact initialProbs_3_5_8
  · exact initialProbs_3_6_7
  · exact initialProbs_4_4_8
  · exact initialProbs_4_5_7
  · exact initialProbs_4_6_6
  · exact initialProbs_5_5_6

end MatrixMultiplication.NativeNumerics

end

end MatrixAllFields

end OAI
