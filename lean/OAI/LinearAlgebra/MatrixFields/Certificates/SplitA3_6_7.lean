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
lemma A3_6_7_below : below (shape 3 6 7) = [
  (shape 0 1 7),
  (shape 0 2 6),
  (shape 0 3 5),
  (shape 0 4 4),
  (shape 0 5 3),
  (shape 0 6 2),
  (shape 1 0 7),
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
  (shape 3 5 0)] := by decide +kernel
def A3_6_7Raw (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(947695798775862187054385307 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(102230605927328755004795179633 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(2485504917108313710539576690779 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(425575504693914482232192681717 / 1562500000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(500087920163149423759661626633 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(14645470457248380324013395549 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(279158785601762653275431827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(63426279861227231827349959449 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(3019453409783584311945978178983 / 25000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨1, 0⟩
  | 1, 4, 3 => ⟨(11504431092583276771638604143613 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(221757384863796084201755173273 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(2211632883128668798193442523 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2211632883128668798193442523 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(221757384863796084201755173273 / 12500000000000000000000000000000), (3 / 50000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(11504431092583276771638604143613 / 20000000000000000000000000000000), (37 / 50000000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨1, 0⟩
  | 2, 4, 2 => ⟨(3019453409783584311945978178983 / 25000000000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(63426279861227231827349959449 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(279158785601762653275431827 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(14645470457248380324013395549 / 25000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(500087920163149423759661626633 / 12500000000000000000000000000000), (3 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(425575504693914482232192681717 / 1562500000000000000000000000000), (71 / 100000000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(2485504917108313710539576690779 / 25000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(102230605927328755004795179633 / 25000000000000000000000000000000), (1 / 50000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(947695798775862187054385307 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
lemma A3_6_7Raw_0_1_7 : (A3_6_7Raw (shape 0 1 7)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 1 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 1 7)
    (-7476) (-24711) (-76548) w143 w81 w10
    (by decide +kernel) w143_sound w81_sound w10_sound) (by decide +kernel)
lemma A3_6_7Raw_0_2_6 : (A3_6_7Raw (shape 0 2 6)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 2 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 2 6)
    (-7476) (-5530) (-41988) w143 w169 w42
    (by decide +kernel) w143_sound w169_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_0_3_5 : (A3_6_7Raw (shape 0 3 5)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 3 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 3 5)
    (-7476) (0) (-15608) w143 w195 w111
    (by decide +kernel) w143_sound w195_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_0_4_4 : (A3_6_7Raw (shape 0 4 4)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 4 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 4 4)
    (-7476) (-5530) (0) w143 w169 w195
    (by decide +kernel) w143_sound w169_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_0_5_3 : (A3_6_7Raw (shape 0 5 3)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 5 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 5 3)
    (-7476) (-24711) (0) w143 w81 w195
    (by decide +kernel) w143_sound w81_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_0_6_2 : (A3_6_7Raw (shape 0 6 2)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 0 6 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 0 6 2)
    (-7476) (-51341) (-15608) w143 w35 w111
    (by decide +kernel) w143_sound w35_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_1_0_7 : (A3_6_7Raw (shape 1 0 7)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 0 7) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 0 7)
    (0) (-51341) (-76548) w195 w35 w10
    (by decide +kernel) w195_sound w35_sound w10_sound) (by decide +kernel)
lemma A3_6_7Raw_1_1_6 : (A3_6_7Raw (shape 1 1 6)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 1 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 1 6)
    (0) (-24711) (-41988) w195 w81 w42
    (by decide +kernel) w195_sound w81_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_1_2_5 : (A3_6_7Raw (shape 1 2 5)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 2 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 2 5)
    (0) (-5530) (-15608) w195 w169 w111
    (by decide +kernel) w195_sound w169_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_1_3_4 : (A3_6_7Raw (shape 1 3 4)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 3 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 3 4)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_1_4_3 : (A3_6_7Raw (shape 1 4 3)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 4 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 4 3)
    (0) (-5530) (0) w195 w169 w195
    (by decide +kernel) w195_sound w169_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_1_5_2 : (A3_6_7Raw (shape 1 5 2)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 5 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 5 2)
    (0) (-24711) (-15608) w195 w81 w111
    (by decide +kernel) w195_sound w81_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_1_6_1 : (A3_6_7Raw (shape 1 6 1)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 1 6 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 1 6 1)
    (0) (-51341) (-41988) w195 w35 w42
    (by decide +kernel) w195_sound w35_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_2_0_6 : (A3_6_7Raw (shape 2 0 6)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 0 6) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 0 6)
    (0) (-51341) (-41988) w195 w35 w42
    (by decide +kernel) w195_sound w35_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_2_1_5 : (A3_6_7Raw (shape 2 1 5)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 1 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 1 5)
    (0) (-24711) (-15608) w195 w81 w111
    (by decide +kernel) w195_sound w81_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_2_2_4 : (A3_6_7Raw (shape 2 2 4)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 2 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 2 4)
    (0) (-5530) (0) w195 w169 w195
    (by decide +kernel) w195_sound w169_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_2_3_3 : (A3_6_7Raw (shape 2 3 3)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 3 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 3 3)
    (0) (0) (0) w195 w195 w195
    (by decide +kernel) w195_sound w195_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_2_4_2 : (A3_6_7Raw (shape 2 4 2)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 4 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 4 2)
    (0) (-5530) (-15608) w195 w169 w111
    (by decide +kernel) w195_sound w169_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_2_5_1 : (A3_6_7Raw (shape 2 5 1)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 5 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 5 1)
    (0) (-24711) (-41988) w195 w81 w42
    (by decide +kernel) w195_sound w81_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_2_6_0 : (A3_6_7Raw (shape 2 6 0)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 2 6 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 2 6 0)
    (0) (-51341) (-76548) w195 w35 w10
    (by decide +kernel) w195_sound w35_sound w10_sound) (by decide +kernel)
lemma A3_6_7Raw_3_0_5 : (A3_6_7Raw (shape 3 0 5)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 0 5) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 0 5)
    (-7476) (-51341) (-15608) w143 w35 w111
    (by decide +kernel) w143_sound w35_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_3_1_4 : (A3_6_7Raw (shape 3 1 4)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 1 4) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 1 4)
    (-7476) (-24711) (0) w143 w81 w195
    (by decide +kernel) w143_sound w81_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_3_2_3 : (A3_6_7Raw (shape 3 2 3)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 2 3) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 2 3)
    (-7476) (-5530) (0) w143 w169 w195
    (by decide +kernel) w143_sound w169_sound w195_sound) (by decide +kernel)
lemma A3_6_7Raw_3_3_2 : (A3_6_7Raw (shape 3 3 2)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 3 2) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 3 2)
    (-7476) (0) (-15608) w143 w195 w111
    (by decide +kernel) w143_sound w195_sound w111_sound) (by decide +kernel)
lemma A3_6_7Raw_3_4_1 : (A3_6_7Raw (shape 3 4 1)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 4 1) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 4 1)
    (-7476) (-5530) (-41988) w143 w169 w42
    (by decide +kernel) w143_sound w169_sound w42_sound) (by decide +kernel)
lemma A3_6_7Raw_3_5_0 : (A3_6_7Raw (shape 3 5 0)).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) (shape 3 5 0) : ℝ) := by
  exact contains_sound (splitWeight_three_enclosed positiveInitial tableP (shape 3 6 7) (shape 3 5 0)
    (-7476) (-24711) (-76548) w143 w81 w10
    (by decide +kernel) w143_sound w81_sound w10_sound) (by decide +kernel)
lemma A3_6_7Raw_sound (u : Shape) (hu : u ∈ below (shape 3 6 7)) :
    (A3_6_7Raw u).Encloses (splitWeight positiveInitial tableP (shape 3 6 7) u : ℝ) := by
  rw [A3_6_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_6_7Raw_0_1_7
  · exact A3_6_7Raw_0_2_6
  · exact A3_6_7Raw_0_3_5
  · exact A3_6_7Raw_0_4_4
  · exact A3_6_7Raw_0_5_3
  · exact A3_6_7Raw_0_6_2
  · exact A3_6_7Raw_1_0_7
  · exact A3_6_7Raw_1_1_6
  · exact A3_6_7Raw_1_2_5
  · exact A3_6_7Raw_1_3_4
  · exact A3_6_7Raw_1_4_3
  · exact A3_6_7Raw_1_5_2
  · exact A3_6_7Raw_1_6_1
  · exact A3_6_7Raw_2_0_6
  · exact A3_6_7Raw_2_1_5
  · exact A3_6_7Raw_2_2_4
  · exact A3_6_7Raw_2_3_3
  · exact A3_6_7Raw_2_4_2
  · exact A3_6_7Raw_2_5_1
  · exact A3_6_7Raw_2_6_0
  · exact A3_6_7Raw_3_0_5
  · exact A3_6_7Raw_3_1_4
  · exact A3_6_7Raw_3_2_3
  · exact A3_6_7Raw_3_3_2
  · exact A3_6_7Raw_3_4_1
  · exact A3_6_7Raw_3_5_0
def A3_6_7Den : Ball := ⟨(26644870182285812255234624802301 / 6250000000000000000000000000000), (57 / 12500000000000000000000000000000)⟩
lemma A3_6_7Den_sound : A3_6_7Den.Encloses (((below (shape 3 6 7)).map (splitWeight positiveInitial tableP (shape 3 6 7))).sum : ℝ) := by
  exact contains_sound (list_cast_enclosed (below (shape 3 6 7)) A3_6_7Raw (splitWeight positiveInitial tableP (shape 3 6 7)) A3_6_7Raw_sound) (by decide +kernel)
lemma A3_6_7Den_positive : 0 < A3_6_7Den.lower := by decide +kernel
def A3_6_7Table (s : Shape) : Ball :=
  match s 0, s 1, s 2 with
  | 0, 1, 7 => ⟨(444595804132456643872751423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 2, 6 => ⟨(95919594679892889239193974057 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 0, 3, 5 => ⟨(466413403425162984942828299979 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 0, 4, 4 => ⟨(159721365419467461928662332981 / 2500000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 0, 5, 3 => ⟨(938431894660947905675404500739 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 0, 6, 2 => ⟨(6870680152058435330563692671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 0, 7 => ⟨(32740681378342119614199523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 1, 6 => ⟨(29755389793283097286725257379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 1, 2, 5 => ⟨(177065826198824108960514164357 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 1, 3, 4 => ⟨(23456672737535644093331931145797 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 1, 4, 3 => ⟨(52706186556690537444005286707 / 390625000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 1, 5, 2 => ⟨(416135232310544407998215611629 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 1, 6, 1 => ⟨(2075101950204864030086128749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 0, 6 => ⟨(2075101950204864030086128749 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 1, 5 => ⟨(416135232310544407998215611629 / 100000000000000000000000000000000), (3 / 100000000000000000000000000000000)⟩
  | 2, 2, 4 => ⟨(52706186556690537444005286707 / 390625000000000000000000000000), (1 / 3125000000000000000000000000000)⟩
  | 2, 3, 3 => ⟨(23456672737535644093331931145797 / 100000000000000000000000000000000), (13 / 50000000000000000000000000000000)⟩
  | 2, 4, 2 => ⟨(177065826198824108960514164357 / 6250000000000000000000000000000), (11 / 100000000000000000000000000000000)⟩
  | 2, 5, 1 => ⟨(29755389793283097286725257379 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 2, 6, 0 => ⟨(32740681378342119614199523 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 0, 5 => ⟨(6870680152058435330563692671 / 50000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 1, 4 => ⟨(938431894660947905675404500739 / 100000000000000000000000000000000), (1 / 25000000000000000000000000000000)⟩
  | 3, 2, 3 => ⟨(159721365419467461928662332981 / 2500000000000000000000000000000), (3 / 12500000000000000000000000000000)⟩
  | 3, 3, 2 => ⟨(466413403425162984942828299979 / 20000000000000000000000000000000), (9 / 100000000000000000000000000000000)⟩
  | 3, 4, 1 => ⟨(95919594679892889239193974057 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | 3, 5, 0 => ⟨(444595804132456643872751423 / 100000000000000000000000000000000), (1 / 100000000000000000000000000000000)⟩
  | _, _, _ => (.exact 0)
def A3_6_7Law (u : Shape) : Ball := if u ∈ below (shape 3 6 7) then A3_6_7Table u else .exact 0
lemma A3_6_7Law_check_0_1_7 : contains (.mul (A3_6_7Raw (shape 0 1 7)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 1 7)) = true := by decide +kernel
lemma A3_6_7Law_check_0_2_6 : contains (.mul (A3_6_7Raw (shape 0 2 6)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 2 6)) = true := by decide +kernel
lemma A3_6_7Law_check_0_3_5 : contains (.mul (A3_6_7Raw (shape 0 3 5)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 3 5)) = true := by decide +kernel
lemma A3_6_7Law_check_0_4_4 : contains (.mul (A3_6_7Raw (shape 0 4 4)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 4 4)) = true := by decide +kernel
lemma A3_6_7Law_check_0_5_3 : contains (.mul (A3_6_7Raw (shape 0 5 3)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 5 3)) = true := by decide +kernel
lemma A3_6_7Law_check_0_6_2 : contains (.mul (A3_6_7Raw (shape 0 6 2)) (.inv A3_6_7Den)) (A3_6_7Table (shape 0 6 2)) = true := by decide +kernel
lemma A3_6_7Law_check_1_0_7 : contains (.mul (A3_6_7Raw (shape 1 0 7)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 0 7)) = true := by decide +kernel
lemma A3_6_7Law_check_1_1_6 : contains (.mul (A3_6_7Raw (shape 1 1 6)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 1 6)) = true := by decide +kernel
lemma A3_6_7Law_check_1_2_5 : contains (.mul (A3_6_7Raw (shape 1 2 5)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 2 5)) = true := by decide +kernel
lemma A3_6_7Law_check_1_3_4 : contains (.mul (A3_6_7Raw (shape 1 3 4)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 3 4)) = true := by decide +kernel
lemma A3_6_7Law_check_1_4_3 : contains (.mul (A3_6_7Raw (shape 1 4 3)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 4 3)) = true := by decide +kernel
lemma A3_6_7Law_check_1_5_2 : contains (.mul (A3_6_7Raw (shape 1 5 2)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 5 2)) = true := by decide +kernel
lemma A3_6_7Law_check_1_6_1 : contains (.mul (A3_6_7Raw (shape 1 6 1)) (.inv A3_6_7Den)) (A3_6_7Table (shape 1 6 1)) = true := by decide +kernel
lemma A3_6_7Law_check_2_0_6 : contains (.mul (A3_6_7Raw (shape 2 0 6)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 0 6)) = true := by decide +kernel
lemma A3_6_7Law_check_2_1_5 : contains (.mul (A3_6_7Raw (shape 2 1 5)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 1 5)) = true := by decide +kernel
lemma A3_6_7Law_check_2_2_4 : contains (.mul (A3_6_7Raw (shape 2 2 4)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 2 4)) = true := by decide +kernel
lemma A3_6_7Law_check_2_3_3 : contains (.mul (A3_6_7Raw (shape 2 3 3)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 3 3)) = true := by decide +kernel
lemma A3_6_7Law_check_2_4_2 : contains (.mul (A3_6_7Raw (shape 2 4 2)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 4 2)) = true := by decide +kernel
lemma A3_6_7Law_check_2_5_1 : contains (.mul (A3_6_7Raw (shape 2 5 1)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 5 1)) = true := by decide +kernel
lemma A3_6_7Law_check_2_6_0 : contains (.mul (A3_6_7Raw (shape 2 6 0)) (.inv A3_6_7Den)) (A3_6_7Table (shape 2 6 0)) = true := by decide +kernel
lemma A3_6_7Law_check_3_0_5 : contains (.mul (A3_6_7Raw (shape 3 0 5)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 0 5)) = true := by decide +kernel
lemma A3_6_7Law_check_3_1_4 : contains (.mul (A3_6_7Raw (shape 3 1 4)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 1 4)) = true := by decide +kernel
lemma A3_6_7Law_check_3_2_3 : contains (.mul (A3_6_7Raw (shape 3 2 3)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 2 3)) = true := by decide +kernel
lemma A3_6_7Law_check_3_3_2 : contains (.mul (A3_6_7Raw (shape 3 3 2)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 3 2)) = true := by decide +kernel
lemma A3_6_7Law_check_3_4_1 : contains (.mul (A3_6_7Raw (shape 3 4 1)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 4 1)) = true := by decide +kernel
lemma A3_6_7Law_check_3_5_0 : contains (.mul (A3_6_7Raw (shape 3 5 0)) (.inv A3_6_7Den)) (A3_6_7Table (shape 3 5 0)) = true := by decide +kernel
lemma A3_6_7Law_check (u : Shape) (hu : u ∈ below (shape 3 6 7)) :
    contains (.mul (A3_6_7Raw u) (.inv A3_6_7Den)) (A3_6_7Table u) = true := by
  rw [A3_6_7_below] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact A3_6_7Law_check_0_1_7
  · exact A3_6_7Law_check_0_2_6
  · exact A3_6_7Law_check_0_3_5
  · exact A3_6_7Law_check_0_4_4
  · exact A3_6_7Law_check_0_5_3
  · exact A3_6_7Law_check_0_6_2
  · exact A3_6_7Law_check_1_0_7
  · exact A3_6_7Law_check_1_1_6
  · exact A3_6_7Law_check_1_2_5
  · exact A3_6_7Law_check_1_3_4
  · exact A3_6_7Law_check_1_4_3
  · exact A3_6_7Law_check_1_5_2
  · exact A3_6_7Law_check_1_6_1
  · exact A3_6_7Law_check_2_0_6
  · exact A3_6_7Law_check_2_1_5
  · exact A3_6_7Law_check_2_2_4
  · exact A3_6_7Law_check_2_3_3
  · exact A3_6_7Law_check_2_4_2
  · exact A3_6_7Law_check_2_5_1
  · exact A3_6_7Law_check_2_6_0
  · exact A3_6_7Law_check_3_0_5
  · exact A3_6_7Law_check_3_1_4
  · exact A3_6_7Law_check_3_2_3
  · exact A3_6_7Law_check_3_3_2
  · exact A3_6_7Law_check_3_4_1
  · exact A3_6_7Law_check_3_5_0
lemma A3_6_7Law_sound (u : Shape) :
    (A3_6_7Law u).Encloses (stageALaw (shape 3 6 7) u : ℝ) := by
  by_cases hu : u ∈ below (shape 3 6 7)
  · have h := contains_sound (Ball.mul_sound (A3_6_7Raw_sound u hu)
      (Ball.inv_sound A3_6_7Den_sound A3_6_7Den_positive)) (A3_6_7Law_check u hu)
    simpa only [A3_6_7Law, hu, ite_true, stageALaw, splitLaw,
      Rat.cast_div, Rat.cast_mul, Rat.cast_inv, div_eq_mul_inv] using h
  · simp only [A3_6_7Law, hu, ite_false, stageALaw, splitLaw, Rat.cast_zero]
    simpa only [Rat.cast_zero] using Ball.exact_sound 0

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
