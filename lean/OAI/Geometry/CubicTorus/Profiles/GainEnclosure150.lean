import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures3143To3335

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open CubicTorus.Arithmetic _root_.OAI.ReusedScalar205.CubicTorus.Nesting _root_.OAI.ReusedScalar205.CubicTorus.Shape

lemma gain_enclosure_150 : Encl (gain (3 / 2 : ℝ)) (3192828203 / 1000000000000 : ℝ) (3192828207 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b2939

lemma baseline_enclosure_154 : Encl (linearBaseline (77 / 50 : ℝ)) (-956610909 / 500000000000 : ℝ) (-956610857 / 500000000000 : ℝ) := by
  exact b2988

lemma gain_enclosure_154 : Encl (gain (77 / 50 : ℝ)) (588754601 / 200000000000 : ℝ) (183985813 / 62500000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3022

lemma baseline_enclosure_158 : Encl (linearBaseline (79 / 50 : ℝ)) (-149307897 / 200000000000 : ℝ) (-373269691 / 500000000000 : ℝ) := by
  exact b3071

lemma gain_enclosure_158 : Encl (gain (79 / 50 : ℝ)) (10636567 / 3906250000 : ℝ) (1361480577 / 500000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3105

lemma baseline_enclosure_162 : Encl (linearBaseline (81 / 50 : ℝ)) (878094887 / 1000000000000 : ℝ) (219523747 / 250000000000 : ℝ) := by
  exact b3154

lemma gain_enclosure_162 : Encl (gain (81 / 50 : ℝ)) (505300523 / 200000000000 : ℝ) (2526502617 / 1000000000000 : ℝ) := by
  rw [gain_formula (by constructor <;> norm_num)]
  exact b3188

lemma baseline_enclosure_170 : Encl (linearBaseline (17 / 10 : ℝ)) (5379096533 / 1000000000000 : ℝ) (5379096629 / 1000000000000 : ℝ) := by
  exact b3237

lemma baseline_enclosure_190 : Encl (linearBaseline (19 / 10 : ℝ)) (22763388121 / 1000000000000 : ℝ) (22763388207 / 1000000000000 : ℝ) := by
  exact b3286

lemma baseline_enclosure_225 : Encl (linearBaseline (9 / 4 : ℝ)) (342738213 / 5000000000 : ℝ) (4284227667 / 62500000000 : ℝ) := by
  exact b3335

lemma baseline_lower_64 : (6874889409 / 500000000000 : ℝ) ≤ baseline (16 / 25 : ℝ) :=
  (baseline_enclosure_64).1.trans (twoChordBaseline_le_of_range (h := (16 / 25 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_74 : (383669089 / 40000000000 : ℝ) ≤ baseline (37 / 50 : ℝ) :=
  (baseline_enclosure_74).1.trans (twoChordBaseline_le_of_range (h := (37 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_84 : (146341961 / 25000000000 : ℝ) ≤ baseline (21 / 25 : ℝ) :=
  (baseline_enclosure_84).1.trans (twoChordBaseline_le_of_range (h := (21 / 25 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_92 : (334736981 / 100000000000 : ℝ) ≤ baseline (23 / 25 : ℝ) :=
  (baseline_enclosure_92).1.trans (twoChordBaseline_le_of_range (h := (23 / 25 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_98 : (1797263411 / 1000000000000 : ℝ) ≤ baseline (49 / 50 : ℝ) :=
  (baseline_enclosure_98).1.trans (twoChordBaseline_le_of_range (h := (49 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma baseline_lower_102 : (926954813 / 1000000000000 : ℝ) ≤ baseline (51 / 50 : ℝ) :=
  (baseline_enclosure_102).1.trans (twoChordBaseline_le_of_range (h := (51 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_102 : (1696987851 / 1000000000000 : ℝ) ≤ baseline (51 / 50 : ℝ) + gain (51 / 50 : ℝ) := by
  have hb := baseline_lower_102
  have hg := (gain_enclosure_102).1
  linarith

lemma baseline_lower_106 : (727511 / 3906250000 : ℝ) ≤ baseline (53 / 50 : ℝ) :=
  (baseline_enclosure_106).1.trans (twoChordBaseline_le_of_range (h := (53 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_106 : (588471367 / 500000000000 : ℝ) ≤ baseline (53 / 50 : ℝ) + gain (53 / 50 : ℝ) := by
  have hb := baseline_lower_106
  have hg := (gain_enclosure_106).1
  linarith

lemma baseline_lower_110 : (-107195367 / 250000000000 : ℝ) ≤ baseline (11 / 10 : ℝ) :=
  (baseline_enclosure_110).1.trans (twoChordBaseline_le_of_range (h := (11 / 10 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_110 : (813603931 / 1000000000000 : ℝ) ≤ baseline (11 / 10 : ℝ) + gain (11 / 10 : ℝ) := by
  have hb := baseline_lower_110
  have hg := (gain_enclosure_110).1
  linarith

lemma baseline_lower_114 : (-924869053 / 1000000000000 : ℝ) ≤ baseline (57 / 50 : ℝ) :=
  (baseline_enclosure_114).1.trans (twoChordBaseline_le_of_range (h := (57 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_114 : (598682283 / 1000000000000 : ℝ) ≤ baseline (57 / 50 : ℝ) + gain (57 / 50 : ℝ) := by
  have hb := baseline_lower_114
  have hg := (gain_enclosure_114).1
  linarith

lemma baseline_lower_118 : (-131180011 / 100000000000 : ℝ) ≤ baseline (59 / 50 : ℝ) :=
  (baseline_enclosure_118).1.trans (twoChordBaseline_le_of_range (h := (59 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_118 : (65023907 / 125000000000 : ℝ) ≤ baseline (59 / 50 : ℝ) + gain (59 / 50 : ℝ) := by
  have hb := baseline_lower_118
  have hg := (gain_enclosure_118).1
  linarith

lemma baseline_lower_122 : (-1602774927 / 1000000000000 : ℝ) ≤ baseline (61 / 50 : ℝ) :=
  (baseline_enclosure_122).1.trans (twoChordBaseline_le_of_range (h := (61 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_122 : (562218681 / 1000000000000 : ℝ) ≤ baseline (61 / 50 : ℝ) + gain (61 / 50 : ℝ) := by
  have hb := baseline_lower_122
  have hg := (gain_enclosure_122).1
  linarith

lemma baseline_lower_126 : (-72604479 / 40000000000 : ℝ) ≤ baseline (63 / 50 : ℝ) :=
  (baseline_enclosure_126).1.trans (twoChordBaseline_le_of_range (h := (63 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_126 : (667302631 / 1000000000000 : ℝ) ≤ baseline (63 / 50 : ℝ) + gain (63 / 50 : ℝ) := by
  have hb := baseline_lower_126
  have hg := (gain_enclosure_126).1
  linarith

lemma baseline_lower_130 : (-985718467 / 500000000000 : ℝ) ≤ baseline (13 / 10 : ℝ) :=
  (baseline_enclosure_130).1.trans (twoChordBaseline_le_of_range (h := (13 / 10 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_130 : (23593217 / 31250000000 : ℝ) ≤ baseline (13 / 10 : ℝ) + gain (13 / 10 : ℝ) := by
  have hb := baseline_lower_130
  have hg := (gain_enclosure_130).1
  linarith

lemma baseline_lower_134 : (-84067367 / 40000000000 : ℝ) ≤ baseline (67 / 50 : ℝ) :=
  (baseline_enclosure_134).1.trans (twoChordBaseline_le_of_range (h := (67 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_134 : (88422833 / 100000000000 : ℝ) ≤ baseline (67 / 50 : ℝ) + gain (67 / 50 : ℝ) := by
  have hb := baseline_lower_134
  have hg := (gain_enclosure_134).1
  linarith

lemma baseline_lower_138 : (-35098821 / 15625000000 : ℝ) ≤ baseline (69 / 50 : ℝ) :=
  (baseline_enclosure_138).1.trans (twoChordBaseline_le_of_range (h := (69 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_138 : (507522239 / 500000000000 : ℝ) ≤ baseline (69 / 50 : ℝ) + gain (69 / 50 : ℝ) := by
  have hb := baseline_lower_138
  have hg := (gain_enclosure_138).1
  linarith

lemma baseline_lower_142 : (-491832859 / 200000000000 : ℝ) ≤ baseline (71 / 50 : ℝ) :=
  (baseline_enclosure_142).1.trans (twoChordBaseline_le_of_range (h := (71 / 50 : ℝ)) (by norm_num) (by norm_num))

lemma combined_lower_142 : (174959141 / 200000000000 : ℝ) ≤ baseline (71 / 50 : ℝ) + gain (71 / 50 : ℝ) := by
  have hb := baseline_lower_142
  have hg := (gain_enclosure_142).1
  linarith

lemma baseline_lower_146 : (-2731694911 / 1000000000000 : ℝ) ≤ baseline (73 / 50 : ℝ) :=
  (baseline_enclosure_146).1.trans ((linearBaseline_eq_of_range (h := (73 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_146 : (602265089 / 1000000000000 : ℝ) ≤ baseline (73 / 50 : ℝ) + gain (73 / 50 : ℝ) := by
  have hb := baseline_lower_146
  have hg := (gain_enclosure_146).1
  linarith

lemma baseline_lower_150 : (-2587585731 / 1000000000000 : ℝ) ≤ baseline (3 / 2 : ℝ) :=
  (baseline_enclosure_150).1.trans ((linearBaseline_eq_of_range (h := (3 / 2 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_150 : (75655309 / 125000000000 : ℝ) ≤ baseline (3 / 2 : ℝ) + gain (3 / 2 : ℝ) := by
  have hb := baseline_lower_150
  have hg := (gain_enclosure_150).1
  linarith

lemma baseline_lower_154 : (-956610909 / 500000000000 : ℝ) ≤ baseline (77 / 50 : ℝ) :=
  (baseline_enclosure_154).1.trans ((linearBaseline_eq_of_range (h := (77 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_154 : (1030551187 / 1000000000000 : ℝ) ≤ baseline (77 / 50 : ℝ) + gain (77 / 50 : ℝ) := by
  have hb := baseline_lower_154
  have hg := (gain_enclosure_154).1
  linarith

lemma baseline_lower_158 : (-149307897 / 200000000000 : ℝ) ≤ baseline (79 / 50 : ℝ) :=
  (baseline_enclosure_158).1.trans ((linearBaseline_eq_of_range (h := (79 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_158 : (1976421667 / 1000000000000 : ℝ) ≤ baseline (79 / 50 : ℝ) + gain (79 / 50 : ℝ) := by
  have hb := baseline_lower_158
  have hg := (gain_enclosure_158).1
  linarith

lemma baseline_lower_162 : (878094887 / 1000000000000 : ℝ) ≤ baseline (81 / 50 : ℝ) :=
  (baseline_enclosure_162).1.trans ((linearBaseline_eq_of_range (h := (81 / 50 : ℝ)) (by norm_num) (by norm_num)).le)

lemma combined_lower_162 : (1702298751 / 500000000000 : ℝ) ≤ baseline (81 / 50 : ℝ) + gain (81 / 50 : ℝ) := by
  have hb := baseline_lower_162
  have hg := (gain_enclosure_162).1
  linarith

lemma baseline_lower_170 : (5379096533 / 1000000000000 : ℝ) ≤ baseline (17 / 10 : ℝ) :=
  (baseline_enclosure_170).1.trans ((linearBaseline_eq_of_range (h := (17 / 10 : ℝ)) (by norm_num) (by norm_num)).le)

lemma baseline_lower_190 : (22763388121 / 1000000000000 : ℝ) ≤ baseline (19 / 10 : ℝ) :=
  (baseline_enclosure_190).1.trans ((linearBaseline_eq_of_range (h := (19 / 10 : ℝ)) (by norm_num) (by norm_num)).le)

lemma baseline_lower_225 : (342738213 / 5000000000 : ℝ) ≤ baseline (9 / 4 : ℝ) :=
  (baseline_enclosure_225).1.trans ((linearBaseline_eq_of_range (h := (9 / 4 : ℝ)) (by norm_num) (by norm_num)).le)

lemma positive_64_74 {h : ℝ} (hh : h ∈ Set.Icc (16 / 25 : ℝ) (37 / 50 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_64 baseline_lower_74
  have hp : (0 : ℝ) < min (6874889409 / 500000000000 : ℝ) (383669089 / 40000000000 : ℝ) - ((37 / 50 : ℝ) - (16 / 25 : ℝ)) ^ 2 / (4 * (16 / 25 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_74_84 {h : ℝ} (hh : h ∈ Set.Icc (37 / 50 : ℝ) (21 / 25 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_74 baseline_lower_84
  have hp : (0 : ℝ) < min (383669089 / 40000000000 : ℝ) (146341961 / 25000000000 : ℝ) - ((21 / 25 : ℝ) - (37 / 50 : ℝ)) ^ 2 / (4 * (37 / 50 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_84_92 {h : ℝ} (hh : h ∈ Set.Icc (21 / 25 : ℝ) (23 / 25 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_84 baseline_lower_92
  have hp : (0 : ℝ) < min (146341961 / 25000000000 : ℝ) (334736981 / 100000000000 : ℝ) - ((23 / 25 : ℝ) - (21 / 25 : ℝ)) ^ 2 / (4 * (21 / 25 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_92_98 {h : ℝ} (hh : h ∈ Set.Icc (23 / 25 : ℝ) (49 / 50 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_92 baseline_lower_98
  have hp : (0 : ℝ) < min (334736981 / 100000000000 : ℝ) (1797263411 / 1000000000000 : ℝ) - ((49 / 50 : ℝ) - (23 / 25 : ℝ)) ^ 2 / (4 * (23 / 25 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_98_102 {h : ℝ} (hh : h ∈ Set.Icc (49 / 50 : ℝ) (51 / 50 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_98 baseline_lower_102
  have hp : (0 : ℝ) < min (1797263411 / 1000000000000 : ℝ) (926954813 / 1000000000000 : ℝ) - ((51 / 50 : ℝ) - (49 / 50 : ℝ)) ^ 2 / (4 * (49 / 50 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_102_106 {h : ℝ} (hh : h ∈ Set.Icc (51 / 50 : ℝ) (53 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_102 combined_lower_106
  have hp : (0 : ℝ) < min (1696987851 / 1000000000000 : ℝ) (588471367 / 500000000000 : ℝ) - (1 / (51 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((53 / 50 : ℝ) - (51 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_106_110 {h : ℝ} (hh : h ∈ Set.Icc (53 / 50 : ℝ) (11 / 10 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_106 combined_lower_110
  have hp : (0 : ℝ) < min (588471367 / 500000000000 : ℝ) (813603931 / 1000000000000 : ℝ) - (1 / (53 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((11 / 10 : ℝ) - (53 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_110_114 {h : ℝ} (hh : h ∈ Set.Icc (11 / 10 : ℝ) (57 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_110 combined_lower_114
  have hp : (0 : ℝ) < min (813603931 / 1000000000000 : ℝ) (598682283 / 1000000000000 : ℝ) - (1 / (11 / 10 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((57 / 50 : ℝ) - (11 / 10 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_114_118 {h : ℝ} (hh : h ∈ Set.Icc (57 / 50 : ℝ) (59 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_114 combined_lower_118
  have hp : (0 : ℝ) < min (598682283 / 1000000000000 : ℝ) (65023907 / 125000000000 : ℝ) - (1 / (57 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((59 / 50 : ℝ) - (57 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_118_122 {h : ℝ} (hh : h ∈ Set.Icc (59 / 50 : ℝ) (61 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_118 combined_lower_122
  have hp : (0 : ℝ) < min (65023907 / 125000000000 : ℝ) (562218681 / 1000000000000 : ℝ) - (1 / (59 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((61 / 50 : ℝ) - (59 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_122_126 {h : ℝ} (hh : h ∈ Set.Icc (61 / 50 : ℝ) (63 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_122 combined_lower_126
  have hp : (0 : ℝ) < min (562218681 / 1000000000000 : ℝ) (667302631 / 1000000000000 : ℝ) - (1 / (61 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((63 / 50 : ℝ) - (61 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_126_130 {h : ℝ} (hh : h ∈ Set.Icc (63 / 50 : ℝ) (13 / 10 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_126 combined_lower_130
  have hp : (0 : ℝ) < min (667302631 / 1000000000000 : ℝ) (23593217 / 31250000000 : ℝ) - (1 / (63 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((13 / 10 : ℝ) - (63 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_130_134 {h : ℝ} (hh : h ∈ Set.Icc (13 / 10 : ℝ) (67 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_130 combined_lower_134
  have hp : (0 : ℝ) < min (23593217 / 31250000000 : ℝ) (88422833 / 100000000000 : ℝ) - (1 / (13 / 10 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((67 / 50 : ℝ) - (13 / 10 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_134_138 {h : ℝ} (hh : h ∈ Set.Icc (67 / 50 : ℝ) (69 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_134 combined_lower_138
  have hp : (0 : ℝ) < min (88422833 / 100000000000 : ℝ) (507522239 / 500000000000 : ℝ) - (1 / (67 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((69 / 50 : ℝ) - (67 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_138_142 {h : ℝ} (hh : h ∈ Set.Icc (69 / 50 : ℝ) (71 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_138 combined_lower_142
  have hp : (0 : ℝ) < min (507522239 / 500000000000 : ℝ) (174959141 / 200000000000 : ℝ) - (1 / (69 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((71 / 50 : ℝ) - (69 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_142_146 {h : ℝ} (hh : h ∈ Set.Icc (71 / 50 : ℝ) (73 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_142 combined_lower_146
  have hp : (0 : ℝ) < min (174959141 / 200000000000 : ℝ) (602265089 / 1000000000000 : ℝ) - (1 / (71 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((73 / 50 : ℝ) - (71 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_146_150 {h : ℝ} (hh : h ∈ Set.Icc (73 / 50 : ℝ) (3 / 2 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_146 combined_lower_150
  have hp : (0 : ℝ) < min (602265089 / 1000000000000 : ℝ) (75655309 / 125000000000 : ℝ) - (1 / (73 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((3 / 2 : ℝ) - (73 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_150_154 {h : ℝ} (hh : h ∈ Set.Icc (3 / 2 : ℝ) (77 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_150 combined_lower_154
  have hp : (0 : ℝ) < min (75655309 / 125000000000 : ℝ) (1030551187 / 1000000000000 : ℝ) - (1 / (3 / 2 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((77 / 50 : ℝ) - (3 / 2 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_154_158 {h : ℝ} (hh : h ∈ Set.Icc (77 / 50 : ℝ) (79 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_154 combined_lower_158
  have hp : (0 : ℝ) < min (1030551187 / 1000000000000 : ℝ) (1976421667 / 1000000000000 : ℝ) - (1 / (77 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((79 / 50 : ℝ) - (77 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_158_162 {h : ℝ} (hh : h ∈ Set.Icc (79 / 50 : ℝ) (81 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hb := combined_chord_lower (by norm_num) (by norm_num) (by norm_num) hh combined_lower_158 combined_lower_162
  have hp : (0 : ℝ) < min (1976421667 / 1000000000000 : ℝ) (1702298751 / 500000000000 : ℝ) - (1 / (79 / 50 : ℝ) ^ 2 + (1 / 5 : ℝ)) * ((81 / 50 : ℝ) - (79 / 50 : ℝ)) ^ 2 / 4 := by norm_num
  exact hp.trans_le hb

lemma positive_162_170 {h : ℝ} (hh : h ∈ Set.Icc (81 / 50 : ℝ) (17 / 10 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_162 baseline_lower_170
  have hp : (0 : ℝ) < min (878094887 / 1000000000000 : ℝ) (5379096533 / 1000000000000 : ℝ) - ((17 / 10 : ℝ) - (81 / 50 : ℝ)) ^ 2 / (4 * (81 / 50 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_170_190 {h : ℝ} (hh : h ∈ Set.Icc (17 / 10 : ℝ) (19 / 10 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_170 baseline_lower_190
  have hp : (0 : ℝ) < min (5379096533 / 1000000000000 : ℝ) (22763388121 / 1000000000000 : ℝ) - ((19 / 10 : ℝ) - (17 / 10 : ℝ)) ^ 2 / (4 * (17 / 10 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma positive_190_225 {h : ℝ} (hh : h ∈ Set.Icc (19 / 10 : ℝ) (9 / 4 : ℝ)) : 0 < baseline h := by
  have hb := baseline_chord_lower (by norm_num) (by norm_num) hh baseline_lower_190 baseline_lower_225
  have hp : (0 : ℝ) < min (22763388121 / 1000000000000 : ℝ) (342738213 / 5000000000 : ℝ) - ((9 / 4 : ℝ) - (19 / 10 : ℝ)) ^ 2 / (4 * (19 / 10 : ℝ) ^ 2) := by norm_num
  exact hp.trans_le hb

lemma baseline_positive_left {h : ℝ} (hh : h ∈ Set.Icc (16 / 25 : ℝ) (51 / 50 : ℝ)) : 0 < baseline h := by
  have hl := hh.1
  have hu := hh.2

  by_cases hx : h ≤ (37 / 50 : ℝ)
  · exact positive_64_74 ⟨by linarith, hx⟩
  have hl : (37 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (21 / 25 : ℝ)
  · exact positive_74_84 ⟨by linarith, hx⟩
  have hl : (21 / 25 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (23 / 25 : ℝ)
  · exact positive_84_92 ⟨by linarith, hx⟩
  have hl : (23 / 25 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (49 / 50 : ℝ)
  · exact positive_92_98 ⟨by linarith, hx⟩
  have hl : (49 / 50 : ℝ) < h := lt_of_not_ge hx

  exact positive_98_102 ⟨by linarith, hu⟩

lemma baseline_positive_right {h : ℝ} (hh : h ∈ Set.Icc (81 / 50 : ℝ) (9 / 4 : ℝ)) : 0 < baseline h := by
  have hl := hh.1
  have hu := hh.2

  by_cases hx : h ≤ (17 / 10 : ℝ)
  · exact positive_162_170 ⟨by linarith, hx⟩
  have hl : (17 / 10 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (19 / 10 : ℝ)
  · exact positive_170_190 ⟨by linarith, hx⟩
  have hl : (19 / 10 : ℝ) < h := lt_of_not_ge hx

  exact positive_190_225 ⟨by linarith, hu⟩

lemma combined_positive {h : ℝ} (hh : h ∈ Set.Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) : 0 < baseline h + gain h := by
  have hl := hh.1
  have hu := hh.2

  by_cases hx : h ≤ (53 / 50 : ℝ)
  · exact positive_102_106 ⟨by linarith, hx⟩
  have hl : (53 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (11 / 10 : ℝ)
  · exact positive_106_110 ⟨by linarith, hx⟩
  have hl : (11 / 10 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (57 / 50 : ℝ)
  · exact positive_110_114 ⟨by linarith, hx⟩
  have hl : (57 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (59 / 50 : ℝ)
  · exact positive_114_118 ⟨by linarith, hx⟩
  have hl : (59 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (61 / 50 : ℝ)
  · exact positive_118_122 ⟨by linarith, hx⟩
  have hl : (61 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (63 / 50 : ℝ)
  · exact positive_122_126 ⟨by linarith, hx⟩
  have hl : (63 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (13 / 10 : ℝ)
  · exact positive_126_130 ⟨by linarith, hx⟩
  have hl : (13 / 10 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (67 / 50 : ℝ)
  · exact positive_130_134 ⟨by linarith, hx⟩
  have hl : (67 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (69 / 50 : ℝ)
  · exact positive_134_138 ⟨by linarith, hx⟩
  have hl : (69 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (71 / 50 : ℝ)
  · exact positive_138_142 ⟨by linarith, hx⟩
  have hl : (71 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (73 / 50 : ℝ)
  · exact positive_142_146 ⟨by linarith, hx⟩
  have hl : (73 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (3 / 2 : ℝ)
  · exact positive_146_150 ⟨by linarith, hx⟩
  have hl : (3 / 2 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (77 / 50 : ℝ)
  · exact positive_150_154 ⟨by linarith, hx⟩
  have hl : (77 / 50 : ℝ) < h := lt_of_not_ge hx

  by_cases hx : h ≤ (79 / 50 : ℝ)
  · exact positive_154_158 ⟨by linarith, hx⟩
  have hl : (79 / 50 : ℝ) < h := lt_of_not_ge hx

  exact positive_158_162 ⟨by linarith, hu⟩

theorem scalar_positive :
    (∀ h ∈ Set.Icc (16 / 25 : ℝ) (51 / 50) ∪ Set.Icc (81 / 50 : ℝ) (9 / 4), 0 < baseline h) ∧
    (∀ h ∈ Set.Icc (51 / 50 : ℝ) (81 / 50), 0 < baseline h + gain h) := by
  constructor
  · intro h hh
    rcases hh with hh | hh
    · exact baseline_positive_left hh
    · exact baseline_positive_right hh
  · exact fun _ hh ↦ combined_positive hh

end CubicTorus.Scalar.Cert

end
end
end
end ReusedScalar205

end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma unitPlanarProfile_eq_reused (v : ℝ) :
    unitPlanarProfile v=2*ReusedScalar205.CubicTorus.Scalar.planarProfile v := by
  unfold unitPlanarProfile ReusedScalar205.CubicTorus.Scalar.planarProfile
  rw [mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2),
    mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)]
  ring_nf

lemma nestingBaseline_eq_reused {h : ℝ} (hh : 0<h) :
    nestingBaseline h=ReusedScalar205.CubicTorus.Scalar.baseline h := by
  have ht := Shape.t_spec hh
  have he : (∫ v in (0 : ℝ)..Shape.t h,sharpSectionWeight (2*h) v)=
      ∫ v in (0 : ℝ)..Shape.t h,
        ReusedScalar205.CubicTorus.Nesting.weight
          (h*v/ReusedScalar205.CubicTorus.Scalar.planarProfile v) := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1.le]
    intro v hv
    have hv1 : v<1 := hv.2.trans_lt ht.2.1
    rw [sharpSectionWeight,ite_eq_left ⟨hv.1,hv1⟩,unitPlanarProfile_eq_reused]
    have hac : 2*h*v/(2*ReusedScalar205.CubicTorus.Scalar.planarProfile v)=
        h*v/ReusedScalar205.CubicTorus.Scalar.planarProfile v := by ring
    rw [hac]
    rfl
  unfold nestingBaseline ReusedScalar205.CubicTorus.Scalar.baseline
  rw [he]
  rfl

lemma nestingGainInfimum_eq_reused (h : ℝ) :
    nestingGainInfimum h=ReusedScalar205.CubicTorus.Scalar.gain h := by
  unfold nestingGainInfimum ReusedScalar205.CubicTorus.Scalar.gain
    ReusedScalar205.CubicTorus.Scalar.cappedInf
  congr 2
  funext y
  unfold nestingExcess nestingC0 nestingP nestingQ
    ReusedScalar205.CubicTorus.Scalar.cappedEnergy
    ReusedScalar205.CubicTorus.Scalar.C₀
    ReusedScalar205.CubicTorus.Scalar.P ReusedScalar205.CubicTorus.Scalar.Q
  norm_num
  rfl

theorem nesting_scalar_positive :
    (∀ h∈Icc (16/25 : ℝ) (51/50) ∪ Icc (81/50 : ℝ) (9/4),0<nestingBaseline h) ∧
    (∀ h∈Icc (51/50 : ℝ) (81/50),0<nestingBaseline h+nestingGainInfimum h) := by
  have hp := ReusedScalar205.CubicTorus.Scalar.Cert.scalar_positive
  constructor
  · intro h hh
    have hpos : 0<h := by
      rcases hh with hl|hr
      · linarith [hl.1]
      · linarith [hr.1]
    rw [nestingBaseline_eq_reused hpos]
    exact hp.1 h hh
  · intro h hh
    have hpos : 0<h := by linarith [hh.1]
    rw [nestingBaseline_eq_reused hpos,nestingGainInfimum_eq_reused]
    exact hp.2 h hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma nesting_scalar_contradiction {A h : ℝ} (hA : A≤1)
    (hh : h∈Icc (16/25 : ℝ) (9/4))
    (hB : nestingBaseline h≤A-1)
    (hBS : h∈Icc (51/50 : ℝ) (81/50) →
      nestingBaseline h+nestingGainInfimum h≤A-1) : False := by
  have hp := nesting_scalar_positive
  by_cases hlo : h≤51/50
  · have hpos := hp.1 h (Or.inl ⟨hh.1,hlo⟩)
    linarith
  · by_cases hhi : h≤81/50
    · have hmid : h∈Icc (51/50 : ℝ) (81/50) := ⟨(lt_of_not_ge hlo).le,hhi⟩
      have hpos := hp.2 h hmid
      have hle := hBS hmid
      linarith
    · have hpos := hp.1 h (Or.inr ⟨(lt_of_not_ge hhi).le,hh.2⟩)
      linarith

theorem isMinimizerAt_nonstandard_not_three_vertices {E : Set Torus}
    (hmin : IsMinimizerAt (1/Real.pi) E)
    (hstd : ¬StandardRegionAt (1/Real.pi) E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E)) :
    ∃ b : Fin 3 →Bool,
      (∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
        quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E) ∧
      ∀ i : Fin 3,
        quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E →
        ¬(∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) := by
  obtain ⟨μ,H,b,hμ,hCMC,hd,ha,hf⟩ :=
    isMinimizerAt_nonstandard_three_vertex_nesting hmin hstd hR
  refine ⟨b,hd,fun i hv haxes ↦ ?_⟩
  obtain ⟨hA,_,_,_,hh,_,hB,hBS⟩ := hf i hv haxes
  exact nesting_scalar_contradiction hA hh hB hBS

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_fixed_downset_not_three_vertices {E : Set Torus}
    (hmin : IsMinimizerAt (1/Real.pi) E) (hstd : ¬StandardRegionAt (1/Real.pi) E)
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E)
    (haxes : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative E) : False := by
  have hV : (1/Real.pi)∈Ioo (0 : ℝ) 1 :=
    ⟨by positivity,(div_lt_one Real.pi_pos).mpr (by linarith [Real.pi_gt_three])⟩
  have hVh : (1/Real.pi)∈Ioc (0 : ℝ) (1/2) :=
    ⟨hV.1,by rw [div_le_iff₀ Real.pi_pos]; linarith [Real.pi_gt_three]⟩
  have hc : IsPreconnected (frontier (openRepresentative E)) :=
    (Periodic.isMinimizerAt_connected_or_standard_slab hV hmin).resolve_right (fun h ↦ hstd h.2.2)
  obtain ⟨μ,H,hμ,hCMC,ha,_⟩ := isMinimizerAt_nonstandard_integrated_flux hVh hmin hstd hR
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [ho]
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hvF : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [ho]
  have haxesF : ∀ j : Fin 2,quotientMap (orientedUpperVertex b (fun k ↦ if k=i.succAbove j then true else false))∈openRepresentative F := by rwa [ho]
  have hμF := hμ.congr_ae hFE.symm
  obtain ⟨hA,hlo,hhi,hs,hcurv,ht⟩ := isMinimizerAt_three_vertex_parameters
    hF hmF hcF hRF b hdF hμF hCMC i (ha i) hvF haxesF
  have hH0 : 0≤H := by linarith [hcurv.1]
  have hflux := isMinimizerAt_missing_neighbor_sharp_area_flux hV hF hmF hRF b hdF
    hμF hH0 (Periodic.coordinateCMC_of_global hμF hCMC) i (ha i) hvF
  have hB : nestingBaseline (H/2)≤(perimeter F).toReal/2-1 := by
    have hb := nestingBaseline_slack (by linarith : 0≤H/2) ht
    rw [show 2*(H/2)=H by ring] at hb
    change Nesting.lambda*H*(1/Real.pi)+2*(∫ v in (0 : ℝ)..
      volume.real (axialSlice (openRepresentative F) i (octantHeight b i 0 : AxisCircle)),sharpSectionWeight H v)≤(perimeter F).toReal at hflux
    have he : Nesting.lambda*H*(1/Real.pi)=2*(Nesting.lambda*(H/2)/Real.pi) := by ring
    rw [he] at hflux
    have hnon := mul_nonneg (show 0≤Nesting.ell by norm_num [Nesting.ell]) (sub_nonneg.mpr ht)
    linarith
  apply nesting_scalar_contradiction hA hcurv hB
  intro hH
  obtain ⟨hout,hin⟩ := isMinimizerAt_three_vertex_bottom hV hmF hcF hRF b hdF i hvF haxesF
  exact isMinimizerAt_nesting_area_bound hF hmF hRF b hdF hμF hCMC i (ha i) hvF hout (hin 0) (hin 1) hH

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set
namespace CubicTorus

lemma isMinimizerAt_missing_neighbor_volume_le_half_null {V : ℝ}
    (hV : V∈Ioo (0 : ℝ) 1) {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3)
    (hv : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative E) :
    V≤1/2 := by
  let F := toMeasurable torusVolume E
  have hF : MeasurableSet F := measurableSet_toMeasurable _ _
  have hFE : F=ᵐ[torusVolume]E := hmin.1.1.toMeasurable_ae_eq
  have hmF := (isMinimizerAt_congr_ae hFE).mpr hmin
  have ho := openRepresentative_congr_ae hFE
  have hcF : IsPreconnected (frontier (openRepresentative F)) := by rwa [ho]
  have hRF (j : Fin 3) : F=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' F) :=
    hFE.trans ((hR j).trans ((axisReflection j).measurePreserving.quasiMeasurePreserving.preimage_ae_eq hFE.symm))
  have hdF : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative F →quotientMap x∈openRepresentative F := by rwa [ho]
  have hvF : quotientMap (orientedUpperVertex b (fun j ↦ if j=i then true else false))∉openRepresentative F := by rwa [ho]
  exact isMinimizerAt_missing_neighbor_volume_le_half hV hF hmF hcF hRF b hdF i hvF

lemma orientedUpperVertex_reverse (b c : Fin 3 →Bool) :
    orientedUpperVertex (fun i ↦ !b i) c=orientedUpperVertex b (fun i ↦ !c i) := by
  ext i
  dsimp [orientedUpperVertex,upperVertex]
  by_cases hb : b i=true <;> by_cases hc : c i=true <;> simp_all

theorem isMinimizerAt_small_side_no_face_vertex {V : ℝ}
    (hV : V∈Ioo (0 : ℝ) (1/2)) {E : Set Torus} (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E)))
    (hR : ∀ i : Fin 3,E=ᵐ[torusVolume]((axisReflection i).torus ⁻¹' E))
    (b : Fin 3 →Bool)
    (hd : ∀ x∈upperOctant,∀ y∈upperOctant,OrientedCoordinateLE b x y →
      quotientMap y∈openRepresentative E →quotientMap x∈openRepresentative E)
    (i : Fin 3) :
    quotientMap (orientedUpperVertex b (fun j ↦ if j=i then false else true))∉openRepresentative E := by
  intro hv
  have hV01 : V∈Ioo (0 : ℝ) 1 := ⟨hV.1,by linarith [hV.2]⟩
  have hVc : 1-V∈Ioo (0 : ℝ) 1 := ⟨by linarith [hV.2],by linarith [hV.1]⟩
  have hmC := (isMinimizerAt_compl ⟨hV01.1.le,hV01.2.le⟩).mpr hmin
  have hcC : IsPreconnected (frontier (openRepresentative Eᶜ)) := by
    rwa [isMinimizerAt_frontier_compl hV01 hmin]
  have hRC (j : Fin 3) : Eᶜ=ᵐ[torusVolume]((axisReflection j).torus ⁻¹' Eᶜ) := (hR j).compl
  have hdC := isMinimizerAt_complement_octant_downset hV01 hmin hR hd
  have hvC : quotientMap (orientedUpperVertex (fun j ↦ !b j)
      (fun j ↦ if j=i then true else false))∉openRepresentative Eᶜ := by
    rw [orientedUpperVertex_reverse,openRepresentative_compl_eq hV01 hmin]
    have he : (fun j : Fin 3 ↦ !(if j=i then true else false))=
        (fun j : Fin 3 ↦ if j=i then false else true) := by
      funext j
      by_cases hj : j=i <;> simp [hj]
    rw [he]
    exact fun hh ↦ hh (subset_closure hv)
  have hle := isMinimizerAt_missing_neighbor_volume_le_half_null hVc hmC hcC hRC
    (fun j ↦ !b j) hdC i hvC
  linarith [hV.2]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma tangentPart_inner_pair {n : Cover} (hn : ‖n‖=1) (a b : Cover) :
    ⟪tangentPart n a,tangentPart n b⟫=⟪a,b⟫-⟪n,a⟫*⟪n,b⟫ := by
  simp only [tangentPart,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,real_inner_self_eq_norm_sq,hn,one_pow,real_inner_comm a n]
  ring

lemma normal_coordinate_trace {n : Cover} (hn : ‖n‖=1)
    (D : Cover →L[ℝ] Cover) (ht : ∀ v,⟪n,D v⟫=0) :
    (∑ i : Fin 3,⟪tangentPart n (D.adjoint (EuclideanSpace.single i 1)),
      tangentPart n (EuclideanSpace.single i 1)⟫)=coverTrace D := by
  simp_rw [tangentPart_inner_pair hn,ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  simp only [EuclideanSpace.inner_single_left,EuclideanSpace.inner_single_right,
    conj_trivial,one_mul]
  rw [Finset.sum_sub_distrib]
  have hz : (∑ i : Fin 3,(D n) i*n i)=0 := by
    have hh := ht n
    simpa only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real] using hh
  rw [hz,sub_zero]
  rfl

lemma periodic_coordinates_trace {N X : Cover → Cover}
    (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hXp : ∀ m x,X (x+latticeVector m)=X x)
    (z : NormalBundle) (he : N z.1=(z.2 : Cover))
    (hu : ∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1)
    (hdX : fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover) :
    (∑ i : Fin 3,⟪smoothScalarGradient (normalComponentScalar N hN hp i) z,
      smoothScalarGradient (normalComponentScalar X hX hXp i) z⟫)=divergence N z.1 := by
  have hd := smooth_unit_normal_derivative (hN.differentiable (by simp) z.1) hu
  have ht (v : Cover) : ⟪N z.1,fderiv ℝ N z.1 v⟫=0 := by
    rw [←ContinuousLinearMap.adjoint_inner_left,hd,inner_zero_left]
  have hg (i : Fin 3) : smoothScalarGradient (normalComponentScalar X hX hXp i) z=
      tangentPart (z.2 : Cover) (EuclideanSpace.single i 1) := by
    change tangentPart _ (gradient (fun y ↦ ⟪EuclideanSpace.single i 1,X y⟫) z.1)=_
    rw [gradient_normal_component hX,hdX]
    simp only [ContinuousLinearMap.adjoint_id,ContinuousLinearMap.id_apply]
  simp_rw [hg]
  change (∑ i : Fin 3,⟪tangentPart (z.2 : Cover)
    (gradient (fun y ↦ ⟪EuclideanSpace.single i 1,N y⟫) z.1),
    tangentPart (z.2 : Cover) (EuclideanSpace.single i 1)⟫)=_
  simp_rw [gradient_normal_component hN,←he]
  rw [normal_coordinate_trace hu.self_of_nhds _ ht,divergence_eq_coverTrace]

lemma periodic_coordinates_divergence {X : Cover → Cover} (z : NormalBundle)
    (hdX : fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover) :
    tangentialDivergence X z.1 z.2=2 := by
  unfold tangentialDivergence
  rw [divergence_eq_coverTrace,hdX,ContinuousLinearMap.id_apply,
    real_inner_self_eq_norm_sq,z.2.property,one_pow]
  norm_num [coverTrace,Fin.sum_univ_three]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus
namespace Periodic

theorem isMinimizerAt_stationary_translation_system {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ (μ : FiniteMeasure NormalBundle) (H : ℝ) (N : Cover → Cover)
      (hN : ContDiff ℝ (⊤ : ℕ∞) N) (hp : ∀ m x,N (x+latticeVector m)=N x),
      IsNormalMeasure E μ ∧
      (∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover)) ∧
      (∀ x : Cover,quotientMap x∈frontier (openRepresentative E) →
        (∀ᶠ y in 𝓝 x,‖N y‖=1) ∧ divergence N x=H) ∧
      (∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
        (∀ m x,F (x+latticeVector m)=F x) →
        (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
          H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle))) ∧
      (∀ u∈surfaceH1 μ,surfaceMean μ u=0 →
        0≤ surfaceJacobiB μ (surfaceCurvatureLp μ N hN) u u) ∧
      ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
        (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0 := by
  obtain ⟨μ,H,hμ,hCMC,hs⟩ := isMinimizerAt_boundary_stability hV hE hmin
  obtain ⟨N,hN,hp,hae,hb⟩ := isMinimizerAt_stationary_tubular_normal hV hE hmin hμ hCMC
  have hbd := normalMeasure_frontier_ae (isOpen_openRepresentative E).measurableSet
    (hμ.congr_ae (isMinimizerAt_openRepresentative_ae hV hE hmin).symm)
  have hn : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H := by
    filter_upwards [hae,hbd] with z hz hzb
    exact ⟨hz,hb z.1 hzb⟩
  have hstab : ∀ f : Cover → ℝ,ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ m x,f (x+latticeVector m)=f x) →
      (∫ z,f z.1 ∂(μ : Measure NormalBundle))=0 → 0≤normalExtensionJacobi μ f N := by
    intro f hf hfp hz
    rw [←boundaryQuadratic_eq_normalExtension hf hN (hn.mono fun _ h _ ↦ h)]
    apply hs _ (hf.smul hN)
    · intro m x
      change f (x+latticeVector m) • N (x+latticeVector m)=f x • N x
      rw [hfp,hp]
    · rw [←hz]
      apply integral_congr_ae
      filter_upwards [hae] with z hz
      change ⟪(z.2 : Cover),f z.1 • N z.1⟫=f z.1
      rw [hz,real_inner_smul_right,real_inner_self_eq_norm_sq,z.2.property,one_pow,mul_one]
  have hm : (μ : Measure NormalBundle).real univ≠0 := by
    rw [Measure.real,←FiniteMeasure.ennreal_mass]
    change (μ.mass : ℝ)≠0
    rw [hμ.1]
    exact (ENNReal.toReal_pos (perimeter_pos_of_volume hV hmin.1.1 hmin.2.1).ne' hmin.1.2.ne).ne'
  have hstable := fun u hu hz ↦ surfaceH1_stability_of_smooth μ hm N hN hstab (u := u) hu hz
  exact ⟨μ,H,N,hN,hp,hμ,hae,hb,hCMC,hstable,fun i ↦
    normalComponentScalar_global_jacobi hV hE hmin hμ hN hp hae (fun x hx ↦ (hb x hx).1) hstable i⟩

end Periodic
end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem periodic_minkowski_identities (μ : FiniteMeasure NormalBundle) (H : ℝ)
    (N : Cover → Cover) (hN : ContDiff ℝ (⊤ : ℕ∞) N)
    (hp : ∀ m x,N (x+latticeVector m)=N x)
    (hae : ∀ᵐ z ∂(μ : Measure NormalBundle),N z.1=(z.2 : Cover) ∧
      (∀ᶠ y in 𝓝 (z.1 : Cover),‖N y‖=1) ∧ divergence N z.1=H)
    (hCMC : ∀ F : Cover → Cover,ContDiff ℝ (⊤ : ℕ∞) F →
      (∀ m x,F (x+latticeVector m)=F x) →
      (∫ z,tangentialDivergence F z.1 z.2 ∂(μ : Measure NormalBundle))=
        H*(∫ z,⟪(z.2 : Cover),F z.1⟫ ∂(μ : Measure NormalBundle)))
    (hj : ∀ i : Fin 3,∀ w∈surfaceH1 μ,surfaceJacobiB μ (surfaceCurvatureLp μ N hN)
      (surfaceSmoothJet μ (normalComponentScalar N hN hp i)) w=0)
    (X : Cover → Cover) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hXp : ∀ m x,X (x+latticeVector m)=X x)
    (hdX : ∀ᵐ z ∂(μ : Measure NormalBundle),fderiv ℝ X z.1=ContinuousLinearMap.id ℝ Cover) :
    H*(∫ z,⟪N z.1,X z.1⟫ ∂(μ : Measure NormalBundle))=2*(μ.mass : ℝ) ∧
    (∫ z,coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))*⟪N z.1,X z.1⟫
      ∂(μ : Measure NormalBundle))=H*(μ.mass : ℝ) := by
  constructor
  · have hh := hCMC X hX hXp
    have hl : (∫ z,tangentialDivergence X z.1 z.2 ∂(μ : Measure NormalBundle))=2*(μ.mass : ℝ) := by
      calc
        _=∫ _ : NormalBundle,(2 : ℝ) ∂(μ : Measure NormalBundle) :=
          integral_congr_ae (hdX.mono fun z hz ↦ periodic_coordinates_divergence z hz)
        _=_ := by simp only [integral_const,smul_eq_mul,Measure.real_def,
          ←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal]; ring
    rw [hl] at hh
    calc
      _=H*(∫ z,⟪(z.2 : Cover),X z.1⟫ ∂(μ : Measure NormalBundle)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hae] with z hz
        rw [hz.1]
      _=_ := hh.symm
  · let f (i : Fin 3) := normalComponentScalar N hN hp i
    let g (i : Fin 3) := normalComponentScalar X hX hXp i
    let q (z : NormalBundle) := coverTrace ((fderiv ℝ N z.1).comp (fderiv ℝ N z.1))
    let J (i : Fin 3) (z : NormalBundle) :=
      ⟪smoothScalarGradient (f i) z,smoothScalarGradient (g i) z⟫-q z*(f i).val z.1*(g i).val z.1
    have hqi : Continuous q := (normal_curvature_continuous hN).comp normalEmbedding_continuous.fst
    have hi (i : Fin 3) : Integrable (J i) (μ : Measure NormalBundle) := by
      have hc : Continuous (J i) := ((smoothScalarGradient (f i)).continuous.inner (𝕜 := ℝ)
        (smoothScalarGradient (g i)).continuous).sub
        ((hqi.mul (smoothScalarValue (f i)).continuous).mul (smoothScalarValue (g i)).continuous)
      exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hz (i : Fin 3) : (∫ z,J i z ∂(μ : Measure NormalBundle))=0 := by
      rw [←surfaceSmoothJet_bilinear μ N hN (f i) (g i)]
      exact hj i _ (subset_closure (LinearMap.mem_range_self _ _))
    have hsum : ∀ᵐ z ∂(μ : Measure NormalBundle),(∑ i : Fin 3,J i z)=H-q z*⟪N z.1,X z.1⟫ := by
      filter_upwards [hae,hdX] with z hn hd
      dsimp only [J]
      rw [Finset.sum_sub_distrib,periodic_coordinates_trace hN hX hp hXp z hn.1 hn.2.1 hd,hn.2.2]
      congr 1
      simp only [f,g,normalComponentScalar_apply,mul_assoc,←Finset.mul_sum]
      simp only [PiLp.inner_apply,RCLike.inner_apply,RCLike.conj_to_real]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have ht : (∫ z,H-q z*⟪N z.1,X z.1⟫ ∂(μ : Measure NormalBundle))=0 := by
      rw [←integral_congr_ae hsum,integral_finsetSum _ (fun i _ ↦ hi i)]
      simp only [hz,Finset.sum_const_zero]
    have hprod : Integrable (fun z : NormalBundle ↦ q z*⟪N z.1,X z.1⟫) (μ : Measure NormalBundle) :=
      (hqi.mul ((hN.continuous.comp normalEmbedding_continuous.fst).inner (𝕜 := ℝ)
        (hX.continuous.comp normalEmbedding_continuous.fst))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [integral_sub (integrable_const _) hprod,integral_const] at ht
    simp only [smul_eq_mul,Measure.real_def,←FiniteMeasure.ennreal_mass,ENNReal.coe_toReal] at ht
    change (∫ z,q z*⟪N z.1,X z.1⟫ ∂(μ : Measure NormalBundle))=_
    linarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

end CubicTorus
end
end
end

end OAI
