import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part0

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node32 : Integer.Sparse (Fin 2886) := [(329, -598371120), (378, 598371120), (840, -406750320), (861, -25456320), (895, 25456320), (948, 406750320)]

theorem node32_check : node32 =
    Integer.Sparse.merge (Integer.Sparse.scale (-564931) entry_1_6) node31 := by decide +kernel

theorem node32_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node32 x = (((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) := by
  rw [node32_check, Integer.Sparse.eval_merge]
  rw [node31_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node33 : Integer.Sparse (Fin 2886) := [(14, -10347120), (35, -93124080), (90, 68980800), (179, 10347120), (326, -10347120), (375, 34490400), (970, -243022320), (1095, 243022320)]

theorem node33_check : node33 =
    Integer.Sparse.merge (Integer.Sparse.scale (337531) entry_1_9) (Integer.Sparse.scale (-143710) entry_1_10) := by decide +kernel

theorem node33_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node33 x = (((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) := by
  rw [node33_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node34 : Integer.Sparse (Fin 2886) := [(841, -217779840), (842, -147175920), (1043, 217779840), (1091, 147175920)]

theorem node34_check : node34 =
    Integer.Sparse.merge (Integer.Sparse.scale (302472) entry_1_11) (Integer.Sparse.scale (204411) entry_1_12) := by decide +kernel

theorem node34_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node34 x = (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x) := by
  rw [node34_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node35 : Integer.Sparse (Fin 2886) := [(14, -10347120), (35, -93124080), (90, 68980800), (179, 10347120), (326, -10347120), (375, 34490400), (841, -217779840), (842, -147175920), (970, -243022320), (1043, 217779840), (1091, 147175920), (1095, 243022320)]

theorem node35_check : node35 =
    Integer.Sparse.merge node33 node34 := by decide +kernel

theorem node35_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node35 x = ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)) := by
  rw [node35_check, Integer.Sparse.eval_merge]
  rw [node33_eval, node34_eval]

def node36 : Integer.Sparse (Fin 2886) := [(14, -10347120), (35, -93124080), (90, 68980800), (179, 10347120), (326, -10347120), (329, -598371120), (375, 34490400), (378, 598371120), (840, -406750320), (841, -217779840), (842, -147175920), (861, -25456320), (895, 25456320), (948, 406750320), (970, -243022320), (1043, 217779840), (1091, 147175920), (1095, 243022320)]

theorem node36_check : node36 =
    Integer.Sparse.merge node32 node35 := by decide +kernel

theorem node36_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node36 x = ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x))) := by
  rw [node36_check, Integer.Sparse.eval_merge]
  rw [node32_eval, node35_eval]

def node37 : Integer.Sparse (Fin 2886) := [(0, 680097600), (3, 188807040), (14, -10347120), (35, -93124080), (75, -680097600), (78, -188807040), (90, 68980800), (179, 10347120), (326, -10347120), (329, -598371120), (375, 34490400), (378, 598371120), (840, -406750320), (841, -217779840), (842, -78432480), (861, -25456320), (893, -923125680), (895, 900300960), (948, 406750320), (950, -68743440), (954, -794857680), (968, 923125680), (970, -1117866960), (1043, 217779840), (1044, 794857680), (1091, 147175920), (1095, 243022320)]

theorem node37_check : node37 =
    Integer.Sparse.merge node30 node36 := by decide +kernel

theorem node37_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node37 x = (((((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) + ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)))) := by
  rw [node37_check, Integer.Sparse.eval_merge]
  rw [node30_eval, node36_eval]

def node38 : Integer.Sparse (Fin 2886) := [(3, -40865760), (129, 40865760), (841, -610840800), (949, 610840800)]

theorem node38_check : node38 =
    Integer.Sparse.merge (Integer.Sparse.scale (56758) entry_1_14) (Integer.Sparse.scale (-848390) entry_1_15) := by decide +kernel

theorem node38_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node38 x = (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x) := by
  rw [node38_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node39 : Integer.Sparse (Fin 2886) := [(3, -40865760), (129, 40865760), (635, -47187360), (820, 47187360), (841, -610840800), (949, 610840800)]

theorem node39_check : node39 =
    Integer.Sparse.merge (Integer.Sparse.scale (-65538) entry_1_13) node38 := by decide +kernel

theorem node39_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node39 x = (((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) := by
  rw [node39_check, Integer.Sparse.eval_merge]
  rw [node38_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node40 : Integer.Sparse (Fin 2886) := [(860, -1364217840), (893, 1364217840), (900, 1221932880), (975, -1221932880)]

theorem node40_check : node40 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1894747) entry_1_16) (Integer.Sparse.scale (1697129) entry_1_17) := by decide +kernel

theorem node40_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node40 x = (((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) := by
  rw [node40_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node41 : Integer.Sparse (Fin 2886) := [(83, -27259920), (134, 27259920), (914, -1697683680), (997, 1697683680)]

theorem node41_check : node41 =
    Integer.Sparse.merge (Integer.Sparse.scale (37861) entry_1_18) (Integer.Sparse.scale (-2357894) entry_1_19) := by decide +kernel

theorem node41_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node41 x = (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x) := by
  rw [node41_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node42 : Integer.Sparse (Fin 2886) := [(83, -27259920), (134, 27259920), (860, -1364217840), (893, 1364217840), (900, 1221932880), (914, -1697683680), (975, -1221932880), (997, 1697683680)]

theorem node42_check : node42 =
    Integer.Sparse.merge node40 node41 := by decide +kernel

theorem node42_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node42 x = ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x)) := by
  rw [node42_check, Integer.Sparse.eval_merge]
  rw [node40_eval, node41_eval]

def node43 : Integer.Sparse (Fin 2886) := [(3, -40865760), (83, -27259920), (129, 40865760), (134, 27259920), (635, -47187360), (820, 47187360), (841, -610840800), (860, -1364217840), (893, 1364217840), (900, 1221932880), (914, -1697683680), (949, 610840800), (975, -1221932880), (997, 1697683680)]

theorem node43_check : node43 =
    Integer.Sparse.merge node39 node42 := by decide +kernel

theorem node43_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node43 x = ((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) := by
  rw [node43_check, Integer.Sparse.eval_merge]
  rw [node39_eval, node42_eval]

def node44 : Integer.Sparse (Fin 2886) := [(894, 815181840), (969, 47571120), (1053, -862752960)]

theorem node44_check : node44 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1198268) entry_1_21) (Integer.Sparse.scale (1132197) entry_1_22) := by decide +kernel

theorem node44_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node44 x = (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x) := by
  rw [node44_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node45 : Integer.Sparse (Fin 2886) := [(600, 184731120), (606, -184731120), (894, 815181840), (969, 47571120), (1053, -862752960)]

theorem node45_check : node45 =
    Integer.Sparse.merge (Integer.Sparse.scale (-256571) entry_1_20) node44 := by decide +kernel

theorem node45_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node45 x = (((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) := by
  rw [node45_check, Integer.Sparse.eval_merge]
  rw [node44_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node46 : Integer.Sparse (Fin 2886) := [(192, 323622720), (428, -323622720), (846, -980369280), (954, 980369280)]

theorem node46_check : node46 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1361624) entry_1_23) (Integer.Sparse.scale (449476) entry_1_24) := by decide +kernel

theorem node46_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node46 x = (((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) := by
  rw [node46_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node47 : Integer.Sparse (Fin 2886) := [(437, -148483440), (487, 148483440), (998, -225234720), (1068, 225234720)]

theorem node47_check : node47 =
    Integer.Sparse.merge (Integer.Sparse.scale (312826) entry_1_25) (Integer.Sparse.scale (206227) entry_1_26) := by decide +kernel

theorem node47_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node47 x = (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x) := by
  rw [node47_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node48 : Integer.Sparse (Fin 2886) := [(192, 323622720), (428, -323622720), (437, -148483440), (487, 148483440), (846, -980369280), (954, 980369280), (998, -225234720), (1068, 225234720)]

theorem node48_check : node48 =
    Integer.Sparse.merge node46 node47 := by decide +kernel

theorem node48_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node48 x = ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x)) := by
  rw [node48_check, Integer.Sparse.eval_merge]
  rw [node46_eval, node47_eval]

def node49 : Integer.Sparse (Fin 2886) := [(192, 323622720), (428, -323622720), (437, -148483440), (487, 148483440), (600, 184731120), (606, -184731120), (846, -980369280), (894, 815181840), (954, 980369280), (969, 47571120), (998, -225234720), (1053, -862752960), (1068, 225234720)]

theorem node49_check : node49 =
    Integer.Sparse.merge node45 node48 := by decide +kernel

theorem node49_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node49 x = ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x))) := by
  rw [node49_check, Integer.Sparse.eval_merge]
  rw [node45_eval, node48_eval]

def node50 : Integer.Sparse (Fin 2886) := [(3, -40865760), (83, -27259920), (129, 40865760), (134, 27259920), (192, 323622720), (428, -323622720), (437, -148483440), (487, 148483440), (600, 184731120), (606, -184731120), (635, -47187360), (820, 47187360), (841, -610840800), (846, -980369280), (860, -1364217840), (893, 1364217840), (894, 815181840), (900, 1221932880), (914, -1697683680), (949, 610840800), (954, 980369280), (969, 47571120), (975, -1221932880), (997, 1697683680), (998, -225234720), (1053, -862752960), (1068, 225234720)]

theorem node50_check : node50 =
    Integer.Sparse.merge node43 node49 := by decide +kernel

theorem node50_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node50 x = (((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) + ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x)))) := by
  rw [node50_check, Integer.Sparse.eval_merge]
  rw [node43_eval, node49_eval]

def node51 : Integer.Sparse (Fin 2886) := [(0, 680097600), (3, 147941280), (14, -10347120), (35, -93124080), (75, -680097600), (78, -188807040), (83, -27259920), (90, 68980800), (129, 40865760), (134, 27259920), (179, 10347120), (192, 323622720), (326, -10347120), (329, -598371120), (375, 34490400), (378, 598371120), (428, -323622720), (437, -148483440), (487, 148483440), (600, 184731120), (606, -184731120), (635, -47187360), (820, 47187360), (840, -406750320), (841, -828620640), (842, -78432480), (846, -980369280), (860, -1364217840), (861, -25456320), (893, 441092160), (894, 815181840), (895, 900300960), (900, 1221932880), (914, -1697683680), (948, 406750320), (949, 610840800), (950, -68743440), (954, 185511600), (968, 923125680), (969, 47571120), (970, -1117866960), (975, -1221932880), (997, 1697683680), (998, -225234720), (1043, 217779840), (1044, 794857680), (1053, -862752960), (1068, 225234720), (1091, 147175920), (1095, 243022320)]

theorem node51_check : node51 =
    Integer.Sparse.merge node37 node50 := by decide +kernel

theorem node51_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node51 x = ((((((1103969 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_0 x + (((944580 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_1 x + ((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_2 x)) + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_3 x + (((95477 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_4 x + ((1215062 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_5 x))) + ((((-564931 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_6 x + (((-35356 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_7 x + ((-831071 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_8 x)) + ((((337531 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_9 x + ((-143710 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_10 x) + (((302472 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_11 x + ((204411 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_12 x)))) + (((((-65538 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_13 x + (((56758 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_14 x + ((-848390 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_15 x)) + ((((-1894747 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_16 x + ((1697129 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_17 x) + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_18 x + ((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_19 x))) + ((((-256571 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_20 x + (((-1198268 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_21 x + ((1132197 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_22 x)) + ((((-1361624 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_23 x + ((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_24 x) + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_25 x + ((206227 : ℤ) : ℝ) * Integer.Sparse.eval entry_1_26 x))))) := by
  rw [node51_check, Integer.Sparse.eval_merge]
  rw [node37_eval, node50_eval]

def node52 : Integer.Sparse (Fin 2886) := [(1, 839532288), (3, 188807040), (7, 2308713792), (76, -839532288), (78, -188807040), (82, -2098830720), (133, -699610240), (167, 279844096), (176, 209883072)]

theorem node52_check : node52 =
    Integer.Sparse.merge (Integer.Sparse.scale (262232) entry_2_1) (Integer.Sparse.scale (4372564) entry_2_2) := by decide +kernel

theorem node52_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node52 x = (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x) := by
  rw [node52_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node53 : Integer.Sparse (Fin 2886) := [(1, 839532288), (3, 188807040), (7, 2308713792), (76, -839532288), (78, -188807040), (82, -2098830720), (133, -699610240), (167, 279844096), (176, 209883072), (848, -17601504), (855, 17601504), (956, 105609024), (964, 88007520), (1035, 70406016), (1046, -88007520), (1049, -105609024), (1085, -70406016)]

theorem node53_check : node53 =
    Integer.Sparse.merge (Integer.Sparse.scale (-366698) entry_2_0) node52 := by decide +kernel

theorem node53_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node53 x = (((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) := by
  rw [node53_check, Integer.Sparse.eval_merge]
  rw [node52_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node54 : Integer.Sparse (Fin 2886) := [(843, -78279552), (851, -215268768), (870, -100437984), (884, 100437984), (897, 401751936), (905, 703065888), (937, 401751936), (951, 78279552), (959, 195698880), (972, -401751936), (980, -502189920), (989, -200875968), (1016, -401751936), (1030, 19569888), (1093, 19569888), (1097, -100437984), (1100, 100437984), (1110, -19569888)]

theorem node54_check : node54 =
    Integer.Sparse.merge (Integer.Sparse.scale (-407706) entry_2_4) (Integer.Sparse.scale (2092458) entry_2_5) := by decide +kernel

theorem node54_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node54 x = (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x) := by
  rw [node54_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node55 : Integer.Sparse (Fin 2886) := [(843, -78279552), (851, -215268768), (865, -179105712), (870, -100437984), (880, 179105712), (884, 100437984), (897, 401751936), (899, 1970162832), (905, 703065888), (933, 716422848), (937, 401751936), (951, 78279552), (959, 195698880), (972, -401751936), (974, -1791057120), (980, -502189920), (985, -179105712), (989, -200875968), (1012, -716422848), (1016, -401751936), (1030, 19569888), (1093, 19569888), (1097, -100437984), (1100, 100437984), (1110, -19569888)]

theorem node55_check : node55 =
    Integer.Sparse.merge (Integer.Sparse.scale (3731369) entry_2_3) node54 := by decide +kernel

theorem node55_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node55 x = (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x)) := by
  rw [node55_check, Integer.Sparse.eval_merge]
  rw [node54_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node56 : Integer.Sparse (Fin 2886) := [(1, 839532288), (3, 188807040), (7, 2308713792), (76, -839532288), (78, -188807040), (82, -2098830720), (133, -699610240), (167, 279844096), (176, 209883072), (843, -78279552), (848, -17601504), (851, -215268768), (855, 17601504), (865, -179105712), (870, -100437984), (880, 179105712), (884, 100437984), (897, 401751936), (899, 1970162832), (905, 703065888), (933, 716422848), (937, 401751936), (951, 78279552), (956, 105609024), (959, 195698880), (964, 88007520), (972, -401751936), (974, -1791057120), (980, -502189920), (985, -179105712), (989, -200875968), (1012, -716422848), (1016, -401751936), (1030, 19569888), (1035, 70406016), (1046, -88007520), (1049, -105609024), (1085, -70406016), (1093, 19569888), (1097, -100437984), (1100, 100437984), (1110, -19569888)]

theorem node56_check : node56 =
    Integer.Sparse.merge node53 node55 := by decide +kernel

theorem node56_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node56 x = ((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) := by
  rw [node56_check, Integer.Sparse.eval_merge]
  rw [node53_eval, node55_eval]

def node57 : Integer.Sparse (Fin 2886) := [(16, -58962024), (19, -58962024), (30, -78616032), (37, -412734168), (42, -766506312), (66, -432388176), (91, 314464128), (94, 353772144), (102, 294810120), (121, 294810120), (169, -29481012), (170, -39308016), (174, -39308016), (180, 58962024), (185, 176886072), (191, -39308016), (327, -58962024), (333, -58962024), (376, 157232064), (380, 235848096), (400, 147405060), (423, -58962024), (427, -78616032), (569, -39308016), (574, 176886072), (578, 39308016), (863, 167748864), (870, 335497728), (884, 125811648), (897, -167748864), (905, -335497728), (937, -125811648), (989, -83874432), (1016, 83874432), (1100, -41937216), (1107, 41937216)]

theorem node57_check : node57 =
    Integer.Sparse.merge (Integer.Sparse.scale (873692) entry_2_7) (Integer.Sparse.scale (-2456751) entry_2_8) := by decide +kernel

theorem node57_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node57 x = (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x) := by
  rw [node57_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node58 : Integer.Sparse (Fin 2886) := [(16, -58962024), (19, -58962024), (30, -78616032), (37, -412734168), (42, -766506312), (66, -432388176), (91, 314464128), (94, 353772144), (102, 294810120), (121, 294810120), (169, -29481012), (170, -39308016), (174, -39308016), (180, 58962024), (185, 176886072), (191, -39308016), (327, -58962024), (333, -58962024), (376, 157232064), (380, 235848096), (400, 147405060), (423, -58962024), (427, -78616032), (569, -39308016), (574, 176886072), (578, 39308016), (845, -725058720), (863, 167748864), (870, 335497728), (884, 125811648), (897, -167748864), (905, -335497728), (937, -125811648), (953, 725058720), (989, -83874432), (1016, 83874432), (1100, -41937216), (1107, 41937216)]

theorem node58_check : node58 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1007026) entry_2_6) node57 := by decide +kernel

theorem node58_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node58 x = (((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) := by
  rw [node58_check, Integer.Sparse.eval_merge]
  rw [node57_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node59 : Integer.Sparse (Fin 2886) := [(17, 75033744), (27, -75033744), (39, -825371184), (64, -300134976), (93, 750337440), (99, 75033744), (118, 300134976), (863, -10379664), (870, 10379664), (897, -10379664), (905, 10379664), (972, 20759328), (980, 51898320), (989, 41518656), (1016, 41518656), (1097, -72657648), (1100, -41518656), (1107, -41518656)]

theorem node59_check : node59 =
    Integer.Sparse.merge (Integer.Sparse.scale (-216243) entry_2_9) (Integer.Sparse.scale (-1563203) entry_2_10) := by decide +kernel

theorem node59_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node59 x = (((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) := by
  rw [node59_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node60 : Integer.Sparse (Fin 2886) := [(843, -6153984), (844, -166542768), (849, -666171072), (851, -24615936), (951, 6153984), (952, 166542768), (1028, -166542768), (1030, -6153984), (1047, 666171072), (1083, 166542768), (1093, 24615936), (1110, 6153984)]

theorem node60_check : node60 =
    Integer.Sparse.merge (Integer.Sparse.scale (1156547) entry_2_11) (Integer.Sparse.scale (42736) entry_2_12) := by decide +kernel

theorem node60_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node60 x = (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x) := by
  rw [node60_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node61 : Integer.Sparse (Fin 2886) := [(17, 75033744), (27, -75033744), (39, -825371184), (64, -300134976), (93, 750337440), (99, 75033744), (118, 300134976), (843, -6153984), (844, -166542768), (849, -666171072), (851, -24615936), (863, -10379664), (870, 10379664), (897, -10379664), (905, 10379664), (951, 6153984), (952, 166542768), (972, 20759328), (980, 51898320), (989, 41518656), (1016, 41518656), (1028, -166542768), (1030, -6153984), (1047, 666171072), (1083, 166542768), (1093, 24615936), (1097, -72657648), (1100, -41518656), (1107, -41518656), (1110, 6153984)]

theorem node61_check : node61 =
    Integer.Sparse.merge node59 node60 := by decide +kernel

theorem node61_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node61 x = ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)) := by
  rw [node61_check, Integer.Sparse.eval_merge]
  rw [node59_eval, node60_eval]

def node62 : Integer.Sparse (Fin 2886) := [(16, -58962024), (17, 75033744), (19, -58962024), (27, -75033744), (30, -78616032), (37, -412734168), (39, -825371184), (42, -766506312), (64, -300134976), (66, -432388176), (91, 314464128), (93, 750337440), (94, 353772144), (99, 75033744), (102, 294810120), (118, 300134976), (121, 294810120), (169, -29481012), (170, -39308016), (174, -39308016), (180, 58962024), (185, 176886072), (191, -39308016), (327, -58962024), (333, -58962024), (376, 157232064), (380, 235848096), (400, 147405060), (423, -58962024), (427, -78616032), (569, -39308016), (574, 176886072), (578, 39308016), (843, -6153984), (844, -166542768), (845, -725058720), (849, -666171072), (851, -24615936), (863, 157369200), (870, 345877392), (884, 125811648), (897, -178128528), (905, -325118064), (937, -125811648), (951, 6153984), (952, 166542768), (953, 725058720), (972, 20759328), (980, 51898320), (989, -42355776), (1016, 125393088), (1028, -166542768), (1030, -6153984), (1047, 666171072), (1083, 166542768), (1093, 24615936), (1097, -72657648), (1100, -83455872), (1107, 418560), (1110, 6153984)]

theorem node62_check : node62 =
    Integer.Sparse.merge node58 node61 := by decide +kernel

theorem node62_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node62 x = ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x))) := by
  rw [node62_check, Integer.Sparse.eval_merge]
  rw [node58_eval, node61_eval]

def node63 : Integer.Sparse (Fin 2886) := [(1, 839532288), (3, 188807040), (7, 2308713792), (16, -58962024), (17, 75033744), (19, -58962024), (27, -75033744), (30, -78616032), (37, -412734168), (39, -825371184), (42, -766506312), (64, -300134976), (66, -432388176), (76, -839532288), (78, -188807040), (82, -2098830720), (91, 314464128), (93, 750337440), (94, 353772144), (99, 75033744), (102, 294810120), (118, 300134976), (121, 294810120), (133, -699610240), (167, 279844096), (169, -29481012), (170, -39308016), (174, -39308016), (176, 209883072), (180, 58962024), (185, 176886072), (191, -39308016), (327, -58962024), (333, -58962024), (376, 157232064), (380, 235848096), (400, 147405060), (423, -58962024), (427, -78616032), (569, -39308016), (574, 176886072), (578, 39308016), (843, -84433536), (844, -166542768), (845, -725058720), (848, -17601504), (849, -666171072), (851, -239884704), (855, 17601504), (863, 157369200), (865, -179105712), (870, 245439408), (880, 179105712), (884, 226249632), (897, 223623408), (899, 1970162832), (905, 377947824), (933, 716422848), (937, 275940288), (951, 84433536), (952, 166542768), (953, 725058720), (956, 105609024), (959, 195698880), (964, 88007520), (972, -380992608), (974, -1791057120), (980, -450291600), (985, -179105712), (989, -243231744), (1012, -716422848), (1016, -276358848), (1028, -166542768), (1030, 13415904), (1035, 70406016), (1046, -88007520), (1047, 666171072), (1049, -105609024), (1083, 166542768), (1085, -70406016), (1093, 44185824), (1097, -173095632), (1100, 16982112), (1107, 418560), (1110, -13415904)]

theorem node63_check : node63 =
    Integer.Sparse.merge node56 node62 := by decide +kernel

theorem node63_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node63 x = (((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) + ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)))) := by
  rw [node63_check, Integer.Sparse.eval_merge]
  rw [node56_eval, node62_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
