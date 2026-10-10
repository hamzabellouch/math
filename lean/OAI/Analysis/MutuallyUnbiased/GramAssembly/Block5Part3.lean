import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block5Part2

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block5

def node96 : Integer.Sparse (Fin 2886) := [(447, -1446969600), (449, -4340908800), (478, -1446969600), (547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520), (1758, 6278866560), (1760, 9418299840)]

theorem node96_check : node96 =
    Integer.Sparse.merge (Integer.Sparse.scale (1090081) entry_8_9) node95 := by decide +kernel

theorem node96_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node96 x = (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x)) := by
  rw [node96_check, Integer.Sparse.eval_merge]
  rw [node95_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node97 : Integer.Sparse (Fin 2886) := [(249, 4187833920), (250, 16751335680), (447, -1446969600), (449, -4340908800), (478, -1446969600), (547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520), (1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (1754, 21735855360), (1756, 7245285120), (1758, 6278866560), (1760, 9418299840), (1762, 7245285120)]

theorem node97_check : node97 =
    Integer.Sparse.merge node94 node96 := by decide +kernel

theorem node97_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node97 x = ((((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x))) := by
  rw [node97_check, Integer.Sparse.eval_merge]
  rw [node94_eval, node96_eval]

def node98 : Integer.Sparse (Fin 2886) := [(249, 4187833920), (250, 16751335680), (447, -1446969600), (449, -4340908800), (478, -1446969600), (538, -2279030400), (540, -6837091200), (547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520), (561, -2279030400), (600, 5447082240), (606, 1361770560), (1656, -613356480), (1657, -5098181760), (1658, -1840069440), (1661, -5098181760), (1665, -2437168320), (1667, -4874336640), (1673, -2437168320), (1683, -2437168320), (1689, -613356480), (1691, -2549090880), (1729, -1062829440), (1730, -3188488320), (1749, -1062829440), (1753, 2231884800), (1754, 21735855360), (1756, 7245285120), (1758, 6278866560), (1760, 9418299840), (1762, 7245285120), (1765, 557971200)]

theorem node98_check : node98 =
    Integer.Sparse.merge node92 node97 := by decide +kernel

theorem node98_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node98 x = (((((-212971 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_0 x + (((472837 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_1 x + ((-846239 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_2 x)) + (((193740 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_3 x + (((-791330 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_4 x + ((-885101 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_5 x))) + ((((-369038 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_6 x + (((2515724 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_7 x + ((1454109 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_8 x)) + (((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_9 x + (((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_10 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_8_11 x)))) := by
  rw [node98_check, Integer.Sparse.eval_merge]
  rw [node92_eval, node97_eval]

def node99 : Integer.Sparse (Fin 2886) := [(914, -480375360), (997, -320250240), (2429, -10777608000), (2436, -5388804000), (2460, -5388804000), (2462, -10777608000), (2563, -5388804000), (2565, -10777608000), (2610, -5388804000)]

theorem node99_check : node99 =
    Integer.Sparse.merge (Integer.Sparse.scale (-55599) entry_9_1) (Integer.Sparse.scale (-3742225) entry_9_2) := by decide +kernel

theorem node99_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node99 x = (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x) := by
  rw [node99_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node100 : Integer.Sparse (Fin 2886) := [(914, -480375360), (997, -320250240), (2166, 74001600), (2173, 74001600), (2239, 24667200), (2241, 74001600), (2429, -10777608000), (2436, -5388804000), (2460, -5388804000), (2462, -10777608000), (2563, -5388804000), (2565, -10777608000), (2610, -5388804000)]

theorem node100_check : node100 =
    Integer.Sparse.merge (Integer.Sparse.scale (17130) entry_9_0) node99 := by decide +kernel

theorem node100_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node100 x = (((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) := by
  rw [node100_check, Integer.Sparse.eval_merge]
  rw [node99_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node101 : Integer.Sparse (Fin 2886) := [(918, -20556218880), (926, -20556218880), (1002, -6852072960), (1004, -20556218880), (2170, 1050524640), (2177, 4202098560), (2188, 1050524640), (2245, 2101049280), (2254, 2101049280)]

theorem node101_check : node101 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4758384) entry_9_4) (Integer.Sparse.scale (729531) entry_9_5) := by decide +kernel

theorem node101_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node101 x = (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x) := by
  rw [node101_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node102 : Integer.Sparse (Fin 2886) := [(918, -20556218880), (926, -20556218880), (1002, -6852072960), (1004, -20556218880), (2162, 8641846080), (2170, 1050524640), (2177, 4202098560), (2188, 1050524640), (2235, 4320923040), (2245, 2101049280), (2254, 2101049280), (2776, 17283692160), (2857, 12962769120)]

theorem node102_check : node102 =
    Integer.Sparse.merge (Integer.Sparse.scale (3000641) entry_9_3) node101 := by decide +kernel

theorem node102_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node102 x = (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x)) := by
  rw [node102_check, Integer.Sparse.eval_merge]
  rw [node101_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node103 : Integer.Sparse (Fin 2886) := [(914, -480375360), (918, -20556218880), (926, -20556218880), (997, -320250240), (1002, -6852072960), (1004, -20556218880), (2162, 8641846080), (2166, 74001600), (2170, 1050524640), (2173, 74001600), (2177, 4202098560), (2188, 1050524640), (2235, 4320923040), (2239, 24667200), (2241, 74001600), (2245, 2101049280), (2254, 2101049280), (2429, -10777608000), (2436, -5388804000), (2460, -5388804000), (2462, -10777608000), (2563, -5388804000), (2565, -10777608000), (2610, -5388804000), (2776, 17283692160), (2857, 12962769120)]

theorem node103_check : node103 =
    Integer.Sparse.merge node100 node102 := by decide +kernel

theorem node103_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node103 x = ((((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) := by
  rw [node103_check, Integer.Sparse.eval_merge]
  rw [node100_eval, node102_eval]

def node104 : Integer.Sparse (Fin 2886) := [(1758, 6278866560), (1760, 9418299840), (2425, 25470819360), (2456, 25470819360), (2559, 16980546240), (2608, 6792218496), (2787, 25470819360), (2799, 25470819360), (2834, 33961092480), (2861, 10188327744)]

theorem node104_check : node104 =
    Integer.Sparse.merge (Integer.Sparse.scale (11792046) entry_9_7) (Integer.Sparse.scale (1090081) entry_9_8) := by decide +kernel

theorem node104_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node104 x = (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x) := by
  rw [node104_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node105 : Integer.Sparse (Fin 2886) := [(1758, 6278866560), (1760, 9418299840), (2163, 30366135360), (2172, 30366135360), (2236, 10122045120), (2240, 30366135360), (2425, 25470819360), (2456, 25470819360), (2559, 16980546240), (2608, 6792218496), (2787, 25470819360), (2799, 25470819360), (2834, 33961092480), (2861, 10188327744)]

theorem node105_check : node105 =
    Integer.Sparse.merge (Integer.Sparse.scale (7029198) entry_9_6) node104 := by decide +kernel

theorem node105_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node105 x = (((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) := by
  rw [node105_check, Integer.Sparse.eval_merge]
  rw [node104_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node106 : Integer.Sparse (Fin 2886) := [(1254, 29820369600), (1258, 14910184800), (1278, 14910184800), (1279, 29820369600), (1340, -18173203200), (1345, -18173203200), (1417, 14910184800), (1418, 29820369600), (1455, 14910184800), (1552, -6057734400), (1554, -18173203200)]

theorem node106_check : node106 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4206760) entry_9_10) (Integer.Sparse.scale (10354295) entry_9_11) := by decide +kernel

theorem node106_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node106 x = (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x) := by
  rw [node106_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node107 : Integer.Sparse (Fin 2886) := [(1254, 29820369600), (1258, 14910184800), (1278, 14910184800), (1279, 29820369600), (1340, -18173203200), (1345, -18173203200), (1417, 14910184800), (1418, 29820369600), (1455, 14910184800), (1552, -6057734400), (1554, -18173203200), (2819, 21477804480), (2824, 128866826880), (2839, 64433413440)]

theorem node107_check : node107 =
    Integer.Sparse.merge (Integer.Sparse.scale (14915142) entry_9_9) node106 := by decide +kernel

theorem node107_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node107 x = (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x)) := by
  rw [node107_check, Integer.Sparse.eval_merge]
  rw [node106_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node108 : Integer.Sparse (Fin 2886) := [(1254, 29820369600), (1258, 14910184800), (1278, 14910184800), (1279, 29820369600), (1340, -18173203200), (1345, -18173203200), (1417, 14910184800), (1418, 29820369600), (1455, 14910184800), (1552, -6057734400), (1554, -18173203200), (1758, 6278866560), (1760, 9418299840), (2163, 30366135360), (2172, 30366135360), (2236, 10122045120), (2240, 30366135360), (2425, 25470819360), (2456, 25470819360), (2559, 16980546240), (2608, 6792218496), (2787, 25470819360), (2799, 25470819360), (2819, 21477804480), (2824, 128866826880), (2834, 33961092480), (2839, 64433413440), (2861, 10188327744)]

theorem node108_check : node108 =
    Integer.Sparse.merge node105 node107 := by decide +kernel

theorem node108_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node108 x = ((((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x))) := by
  rw [node108_check, Integer.Sparse.eval_merge]
  rw [node105_eval, node107_eval]

def node109 : Integer.Sparse (Fin 2886) := [(914, -480375360), (918, -20556218880), (926, -20556218880), (997, -320250240), (1002, -6852072960), (1004, -20556218880), (1254, 29820369600), (1258, 14910184800), (1278, 14910184800), (1279, 29820369600), (1340, -18173203200), (1345, -18173203200), (1417, 14910184800), (1418, 29820369600), (1455, 14910184800), (1552, -6057734400), (1554, -18173203200), (1758, 6278866560), (1760, 9418299840), (2162, 8641846080), (2163, 30366135360), (2166, 74001600), (2170, 1050524640), (2172, 30366135360), (2173, 74001600), (2177, 4202098560), (2188, 1050524640), (2235, 4320923040), (2236, 10122045120), (2239, 24667200), (2240, 30366135360), (2241, 74001600), (2245, 2101049280), (2254, 2101049280), (2425, 25470819360), (2429, -10777608000), (2436, -5388804000), (2456, 25470819360), (2460, -5388804000), (2462, -10777608000), (2559, 16980546240), (2563, -5388804000), (2565, -10777608000), (2608, 6792218496), (2610, -5388804000), (2776, 17283692160), (2787, 25470819360), (2799, 25470819360), (2819, 21477804480), (2824, 128866826880), (2834, 33961092480), (2839, 64433413440), (2857, 12962769120), (2861, 10188327744)]

theorem node109_check : node109 =
    Integer.Sparse.merge node103 node108 := by decide +kernel

theorem node109_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node109 x = (((((17130 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_0 x + (((-55599 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_1 x + ((-3742225 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_2 x)) + (((3000641 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_3 x + (((-4758384 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_4 x + ((729531 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_5 x))) + ((((7029198 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_6 x + (((11792046 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_7 x + ((1090081 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_8 x)) + (((14915142 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_9 x + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_10 x + ((10354295 : ℤ) : ℝ) * Integer.Sparse.eval entry_9_11 x)))) := by
  rw [node109_check, Integer.Sparse.eval_merge]
  rw [node103_eval, node108_eval]

def node110 : Integer.Sparse (Fin 2886) := [(195, -1589368320), (431, -4768104960), (479, -1589368320), (1212, 681296400), (1217, 1362592800), (1226, 681296400), (1324, 681296400), (1330, 1362592800), (1351, 681296400), (1530, 1362592800), (1535, 1362592800), (1542, 1362592800), (1560, 1362592800), (1734, 1362592800), (1737, 681296400), (1745, 681296400)]

theorem node110_check : node110 =
    Integer.Sparse.merge (Integer.Sparse.scale (-551864) entry_10_1) (Integer.Sparse.scale (946245) entry_10_2) := by decide +kernel

theorem node110_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node110 x = (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x) := by
  rw [node110_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node111 : Integer.Sparse (Fin 2886) := [(195, -1589368320), (431, -4768104960), (479, -1589368320), (1133, 662273280), (1138, 1986819840), (1212, 681296400), (1217, 1362592800), (1226, 681296400), (1324, 681296400), (1330, 1362592800), (1351, 681296400), (1516, 1986819840), (1521, 3973639680), (1530, 1362592800), (1535, 1362592800), (1542, 1362592800), (1560, 1362592800), (1569, 1986819840), (1730, 1986819840), (1734, 1362592800), (1737, 681296400), (1745, 681296400), (1749, 662273280)]

theorem node111_check : node111 =
    Integer.Sparse.merge (Integer.Sparse.scale (919824) entry_10_0) node110 := by decide +kernel

theorem node111_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node111 x = (((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) := by
  rw [node111_check, Integer.Sparse.eval_merge]
  rw [node110_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node112 : Integer.Sparse (Fin 2886) := [(193, 821512800), (197, 2464538400), (429, 2464538400), (434, 4929076800), (481, 2464538400), (579, 2464538400), (596, 821512800), (1137, 1967153760), (1142, 1967153760), (1520, 3934307520), (1526, 1967153760), (1574, 1967153760), (1657, 1967153760), (1661, 3934307520), (1691, 1967153760)]

theorem node112_check : node112 =
    Integer.Sparse.merge (Integer.Sparse.scale (1140990) entry_10_4) (Integer.Sparse.scale (1366079) entry_10_5) := by decide +kernel

theorem node112_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node112 x = (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x) := by
  rw [node112_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node113 : Integer.Sparse (Fin 2886) := [(193, 821512800), (197, 2464538400), (429, 2464538400), (434, 4929076800), (481, 2464538400), (579, 2464538400), (596, 821512800), (1135, -1548334080), (1137, 1967153760), (1142, 1967153760), (1518, -4645002240), (1520, 3934307520), (1526, 1967153760), (1568, -1548334080), (1574, 1967153760), (1657, 1967153760), (1661, 3934307520), (1691, 1967153760)]

theorem node113_check : node113 =
    Integer.Sparse.merge (Integer.Sparse.scale (-537616) entry_10_3) node112 := by decide +kernel

theorem node113_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node113 x = (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x)) := by
  rw [node113_check, Integer.Sparse.eval_merge]
  rw [node112_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node114 : Integer.Sparse (Fin 2886) := [(193, 821512800), (195, -1589368320), (197, 2464538400), (429, 2464538400), (431, -4768104960), (434, 4929076800), (479, -1589368320), (481, 2464538400), (579, 2464538400), (596, 821512800), (1133, 662273280), (1135, -1548334080), (1137, 1967153760), (1138, 1986819840), (1142, 1967153760), (1212, 681296400), (1217, 1362592800), (1226, 681296400), (1324, 681296400), (1330, 1362592800), (1351, 681296400), (1516, 1986819840), (1518, -4645002240), (1520, 3934307520), (1521, 3973639680), (1526, 1967153760), (1530, 1362592800), (1535, 1362592800), (1542, 1362592800), (1560, 1362592800), (1568, -1548334080), (1569, 1986819840), (1574, 1967153760), (1657, 1967153760), (1661, 3934307520), (1691, 1967153760), (1730, 1986819840), (1734, 1362592800), (1737, 681296400), (1745, 681296400), (1749, 662273280)]

theorem node114_check : node114 =
    Integer.Sparse.merge node111 node113 := by decide +kernel

theorem node114_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node114 x = ((((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) := by
  rw [node114_check, Integer.Sparse.eval_merge]
  rw [node111_eval, node113_eval]

def node115 : Integer.Sparse (Fin 2886) := [(447, -1446969600), (449, -4340908800), (478, -1446969600), (1214, -12324465360), (1224, -4108155120), (1326, -12324465360), (1349, -4108155120), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360)]

theorem node115_check : node115 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5705771) entry_10_7) (Integer.Sparse.scale (-502420) entry_10_8) := by decide +kernel

theorem node115_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node115 x = (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x) := by
  rw [node115_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node116 : Integer.Sparse (Fin 2886) := [(447, -1446969600), (449, -4340908800), (478, -1446969600), (1134, -107600400), (1138, -322801200), (1214, -12324465360), (1224, -4108155120), (1326, -12324465360), (1349, -4108155120), (1517, -322801200), (1521, -645602400), (1532, -24648930720), (1540, -12324465360), (1558, -12324465360), (1569, -322801200), (1658, -322801200), (1689, -107600400)]

theorem node116_check : node116 =
    Integer.Sparse.merge (Integer.Sparse.scale (-149445) entry_10_6) node115 := by decide +kernel

theorem node116_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node116 x = (((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) := by
  rw [node116_check, Integer.Sparse.eval_merge]
  rw [node115_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node117 : Integer.Sparse (Fin 2886) := [(241, -2925531360), (244, -5851062720), (249, 2572848000), (250, 7718544000), (253, -2925531360), (303, -2925531360), (306, -5851062720), (322, -2925531360), (442, -5851062720), (444, -5851062720), (447, 7718544000), (449, 15437088000), (454, -5851062720), (472, -5851062720), (478, 10291392000), (582, -5851062720), (585, 5145696000), (586, -2925531360), (592, -2925531360), (595, 2572848000)]

theorem node117_check : node117 =
    Integer.Sparse.merge (Integer.Sparse.scale (3573400) entry_10_10) (Integer.Sparse.scale (-4063238) entry_10_11) := by decide +kernel

theorem node117_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node117 x = (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x) := by
  rw [node117_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node118 : Integer.Sparse (Fin 2886) := [(241, -2925531360), (244, -5851062720), (249, 2572848000), (250, 7718544000), (253, -2925531360), (303, -2925531360), (306, -5851062720), (322, -2925531360), (442, -5851062720), (444, -5851062720), (447, 7718544000), (449, 15437088000), (454, -5851062720), (472, -5851062720), (478, 10291392000), (582, -5851062720), (585, 5145696000), (586, -2925531360), (592, -2925531360), (595, 2572848000), (1340, -18173203200), (1345, -18173203200), (1552, -6057734400), (1554, -18173203200)]

theorem node118_check : node118 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4206760) entry_10_9) node117 := by decide +kernel

theorem node118_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node118 x = (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x)) := by
  rw [node118_check, Integer.Sparse.eval_merge]
  rw [node117_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node119 : Integer.Sparse (Fin 2886) := [(241, -2925531360), (244, -5851062720), (249, 2572848000), (250, 7718544000), (253, -2925531360), (303, -2925531360), (306, -5851062720), (322, -2925531360), (442, -5851062720), (444, -5851062720), (447, 6271574400), (449, 11096179200), (454, -5851062720), (472, -5851062720), (478, 8844422400), (582, -5851062720), (585, 5145696000), (586, -2925531360), (592, -2925531360), (595, 2572848000), (1134, -107600400), (1138, -322801200), (1214, -12324465360), (1224, -4108155120), (1326, -12324465360), (1340, -18173203200), (1345, -18173203200), (1349, -4108155120), (1517, -322801200), (1521, -645602400), (1532, -24648930720), (1540, -12324465360), (1552, -6057734400), (1554, -18173203200), (1558, -12324465360), (1569, -322801200), (1658, -322801200), (1689, -107600400)]

theorem node119_check : node119 =
    Integer.Sparse.merge node116 node118 := by decide +kernel

theorem node119_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node119 x = ((((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x))) := by
  rw [node119_check, Integer.Sparse.eval_merge]
  rw [node116_eval, node118_eval]

def node120 : Integer.Sparse (Fin 2886) := [(193, 821512800), (195, -1589368320), (197, 2464538400), (241, -2925531360), (244, -5851062720), (249, 2572848000), (250, 7718544000), (253, -2925531360), (303, -2925531360), (306, -5851062720), (322, -2925531360), (429, 2464538400), (431, -4768104960), (434, 4929076800), (442, -5851062720), (444, -5851062720), (447, 6271574400), (449, 11096179200), (454, -5851062720), (472, -5851062720), (478, 8844422400), (479, -1589368320), (481, 2464538400), (579, 2464538400), (582, -5851062720), (585, 5145696000), (586, -2925531360), (592, -2925531360), (595, 2572848000), (596, 821512800), (1133, 662273280), (1134, -107600400), (1135, -1548334080), (1137, 1967153760), (1138, 1664018640), (1142, 1967153760), (1212, 681296400), (1214, -12324465360), (1217, 1362592800), (1224, -4108155120), (1226, 681296400), (1324, 681296400), (1326, -12324465360), (1330, 1362592800), (1340, -18173203200), (1345, -18173203200), (1349, -4108155120), (1351, 681296400), (1516, 1986819840), (1517, -322801200), (1518, -4645002240), (1520, 3934307520), (1521, 3328037280), (1526, 1967153760), (1530, 1362592800), (1532, -24648930720), (1535, 1362592800), (1540, -12324465360), (1542, 1362592800), (1552, -6057734400), (1554, -18173203200), (1558, -12324465360), (1560, 1362592800), (1568, -1548334080), (1569, 1664018640), (1574, 1967153760), (1657, 1967153760), (1658, -322801200), (1661, 3934307520), (1689, -107600400), (1691, 1967153760), (1730, 1986819840), (1734, 1362592800), (1737, 681296400), (1745, 681296400), (1749, 662273280)]

theorem node120_check : node120 =
    Integer.Sparse.merge node114 node119 := by decide +kernel

theorem node120_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node120 x = (((((919824 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_0 x + (((-551864 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_1 x + ((946245 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_2 x)) + (((-537616 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_3 x + (((1140990 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_4 x + ((1366079 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_5 x))) + ((((-149445 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_6 x + (((-5705771 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_7 x + ((-502420 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_8 x)) + (((-4206760 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_9 x + (((3573400 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_10 x + ((-4063238 : ℤ) : ℝ) * Integer.Sparse.eval entry_10_11 x)))) := by
  rw [node120_check, Integer.Sparse.eval_merge]
  rw [node114_eval, node119_eval]

def node121 : Integer.Sparse (Fin 2886) := [(181, -2131646400), (329, -2131646400), (378, -4263292800), (396, -2131646400), (1149, -532194480), (1157, -1064388960), (1168, -1064388960), (1176, -1064388960), (1183, -1064388960), (1206, -1064388960), (1209, -532194480), (1235, -532194480), (1243, -1064388960), (1262, -1064388960), (1270, -1064388960), (1287, -1064388960), (1313, -1064388960), (1321, -532194480), (1377, -1064388960), (1385, -1064388960), (1393, -1064388960), (1403, -1064388960), (1411, -1064388960), (1426, -1064388960), (1445, -1064388960), (1453, -1064388960), (1461, -1064388960), (1504, -1064388960), (1506, -1064388960), (1511, -1064388960), (1701, -1064388960), (1704, -532194480), (1708, -1064388960), (1713, -532194480), (1719, -1064388960), (1721, -1064388960), (1726, -1064388960)]

theorem node121_check : node121 =
    Integer.Sparse.merge (Integer.Sparse.scale (-740155) entry_11_1) (Integer.Sparse.scale (-2217477) entry_11_2) := by decide +kernel

theorem node121_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node121 x = (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x) := by
  rw [node121_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node122 : Integer.Sparse (Fin 2886) := [(181, -2131646400), (329, -2131646400), (378, -4263292800), (396, -2131646400), (1115, -301018320), (1121, -602036640), (1131, -301018320), (1149, -532194480), (1157, -1064388960), (1168, -1064388960), (1176, -1064388960), (1183, -1064388960), (1206, -1064388960), (1209, -532194480), (1235, -532194480), (1243, -1064388960), (1262, -1064388960), (1270, -1064388960), (1287, -1064388960), (1313, -1064388960), (1321, -532194480), (1362, -301018320), (1370, -602036640), (1377, -1064388960), (1385, -1064388960), (1393, -1064388960), (1403, -1064388960), (1411, -1064388960), (1426, -1064388960), (1435, -602036640), (1441, -602036640), (1445, -1064388960), (1453, -1064388960), (1461, -1064388960), (1466, -602036640), (1501, -602036640), (1504, -1064388960), (1506, -1064388960), (1511, -1064388960), (1514, -301018320), (1698, -301018320), (1701, -1064388960), (1704, -532194480), (1708, -1064388960), (1713, -532194480), (1716, -602036640), (1719, -1064388960), (1721, -1064388960), (1726, -1064388960), (1728, -301018320)]

theorem node122_check : node122 =
    Integer.Sparse.merge (Integer.Sparse.scale (-418081) entry_11_0) node121 := by decide +kernel

theorem node122_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node122 x = (((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) := by
  rw [node122_check, Integer.Sparse.eval_merge]
  rw [node121_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node123 : Integer.Sparse (Fin 2886) := [(16, -1325479320), (19, -2650958640), (30, -1767305760), (37, -1325479320), (42, -2650958640), (66, -1767305760), (91, -1767305760), (94, -2120766912), (102, -2650958640), (121, -2650958640), (169, -1325479320), (170, -883652880), (174, -883652880), (180, -1325479320), (185, -2650958640), (191, -883652880), (327, -1325479320), (333, -2650958640), (376, -3534611520), (380, -3181150368), (400, -3976437960), (423, -2650958640), (427, -1767305760), (569, -883652880), (574, -2650958640), (578, -1767305760), (1119, -771840), (1123, -385920), (1126, -385920), (1129, -771840), (1367, -771840), (1372, -385920), (1439, -771840), (1468, -385920), (1472, -771840), (1475, -771840), (1498, -771840), (1582, -385920), (1585, -771840), (1620, -771840), (1623, -771840), (1644, -771840), (1647, -771840), (1655, -385920)]

theorem node123_check : node123 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3681887) entry_11_4) (Integer.Sparse.scale (-804) entry_11_5) := by decide +kernel

theorem node123_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node123 x = (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x) := by
  rw [node123_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node124 : Integer.Sparse (Fin 2886) := [(16, -1325479320), (19, -2650958640), (30, -1767305760), (37, -1325479320), (42, -2650958640), (66, -1767305760), (91, -1767305760), (94, -2120766912), (102, -2650958640), (121, -2650958640), (169, -1325479320), (170, -883652880), (174, -883652880), (180, -1325479320), (185, -2650958640), (191, -883652880), (327, -1325479320), (333, -2650958640), (376, -3534611520), (380, -3181150368), (400, -3976437960), (423, -2650958640), (427, -1767305760), (569, -883652880), (574, -2650958640), (578, -1767305760), (1117, 6115821120), (1119, -771840), (1123, -385920), (1126, -385920), (1129, -771840), (1364, 6115821120), (1367, -771840), (1372, -385920), (1437, 12231642240), (1439, -771840), (1462, 6115821120), (1468, -385920), (1472, -771840), (1475, -771840), (1498, -771840), (1582, -385920), (1585, -771840), (1620, -771840), (1623, -771840), (1644, -771840), (1647, -771840), (1655, -385920)]

theorem node124_check : node124 =
    Integer.Sparse.merge (Integer.Sparse.scale (2123549) entry_11_3) node123 := by decide +kernel

theorem node124_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node124 x = (((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x)) := by
  rw [node124_check, Integer.Sparse.eval_merge]
  rw [node123_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node125 : Integer.Sparse (Fin 2886) := [(16, -1325479320), (19, -2650958640), (30, -1767305760), (37, -1325479320), (42, -2650958640), (66, -1767305760), (91, -1767305760), (94, -2120766912), (102, -2650958640), (121, -2650958640), (169, -1325479320), (170, -883652880), (174, -883652880), (180, -1325479320), (181, -2131646400), (185, -2650958640), (191, -883652880), (327, -1325479320), (329, -2131646400), (333, -2650958640), (376, -3534611520), (378, -4263292800), (380, -3181150368), (396, -2131646400), (400, -3976437960), (423, -2650958640), (427, -1767305760), (569, -883652880), (574, -2650958640), (578, -1767305760), (1115, -301018320), (1117, 6115821120), (1119, -771840), (1121, -602036640), (1123, -385920), (1126, -385920), (1129, -771840), (1131, -301018320), (1149, -532194480), (1157, -1064388960), (1168, -1064388960), (1176, -1064388960), (1183, -1064388960), (1206, -1064388960), (1209, -532194480), (1235, -532194480), (1243, -1064388960), (1262, -1064388960), (1270, -1064388960), (1287, -1064388960), (1313, -1064388960), (1321, -532194480), (1362, -301018320), (1364, 6115821120), (1367, -771840), (1370, -602036640), (1372, -385920), (1377, -1064388960), (1385, -1064388960), (1393, -1064388960), (1403, -1064388960), (1411, -1064388960), (1426, -1064388960), (1435, -602036640), (1437, 12231642240), (1439, -771840), (1441, -602036640), (1445, -1064388960), (1453, -1064388960), (1461, -1064388960), (1462, 6115821120), (1466, -602036640), (1468, -385920), (1472, -771840), (1475, -771840), (1498, -771840), (1501, -602036640), (1504, -1064388960), (1506, -1064388960), (1511, -1064388960), (1514, -301018320), (1582, -385920), (1585, -771840), (1620, -771840), (1623, -771840), (1644, -771840), (1647, -771840), (1655, -385920), (1698, -301018320), (1701, -1064388960), (1704, -532194480), (1708, -1064388960), (1713, -532194480), (1716, -602036640), (1719, -1064388960), (1721, -1064388960), (1726, -1064388960), (1728, -301018320)]

theorem node125_check : node125 =
    Integer.Sparse.merge node122 node124 := by decide +kernel

theorem node125_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node125 x = ((((-418081 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_0 x + (((-740155 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_1 x + ((-2217477 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_2 x)) + (((2123549 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_3 x + (((-3681887 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_4 x + ((-804 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_5 x))) := by
  rw [node125_check, Integer.Sparse.eval_merge]
  rw [node122_eval, node124_eval]

def node126 : Integer.Sparse (Fin 2886) := [(547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520), (1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800)]

theorem node126_check : node126 =
    Integer.Sparse.merge (Integer.Sparse.scale (8194820) entry_11_7) (Integer.Sparse.scale (-325129) entry_11_8) := by decide +kernel

theorem node126_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node126 x = (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x) := by
  rw [node126_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node127 : Integer.Sparse (Fin 2886) := [(547, -936371520), (548, -1872743040), (550, -936371520), (558, -936371520), (1116, 3831340320), (1120, 7662680640), (1127, 3831340320), (1151, 5900270400), (1170, 11800540800), (1179, 5900270400), (1237, 5900270400), (1264, 11800540800), (1283, 5900270400), (1363, 3831340320), (1368, 7662680640), (1379, 11800540800), (1389, 5900270400), (1405, 11800540800), (1422, 5900270400), (1436, 7662680640), (1440, 7662680640), (1447, 11800540800), (1449, 11800540800), (1457, 11800540800), (1464, 7662680640), (1473, 7662680640), (1496, 3831340320), (1583, 3831340320), (1621, 7662680640), (1642, 3831340320)]

theorem node127_check : node127 =
    Integer.Sparse.merge (Integer.Sparse.scale (5321306) entry_11_6) node126 := by decide +kernel

theorem node127_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node127 x = (((5321306 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_6 x + (((8194820 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_7 x + ((-325129 : ℤ) : ℝ) * Integer.Sparse.eval entry_11_8 x)) := by
  rw [node127_check, Integer.Sparse.eval_merge]
  rw [node126_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block5

end OAI
