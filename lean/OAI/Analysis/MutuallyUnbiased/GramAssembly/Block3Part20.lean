import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part19

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node640 : Integer.Sparse (Fin 2886) := [(105, 2484252000), (137, -2484252000), (1211, -2167367040), (1323, 2167367040), (1329, 807343920), (1338, 1283548320), (1534, -807343920), (1549, -1283548320)]

theorem node640_check : node640 =
    Integer.Sparse.merge node638 node639 := by decide +kernel

theorem node640_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node640 x = ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x)) := by
  rw [node640_check, Integer.Sparse.eval_merge]
  rw [node638_eval, node639_eval]

def node641 : Integer.Sparse (Fin 2886) := [(26, 76381920), (105, 2484252000), (128, -76381920), (137, -2484252000), (657, 362783520), (807, -362783520), (1133, -460473120), (1211, -2167367040), (1323, 2167367040), (1329, 807343920), (1338, 1283548320), (1516, 460473120), (1534, -807343920), (1549, -1283548320)]

theorem node641_check : node641 =
    Integer.Sparse.merge node637 node640 := by decide +kernel

theorem node641_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node641 x = ((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) := by
  rw [node641_check, Integer.Sparse.eval_merge]
  rw [node637_eval, node640_eval]

def node642 : Integer.Sparse (Fin 2886) := [(1324, 5066804160), (1530, -4851463680), (1665, -215340480)]

theorem node642_check : node642 =
    Integer.Sparse.merge (Integer.Sparse.scale (-299084) entry_24_21) (Integer.Sparse.scale (7037228) entry_24_22) := by decide +kernel

theorem node642_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node642 x = (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x) := by
  rw [node642_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node643 : Integer.Sparse (Fin 2886) := [(585, -168154560), (595, 168154560), (1324, 5066804160), (1530, -4851463680), (1665, -215340480)]

theorem node643_check : node643 =
    Integer.Sparse.merge (Integer.Sparse.scale (233548) entry_24_20) node642 := by decide +kernel

theorem node643_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node643 x = (((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) := by
  rw [node643_check, Integer.Sparse.eval_merge]
  rw [node642_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node644 : Integer.Sparse (Fin 2886) := [(249, 1814812560), (447, -1814812560), (1137, 339840), (1520, -339840)]

theorem node644_check : node644 =
    Integer.Sparse.merge (Integer.Sparse.scale (472) entry_24_23) (Integer.Sparse.scale (2520573) entry_24_24) := by decide +kernel

theorem node644_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node644 x = (((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) := by
  rw [node644_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node645 : Integer.Sparse (Fin 2886) := [(458, 926922240), (485, -926922240), (1550, 2389706640), (1679, -2389706640)]

theorem node645_check : node645 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3319037) entry_24_25) (Integer.Sparse.scale (-1287392) entry_24_26) := by decide +kernel

theorem node645_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node645 x = (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x) := by
  rw [node645_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node646 : Integer.Sparse (Fin 2886) := [(249, 1814812560), (447, -1814812560), (458, 926922240), (485, -926922240), (1137, 339840), (1520, -339840), (1550, 2389706640), (1679, -2389706640)]

theorem node646_check : node646 =
    Integer.Sparse.merge node644 node645 := by decide +kernel

theorem node646_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node646 x = ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x)) := by
  rw [node646_check, Integer.Sparse.eval_merge]
  rw [node644_eval, node645_eval]

def node647 : Integer.Sparse (Fin 2886) := [(249, 1814812560), (447, -1814812560), (458, 926922240), (485, -926922240), (585, -168154560), (595, 168154560), (1137, 339840), (1324, 5066804160), (1520, -339840), (1530, -4851463680), (1550, 2389706640), (1665, -215340480), (1679, -2389706640)]

theorem node647_check : node647 =
    Integer.Sparse.merge node643 node646 := by decide +kernel

theorem node647_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node647 x = ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x))) := by
  rw [node647_check, Integer.Sparse.eval_merge]
  rw [node643_eval, node646_eval]

def node648 : Integer.Sparse (Fin 2886) := [(26, 76381920), (105, 2484252000), (128, -76381920), (137, -2484252000), (249, 1814812560), (447, -1814812560), (458, 926922240), (485, -926922240), (585, -168154560), (595, 168154560), (657, 362783520), (807, -362783520), (1133, -460473120), (1137, 339840), (1211, -2167367040), (1323, 2167367040), (1324, 5066804160), (1329, 807343920), (1338, 1283548320), (1516, 460473120), (1520, -339840), (1530, -4851463680), (1534, -807343920), (1549, -1283548320), (1550, 2389706640), (1665, -215340480), (1679, -2389706640)]

theorem node648_check : node648 =
    Integer.Sparse.merge node641 node647 := by decide +kernel

theorem node648_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node648 x = (((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) + ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x)))) := by
  rw [node648_check, Integer.Sparse.eval_merge]
  rw [node641_eval, node647_eval]

def node649 : Integer.Sparse (Fin 2886) := [(26, -13275360), (98, 89657280), (105, 2484252000), (128, -76381920), (137, -2484252000), (192, 323622720), (249, 1814812560), (302, 1576275840), (347, 2099803680), (387, -2099803680), (428, -323622720), (441, -1576275840), (447, -1814812560), (458, 926922240), (485, -926922240), (585, -168154560), (595, 168154560), (657, 362783520), (807, -362783520), (1132, -336582000), (1133, -2256103440), (1134, 220646880), (1137, 339840), (1211, -2167367040), (1213, -1241195760), (1323, 3050947440), (1324, 5066804160), (1325, 1686981600), (1329, 807343920), (1338, 1283548320), (1515, 336582000), (1516, 460473120), (1517, -1068150240), (1520, -1876092480), (1529, -883580400), (1530, -4851463680), (1531, -2109233520), (1534, -807343920), (1549, -1283548320), (1550, 2389706640), (1656, 1795630320), (1657, 1875752640), (1665, -215340480), (1679, -2389706640), (1729, 847503360), (1733, 1663447680)]

theorem node649_check : node649 =
    Integer.Sparse.merge node635 node648 := by decide +kernel

theorem node649_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node649 x = ((((((2605212 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_0 x + (((449476 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_1 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_2 x)) + (((1227195 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_3 x + (((1483542 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_4 x + ((619147 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_5 x))) + ((((-467475 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_6 x + (((-1723883 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_7 x + ((2916394 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_8 x)) + ((((2310344 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_9 x + ((2189272 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_10 x) + (((2493931 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_11 x + ((1177088 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_12 x)))) + (((((503866 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_13 x + (((-106086 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_14 x + ((-639546 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_15 x)) + ((((-3010232 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_16 x + ((1121311 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_17 x) + (((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_18 x + ((1782706 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_19 x))) + ((((233548 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_20 x + (((-299084 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_21 x + ((7037228 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_22 x)) + ((((472 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_23 x + ((2520573 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_24 x) + (((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_25 x + ((-1287392 : ℤ) : ℝ) * Integer.Sparse.eval entry_24_26 x))))) := by
  rw [node649_check, Integer.Sparse.eval_merge]
  rw [node635_eval, node648_eval]

def node650 : Integer.Sparse (Fin 2886) := [(917, 846175680), (920, -846175680), (998, -225234720), (1001, -846175680), (1006, -3384702720), (1068, 225234720), (1070, 846175680), (1072, 3384702720)]

theorem node650_check : node650 =
    Integer.Sparse.merge (Integer.Sparse.scale (312826) entry_25_1) (Integer.Sparse.scale (5876220) entry_25_2) := by decide +kernel

theorem node650_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node650 x = (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x) := by
  rw [node650_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node651 : Integer.Sparse (Fin 2886) := [(917, 846175680), (920, -846175680), (998, -225234720), (1001, -846175680), (1006, -3384702720), (1068, 225234720), (1070, 846175680), (1072, 3384702720), (2178, -5732563392), (2179, 5732563392), (2246, -1433140848), (2258, 1433140848), (2300, 1433140848), (2306, -1433140848)]

theorem node651_check : node651 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9952367) entry_25_0) node650 := by decide +kernel

theorem node651_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node651 x = (((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) := by
  rw [node651_check, Integer.Sparse.eval_merge]
  rw [node650_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node652 : Integer.Sparse (Fin 2886) := [(2165, -160253568), (2168, 160253568), (2238, 160253568), (2243, 641014272), (2297, -160253568), (2299, -641014272), (2428, 125228016), (2431, -125228016), (2459, -125228016), (2464, -375684048), (2489, 125228016), (2491, 375684048), (2567, -125228016), (2647, 125228016), (2702, 125228016), (2725, -125228016)]

theorem node652_check : node652 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1112872) entry_25_4) (Integer.Sparse.scale (869639) entry_25_5) := by decide +kernel

theorem node652_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node652 x = (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x) := by
  rw [node652_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node653 : Integer.Sparse (Fin 2886) := [(2165, -160253568), (2168, 160253568), (2238, 160253568), (2243, 641014272), (2297, -160253568), (2299, -641014272), (2428, 125228016), (2431, -125228016), (2459, -125228016), (2464, -375684048), (2489, 125228016), (2491, 375684048), (2567, -125228016), (2647, 125228016), (2702, 125228016), (2725, -125228016), (2800, -1724050368), (2804, 1724050368), (2835, -431012592), (2841, 431012592), (2862, 431012592), (2864, -431012592)]

theorem node653_check : node653 =
    Integer.Sparse.merge (Integer.Sparse.scale (2993143) entry_25_3) node652 := by decide +kernel

theorem node653_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node653 x = (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x)) := by
  rw [node653_check, Integer.Sparse.eval_merge]
  rw [node652_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node654 : Integer.Sparse (Fin 2886) := [(917, 846175680), (920, -846175680), (998, -225234720), (1001, -846175680), (1006, -3384702720), (1068, 225234720), (1070, 846175680), (1072, 3384702720), (2165, -160253568), (2168, 160253568), (2178, -5732563392), (2179, 5732563392), (2238, 160253568), (2243, 641014272), (2246, -1433140848), (2258, 1433140848), (2297, -160253568), (2299, -641014272), (2300, 1433140848), (2306, -1433140848), (2428, 125228016), (2431, -125228016), (2459, -125228016), (2464, -375684048), (2489, 125228016), (2491, 375684048), (2567, -125228016), (2647, 125228016), (2702, 125228016), (2725, -125228016), (2800, -1724050368), (2804, 1724050368), (2835, -431012592), (2841, 431012592), (2862, 431012592), (2864, -431012592)]

theorem node654_check : node654 =
    Integer.Sparse.merge node651 node653 := by decide +kernel

theorem node654_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node654 x = ((((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x))) := by
  rw [node654_check, Integer.Sparse.eval_merge]
  rw [node651_eval, node653_eval]

def node655 : Integer.Sparse (Fin 2886) := [(1253, -1504600560), (1255, 1504600560), (1277, 1504600560), (1280, 4513801680), (1303, -1504600560), (1304, -4513801680), (1419, 1504600560), (1488, -1504600560), (1611, -1504600560), (1635, 1504600560), (2459, 616963968), (2464, 1233927936), (2489, -616963968), (2491, -1233927936), (2562, -616963968), (2567, -1233927936), (2647, -1233927936), (2700, 616963968), (2702, 1233927936), (2725, 1233927936)]

theorem node655_check : node655 =
    Integer.Sparse.merge (Integer.Sparse.scale (4284472) entry_25_7) (Integer.Sparse.scale (-10448615) entry_25_8) := by decide +kernel

theorem node655_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node655 x = (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x) := by
  rw [node655_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node656 : Integer.Sparse (Fin 2886) := [(1253, -1504600560), (1255, 1504600560), (1277, 1504600560), (1280, 4513801680), (1303, -1504600560), (1304, -4513801680), (1419, 1504600560), (1488, -1504600560), (1611, -1504600560), (1635, 1504600560), (2459, 616963968), (2464, 1233927936), (2489, -616963968), (2491, -1233927936), (2562, -616963968), (2567, -1233927936), (2647, -1233927936), (2700, 616963968), (2702, 1233927936), (2725, 1233927936), (2858, 1420727760), (2866, -1420727760)]

theorem node656_check : node656 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1973233) entry_25_6) node655 := by decide +kernel

theorem node656_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node656 x = (((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) := by
  rw [node656_check, Integer.Sparse.eval_merge]
  rw [node655_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node657 : Integer.Sparse (Fin 2886) := [(1274, 5531296320), (1302, -5531296320), (1415, 1382824080), (1487, -1382824080), (1610, -1382824080), (1634, 1382824080), (2428, -610802208), (2431, 610802208), (2459, -203600736), (2464, 203600736), (2489, 203600736), (2491, -203600736), (2562, -203600736), (2567, 203600736), (2700, 203600736), (2702, -203600736)]

theorem node657_check : node657 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1413894) entry_25_9) (Integer.Sparse.scale (-9602945) entry_25_10) := by decide +kernel

theorem node657_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node657 x = (((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) := by
  rw [node657_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node658 : Integer.Sparse (Fin 2886) := [(2164, 65954304), (2165, -1384581168), (2168, 1384581168), (2237, 82442880), (2238, -923054112), (2242, 197862912), (2243, -1384581168), (2296, -65954304), (2297, 923054112), (2298, -197862912), (2299, 1384581168), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node658_check : node658 =
    Integer.Sparse.merge (Integer.Sparse.scale (458016) entry_25_11) (Integer.Sparse.scale (-3205049) entry_25_12) := by decide +kernel

theorem node658_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node658 x = (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x) := by
  rw [node658_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node659 : Integer.Sparse (Fin 2886) := [(1274, 5531296320), (1302, -5531296320), (1415, 1382824080), (1487, -1382824080), (1610, -1382824080), (1634, 1382824080), (2164, 65954304), (2165, -1384581168), (2168, 1384581168), (2237, 82442880), (2238, -923054112), (2242, 197862912), (2243, -1384581168), (2296, -65954304), (2297, 923054112), (2298, -197862912), (2299, 1384581168), (2428, -610802208), (2431, 610802208), (2459, -203600736), (2464, 203600736), (2489, 203600736), (2491, -203600736), (2562, -203600736), (2567, 203600736), (2700, 203600736), (2702, -203600736), (2777, 131908608), (2779, -197862912), (2859, 49465728), (2867, -65954304)]

theorem node659_check : node659 =
    Integer.Sparse.merge node657 node658 := by decide +kernel

theorem node659_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node659 x = ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x)) := by
  rw [node659_check, Integer.Sparse.eval_merge]
  rw [node657_eval, node658_eval]

def node660 : Integer.Sparse (Fin 2886) := [(1253, -1504600560), (1255, 1504600560), (1274, 5531296320), (1277, 1504600560), (1280, 4513801680), (1302, -5531296320), (1303, -1504600560), (1304, -4513801680), (1415, 1382824080), (1419, 1504600560), (1487, -1382824080), (1488, -1504600560), (1610, -1382824080), (1611, -1504600560), (1634, 1382824080), (1635, 1504600560), (2164, 65954304), (2165, -1384581168), (2168, 1384581168), (2237, 82442880), (2238, -923054112), (2242, 197862912), (2243, -1384581168), (2296, -65954304), (2297, 923054112), (2298, -197862912), (2299, 1384581168), (2428, -610802208), (2431, 610802208), (2459, 413363232), (2464, 1437528672), (2489, -413363232), (2491, -1437528672), (2562, -820564704), (2567, -1030327200), (2647, -1233927936), (2700, 820564704), (2702, 1030327200), (2725, 1233927936), (2777, 131908608), (2779, -197862912), (2858, 1420727760), (2859, 49465728), (2866, -1420727760), (2867, -65954304)]

theorem node660_check : node660 =
    Integer.Sparse.merge node656 node659 := by decide +kernel

theorem node660_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node660 x = ((((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) + ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x))) := by
  rw [node660_check, Integer.Sparse.eval_merge]
  rw [node656_eval, node659_eval]

def node661 : Integer.Sparse (Fin 2886) := [(917, 846175680), (920, -846175680), (998, -225234720), (1001, -846175680), (1006, -3384702720), (1068, 225234720), (1070, 846175680), (1072, 3384702720), (1253, -1504600560), (1255, 1504600560), (1274, 5531296320), (1277, 1504600560), (1280, 4513801680), (1302, -5531296320), (1303, -1504600560), (1304, -4513801680), (1415, 1382824080), (1419, 1504600560), (1487, -1382824080), (1488, -1504600560), (1610, -1382824080), (1611, -1504600560), (1634, 1382824080), (1635, 1504600560), (2164, 65954304), (2165, -1544834736), (2168, 1544834736), (2178, -5732563392), (2179, 5732563392), (2237, 82442880), (2238, -762800544), (2242, 197862912), (2243, -743566896), (2246, -1433140848), (2258, 1433140848), (2296, -65954304), (2297, 762800544), (2298, -197862912), (2299, 743566896), (2300, 1433140848), (2306, -1433140848), (2428, -485574192), (2431, 485574192), (2459, 288135216), (2464, 1061844624), (2489, -288135216), (2491, -1061844624), (2562, -820564704), (2567, -1155555216), (2647, -1108699920), (2700, 820564704), (2702, 1155555216), (2725, 1108699920), (2777, 131908608), (2779, -197862912), (2800, -1724050368), (2804, 1724050368), (2835, -431012592), (2841, 431012592), (2858, 1420727760), (2859, 49465728), (2862, 431012592), (2864, -431012592), (2866, -1420727760), (2867, -65954304)]

theorem node661_check : node661 =
    Integer.Sparse.merge node654 node660 := by decide +kernel

theorem node661_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node661 x = (((((-9952367 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_0 x + (((312826 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_1 x + ((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_2 x)) + (((2993143 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_3 x + (((-1112872 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_4 x + ((869639 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_5 x))) + ((((-1973233 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_6 x + (((4284472 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_7 x + ((-10448615 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_8 x)) + ((((-1413894 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_9 x + ((-9602945 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_10 x) + (((458016 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_11 x + ((-3205049 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_12 x)))) := by
  rw [node661_check, Integer.Sparse.eval_merge]
  rw [node654_eval, node660_eval]

def node662 : Integer.Sparse (Fin 2886) := [(917, 1126529424), (920, -1126529424), (1001, 751019616), (1006, 1126529424), (1070, -751019616), (1072, -1126529424), (2164, -236076480), (2167, 708229440), (2174, 708229440), (2237, 708229440), (2242, 2832917760), (2296, -708229440), (2298, -2301745680), (2777, -472152960), (2782, -708229440), (2875, -531172080)]

theorem node662_check : node662 =
    Integer.Sparse.merge (Integer.Sparse.scale (2607707) entry_25_14) (Integer.Sparse.scale (-4918260) entry_25_15) := by decide +kernel

theorem node662_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node662 x = (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x) := by
  rw [node662_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node663 : Integer.Sparse (Fin 2886) := [(917, 1126529424), (920, -1126529424), (1001, 751019616), (1006, 1126529424), (1070, -751019616), (1072, -1126529424), (1969, 281771568), (1970, -281771568), (2062, -281771568), (2063, -1127086272), (2095, 281771568), (2096, 1127086272), (2164, -236076480), (2167, 708229440), (2174, 708229440), (2237, 708229440), (2242, 2832917760), (2296, -708229440), (2298, -2301745680), (2777, -472152960), (2782, -708229440), (2875, -531172080)]

theorem node663_check : node663 =
    Integer.Sparse.merge (Integer.Sparse.scale (1956747) entry_25_13) node662 := by decide +kernel

theorem node663_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node663 x = (((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) := by
  rw [node663_check, Integer.Sparse.eval_merge]
  rw [node662_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node664 : Integer.Sparse (Fin 2886) := [(2441, 1920707424), (2442, -1920707424), (2467, -1920707424), (2479, -1920707424), (2492, 1920707424), (2498, 1920707424), (2581, -960353712), (2653, 960353712), (2708, 960353712), (2731, -960353712), (2800, 2751133680), (2804, -2751133680), (2835, -2751133680), (2841, 2751133680), (2862, -1834089120), (2864, 1834089120)]

theorem node664_check : node664 =
    Integer.Sparse.merge (Integer.Sparse.scale (6368365) entry_25_16) (Integer.Sparse.scale (6669123) entry_25_17) := by decide +kernel

theorem node664_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node664 x = (((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) := by
  rw [node664_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node665 : Integer.Sparse (Fin 2886) := [(930, 10184980032), (931, -10184980032), (1010, 2546245008), (1024, -2546245008), (1073, -2546245008), (1080, 2546245008), (2825, 1390038480), (2827, -1390038480)]

theorem node665_check : node665 =
    Integer.Sparse.merge (Integer.Sparse.scale (17682257) entry_25_18) (Integer.Sparse.scale (-1930609) entry_25_19) := by decide +kernel

theorem node665_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node665 x = (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x) := by
  rw [node665_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node666 : Integer.Sparse (Fin 2886) := [(930, 10184980032), (931, -10184980032), (1010, 2546245008), (1024, -2546245008), (1073, -2546245008), (1080, 2546245008), (2441, 1920707424), (2442, -1920707424), (2467, -1920707424), (2479, -1920707424), (2492, 1920707424), (2498, 1920707424), (2581, -960353712), (2653, 960353712), (2708, 960353712), (2731, -960353712), (2800, 2751133680), (2804, -2751133680), (2825, 1390038480), (2827, -1390038480), (2835, -2751133680), (2841, 2751133680), (2862, -1834089120), (2864, 1834089120)]

theorem node666_check : node666 =
    Integer.Sparse.merge node664 node665 := by decide +kernel

theorem node666_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node666 x = ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x)) := by
  rw [node666_check, Integer.Sparse.eval_merge]
  rw [node664_eval, node665_eval]

def node667 : Integer.Sparse (Fin 2886) := [(917, 1126529424), (920, -1126529424), (930, 10184980032), (931, -10184980032), (1001, 751019616), (1006, 1126529424), (1010, 2546245008), (1024, -2546245008), (1070, -751019616), (1072, -1126529424), (1073, -2546245008), (1080, 2546245008), (1969, 281771568), (1970, -281771568), (2062, -281771568), (2063, -1127086272), (2095, 281771568), (2096, 1127086272), (2164, -236076480), (2167, 708229440), (2174, 708229440), (2237, 708229440), (2242, 2832917760), (2296, -708229440), (2298, -2301745680), (2441, 1920707424), (2442, -1920707424), (2467, -1920707424), (2479, -1920707424), (2492, 1920707424), (2498, 1920707424), (2581, -960353712), (2653, 960353712), (2708, 960353712), (2731, -960353712), (2777, -472152960), (2782, -708229440), (2800, 2751133680), (2804, -2751133680), (2825, 1390038480), (2827, -1390038480), (2835, -2751133680), (2841, 2751133680), (2862, -1834089120), (2864, 1834089120), (2875, -531172080)]

theorem node667_check : node667 =
    Integer.Sparse.merge node663 node666 := by decide +kernel

theorem node667_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node667 x = ((((1956747 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_13 x + (((2607707 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_14 x + ((-4918260 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_15 x)) + ((((6368365 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_16 x + ((6669123 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_17 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_18 x + ((-1930609 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_19 x))) := by
  rw [node667_check, Integer.Sparse.eval_merge]
  rw [node663_eval, node666_eval]

def node668 : Integer.Sparse (Fin 2886) := [(2427, -4083001848), (2430, 4696948944), (2437, 1565649648), (2458, 2095157880), (2463, 10621792080), (2488, -2962421568), (2490, -8273317608), (2561, -578175792), (2566, 4696948944), (2646, -2962421568), (2701, -1565649648), (2724, 2962421568), (2789, -4083001848), (2791, 3469054752), (2795, -1565649648), (2801, -867263688), (2806, 1734527376), (2812, -2348474472), (2836, -1156351584), (2843, 1734527376), (2850, -3131299296)]

theorem node668_check : node668 =
    Integer.Sparse.merge (Integer.Sparse.scale (-12045329) entry_25_21) (Integer.Sparse.scale (-20572372) entry_25_22) := by decide +kernel

theorem node668_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node668 x = (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x) := by
  rw [node668_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node669 : Integer.Sparse (Fin 2886) := [(1740, 1185227280), (1741, -1185227280), (2427, -4083001848), (2430, 4696948944), (2437, 1565649648), (2458, 2095157880), (2463, 10621792080), (2488, -2962421568), (2490, -8273317608), (2561, -578175792), (2566, 4696948944), (2646, -2962421568), (2701, -1565649648), (2724, 2962421568), (2789, -4083001848), (2791, 3469054752), (2795, -1565649648), (2801, -867263688), (2806, 1734527376), (2812, -2348474472), (2836, -1156351584), (2843, 1734527376), (2850, -3131299296)]

theorem node669_check : node669 =
    Integer.Sparse.merge (Integer.Sparse.scale (1646149) entry_25_20) node668 := by decide +kernel

theorem node669_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node669 x = (((1646149 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_20 x + (((-12045329 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_21 x + ((-20572372 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_22 x)) := by
  rw [node669_check, Integer.Sparse.eval_merge]
  rw [node668_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node670 : Integer.Sparse (Fin 2886) := [(1550, 2389706640), (1679, -2389706640), (2178, 1804108320), (2179, -1804108320), (2246, -1804108320), (2258, -2706162480), (2300, 1804108320), (2306, 2706162480)]

theorem node670_check : node670 =
    Integer.Sparse.merge (Integer.Sparse.scale (6264265) entry_25_23) (Integer.Sparse.scale (-3319037) entry_25_24) := by decide +kernel

theorem node670_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node670 x = (((6264265 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_23 x + ((-3319037 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_24 x) := by
  rw [node670_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node671 : Integer.Sparse (Fin 2886) := [(1347, 2615558400), (1348, -2615558400), (1556, 653889600), (1567, -653889600), (1682, -653889600), (1687, 653889600), (2821, 7181156736), (2822, -7181156736), (2826, 10771735104), (2828, -21543470208), (2831, 10771735104)]

theorem node671_check : node671 =
    Integer.Sparse.merge (Integer.Sparse.scale (24934572) entry_25_25) (Integer.Sparse.scale (4540900) entry_25_26) := by decide +kernel

theorem node671_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node671 x = (((24934572 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_25 x + ((4540900 : ℤ) : ℝ) * Integer.Sparse.eval entry_25_26 x) := by
  rw [node671_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block3

end OAI
