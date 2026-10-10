import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part1

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node64 : Integer.Sparse (Fin 2886) := [(1, -333424512), (7, -1333698048), (76, 333424512), (167, 1000273536), (176, 333424512), (844, -500003712), (849, -1375010208), (952, 500003712), (957, 1250009280), (1028, 125000928), (1047, 125000928), (1083, -125000928)]

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (2315448) entry_2_14) (Integer.Sparse.scale (-2604186) entry_2_15) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node65 : Integer.Sparse (Fin 2886) := [(1, -333424512), (7, -1333698048), (76, 333424512), (167, 1000273536), (176, 333424512), (624, 141505152), (626, 389139168), (775, -141505152), (777, -353762880), (798, -35376288), (836, -35376288), (839, 35376288), (844, -500003712), (849, -1375010208), (952, 500003712), (957, 1250009280), (1028, 125000928), (1047, 125000928), (1083, -125000928)]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (737006) entry_2_13) node64 := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  rw [node64_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node66 : Integer.Sparse (Fin 2886) := [(865, 478472256), (875, -113216880), (880, 119618064), (888, 113216880), (899, -478472256), (902, 905735040), (910, 339650640), (933, -119618064), (942, 452867520), (977, -905735040), (985, -119618064), (993, -339650640), (1012, 119618064), (1021, -452867520), (1058, -226433760), (1064, 226433760)]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (830681) entry_2_16) (Integer.Sparse.scale (2358685) entry_2_17) := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node67 : Integer.Sparse (Fin 2886) := [(8, 224285904), (10, -299047872), (12, 74761968), (80, -1570001328), (84, 224285904), (86, -1121429520), (135, 299047872), (138, -953215092), (142, 224285904), (146, 822381648), (148, 1121429520), (163, 747619680), (168, 56071476), (177, 149523936), (918, -33659760), (926, -67319520), (1002, 33659760), (1004, 67319520)]

theorem node67_check : node67 =
    Integer.Sparse.merge (Integer.Sparse.scale (4672623) entry_2_18) (Integer.Sparse.scale (-140249) entry_2_19) := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node68 : Integer.Sparse (Fin 2886) := [(8, 224285904), (10, -299047872), (12, 74761968), (80, -1570001328), (84, 224285904), (86, -1121429520), (135, 299047872), (138, -953215092), (142, 224285904), (146, 822381648), (148, 1121429520), (163, 747619680), (168, 56071476), (177, 149523936), (865, 478472256), (875, -113216880), (880, 119618064), (888, 113216880), (899, -478472256), (902, 905735040), (910, 339650640), (918, -33659760), (926, -67319520), (933, -119618064), (942, 452867520), (977, -905735040), (985, -119618064), (993, -339650640), (1002, 33659760), (1004, 67319520), (1012, 119618064), (1021, -452867520), (1058, -226433760), (1064, 226433760)]

theorem node68_check : node68 =
    Integer.Sparse.merge node66 node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x)) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node66_eval, node67_eval]

def node69 : Integer.Sparse (Fin 2886) := [(1, -333424512), (7, -1333698048), (8, 224285904), (10, -299047872), (12, 74761968), (76, 333424512), (80, -1570001328), (84, 224285904), (86, -1121429520), (135, 299047872), (138, -953215092), (142, 224285904), (146, 822381648), (148, 1121429520), (163, 747619680), (167, 1000273536), (168, 56071476), (176, 333424512), (177, 149523936), (624, 141505152), (626, 389139168), (775, -141505152), (777, -353762880), (798, -35376288), (836, -35376288), (839, 35376288), (844, -500003712), (849, -1375010208), (865, 478472256), (875, -113216880), (880, 119618064), (888, 113216880), (899, -478472256), (902, 905735040), (910, 339650640), (918, -33659760), (926, -67319520), (933, -119618064), (942, 452867520), (952, 500003712), (957, 1250009280), (977, -905735040), (985, -119618064), (993, -339650640), (1002, 33659760), (1004, 67319520), (1012, 119618064), (1021, -452867520), (1028, 125000928), (1047, 125000928), (1058, -226433760), (1064, 226433760), (1083, -125000928)]

theorem node69_check : node69 =
    Integer.Sparse.merge node65 node68 := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = ((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  rw [node65_eval, node68_eval]

def node70 : Integer.Sparse (Fin 2886) := [(864, -76333392), (868, 87582912), (882, -11249520), (898, -121331472), (903, -2413248), (935, -44998080), (973, 197664864), (978, 437914560), (987, 327832608), (1014, 350331648), (1056, -523084224), (1062, -316583088), (1075, -305333568)]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1590279) entry_2_21) (Integer.Sparse.scale (-234365) entry_2_22) := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node71 : Integer.Sparse (Fin 2886) := [(540, -328612320), (561, 328612320), (864, -76333392), (868, 87582912), (882, -11249520), (898, -121331472), (903, -2413248), (935, -44998080), (973, 197664864), (978, 437914560), (987, 327832608), (1014, 350331648), (1056, -523084224), (1062, -316583088), (1075, -305333568)]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (456406) entry_2_20) node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node70_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node72 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (848, -185839488), (855, -162609552), (956, 185839488), (964, 116149680), (1035, 46459872), (1049, 46459872), (1085, -46459872)]

theorem node72_check : node72 =
    Integer.Sparse.merge (Integer.Sparse.scale (-483957) entry_2_23) (Integer.Sparse.scale (-124524) entry_2_24) := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = (((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node73 : Integer.Sparse (Fin 2886) := [(198, -63407088), (201, 63407088), (435, 380442528), (440, 317035440), (482, -317035440), (491, -380442528), (581, 253628352), (598, -253628352), (917, 846175680), (920, -846175680), (1001, -846175680), (1006, -3384702720), (1070, 846175680), (1072, 3384702720)]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (5876220) entry_2_25) (Integer.Sparse.scale (-1320981) entry_2_26) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node74 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (198, -63407088), (201, 63407088), (435, 380442528), (440, 317035440), (482, -317035440), (491, -380442528), (581, 253628352), (598, -253628352), (848, -185839488), (855, -162609552), (917, 846175680), (920, -846175680), (956, 185839488), (964, 116149680), (1001, -846175680), (1006, -3384702720), (1035, 46459872), (1049, 46459872), (1070, 846175680), (1072, 3384702720), (1085, -46459872)]

theorem node74_check : node74 =
    Integer.Sparse.merge node72 node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node73_eval]

def node75 : Integer.Sparse (Fin 2886) := [(26, -89657280), (98, 89657280), (198, -63407088), (201, 63407088), (435, 380442528), (440, 317035440), (482, -317035440), (491, -380442528), (540, -328612320), (561, 328612320), (581, 253628352), (598, -253628352), (848, -185839488), (855, -162609552), (864, -76333392), (868, 87582912), (882, -11249520), (898, -121331472), (903, -2413248), (917, 846175680), (920, -846175680), (935, -44998080), (956, 185839488), (964, 116149680), (973, 197664864), (978, 437914560), (987, 327832608), (1001, -846175680), (1006, -3384702720), (1014, 350331648), (1035, 46459872), (1049, 46459872), (1056, -523084224), (1062, -316583088), (1070, 846175680), (1072, 3384702720), (1075, -305333568), (1085, -46459872)]

theorem node75_check : node75 =
    Integer.Sparse.merge node71 node74 := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x))) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  rw [node71_eval, node74_eval]

def node76 : Integer.Sparse (Fin 2886) := [(1, -333424512), (7, -1333698048), (8, 224285904), (10, -299047872), (12, 74761968), (26, -89657280), (76, 333424512), (80, -1570001328), (84, 224285904), (86, -1121429520), (98, 89657280), (135, 299047872), (138, -953215092), (142, 224285904), (146, 822381648), (148, 1121429520), (163, 747619680), (167, 1000273536), (168, 56071476), (176, 333424512), (177, 149523936), (198, -63407088), (201, 63407088), (435, 380442528), (440, 317035440), (482, -317035440), (491, -380442528), (540, -328612320), (561, 328612320), (581, 253628352), (598, -253628352), (624, 141505152), (626, 389139168), (775, -141505152), (777, -353762880), (798, -35376288), (836, -35376288), (839, 35376288), (844, -500003712), (848, -185839488), (849, -1375010208), (855, -162609552), (864, -76333392), (865, 478472256), (868, 87582912), (875, -113216880), (880, 119618064), (882, -11249520), (888, 113216880), (898, -121331472), (899, -478472256), (902, 905735040), (903, -2413248), (910, 339650640), (917, 846175680), (918, -33659760), (920, -846175680), (926, -67319520), (933, -119618064), (935, -44998080), (942, 452867520), (952, 500003712), (956, 185839488), (957, 1250009280), (964, 116149680), (973, 197664864), (977, -905735040), (978, 437914560), (985, -119618064), (987, 327832608), (993, -339650640), (1001, -846175680), (1002, 33659760), (1004, 67319520), (1006, -3384702720), (1012, 119618064), (1014, 350331648), (1021, -452867520), (1028, 125000928), (1035, 46459872), (1047, 125000928), (1049, 46459872), (1056, -523084224), (1058, -226433760), (1062, -316583088), (1064, 226433760), (1070, 846175680), (1072, 3384702720), (1075, -305333568), (1083, -125000928), (1085, -46459872)]

theorem node76_check : node76 =
    Integer.Sparse.merge node69 node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) + ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x)))) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node69_eval, node75_eval]

def node77 : Integer.Sparse (Fin 2886) := [(1, 506107776), (3, 188807040), (7, 975015744), (8, 224285904), (10, -299047872), (12, 74761968), (16, -58962024), (17, 75033744), (19, -58962024), (26, -89657280), (27, -75033744), (30, -78616032), (37, -412734168), (39, -825371184), (42, -766506312), (64, -300134976), (66, -432388176), (76, -506107776), (78, -188807040), (80, -1570001328), (82, -2098830720), (84, 224285904), (86, -1121429520), (91, 314464128), (93, 750337440), (94, 353772144), (98, 89657280), (99, 75033744), (102, 294810120), (118, 300134976), (121, 294810120), (133, -699610240), (135, 299047872), (138, -953215092), (142, 224285904), (146, 822381648), (148, 1121429520), (163, 747619680), (167, 1280117632), (168, 56071476), (169, -29481012), (170, -39308016), (174, -39308016), (176, 543307584), (177, 149523936), (180, 58962024), (185, 176886072), (191, -39308016), (198, -63407088), (201, 63407088), (327, -58962024), (333, -58962024), (376, 157232064), (380, 235848096), (400, 147405060), (423, -58962024), (427, -78616032), (435, 380442528), (440, 317035440), (482, -317035440), (491, -380442528), (540, -328612320), (561, 328612320), (569, -39308016), (574, 176886072), (578, 39308016), (581, 253628352), (598, -253628352), (624, 141505152), (626, 389139168), (775, -141505152), (777, -353762880), (798, -35376288), (836, -35376288), (839, 35376288), (843, -84433536), (844, -666546480), (845, -725058720), (848, -203440992), (849, -2041181280), (851, -239884704), (855, -145008048), (863, 157369200), (864, -76333392), (865, 299366544), (868, 87582912), (870, 245439408), (875, -113216880), (880, 298723776), (882, -11249520), (884, 226249632), (888, 113216880), (897, 223623408), (898, -121331472), (899, 1491690576), (902, 905735040), (903, -2413248), (905, 377947824), (910, 339650640), (917, 846175680), (918, -33659760), (920, -846175680), (926, -67319520), (933, 596804784), (935, -44998080), (937, 275940288), (942, 452867520), (951, 84433536), (952, 666546480), (953, 725058720), (956, 291448512), (957, 1250009280), (959, 195698880), (964, 204157200), (972, -380992608), (973, 197664864), (974, -1791057120), (977, -905735040), (978, 437914560), (980, -450291600), (985, -298723776), (987, 327832608), (989, -243231744), (993, -339650640), (1001, -846175680), (1002, 33659760), (1004, 67319520), (1006, -3384702720), (1012, -596804784), (1014, 350331648), (1016, -276358848), (1021, -452867520), (1028, -41541840), (1030, 13415904), (1035, 116865888), (1046, -88007520), (1047, 791172000), (1049, -59149152), (1056, -523084224), (1058, -226433760), (1062, -316583088), (1064, 226433760), (1070, 846175680), (1072, 3384702720), (1075, -305333568), (1083, 41541840), (1085, -116865888), (1093, 44185824), (1097, -173095632), (1100, 16982112), (1107, 418560), (1110, -13415904)]

theorem node77_check : node77 =
    Integer.Sparse.merge node63 node76 := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = ((((((-366698 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_0 x + (((262232 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_1 x + ((4372564 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_2 x)) + (((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_3 x + (((-407706 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_4 x + ((2092458 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_5 x))) + ((((-1007026 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_6 x + (((873692 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_7 x + ((-2456751 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_8 x)) + ((((-216243 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_9 x + ((-1563203 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_10 x) + (((1156547 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_11 x + ((42736 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_12 x)))) + (((((737006 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_13 x + (((2315448 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_14 x + ((-2604186 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_15 x)) + ((((830681 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_16 x + ((2358685 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_17 x) + (((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_18 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_19 x))) + ((((456406 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_20 x + (((-1590279 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_21 x + ((-234365 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_22 x)) + ((((-483957 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_23 x + ((-124524 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_24 x) + (((5876220 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_25 x + ((-1320981 : ℤ) : ℝ) * Integer.Sparse.eval entry_2_26 x))))) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node76_eval]

def node78 : Integer.Sparse (Fin 2886) := [(865, -179105712), (880, 179105712), (893, -923125680), (899, 1970162832), (933, 716422848), (968, 923125680), (974, -1791057120), (985, -179105712), (1012, -716422848)]

theorem node78_check : node78 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1282119) entry_3_1) (Integer.Sparse.scale (3731369) entry_3_2) := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node79 : Integer.Sparse (Fin 2886) := [(865, -179105712), (880, 179105712), (893, -923125680), (899, 1970162832), (933, 716422848), (968, 923125680), (974, -1791057120), (985, -179105712), (1012, -716422848), (2127, -858797376), (2139, 858797376), (2155, -214699344), (2186, 214699344), (2221, -1073496720), (2229, 1288196064), (2252, -1288196064), (2268, 1073496720)]

theorem node79_check : node79 =
    Integer.Sparse.merge (Integer.Sparse.scale (4472903) entry_3_0) node78 := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = (((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  rw [node78_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node80 : Integer.Sparse (Fin 2886) := [(2122, 6927792), (2135, -6927792), (2150, -76205712), (2182, -27711168), (2216, 69277920), (2225, 6927792), (2248, 27711168), (2358, -82031232), (2374, 82031232), (2413, -20507808), (2448, 20507808), (2528, 41015616), (2537, -20507808), (2551, -143554656), (2571, -82031232), (2600, 102539040), (2602, 20507808), (2612, 82031232)]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (-144329) entry_3_4) (Integer.Sparse.scale (-427246) entry_3_5) := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node81 : Integer.Sparse (Fin 2886) := [(2122, 6927792), (2135, -6927792), (2150, -76205712), (2182, -27711168), (2216, 69277920), (2225, 6927792), (2248, 27711168), (2354, 3740509248), (2358, -82031232), (2370, -3740509248), (2374, 82031232), (2409, 935127312), (2413, -20507808), (2444, -3117091040), (2448, 20507808), (2524, 1246836416), (2528, 41015616), (2537, -20507808), (2547, 10286400432), (2551, -143554656), (2571, -82031232), (2596, -9351273120), (2600, 102539040), (2602, 20507808), (2612, 82031232)]

theorem node81_check : node81 =
    Integer.Sparse.merge (Integer.Sparse.scale (19481819) entry_3_3) node80 := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x)) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  rw [node80_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node82 : Integer.Sparse (Fin 2886) := [(865, -179105712), (880, 179105712), (893, -923125680), (899, 1970162832), (933, 716422848), (968, 923125680), (974, -1791057120), (985, -179105712), (1012, -716422848), (2122, 6927792), (2127, -858797376), (2135, -6927792), (2139, 858797376), (2150, -76205712), (2155, -214699344), (2182, -27711168), (2186, 214699344), (2216, 69277920), (2221, -1073496720), (2225, 6927792), (2229, 1288196064), (2248, 27711168), (2252, -1288196064), (2268, 1073496720), (2354, 3740509248), (2358, -82031232), (2370, -3740509248), (2374, 82031232), (2409, 935127312), (2413, -20507808), (2444, -3117091040), (2448, 20507808), (2524, 1246836416), (2528, 41015616), (2537, -20507808), (2547, 10286400432), (2551, -143554656), (2571, -82031232), (2596, -9351273120), (2600, 102539040), (2602, 20507808), (2612, 82031232)]

theorem node82_check : node82 =
    Integer.Sparse.merge node79 node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = ((((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node79_eval, node81_eval]

def node83 : Integer.Sparse (Fin 2886) := [(1151, -13082688), (1170, 13082688), (1237, -3270672), (1264, 3270672), (1379, 6541344), (1389, -3270672), (1405, -22894704), (1422, -13082688), (1447, 16353360), (1449, 3270672), (1457, 13082688), (2358, 271207440), (2374, -180804960), (2383, -90402480), (2413, -271207440), (2448, -723219840), (2469, -361609920), (2528, 180804960), (2537, 90402480), (2551, 723219840), (2571, 361609920)]

theorem node83_check : node83 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1883385) entry_3_7) (Integer.Sparse.scale (-68139) entry_3_8) := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node84 : Integer.Sparse (Fin 2886) := [(1151, -13082688), (1170, 13082688), (1237, -3270672), (1264, 3270672), (1379, 6541344), (1389, -3270672), (1405, -22894704), (1422, -13082688), (1447, 16353360), (1449, 3270672), (1457, 13082688), (2118, -228670344), (2146, -2058033096), (2212, 1524468960), (2331, 228670344), (2358, 271207440), (2374, -180804960), (2383, -90402480), (2413, -271207440), (2448, -723219840), (2469, -361609920), (2508, -228670344), (2528, 180804960), (2537, 90402480), (2551, 723219840), (2571, 361609920), (2584, 762234480)]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3175977) entry_3_6) node83 := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  rw [node83_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node85 : Integer.Sparse (Fin 2886) := [(1146, 718840512), (1165, -718840512), (1232, 179710128), (1259, -179710128), (1373, -179710128), (1399, 1976811408), (1442, -1797101280), (2374, 677142912), (2383, -677142912), (2448, 169285728), (2469, -169285728), (2528, 677142912), (2537, -677142912), (2551, 169285728), (2571, -169285728), (2600, 846428640), (2602, -1185000096), (2612, 338571456)]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3526786) entry_3_9) (Integer.Sparse.scale (3743961) entry_3_10) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node86 : Integer.Sparse (Fin 2886) := [(2119, -962700480), (2122, -194773968), (2134, 962700480), (2135, 194773968), (2147, -3850801920), (2150, -779095872), (2181, -962700480), (2182, -194773968), (2224, 3850801920), (2225, 779095872), (2247, 962700480), (2248, 194773968)]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (6685420) entry_3_11) (Integer.Sparse.scale (1352597) entry_3_12) := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node87 : Integer.Sparse (Fin 2886) := [(1146, 718840512), (1165, -718840512), (1232, 179710128), (1259, -179710128), (1373, -179710128), (1399, 1976811408), (1442, -1797101280), (2119, -962700480), (2122, -194773968), (2134, 962700480), (2135, 194773968), (2147, -3850801920), (2150, -779095872), (2181, -962700480), (2182, -194773968), (2224, 3850801920), (2225, 779095872), (2247, 962700480), (2248, 194773968), (2374, 677142912), (2383, -677142912), (2448, 169285728), (2469, -169285728), (2528, 677142912), (2537, -677142912), (2551, 169285728), (2571, -169285728), (2600, 846428640), (2602, -1185000096), (2612, 338571456)]

theorem node87_check : node87 =
    Integer.Sparse.merge node85 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x)) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node85_eval, node86_eval]

def node88 : Integer.Sparse (Fin 2886) := [(1146, 718840512), (1151, -13082688), (1165, -718840512), (1170, 13082688), (1232, 179710128), (1237, -3270672), (1259, -179710128), (1264, 3270672), (1373, -179710128), (1379, 6541344), (1389, -3270672), (1399, 1976811408), (1405, -22894704), (1422, -13082688), (1442, -1797101280), (1447, 16353360), (1449, 3270672), (1457, 13082688), (2118, -228670344), (2119, -962700480), (2122, -194773968), (2134, 962700480), (2135, 194773968), (2146, -2058033096), (2147, -3850801920), (2150, -779095872), (2181, -962700480), (2182, -194773968), (2212, 1524468960), (2224, 3850801920), (2225, 779095872), (2247, 962700480), (2248, 194773968), (2331, 228670344), (2358, 271207440), (2374, 496337952), (2383, -767545392), (2413, -271207440), (2448, -553934112), (2469, -530895648), (2508, -228670344), (2528, 857947872), (2537, -586740432), (2551, 892505568), (2571, 192324192), (2584, 762234480), (2600, 846428640), (2602, -1185000096), (2612, 338571456)]

theorem node88_check : node88 =
    Integer.Sparse.merge node84 node87 := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = ((((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x))) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node87_eval]

def node89 : Integer.Sparse (Fin 2886) := [(865, -179105712), (880, 179105712), (893, -923125680), (899, 1970162832), (933, 716422848), (968, 923125680), (974, -1791057120), (985, -179105712), (1012, -716422848), (1146, 718840512), (1151, -13082688), (1165, -718840512), (1170, 13082688), (1232, 179710128), (1237, -3270672), (1259, -179710128), (1264, 3270672), (1373, -179710128), (1379, 6541344), (1389, -3270672), (1399, 1976811408), (1405, -22894704), (1422, -13082688), (1442, -1797101280), (1447, 16353360), (1449, 3270672), (1457, 13082688), (2118, -228670344), (2119, -962700480), (2122, -187846176), (2127, -858797376), (2134, 962700480), (2135, 187846176), (2139, 858797376), (2146, -2058033096), (2147, -3850801920), (2150, -855301584), (2155, -214699344), (2181, -962700480), (2182, -222485136), (2186, 214699344), (2212, 1524468960), (2216, 69277920), (2221, -1073496720), (2224, 3850801920), (2225, 786023664), (2229, 1288196064), (2247, 962700480), (2248, 222485136), (2252, -1288196064), (2268, 1073496720), (2331, 228670344), (2354, 3740509248), (2358, 189176208), (2370, -3740509248), (2374, 578369184), (2383, -767545392), (2409, 935127312), (2413, -291715248), (2444, -3117091040), (2448, -533426304), (2469, -530895648), (2508, -228670344), (2524, 1246836416), (2528, 898963488), (2537, -607248240), (2547, 10286400432), (2551, 748950912), (2571, 110292960), (2584, 762234480), (2596, -9351273120), (2600, 948967680), (2602, -1164492288), (2612, 420602688)]

theorem node89_check : node89 =
    Integer.Sparse.merge node82 node88 := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((((4472903 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + (((-1282119 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x + ((3731369 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x)) + (((19481819 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + (((-144329 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x + ((-427246 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x))) + ((((-3175977 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x + (((-1883385 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + ((-68139 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x)) + ((((-3526786 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x + ((3743961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x) + (((6685420 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x + ((1352597 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x)))) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  rw [node82_eval, node88_eval]

def node90 : Integer.Sparse (Fin 2886) := [(865, -389772576), (880, 389772576), (899, -1559090304), (933, -389772576), (985, 1559090304), (1012, 389772576), (2119, 540914448), (2134, -540914448), (2147, -5950058928), (2181, -2163657792), (2213, 5409144480), (2224, 540914448), (2247, 2163657792)]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (2706754) entry_3_14) (Integer.Sparse.scale (-11269051) entry_3_15) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node91 : Integer.Sparse (Fin 2886) := [(865, -389772576), (880, 389772576), (899, -1559090304), (933, -389772576), (985, 1559090304), (1012, 389772576), (1889, -109453152), (1890, 109453152), (1974, 1203984672), (1977, 437812608), (2069, -1094531520), (2070, -109453152), (2073, -437812608), (2119, 540914448), (2134, -540914448), (2147, -5950058928), (2181, -2163657792), (2213, 5409144480), (2224, 540914448), (2247, 2163657792)]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (2280274) entry_3_13) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node92 : Integer.Sparse (Fin 2886) := [(2354, -689456016), (2363, -619298688), (2370, 689456016), (2379, 619298688), (2409, 689456016), (2418, -154824672), (2444, 2757824064), (2453, 154824672), (2524, -689456016), (2533, 464474016), (2541, -309649344), (2547, -2757824064), (2556, -464474016), (2575, -1238597376), (2606, 309649344), (2616, 1238597376)]

theorem node92_check : node92 =
    Integer.Sparse.merge (Integer.Sparse.scale (4787889) entry_3_16) (Integer.Sparse.scale (-3225514) entry_3_17) := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = (((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node93 : Integer.Sparse (Fin 2886) := [(871, -693434304), (885, 693434304), (906, -173358576), (938, 173358576), (981, -866792880), (990, 1040151456), (1017, -1040151456), (1033, 866792880), (2425, 6314217120), (2456, -7892771400), (2559, 3157108560), (2608, -3157108560), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2861, -2104739040)]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (3611637) entry_3_18) (Integer.Sparse.scale (21924365) entry_3_19) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node94 : Integer.Sparse (Fin 2886) := [(871, -693434304), (885, 693434304), (906, -173358576), (938, 173358576), (981, -866792880), (990, 1040151456), (1017, -1040151456), (1033, 866792880), (2354, -689456016), (2363, -619298688), (2370, 689456016), (2379, 619298688), (2409, 689456016), (2418, -154824672), (2425, 6314217120), (2444, 2757824064), (2453, 154824672), (2456, -7892771400), (2524, -689456016), (2533, 464474016), (2541, -309649344), (2547, -2757824064), (2556, -464474016), (2559, 3157108560), (2575, -1238597376), (2606, 309649344), (2608, -3157108560), (2616, 1238597376), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2861, -2104739040)]

theorem node94_check : node94 =
    Integer.Sparse.merge node92 node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node92_eval, node93_eval]

def node95 : Integer.Sparse (Fin 2886) := [(865, -389772576), (871, -693434304), (880, 389772576), (885, 693434304), (899, -1559090304), (906, -173358576), (933, -389772576), (938, 173358576), (981, -866792880), (985, 1559090304), (990, 1040151456), (1012, 389772576), (1017, -1040151456), (1033, 866792880), (1889, -109453152), (1890, 109453152), (1974, 1203984672), (1977, 437812608), (2069, -1094531520), (2070, -109453152), (2073, -437812608), (2119, 540914448), (2134, -540914448), (2147, -5950058928), (2181, -2163657792), (2213, 5409144480), (2224, 540914448), (2247, 2163657792), (2354, -689456016), (2363, -619298688), (2370, 689456016), (2379, 619298688), (2409, 689456016), (2418, -154824672), (2425, 6314217120), (2444, 2757824064), (2453, 154824672), (2456, -7892771400), (2524, -689456016), (2533, 464474016), (2541, -309649344), (2547, -2757824064), (2556, -464474016), (2559, 3157108560), (2575, -1238597376), (2606, 309649344), (2608, -3157108560), (2616, 1238597376), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2861, -2104739040)]

theorem node95_check : node95 =
    Integer.Sparse.merge node91 node94 := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = ((((2280274 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + (((2706754 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x + ((-11269051 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x)) + ((((4787889 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((-3225514 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + ((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x))) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  rw [node91_eval, node94_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
