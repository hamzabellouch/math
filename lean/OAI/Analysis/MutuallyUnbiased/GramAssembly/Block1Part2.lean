import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block1Part1

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block1

def node64 : Integer.Sparse (Fin 2886) := [(16, 1139532), (19, -1139532), (30, 1139532), (37, 10255788), (42, -6837192), (91, -7217036), (102, 7976724), (121, 1139532), (169, 3418596), (170, -5697660), (174, -1139532), (180, -1139532), (185, 1139532), (191, -1139532), (327, 1139532), (333, -4558128), (376, -4178284), (400, 7976724), (423, 3418596), (427, -5697660), (574, -1139532), (578, 1139532), (916, 36039360), (922, -36039360), (1000, -36039360), (1008, 36039360), (1103, 36039360), (1105, -36039360)]

theorem node64_check : node64 =
    Integer.Sparse.merge (Integer.Sparse.scale (94961) entry_3_5) (Integer.Sparse.scale (300328) entry_3_6) := by decide +kernel

theorem node64_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node64 x = (((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) := by
  rw [node64_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node65 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (77, -20908800), (132, 20908800), (147, 20908800), (162, -20908800), (867, -126861240), (875, 126861240), (977, 126861240), (1021, -126861240), (1058, -126861240), (1077, 126861240)]

theorem node65_check : node65 =
    Integer.Sparse.merge (Integer.Sparse.scale (174240) entry_3_8) (Integer.Sparse.scale (-1057177) entry_3_9) := by decide +kernel

theorem node65_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node65 x = (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x) := by
  rw [node65_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node66 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (16, 2347296), (19, -7041888), (30, 11736480), (37, -2347296), (42, 7041888), (66, -11736480), (77, -20908800), (102, -9389184), (121, 9389184), (132, 20908800), (147, 20908800), (162, -20908800), (180, -2347296), (185, -16431072), (191, 11736480), (327, 2347296), (333, 16431072), (423, -14083776), (569, -11736480), (574, 14083776), (867, -126861240), (875, 126861240), (977, 126861240), (1021, -126861240), (1058, -126861240), (1077, 126861240)]

theorem node66_check : node66 =
    Integer.Sparse.merge (Integer.Sparse.scale (-195608) entry_3_7) node65 := by decide +kernel

theorem node66_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node66 x = (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)) := by
  rw [node66_check, Integer.Sparse.eval_merge]
  rw [node65_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node67 : Integer.Sparse (Fin 2886) := [(2, 20908800), (6, -20908800), (16, 3486828), (19, -8181420), (30, 12876012), (37, 7908492), (42, 204696), (66, -11736480), (77, -20908800), (91, -7217036), (102, -1412460), (121, 10528716), (132, 20908800), (147, 20908800), (162, -20908800), (169, 3418596), (170, -5697660), (174, -1139532), (180, -3486828), (185, -15291540), (191, 10596948), (327, 3486828), (333, 11872944), (376, -4178284), (400, 7976724), (423, -10665180), (427, -5697660), (569, -11736480), (574, 12944244), (578, 1139532), (867, -126861240), (875, 126861240), (916, 36039360), (922, -36039360), (977, 126861240), (1000, -36039360), (1008, 36039360), (1021, -126861240), (1058, -126861240), (1077, 126861240), (1103, 36039360), (1105, -36039360)]

theorem node67_check : node67 =
    Integer.Sparse.merge node64 node66 := by decide +kernel

theorem node67_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node67 x = ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x))) := by
  rw [node67_check, Integer.Sparse.eval_merge]
  rw [node64_eval, node66_eval]

def node68 : Integer.Sparse (Fin 2886) := [(1, 32882040), (2, 20908800), (6, -20908800), (7, -32882040), (16, 3486828), (17, -6284640), (19, -8181420), (27, 6284640), (30, 12876012), (37, 7908492), (39, 6284640), (42, 204696), (64, -6284640), (66, -11736480), (76, -32882040), (77, -20908800), (91, -7217036), (99, -6284640), (102, -1412460), (118, 6284640), (121, 10528716), (132, 20908800), (133, 52611264), (147, 20908800), (162, -20908800), (167, 13152816), (169, 3418596), (170, -5697660), (174, -1139532), (176, -32882040), (180, -3486828), (185, -15291540), (191, 10596948), (327, 3486828), (333, 11872944), (376, -4178284), (400, 7976724), (423, -10665180), (427, -5697660), (569, -11736480), (574, 12944244), (578, 1139532), (865, -21811320), (867, -126861240), (870, 13578840), (875, 126861240), (880, 21811320), (884, -13578840), (899, 21811320), (902, 70989360), (905, -13578840), (910, -70989360), (916, 36039360), (922, -36039360), (933, -21811320), (937, 13578840), (977, 55871880), (985, -21811320), (989, 13578840), (993, 70989360), (1000, -36039360), (1008, 36039360), (1012, 21811320), (1016, -13578840), (1021, -126861240), (1058, -55871880), (1064, -70989360), (1077, 126861240), (1103, 36039360), (1105, -36039360)]

theorem node68_check : node68 =
    Integer.Sparse.merge node63 node67 := by decide +kernel

theorem node68_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node68 x = (((((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)))) := by
  rw [node68_check, Integer.Sparse.eval_merge]
  rw [node63_eval, node67_eval]

def node69 : Integer.Sparse (Fin 2886) := [(843, -8359080), (844, -6641400), (849, 6641400), (851, 8359080), (951, 8359080), (952, 6641400), (1028, -6641400), (1030, -8359080), (1047, -6641400), (1083, 6641400), (1093, -8359080), (1110, 8359080)]

theorem node69_check : node69 =
    Integer.Sparse.merge (Integer.Sparse.scale (-69659) entry_3_10) (Integer.Sparse.scale (-55345) entry_3_11) := by decide +kernel

theorem node69_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node69 x = (((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) := by
  rw [node69_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node70 : Integer.Sparse (Fin 2886) := [(624, 3152520), (626, -3152520), (775, -3152520), (798, 3152520), (836, 3152520), (839, -3152520), (848, -20094720), (855, 20094720), (956, 20094720), (1035, -20094720), (1049, -20094720), (1085, 20094720)]

theorem node70_check : node70 =
    Integer.Sparse.merge (Integer.Sparse.scale (26271) entry_3_13) (Integer.Sparse.scale (-167456) entry_3_14) := by decide +kernel

theorem node70_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node70 x = (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x) := by
  rw [node70_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node71 : Integer.Sparse (Fin 2886) := [(624, 3152520), (626, -3152520), (775, -3152520), (798, 3152520), (836, 3152520), (839, -3152520), (848, -20094720), (855, 20094720), (868, -86982240), (882, 86982240), (903, 86982240), (935, -86982240), (956, 20094720), (987, -86982240), (1014, 86982240), (1035, -20094720), (1049, -20094720), (1085, 20094720)]

theorem node71_check : node71 =
    Integer.Sparse.merge (Integer.Sparse.scale (-724852) entry_3_12) node70 := by decide +kernel

theorem node71_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node71 x = (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x)) := by
  rw [node71_check, Integer.Sparse.eval_merge]
  rw [node70_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node72 : Integer.Sparse (Fin 2886) := [(624, 3152520), (626, -3152520), (775, -3152520), (798, 3152520), (836, 3152520), (839, -3152520), (843, -8359080), (844, -6641400), (848, -20094720), (849, 6641400), (851, 8359080), (855, 20094720), (868, -86982240), (882, 86982240), (903, 86982240), (935, -86982240), (951, 8359080), (952, 6641400), (956, 20094720), (987, -86982240), (1014, 86982240), (1028, -6641400), (1030, -8359080), (1035, -20094720), (1047, -6641400), (1049, -20094720), (1083, 6641400), (1085, 20094720), (1093, -8359080), (1110, 8359080)]

theorem node72_check : node72 =
    Integer.Sparse.merge node69 node71 := by decide +kernel

theorem node72_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node72 x = ((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) := by
  rw [node72_check, Integer.Sparse.eval_merge]
  rw [node69_eval, node71_eval]

def node73 : Integer.Sparse (Fin 2886) := [(38, 7706640), (41, -7706640), (92, -7706640), (101, 7706640), (152, 7706640), (155, -7706640), (864, -69408720), (882, 69408720), (898, 69408720), (935, -69408720), (1062, -69408720), (1075, 69408720)]

theorem node73_check : node73 =
    Integer.Sparse.merge (Integer.Sparse.scale (-578406) entry_3_16) (Integer.Sparse.scale (64222) entry_3_17) := by decide +kernel

theorem node73_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node73 x = (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x) := by
  rw [node73_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node74 : Integer.Sparse (Fin 2886) := [(38, 7706640), (41, -7706640), (92, -7706640), (101, 7706640), (152, 7706640), (155, -7706640), (864, -69408720), (882, 69408720), (897, 73267800), (898, 69408720), (905, -73267800), (935, -69408720), (972, -73267800), (989, 73267800), (1062, -69408720), (1075, 69408720), (1097, 73267800), (1100, -73267800)]

theorem node74_check : node74 =
    Integer.Sparse.merge (Integer.Sparse.scale (610565) entry_3_15) node73 := by decide +kernel

theorem node74_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node74 x = (((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) := by
  rw [node74_check, Integer.Sparse.eval_merge]
  rw [node73_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node75 : Integer.Sparse (Fin 2886) := [(25, 9198120), (29, -11037744), (97, -7358496), (131, 14716992), (154, 3679248), (161, -9198120), (196, 9198120), (200, -7358496), (432, -11037744), (484, 14716992), (580, 3679248), (597, -9198120), (875, -86496240), (888, 86496240), (910, 86496240), (942, -86496240), (993, -86496240), (1021, 86496240)]

theorem node75_check : node75 =
    Integer.Sparse.merge (Integer.Sparse.scale (153302) entry_3_19) (Integer.Sparse.scale (-720802) entry_3_20) := by decide +kernel

theorem node75_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node75 x = (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x) := by
  rw [node75_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node76 : Integer.Sparse (Fin 2886) := [(25, 9198120), (29, -11037744), (97, -7358496), (131, 14716992), (154, 3679248), (161, -9198120), (196, 9198120), (200, -7358496), (432, -11037744), (484, 14716992), (580, 3679248), (597, -9198120), (875, -86496240), (888, 86496240), (898, 36105360), (903, -36105360), (910, 86496240), (942, -86496240), (973, -36105360), (987, 36105360), (993, -86496240), (1021, 86496240), (1056, 36105360), (1062, -36105360)]

theorem node76_check : node76 =
    Integer.Sparse.merge (Integer.Sparse.scale (300878) entry_3_18) node75 := by decide +kernel

theorem node76_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node76 x = (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x)) := by
  rw [node76_check, Integer.Sparse.eval_merge]
  rw [node75_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node77 : Integer.Sparse (Fin 2886) := [(25, 9198120), (29, -11037744), (38, 7706640), (41, -7706640), (92, -7706640), (97, -7358496), (101, 7706640), (131, 14716992), (152, 7706640), (154, 3679248), (155, -7706640), (161, -9198120), (196, 9198120), (200, -7358496), (432, -11037744), (484, 14716992), (580, 3679248), (597, -9198120), (864, -69408720), (875, -86496240), (882, 69408720), (888, 86496240), (897, 73267800), (898, 105514080), (903, -36105360), (905, -73267800), (910, 86496240), (935, -69408720), (942, -86496240), (972, -73267800), (973, -36105360), (987, 36105360), (989, 73267800), (993, -86496240), (1021, 86496240), (1056, 36105360), (1062, -105514080), (1075, 69408720), (1097, 73267800), (1100, -73267800)]

theorem node77_check : node77 =
    Integer.Sparse.merge node74 node76 := by decide +kernel

theorem node77_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node77 x = ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x))) := by
  rw [node77_check, Integer.Sparse.eval_merge]
  rw [node74_eval, node76_eval]

def node78 : Integer.Sparse (Fin 2886) := [(25, 9198120), (29, -11037744), (38, 7706640), (41, -7706640), (92, -7706640), (97, -7358496), (101, 7706640), (131, 14716992), (152, 7706640), (154, 3679248), (155, -7706640), (161, -9198120), (196, 9198120), (200, -7358496), (432, -11037744), (484, 14716992), (580, 3679248), (597, -9198120), (624, 3152520), (626, -3152520), (775, -3152520), (798, 3152520), (836, 3152520), (839, -3152520), (843, -8359080), (844, -6641400), (848, -20094720), (849, 6641400), (851, 8359080), (855, 20094720), (864, -69408720), (868, -86982240), (875, -86496240), (882, 156390960), (888, 86496240), (897, 73267800), (898, 105514080), (903, 50876880), (905, -73267800), (910, 86496240), (935, -156390960), (942, -86496240), (951, 8359080), (952, 6641400), (956, 20094720), (972, -73267800), (973, -36105360), (987, -50876880), (989, 73267800), (993, -86496240), (1014, 86982240), (1021, 86496240), (1028, -6641400), (1030, -8359080), (1035, -20094720), (1047, -6641400), (1049, -20094720), (1056, 36105360), (1062, -105514080), (1075, 69408720), (1083, 6641400), (1085, 20094720), (1093, -8359080), (1097, 73267800), (1100, -73267800), (1110, 8359080)]

theorem node78_check : node78 =
    Integer.Sparse.merge node72 node77 := by decide +kernel

theorem node78_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node78 x = (((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) + ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x)))) := by
  rw [node78_check, Integer.Sparse.eval_merge]
  rw [node72_eval, node77_eval]

def node79 : Integer.Sparse (Fin 2886) := [(1, 32882040), (2, 20908800), (6, -20908800), (7, -32882040), (16, 3486828), (17, -6284640), (19, -8181420), (25, 9198120), (27, 6284640), (29, -11037744), (30, 12876012), (37, 7908492), (38, 7706640), (39, 6284640), (41, -7706640), (42, 204696), (64, -6284640), (66, -11736480), (76, -32882040), (77, -20908800), (91, -7217036), (92, -7706640), (97, -7358496), (99, -6284640), (101, 7706640), (102, -1412460), (118, 6284640), (121, 10528716), (131, 14716992), (132, 20908800), (133, 52611264), (147, 20908800), (152, 7706640), (154, 3679248), (155, -7706640), (161, -9198120), (162, -20908800), (167, 13152816), (169, 3418596), (170, -5697660), (174, -1139532), (176, -32882040), (180, -3486828), (185, -15291540), (191, 10596948), (196, 9198120), (200, -7358496), (327, 3486828), (333, 11872944), (376, -4178284), (400, 7976724), (423, -10665180), (427, -5697660), (432, -11037744), (484, 14716992), (569, -11736480), (574, 12944244), (578, 1139532), (580, 3679248), (597, -9198120), (624, 3152520), (626, -3152520), (775, -3152520), (798, 3152520), (836, 3152520), (839, -3152520), (843, -8359080), (844, -6641400), (848, -20094720), (849, 6641400), (851, 8359080), (855, 20094720), (864, -69408720), (865, -21811320), (867, -126861240), (868, -86982240), (870, 13578840), (875, 40365000), (880, 21811320), (882, 156390960), (884, -13578840), (888, 86496240), (897, 73267800), (898, 105514080), (899, 21811320), (902, 70989360), (903, 50876880), (905, -86846640), (910, 15506880), (916, 36039360), (922, -36039360), (933, -21811320), (935, -156390960), (937, 13578840), (942, -86496240), (951, 8359080), (952, 6641400), (956, 20094720), (972, -73267800), (973, -36105360), (977, 55871880), (985, -21811320), (987, -50876880), (989, 86846640), (993, -15506880), (1000, -36039360), (1008, 36039360), (1012, 21811320), (1014, 86982240), (1016, -13578840), (1021, -40365000), (1028, -6641400), (1030, -8359080), (1035, -20094720), (1047, -6641400), (1049, -20094720), (1056, 36105360), (1058, -55871880), (1062, -105514080), (1064, -70989360), (1075, 69408720), (1077, 126861240), (1083, 6641400), (1085, 20094720), (1093, -8359080), (1097, 73267800), (1100, -73267800), (1103, 36039360), (1105, -36039360), (1110, 8359080)]

theorem node79_check : node79 =
    Integer.Sparse.merge node68 node78 := by decide +kernel

theorem node79_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node79 x = ((((((591578 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_0 x + ((-52372 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_1 x) + (((113157 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_2 x + (((274017 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_3 x + ((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_4 x))) + ((((94961 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_5 x + ((300328 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_6 x) + (((-195608 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_7 x + (((174240 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_8 x + ((-1057177 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_9 x)))) + (((((-69659 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_10 x + ((-55345 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_11 x) + (((-724852 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_12 x + (((26271 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_13 x + ((-167456 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_14 x))) + ((((610565 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_15 x + (((-578406 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_16 x + ((64222 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_17 x)) + (((300878 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_18 x + (((153302 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_19 x + ((-720802 : ℤ) : ℝ) * Integer.Sparse.eval entry_3_20 x))))) := by
  rw [node79_check, Integer.Sparse.eval_merge]
  rw [node68_eval, node78_eval]

def node80 : Integer.Sparse (Fin 2886) := [(1146, 36407640), (1165, -36407640), (1232, -36407640), (1259, 36407640), (1373, 36407640), (1399, -36407640), (2533, -427788720), (2541, 427788720), (2556, 427788720), (2575, -427788720), (2606, -427788720), (2616, 427788720)]

theorem node80_check : node80 =
    Integer.Sparse.merge (Integer.Sparse.scale (-3564906) entry_4_0) (Integer.Sparse.scale (303397) entry_4_1) := by decide +kernel

theorem node80_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node80 x = (((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) := by
  rw [node80_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node81 : Integer.Sparse (Fin 2886) := [(865, -21811320), (880, 21811320), (899, 21811320), (933, -21811320), (985, -21811320), (1012, 21811320), (2354, 371224920), (2370, -371224920), (2409, -371224920), (2444, 445469904), (2524, 296979936), (2547, -371224920)]

theorem node81_check : node81 =
    Integer.Sparse.merge (Integer.Sparse.scale (-181761) entry_4_3) (Integer.Sparse.scale (3093541) entry_4_4) := by decide +kernel

theorem node81_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node81 x = (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x) := by
  rw [node81_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node82 : Integer.Sparse (Fin 2886) := [(865, -21811320), (880, 21811320), (899, 21811320), (933, -21811320), (985, -21811320), (1012, 21811320), (2354, 371224920), (2358, 385011240), (2370, -371224920), (2374, -385011240), (2409, -371224920), (2413, -385011240), (2444, 445469904), (2448, 385011240), (2524, 296979936), (2528, 385011240), (2547, -371224920), (2551, -385011240)]

theorem node82_check : node82 =
    Integer.Sparse.merge (Integer.Sparse.scale (3208427) entry_4_2) node81 := by decide +kernel

theorem node82_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node82 x = (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x)) := by
  rw [node82_check, Integer.Sparse.eval_merge]
  rw [node81_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node83 : Integer.Sparse (Fin 2886) := [(865, -21811320), (880, 21811320), (899, 21811320), (933, -21811320), (985, -21811320), (1012, 21811320), (1146, 36407640), (1165, -36407640), (1232, -36407640), (1259, 36407640), (1373, 36407640), (1399, -36407640), (2354, 371224920), (2358, 385011240), (2370, -371224920), (2374, -385011240), (2409, -371224920), (2413, -385011240), (2444, 445469904), (2448, 385011240), (2524, 296979936), (2528, 385011240), (2533, -427788720), (2541, 427788720), (2547, -371224920), (2551, -385011240), (2556, 427788720), (2575, -427788720), (2606, -427788720), (2616, 427788720)]

theorem node83_check : node83 =
    Integer.Sparse.merge node80 node82 := by decide +kernel

theorem node83_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node83 x = ((((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) := by
  rw [node83_check, Integer.Sparse.eval_merge]
  rw [node80_eval, node82_eval]

def node84 : Integer.Sparse (Fin 2886) := [(1379, 95074440), (1389, -95074440), (1405, -95074440), (1422, 95074440), (1449, 95074440), (1457, -95074440), (2803, -282378360), (2805, 282378360), (2838, 282378360), (2842, -282378360), (2863, -282378360), (2865, 282378360)]

theorem node84_check : node84 =
    Integer.Sparse.merge (Integer.Sparse.scale (792287) entry_4_5) (Integer.Sparse.scale (-2353153) entry_4_6) := by decide +kernel

theorem node84_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node84 x = (((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) := by
  rw [node84_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node85 : Integer.Sparse (Fin 2886) := [(862, -43985400), (879, 43985400), (896, 43985400), (932, -43985400), (984, -43985400), (1011, 43985400), (2379, 31560960), (2387, -31560960), (2453, -31560960), (2473, 31560960), (2606, 31560960), (2616, -31560960)]

theorem node85_check : node85 =
    Integer.Sparse.merge (Integer.Sparse.scale (-366545) entry_4_8) (Integer.Sparse.scale (263008) entry_4_9) := by decide +kernel

theorem node85_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node85 x = (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x) := by
  rw [node85_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node86 : Integer.Sparse (Fin 2886) := [(862, -43985400), (879, 43985400), (896, 43985400), (932, -43985400), (984, -43985400), (1011, 43985400), (1151, -59629680), (1170, 59629680), (1237, 59629680), (1264, -59629680), (1379, -59629680), (1405, 59629680), (2379, 31560960), (2387, -31560960), (2453, -31560960), (2473, 31560960), (2606, 31560960), (2616, -31560960)]

theorem node86_check : node86 =
    Integer.Sparse.merge (Integer.Sparse.scale (-496914) entry_4_7) node85 := by decide +kernel

theorem node86_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node86 x = (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x)) := by
  rw [node86_check, Integer.Sparse.eval_merge]
  rw [node85_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node87 : Integer.Sparse (Fin 2886) := [(862, -43985400), (879, 43985400), (896, 43985400), (932, -43985400), (984, -43985400), (1011, 43985400), (1151, -59629680), (1170, 59629680), (1237, 59629680), (1264, -59629680), (1379, 35444760), (1389, -95074440), (1405, -35444760), (1422, 95074440), (1449, 95074440), (1457, -95074440), (2379, 31560960), (2387, -31560960), (2453, -31560960), (2473, 31560960), (2606, 31560960), (2616, -31560960), (2803, -282378360), (2805, 282378360), (2838, 282378360), (2842, -282378360), (2863, -282378360), (2865, 282378360)]

theorem node87_check : node87 =
    Integer.Sparse.merge node84 node86 := by decide +kernel

theorem node87_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node87 x = ((((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) + (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x))) := by
  rw [node87_check, Integer.Sparse.eval_merge]
  rw [node84_eval, node86_eval]

def node88 : Integer.Sparse (Fin 2886) := [(862, -43985400), (865, -21811320), (879, 43985400), (880, 21811320), (896, 43985400), (899, 21811320), (932, -43985400), (933, -21811320), (984, -43985400), (985, -21811320), (1011, 43985400), (1012, 21811320), (1146, 36407640), (1151, -59629680), (1165, -36407640), (1170, 59629680), (1232, -36407640), (1237, 59629680), (1259, 36407640), (1264, -59629680), (1373, 36407640), (1379, 35444760), (1389, -95074440), (1399, -36407640), (1405, -35444760), (1422, 95074440), (1449, 95074440), (1457, -95074440), (2354, 371224920), (2358, 385011240), (2370, -371224920), (2374, -385011240), (2379, 31560960), (2387, -31560960), (2409, -371224920), (2413, -385011240), (2444, 445469904), (2448, 385011240), (2453, -31560960), (2473, 31560960), (2524, 296979936), (2528, 385011240), (2533, -427788720), (2541, 427788720), (2547, -371224920), (2551, -385011240), (2556, 427788720), (2575, -427788720), (2606, -396227760), (2616, 396227760), (2803, -282378360), (2805, 282378360), (2838, 282378360), (2842, -282378360), (2863, -282378360), (2865, 282378360)]

theorem node88_check : node88 =
    Integer.Sparse.merge node83 node87 := by decide +kernel

theorem node88_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node88 x = (((((-3564906 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_0 x + ((303397 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_1 x) + (((3208427 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_2 x + (((-181761 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_3 x + ((3093541 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_4 x))) + ((((792287 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_5 x + ((-2353153 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_6 x) + (((-496914 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_7 x + (((-366545 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_8 x + ((263008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_9 x)))) := by
  rw [node88_check, Integer.Sparse.eval_merge]
  rw [node83_eval, node87_eval]

def node89 : Integer.Sparse (Fin 2886) := [(2119, 76452000), (2122, 100237560), (2134, -76452000), (2135, -100237560), (2147, -76452000), (2150, -100237560), (2181, 76452000), (2182, 100237560), (2224, 76452000), (2225, 100237560), (2247, -76452000), (2248, -100237560)]

theorem node89_check : node89 =
    Integer.Sparse.merge (Integer.Sparse.scale (835313) entry_4_10) (Integer.Sparse.scale (637100) entry_4_11) := by decide +kernel

theorem node89_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node89 x = (((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) := by
  rw [node89_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node90 : Integer.Sparse (Fin 2886) := [(1889, -80790840), (1890, 80790840), (1974, 80790840), (1977, -80790840), (2070, -80790840), (2073, 80790840), (2127, 228328800), (2139, -228328800), (2155, -228328800), (2186, 228328800), (2229, 228328800), (2252, -228328800)]

theorem node90_check : node90 =
    Integer.Sparse.merge (Integer.Sparse.scale (-673257) entry_4_13) (Integer.Sparse.scale (1902740) entry_4_14) := by decide +kernel

theorem node90_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node90 x = (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x) := by
  rw [node90_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node91 : Integer.Sparse (Fin 2886) := [(1889, -80790840), (1890, 80790840), (1974, 80790840), (1977, -80790840), (2070, -80790840), (2073, 80790840), (2127, 228328800), (2139, -228328800), (2155, -228328800), (2186, 228328800), (2229, 228328800), (2252, -228328800), (2355, 455364360), (2371, -455364360), (2410, -455364360), (2445, 455364360), (2525, 455364360), (2548, -455364360)]

theorem node91_check : node91 =
    Integer.Sparse.merge (Integer.Sparse.scale (3794703) entry_4_12) node90 := by decide +kernel

theorem node91_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node91 x = (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x)) := by
  rw [node91_check, Integer.Sparse.eval_merge]
  rw [node90_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node92 : Integer.Sparse (Fin 2886) := [(1889, -80790840), (1890, 80790840), (1974, 80790840), (1977, -80790840), (2070, -80790840), (2073, 80790840), (2119, 76452000), (2122, 100237560), (2127, 228328800), (2134, -76452000), (2135, -100237560), (2139, -228328800), (2147, -76452000), (2150, -100237560), (2155, -228328800), (2181, 76452000), (2182, 100237560), (2186, 228328800), (2224, 76452000), (2225, 100237560), (2229, 228328800), (2247, -76452000), (2248, -100237560), (2252, -228328800), (2355, 455364360), (2371, -455364360), (2410, -455364360), (2445, 455364360), (2525, 455364360), (2548, -455364360)]

theorem node92_check : node92 =
    Integer.Sparse.merge node89 node91 := by decide +kernel

theorem node92_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node92 x = ((((835313 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_10 x + ((637100 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_11 x) + (((3794703 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_12 x + (((-673257 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_13 x + ((1902740 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_14 x))) := by
  rw [node92_check, Integer.Sparse.eval_merge]
  rw [node89_eval, node91_eval]

def node93 : Integer.Sparse (Fin 2886) := [(1376, 123035280), (1388, -123035280), (1402, -123035280), (1421, 123035280), (1448, 123035280), (1456, -123035280), (2355, -37930200), (2382, 37930200), (2410, 37930200), (2468, -37930200), (2536, -37930200), (2570, 37930200)]

theorem node93_check : node93 =
    Integer.Sparse.merge (Integer.Sparse.scale (-316085) entry_4_16) (Integer.Sparse.scale (1025294) entry_4_17) := by decide +kernel

theorem node93_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node93 x = (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x) := by
  rw [node93_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node94 : Integer.Sparse (Fin 2886) := [(1376, 123035280), (1388, -123035280), (1402, -123035280), (1421, 123035280), (1448, 123035280), (1456, -123035280), (2355, -37930200), (2382, 37930200), (2410, 37930200), (2468, -37930200), (2528, -480724920), (2536, -37930200), (2537, 480724920), (2551, 480724920), (2570, 37930200), (2571, -480724920), (2602, -480724920), (2612, 480724920)]

theorem node94_check : node94 =
    Integer.Sparse.merge (Integer.Sparse.scale (-4006041) entry_4_15) node93 := by decide +kernel

theorem node94_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node94 x = (((-4006041 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_15 x + (((-316085 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_16 x + ((1025294 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_17 x)) := by
  rw [node94_check, Integer.Sparse.eval_merge]
  rw [node93_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node95 : Integer.Sparse (Fin 2886) := [(1215, -110520960), (1225, 110520960), (1327, 110520960), (1350, -110520960), (1541, -110520960), (1559, 110520960), (2363, 159334320), (2379, -159334320), (2418, -159334320), (2453, 159334320), (2533, 159334320), (2556, -159334320)]

theorem node95_check : node95 =
    Integer.Sparse.merge (Integer.Sparse.scale (-921008) entry_4_19) (Integer.Sparse.scale (1327786) entry_4_20) := by decide +kernel

theorem node95_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node95 x = (((-921008 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_19 x + ((1327786 : ℤ) : ℝ) * Integer.Sparse.eval entry_4_20 x) := by
  rw [node95_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

end MUB6.Certificate.GramAssembly.Block1

end OAI
