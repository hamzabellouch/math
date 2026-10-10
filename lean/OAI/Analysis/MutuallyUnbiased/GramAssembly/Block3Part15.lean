import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Data
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Block3Part14

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

def node480 : Integer.Sparse (Fin 2886) := [(8, 353171520), (12, -353171520), (80, 706343040), (84, 706343040), (86, 353171520), (89, -353171520), (135, 353171520), (138, 353171520), (142, -706343040), (146, -353171520), (148, -706343040), (163, -353171520), (852, -303181152), (856, 303181152), (961, 1819086912), (965, 1515905760), (1032, -1515905760), (1036, -1819086912), (1050, 1212724608), (1086, -1212724608)]

theorem node480_check : node480 =
    Integer.Sparse.merge (Integer.Sparse.scale (2452580) entry_18_14) (Integer.Sparse.scale (-6316274) entry_18_15) := by decide +kernel

theorem node480_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node480 x = (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x) := by
  rw [node480_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node481 : Integer.Sparse (Fin 2886) := [(8, 353171520), (12, -353171520), (80, 706343040), (84, 706343040), (86, 353171520), (89, -353171520), (135, 353171520), (138, 353171520), (142, -706343040), (146, -353171520), (148, -706343040), (163, -353171520), (625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (852, -303181152), (856, 303181152), (961, 1819086912), (965, 1515905760), (1032, -1515905760), (1036, -1819086912), (1050, 1212724608), (1086, -1212724608)]

theorem node481_check : node481 =
    Integer.Sparse.merge (Integer.Sparse.scale (1117744) entry_18_13) node480 := by decide +kernel

theorem node481_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node481 x = (((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) := by
  rw [node481_check, Integer.Sparse.eval_merge]
  rw [node480_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node482 : Integer.Sparse (Fin 2886) := [(871, 651365568), (877, -396694272), (885, -651365568), (890, 396694272), (906, -651365568), (908, 99173568), (912, -198347136), (938, 651365568), (944, 198347136), (947, -99173568), (983, -99173568), (990, -2605462272), (995, 198347136), (1017, 2605462272), (1023, -198347136), (1042, 99173568), (1060, -396694272), (1066, 396694272), (1081, -396694272), (1090, 396694272)]

theorem node482_check : node482 =
    Integer.Sparse.merge (Integer.Sparse.scale (4523372) entry_18_16) (Integer.Sparse.scale (2066116) entry_18_17) := by decide +kernel

theorem node482_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node482 x = (((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) := by
  rw [node482_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node483 : Integer.Sparse (Fin 2886) := [(9, 1532228256), (13, -1532228256), (85, 2298342384), (88, -1532228256), (140, 1021485504), (144, -3064456512), (149, 2042971008), (150, -1532228256), (164, 2298342384), (166, -1532228256), (923, -216511920), (940, 216511920), (1009, -216511920), (1019, 216511920)]

theorem node483_check : node483 =
    Integer.Sparse.merge (Integer.Sparse.scale (15960711) entry_18_18) (Integer.Sparse.scale (902133) entry_18_19) := by decide +kernel

theorem node483_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node483 x = (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x) := by
  rw [node483_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node484 : Integer.Sparse (Fin 2886) := [(9, 1532228256), (13, -1532228256), (85, 2298342384), (88, -1532228256), (140, 1021485504), (144, -3064456512), (149, 2042971008), (150, -1532228256), (164, 2298342384), (166, -1532228256), (871, 651365568), (877, -396694272), (885, -651365568), (890, 396694272), (906, -651365568), (908, 99173568), (912, -198347136), (923, -216511920), (938, 651365568), (940, 216511920), (944, 198347136), (947, -99173568), (983, -99173568), (990, -2605462272), (995, 198347136), (1009, -216511920), (1017, 2605462272), (1019, 216511920), (1023, -198347136), (1042, 99173568), (1060, -396694272), (1066, 396694272), (1081, -396694272), (1090, 396694272)]

theorem node484_check : node484 =
    Integer.Sparse.merge node482 node483 := by decide +kernel

theorem node484_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node484 x = ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x)) := by
  rw [node484_check, Integer.Sparse.eval_merge]
  rw [node482_eval, node483_eval]

def node485 : Integer.Sparse (Fin 2886) := [(8, 353171520), (9, 1532228256), (12, -353171520), (13, -1532228256), (80, 706343040), (84, 706343040), (85, 2298342384), (86, 353171520), (88, -1532228256), (89, -353171520), (135, 353171520), (138, 353171520), (140, 1021485504), (142, -706343040), (144, -3064456512), (146, -353171520), (148, -706343040), (149, 2042971008), (150, -1532228256), (163, -353171520), (164, 2298342384), (166, -1532228256), (625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (852, -303181152), (856, 303181152), (871, 651365568), (877, -396694272), (885, -651365568), (890, 396694272), (906, -651365568), (908, 99173568), (912, -198347136), (923, -216511920), (938, 651365568), (940, 216511920), (944, 198347136), (947, -99173568), (961, 1819086912), (965, 1515905760), (983, -99173568), (990, -2605462272), (995, 198347136), (1009, -216511920), (1017, 2605462272), (1019, 216511920), (1023, -198347136), (1032, -1515905760), (1036, -1819086912), (1042, 99173568), (1050, 1212724608), (1060, -396694272), (1066, 396694272), (1081, -396694272), (1086, -1212724608), (1090, 396694272)]

theorem node485_check : node485 =
    Integer.Sparse.merge node481 node484 := by decide +kernel

theorem node485_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node485 x = ((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) := by
  rw [node485_check, Integer.Sparse.eval_merge]
  rw [node481_eval, node484_eval]

def node486 : Integer.Sparse (Fin 2886) := [(872, 743502048), (876, 2385968160), (886, -2385968160), (889, -743502048), (907, -821233056), (911, 1603600608), (939, -1603600608), (943, 821233056), (982, 1936486128), (991, -3578952240), (994, 449482032), (1018, -449482032), (1022, 3578952240), (1038, -1936486128), (1059, 1975351632), (1065, -1564735104), (1078, 1564735104), (1088, -1975351632)]

theorem node486_check : node486 =
    Integer.Sparse.merge (Integer.Sparse.scale (-8554511) entry_18_21) (Integer.Sparse.scale (-16299324) entry_18_22) := by decide +kernel

theorem node486_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node486 x = (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x) := by
  rw [node486_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node487 : Integer.Sparse (Fin 2886) := [(539, 567596880), (543, -567596880), (872, 743502048), (876, 2385968160), (886, -2385968160), (889, -743502048), (907, -821233056), (911, 1603600608), (939, -1603600608), (943, 821233056), (982, 1936486128), (991, -3578952240), (994, 449482032), (1018, -449482032), (1022, 3578952240), (1038, -1936486128), (1059, 1975351632), (1065, -1564735104), (1078, 1564735104), (1088, -1975351632)]

theorem node487_check : node487 =
    Integer.Sparse.merge (Integer.Sparse.scale (788329) entry_18_20) node486 := by decide +kernel

theorem node487_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node487 x = (((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) := by
  rw [node487_check, Integer.Sparse.eval_merge]
  rw [node486_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node488 : Integer.Sparse (Fin 2886) := [(105, 2484252000), (137, -2484252000), (853, 157413024), (859, -157413024), (962, -157413024), (966, -944478144), (1037, 944478144), (1041, 157413024), (1051, -629652096), (1052, -629652096), (1087, 629652096), (1089, 629652096)]

theorem node488_check : node488 =
    Integer.Sparse.merge (Integer.Sparse.scale (3279438) entry_18_23) (Integer.Sparse.scale (-3450350) entry_18_24) := by decide +kernel

theorem node488_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node488 x = (((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) := by
  rw [node488_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node489 : Integer.Sparse (Fin 2886) := [(199, 302643648), (202, -302643648), (436, 453965472), (439, -302643648), (489, 302643648), (493, -453965472), (544, 302643648), (546, -453965472), (564, 453965472), (568, -302643648), (930, 10184980032), (931, -10184980032), (1010, 2546245008), (1024, -2546245008), (1073, -2546245008), (1080, 2546245008)]

theorem node489_check : node489 =
    Integer.Sparse.merge (Integer.Sparse.scale (17682257) entry_18_25) (Integer.Sparse.scale (3152538) entry_18_26) := by decide +kernel

theorem node489_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node489 x = (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x) := by
  rw [node489_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node490 : Integer.Sparse (Fin 2886) := [(105, 2484252000), (137, -2484252000), (199, 302643648), (202, -302643648), (436, 453965472), (439, -302643648), (489, 302643648), (493, -453965472), (544, 302643648), (546, -453965472), (564, 453965472), (568, -302643648), (853, 157413024), (859, -157413024), (930, 10184980032), (931, -10184980032), (962, -157413024), (966, -944478144), (1010, 2546245008), (1024, -2546245008), (1037, 944478144), (1041, 157413024), (1051, -629652096), (1052, -629652096), (1073, -2546245008), (1080, 2546245008), (1087, 629652096), (1089, 629652096)]

theorem node490_check : node490 =
    Integer.Sparse.merge node488 node489 := by decide +kernel

theorem node490_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node490 x = ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x)) := by
  rw [node490_check, Integer.Sparse.eval_merge]
  rw [node488_eval, node489_eval]

def node491 : Integer.Sparse (Fin 2886) := [(105, 2484252000), (137, -2484252000), (199, 302643648), (202, -302643648), (436, 453965472), (439, -302643648), (489, 302643648), (493, -453965472), (539, 567596880), (543, -567596880), (544, 302643648), (546, -453965472), (564, 453965472), (568, -302643648), (853, 157413024), (859, -157413024), (872, 743502048), (876, 2385968160), (886, -2385968160), (889, -743502048), (907, -821233056), (911, 1603600608), (930, 10184980032), (931, -10184980032), (939, -1603600608), (943, 821233056), (962, -157413024), (966, -944478144), (982, 1936486128), (991, -3578952240), (994, 449482032), (1010, 2546245008), (1018, -449482032), (1022, 3578952240), (1024, -2546245008), (1037, 944478144), (1038, -1936486128), (1041, 157413024), (1051, -629652096), (1052, -629652096), (1059, 1975351632), (1065, -1564735104), (1073, -2546245008), (1078, 1564735104), (1080, 2546245008), (1087, 629652096), (1088, -1975351632), (1089, 629652096)]

theorem node491_check : node491 =
    Integer.Sparse.merge node487 node490 := by decide +kernel

theorem node491_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node491 x = ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x))) := by
  rw [node491_check, Integer.Sparse.eval_merge]
  rw [node487_eval, node490_eval]

def node492 : Integer.Sparse (Fin 2886) := [(8, 353171520), (9, 1532228256), (12, -353171520), (13, -1532228256), (80, 706343040), (84, 706343040), (85, 2298342384), (86, 353171520), (88, -1532228256), (89, -353171520), (105, 2484252000), (135, 353171520), (137, -2484252000), (138, 353171520), (140, 1021485504), (142, -706343040), (144, -3064456512), (146, -353171520), (148, -706343040), (149, 2042971008), (150, -1532228256), (163, -353171520), (164, 2298342384), (166, -1532228256), (199, 302643648), (202, -302643648), (436, 453965472), (439, -302643648), (489, 302643648), (493, -453965472), (539, 567596880), (543, -567596880), (544, 302643648), (546, -453965472), (564, 453965472), (568, -302643648), (625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (852, -303181152), (853, 157413024), (856, 303181152), (859, -157413024), (871, 651365568), (872, 743502048), (876, 2385968160), (877, -396694272), (885, -651365568), (886, -2385968160), (889, -743502048), (890, 396694272), (906, -651365568), (907, -821233056), (908, 99173568), (911, 1603600608), (912, -198347136), (923, -216511920), (930, 10184980032), (931, -10184980032), (938, 651365568), (939, -1603600608), (940, 216511920), (943, 821233056), (944, 198347136), (947, -99173568), (961, 1819086912), (962, -157413024), (965, 1515905760), (966, -944478144), (982, 1936486128), (983, -99173568), (990, -2605462272), (991, -3578952240), (994, 449482032), (995, 198347136), (1009, -216511920), (1010, 2546245008), (1017, 2605462272), (1018, -449482032), (1019, 216511920), (1022, 3578952240), (1023, -198347136), (1024, -2546245008), (1032, -1515905760), (1036, -1819086912), (1037, 944478144), (1038, -1936486128), (1041, 157413024), (1042, 99173568), (1050, 1212724608), (1051, -629652096), (1052, -629652096), (1059, 1975351632), (1060, -396694272), (1065, -1564735104), (1066, 396694272), (1073, -2546245008), (1078, 1564735104), (1080, 2546245008), (1081, -396694272), (1086, -1212724608), (1087, 629652096), (1088, -1975351632), (1089, 629652096), (1090, 396694272)]

theorem node492_check : node492 =
    Integer.Sparse.merge node485 node491 := by decide +kernel

theorem node492_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node492 x = (((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) + ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x)))) := by
  rw [node492_check, Integer.Sparse.eval_merge]
  rw [node485_eval, node491_eval]

def node493 : Integer.Sparse (Fin 2886) := [(8, 577457424), (9, 1532228256), (10, -299047872), (12, -278409552), (13, -1532228256), (20, 1322762688), (21, -224300016), (31, -1322762688), (32, -299066688), (34, -224300016), (43, 330690672), (44, -224300016), (67, -330690672), (68, -299066688), (73, -224300016), (80, -863658288), (83, -27259920), (84, 930628944), (85, 2298342384), (86, -768258000), (88, -1532228256), (89, -353171520), (95, 1653453360), (103, -1984144032), (104, -224300016), (105, 2484252000), (122, 1984144032), (123, -224300016), (134, 27259920), (135, 652219392), (136, -1653453360), (137, -2484252000), (138, -600043572), (140, 1021485504), (142, -482057136), (143, -224300016), (144, -3064456512), (146, 469210128), (148, 415086480), (149, 2042971008), (150, -1532228256), (163, 394448160), (164, 2298342384), (166, -1532228256), (168, 56071476), (171, -112150008), (175, -112150008), (177, 149523936), (178, -149533344), (183, 1121500080), (186, 897200064), (188, -598133376), (190, -672900048), (199, 302643648), (202, -302643648), (331, 224300016), (334, 448600032), (379, 1345800096), (401, 897200064), (403, -1121500080), (405, -448600032), (422, -785050056), (436, 453965472), (439, -302643648), (489, 302643648), (493, -453965472), (494, -149533344), (496, 224300016), (517, 672900048), (519, 1345800096), (535, 1009350072), (536, -1121500080), (537, -747666720), (539, 567596880), (543, -567596880), (544, 302643648), (546, -453965472), (564, 453965472), (568, -302643648), (625, 53651712), (629, -53651712), (776, -321910272), (780, -268258560), (799, -214606848), (824, 268258560), (825, 321910272), (832, 214606848), (852, -1231637856), (853, -659573376), (856, 585202272), (858, 646435584), (859, 659573376), (871, -42068736), (872, 520379904), (876, 2385968160), (877, -396694272), (878, 517734336), (885, 42068736), (886, -2903702496), (889, -743502048), (890, 396694272), (891, 223122144), (906, -824724144), (907, -1690550016), (908, 99173568), (911, 1603600608), (912, -198347136), (913, 194636928), (923, -216511920), (930, 10184980032), (931, -10184980032), (938, 824724144), (939, -1798237536), (940, 216511920), (943, 821233056), (944, 198347136), (946, 869316960), (947, -99173568), (960, 826673040), (961, -794955744), (962, -1382892624), (965, 1515905760), (966, -127491744), (967, 549892080), (981, -866792880), (982, 1473342432), (983, -99173568), (990, -1565310816), (991, -4854442464), (994, 449482032), (995, 198347136), (996, -16899408), (1009, -216511920), (1010, 2546245008), (1017, 1565310816), (1018, -432582624), (1019, 216511920), (1022, 3578952240), (1023, -198347136), (1024, -2546245008), (1025, 1275490224), (1031, -826673040), (1032, -2065797840), (1033, 866792880), (1036, -691002432), (1037, 127491744), (1038, -1936486128), (1039, 1485958176), (1040, 463143696), (1041, 1382892624), (1042, 99173568), (1050, 930703488), (1051, -1446638496), (1052, 595827504), (1059, 1975351632), (1060, -396694272), (1065, -1564735104), (1066, 396694272), (1073, -2546245008), (1078, 1564735104), (1080, 2546245008), (1081, -396694272), (1086, -930703488), (1087, -595827504), (1088, -1975351632), (1089, 1446638496), (1090, 396694272), (1094, -96543504), (1098, 83075856), (1101, -646194816), (1108, 646194816), (1111, 96543504), (1112, -83075856)]

theorem node493_check : node493 =
    Integer.Sparse.merge node479 node492 := by decide +kernel

theorem node493_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node493 x = ((((((-8510275 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_0 x + (((37861 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_1 x + ((4672623 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_2 x)) + (((3611637 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_3 x + (((-2291217 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_4 x + ((1583616 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_5 x))) + ((((-1148157 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_6 x + (((4157406 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_7 x + ((-9345834 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_8 x)) + ((((-4897979 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_9 x + ((-6889389 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_10 x) + (((-1958480 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_11 x + ((-3725397 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_12 x)))) + (((((1117744 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_13 x + (((2452580 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_14 x + ((-6316274 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_15 x)) + ((((4523372 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_16 x + ((2066116 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_17 x) + (((15960711 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_18 x + ((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_19 x))) + ((((788329 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_20 x + (((-8554511 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_21 x + ((-16299324 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_22 x)) + ((((3279438 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_23 x + ((-3450350 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_24 x) + (((17682257 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_25 x + ((3152538 : ℤ) : ℝ) * Integer.Sparse.eval entry_18_26 x))))) := by
  rw [node493_check, Integer.Sparse.eval_merge]
  rw [node479_eval, node492_eval]

def node494 : Integer.Sparse (Fin 2886) := [(914, -1697683680), (918, -33659760), (926, -67319520), (997, 1697683680), (1002, 33659760), (1004, 67319520)]

theorem node494_check : node494 =
    Integer.Sparse.merge (Integer.Sparse.scale (-2357894) entry_19_1) (Integer.Sparse.scale (-140249) entry_19_2) := by decide +kernel

theorem node494_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node494 x = (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x) := by
  rw [node494_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node495 : Integer.Sparse (Fin 2886) := [(914, -1697683680), (918, -33659760), (926, -67319520), (997, 1697683680), (1002, 33659760), (1004, 67319520), (2170, -1140278160), (2188, 1140278160), (2245, -1140278160), (2254, 1140278160)]

theorem node495_check : node495 =
    Integer.Sparse.merge (Integer.Sparse.scale (4751159) entry_19_0) node494 := by decide +kernel

theorem node495_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node495 x = (((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) := by
  rw [node495_check, Integer.Sparse.eval_merge]
  rw [node494_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node496 : Integer.Sparse (Fin 2886) := [(2166, -115473120), (2173, -230946240), (2239, 115473120), (2241, 230946240), (2429, -660257520), (2436, -660257520), (2460, 660257520), (2462, 660257520), (2565, -660257520), (2610, 660257520)]

theorem node496_check : node496 =
    Integer.Sparse.merge (Integer.Sparse.scale (-481138) entry_19_4) (Integer.Sparse.scale (-2751073) entry_19_5) := by decide +kernel

theorem node496_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node496 x = (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x) := by
  rw [node496_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node497 : Integer.Sparse (Fin 2886) := [(2166, -115473120), (2173, -230946240), (2239, 115473120), (2241, 230946240), (2425, 6314217120), (2429, -660257520), (2436, -660257520), (2456, -7892771400), (2460, 660257520), (2462, 660257520), (2559, 3157108560), (2565, -660257520), (2608, -3157108560), (2610, 660257520), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2861, -2104739040)]

theorem node497_check : node497 =
    Integer.Sparse.merge (Integer.Sparse.scale (21924365) entry_19_3) node496 := by decide +kernel

theorem node497_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node497 x = (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x)) := by
  rw [node497_check, Integer.Sparse.eval_merge]
  rw [node496_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node498 : Integer.Sparse (Fin 2886) := [(914, -1697683680), (918, -33659760), (926, -67319520), (997, 1697683680), (1002, 33659760), (1004, 67319520), (2166, -115473120), (2170, -1140278160), (2173, -230946240), (2188, 1140278160), (2239, 115473120), (2241, 230946240), (2245, -1140278160), (2254, 1140278160), (2425, 6314217120), (2429, -660257520), (2436, -660257520), (2456, -7892771400), (2460, 660257520), (2462, 660257520), (2559, 3157108560), (2565, -660257520), (2608, -3157108560), (2610, 660257520), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2861, -2104739040)]

theorem node498_check : node498 =
    Integer.Sparse.merge node495 node497 := by decide +kernel

theorem node498_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node498 x = ((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) := by
  rw [node498_check, Integer.Sparse.eval_merge]
  rw [node495_eval, node497_eval]

def node499 : Integer.Sparse (Fin 2886) := [(1254, -253890240), (1258, -253890240), (1278, 253890240), (1279, 253890240), (1418, -253890240), (1455, 253890240), (2460, 91236480), (2462, 182472960), (2563, -91236480), (2565, -182472960)]

theorem node499_check : node499 =
    Integer.Sparse.merge (Integer.Sparse.scale (380152) entry_19_7) (Integer.Sparse.scale (-1057876) entry_19_8) := by decide +kernel

theorem node499_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node499 x = (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x) := by
  rw [node499_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node500 : Integer.Sparse (Fin 2886) := [(1254, -253890240), (1258, -253890240), (1278, 253890240), (1279, 253890240), (1418, -253890240), (1455, 253890240), (2162, -4213756080), (2235, 3160317060), (2460, 91236480), (2462, 182472960), (2563, -91236480), (2565, -182472960), (2857, 1053439020)]

theorem node500_check : node500 =
    Integer.Sparse.merge (Integer.Sparse.scale (-5852439) entry_19_6) node499 := by decide +kernel

theorem node500_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node500 x = (((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) := by
  rw [node500_check, Integer.Sparse.eval_merge]
  rw [node499_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node501 : Integer.Sparse (Fin 2886) := [(1251, 4551535680), (1273, -4551535680), (1414, 2275767840), (1454, -2275767840), (2429, 2341711920), (2436, -2341711920), (2460, 2341711920), (2462, -2341711920), (2563, 2341711920), (2565, -2341711920)]

theorem node501_check : node501 =
    Integer.Sparse.merge (Integer.Sparse.scale (-9757133) entry_19_9) (Integer.Sparse.scale (9482366) entry_19_10) := by decide +kernel

theorem node501_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node501 x = (((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) := by
  rw [node501_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node502 : Integer.Sparse (Fin 2886) := [(2163, -4301709120), (2166, -321689520), (2240, 4301709120), (2241, 321689520)]

theorem node502_check : node502 =
    Integer.Sparse.merge (Integer.Sparse.scale (5974596) entry_19_11) (Integer.Sparse.scale (446791) entry_19_12) := by decide +kernel

theorem node502_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node502 x = (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x) := by
  rw [node502_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node503 : Integer.Sparse (Fin 2886) := [(1251, 4551535680), (1273, -4551535680), (1414, 2275767840), (1454, -2275767840), (2163, -4301709120), (2166, -321689520), (2240, 4301709120), (2241, 321689520), (2429, 2341711920), (2436, -2341711920), (2460, 2341711920), (2462, -2341711920), (2563, 2341711920), (2565, -2341711920)]

theorem node503_check : node503 =
    Integer.Sparse.merge node501 node502 := by decide +kernel

theorem node503_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node503 x = ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)) := by
  rw [node503_check, Integer.Sparse.eval_merge]
  rw [node501_eval, node502_eval]

def node504 : Integer.Sparse (Fin 2886) := [(1251, 4551535680), (1254, -253890240), (1258, -253890240), (1273, -4551535680), (1278, 253890240), (1279, 253890240), (1414, 2275767840), (1418, -253890240), (1454, -2275767840), (1455, 253890240), (2162, -4213756080), (2163, -4301709120), (2166, -321689520), (2235, 3160317060), (2240, 4301709120), (2241, 321689520), (2429, 2341711920), (2436, -2341711920), (2460, 2432948400), (2462, -2159238960), (2563, 2250475440), (2565, -2524184880), (2857, 1053439020)]

theorem node504_check : node504 =
    Integer.Sparse.merge node500 node503 := by decide +kernel

theorem node504_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node504 x = ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x))) := by
  rw [node504_check, Integer.Sparse.eval_merge]
  rw [node500_eval, node503_eval]

def node505 : Integer.Sparse (Fin 2886) := [(914, -1697683680), (918, -33659760), (926, -67319520), (997, 1697683680), (1002, 33659760), (1004, 67319520), (1251, 4551535680), (1254, -253890240), (1258, -253890240), (1273, -4551535680), (1278, 253890240), (1279, 253890240), (1414, 2275767840), (1418, -253890240), (1454, -2275767840), (1455, 253890240), (2162, -4213756080), (2163, -4301709120), (2166, -437162640), (2170, -1140278160), (2173, -230946240), (2188, 1140278160), (2235, 3160317060), (2239, 115473120), (2240, 4301709120), (2241, 552635760), (2245, -1140278160), (2254, 1140278160), (2425, 6314217120), (2429, 1681454400), (2436, -3001969440), (2456, -7892771400), (2460, 3093205920), (2462, -1498981440), (2559, 3157108560), (2563, 2250475440), (2565, -3184442400), (2608, -3157108560), (2610, 660257520), (2787, 4209478080), (2799, -2630923800), (2834, 2104739040), (2857, 1053439020), (2861, -2104739040)]

theorem node505_check : node505 =
    Integer.Sparse.merge node498 node504 := by decide +kernel

theorem node505_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node505 x = (((((4751159 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_0 x + (((-2357894 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_1 x + ((-140249 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_2 x)) + (((21924365 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_3 x + (((-481138 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_4 x + ((-2751073 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_5 x))) + ((((-5852439 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_6 x + (((380152 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_7 x + ((-1057876 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_8 x)) + ((((-9757133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_9 x + ((9482366 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_10 x) + (((5974596 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_11 x + ((446791 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_12 x)))) := by
  rw [node505_check, Integer.Sparse.eval_merge]
  rw [node498_eval, node504_eval]

def node506 : Integer.Sparse (Fin 2886) := [(918, 720293760), (1004, -720293760), (2163, -6006663120), (2172, -12013326240), (2236, 6006663120), (2240, 12013326240)]

theorem node506_check : node506 =
    Integer.Sparse.merge (Integer.Sparse.scale (-1000408) entry_19_14) (Integer.Sparse.scale (-25027763) entry_19_15) := by decide +kernel

theorem node506_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node506 x = (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x) := by
  rw [node506_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node507 : Integer.Sparse (Fin 2886) := [(918, 720293760), (1004, -720293760), (1975, 862133520), (1976, 1724267040), (2071, -862133520), (2072, -1724267040), (2163, -6006663120), (2172, -12013326240), (2236, 6006663120), (2240, 12013326240)]

theorem node507_check : node507 =
    Integer.Sparse.merge (Integer.Sparse.scale (3592223) entry_19_13) node506 := by decide +kernel

theorem node507_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node507 x = (((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) := by
  rw [node507_check, Integer.Sparse.eval_merge]
  rw [node506_eval]
  all_goals simp only [Integer.Sparse.eval_scale]

def node508 : Integer.Sparse (Fin 2886) := [(2425, 456104160), (2440, -6515904000), (2456, 2280520800), (2466, 6515904000), (2559, -1672381920), (2577, -3257952000), (2618, 3257952000), (2787, -456104160), (2834, -608138880)]

theorem node508_check : node508 =
    Integer.Sparse.merge (Integer.Sparse.scale (3167390) entry_19_16) (Integer.Sparse.scale (-13574800) entry_19_17) := by decide +kernel

theorem node508_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node508 x = (((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) := by
  rw [node508_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node509 : Integer.Sparse (Fin 2886) := [(923, -216511920), (940, 216511920), (1009, -216511920), (1019, 216511920), (2819, 10071274080), (2824, 10071274080), (2839, -20142548160)]

theorem node509_check : node509 =
    Integer.Sparse.merge (Integer.Sparse.scale (902133) entry_19_18) (Integer.Sparse.scale (41963642) entry_19_19) := by decide +kernel

theorem node509_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node509 x = (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x) := by
  rw [node509_check, Integer.Sparse.eval_merge]
  all_goals simp only [Integer.Sparse.eval_scale]

def node510 : Integer.Sparse (Fin 2886) := [(923, -216511920), (940, 216511920), (1009, -216511920), (1019, 216511920), (2425, 456104160), (2440, -6515904000), (2456, 2280520800), (2466, 6515904000), (2559, -1672381920), (2577, -3257952000), (2618, 3257952000), (2787, -456104160), (2819, 10071274080), (2824, 10071274080), (2834, -608138880), (2839, -20142548160)]

theorem node510_check : node510 =
    Integer.Sparse.merge node508 node509 := by decide +kernel

theorem node510_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node510 x = ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x)) := by
  rw [node510_check, Integer.Sparse.eval_merge]
  rw [node508_eval, node509_eval]

def node511 : Integer.Sparse (Fin 2886) := [(918, 720293760), (923, -216511920), (940, 216511920), (1004, -720293760), (1009, -216511920), (1019, 216511920), (1975, 862133520), (1976, 1724267040), (2071, -862133520), (2072, -1724267040), (2163, -6006663120), (2172, -12013326240), (2236, 6006663120), (2240, 12013326240), (2425, 456104160), (2440, -6515904000), (2456, 2280520800), (2466, 6515904000), (2559, -1672381920), (2577, -3257952000), (2618, 3257952000), (2787, -456104160), (2819, 10071274080), (2824, 10071274080), (2834, -608138880), (2839, -20142548160)]

theorem node511_check : node511 =
    Integer.Sparse.merge node507 node510 := by decide +kernel

theorem node511_eval (x : Fin 2886 → ℝ) :
    Integer.Sparse.eval node511 x = ((((3592223 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_13 x + (((-1000408 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_14 x + ((-25027763 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_15 x)) + ((((3167390 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_16 x + ((-13574800 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_17 x) + (((902133 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_18 x + ((41963642 : ℤ) : ℝ) * Integer.Sparse.eval entry_19_19 x))) := by
  rw [node511_check, Integer.Sparse.eval_merge]
  rw [node507_eval, node510_eval]

end MUB6.Certificate.GramAssembly.Block3

end OAI
