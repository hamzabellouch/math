import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures2263To2479

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

def e2480 : ℝ := e2414 + e4
lemma b2480 : Encl e2480 (482618918919 / 250000000000 : ℝ) (1930475675679 / 1000000000000 : ℝ) := by
  exact Encl.add b2414 b4 (by norm_num) (by norm_num)

def e2481 : ℝ := e2480 / e23
lemma b2481 : Encl e2481 (482618918919 / 500000000000 : ℝ) (12065472973 / 12500000000 : ℝ) := by
  exact Encl.div_nonneg b2480 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2482 : ℝ := e2414 / e2412
lemma b2482 : Encl e2482 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2414 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2483 : ℝ := e89 * e2482
lemma b2483 : Encl e2483 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2482 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2484 : ℝ := e2482 ^ 2
lemma b2484 : Encl e2484 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2482 (by norm_num) 2 (by norm_num) (by norm_num)

def e2485 : ℝ := e91 * e2484
lemma b2485 : Encl e2485 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2486 : ℝ := e5 + e2485
lemma b2486 : Encl e2486 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2485 (by norm_num) (by norm_num)

def e2487 : ℝ := Real.sqrt e2486
lemma b2487 : Encl e2487 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2486 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2488 : ℝ := e2483 * e2487
lemma b2488 : Encl e2488 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2483 b2487 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2489 : ℝ := e97 * e2484
lemma b2489 : Encl e2489 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2490 : ℝ := e2488 - e2489
lemma b2490 : Encl e2490 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2488 b2489 (by norm_num) (by norm_num)

def e2491 : ℝ := e2481 * e2490
lemma b2491 : Encl e2491 (164498272881 / 250000000000 : ℝ) (657993091549 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2481 b2490 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2492 : ℝ := e2481 / e2412
lemma b2492 : Encl e2492 (349723854289 / 500000000000 : ℝ) (34972385429 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2493 : ℝ := e89 * e2492
lemma b2493 : Encl e2493 (49589551383 / 40000000000 : ℝ) (61986939229 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2492 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2494 : ℝ := e2492 ^ 2
lemma b2494 : Encl e2494 (97845419407 / 200000000000 : ℝ) (244613548519 / 500000000000 : ℝ) := by
  exact Encl.pow b2492 (by norm_num) 2 (by norm_num) (by norm_num)

def e2495 : ℝ := e91 * e2494
lemma b2495 : Encl e2495 (76847612699 / 200000000000 : ℝ) (384238063499 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2496 : ℝ := e5 + e2495
lemma b2496 : Encl e2496 (276847612699 / 200000000000 : ℝ) (1384238063499 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2495 (by norm_num) (by norm_num)

def e2497 : ℝ := Real.sqrt e2496
lemma b2497 : Encl e2497 (588268234629 / 500000000000 : ℝ) (1176536469261 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2496 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2498 : ℝ := e2493 * e2497
lemma b2498 : Encl e2498 (729298946203 / 500000000000 : ℝ) (22790592069 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b2493 b2497 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2499 : ℝ := e97 * e2494
lemma b2499 : Encl e2499 (76847612699 / 100000000000 : ℝ) (192119031749 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2494 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2500 : ℝ := e2498 - e2499
lemma b2500 : Encl e2500 (69012176541 / 100000000000 : ℝ) (345060882713 / 500000000000 : ℝ) := by
  exact Encl.sub b2498 b2499 (by norm_num) (by norm_num)

def e2501 : ℝ := e2414 * e2500
lemma b2501 : Encl e2501 (162304968759 / 250000000000 : ℝ) (324609937527 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2414 b2500 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2502 : ℝ := e2491 - e2501
lemma b2502 : Encl e2502 (877321647 / 100000000000 : ℝ) (8773216513 / 1000000000000 : ℝ) := by
  exact Encl.sub b2491 b2501 (by norm_num) (by norm_num)

def e2503 : ℝ := e2481 ^ 2
lemma b2503 : Encl e2503 (465842041797 / 500000000000 : ℝ) (931684083599 / 1000000000000 : ℝ) := by
  exact Encl.pow b2481 (by norm_num) 2 (by norm_num) (by norm_num)

def e2504 : ℝ := e8 * e2503
lemma b2504 : Encl e2504 (456525200961 / 500000000000 : ℝ) (114131300241 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2503 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2505 : ℝ := e5 - e2504
lemma b2505 : Encl e2505 (10868699759 / 125000000000 : ℝ) (43474799039 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2504 (by norm_num) (by norm_num)

def e2506 : ℝ := e5 - e2503
lemma b2506 : Encl e2506 (68315916401 / 1000000000000 : ℝ) (34157958203 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2503 (by norm_num) (by norm_num)

def e2507 : ℝ := Real.sqrt e2506
lemma b2507 : Encl e2507 (261373136341 / 1000000000000 : ℝ) (8167910511 / 31250000000 : ℝ) := by
  exact Encl.sqrt b2506 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2508 : ℝ := e2505 / e2507
lemma b2508 : Encl e2508 (83166157859 / 250000000000 : ℝ) (166332315737 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2505 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2509 : ℝ := e5 - e2508
lemma b2509 : Encl e2509 (333667684263 / 500000000000 : ℝ) (166833842141 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2508 (by norm_num) (by norm_num)

def e2510 : ℝ := e8 * e2444
lemma b2510 : Encl e2510 (867277820277 / 1000000000000 : ℝ) (867277820283 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2444 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2511 : ℝ := e5 - e2510
lemma b2511 : Encl e2511 (132722179717 / 1000000000000 : ℝ) (132722179723 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2510 (by norm_num) (by norm_num)

def e2512 : ℝ := e2511 / e2446
lemma b2512 : Encl e2512 (48917231209 / 125000000000 : ℝ) (3913378497 / 10000000000 : ℝ) := by
  exact Encl.div_nonneg b2511 b2446 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2513 : ℝ := e5 - e2512
lemma b2513 : Encl e2513 (6086621503 / 10000000000 : ℝ) (76082768791 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b2512 (by norm_num) (by norm_num)

def e2514 : ℝ := e2509 - e2513
lemma b2514 : Encl e2514 (29336609099 / 500000000000 : ℝ) (7334152283 / 125000000000 : ℝ) := by
  exact Encl.sub b2509 b2513 (by norm_num) (by norm_num)

def e2515 : ℝ := e2502 * e2514
lemma b2515 : Encl e2515 (128688211 / 250000000000 : ℝ) (32172053 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2502 b2514 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2516 : ℝ := e2500 - e2490
lemma b2516 : Encl e2516 (4215825791 / 500000000000 : ℝ) (8431651621 / 1000000000000 : ℝ) := by
  exact Encl.sub b2500 b2490 (by norm_num) (by norm_num)

def e2517 : ℝ := e5 + e2507
lemma b2517 : Encl e2517 (1261373136341 / 1000000000000 : ℝ) (39417910511 / 31250000000 : ℝ) := by
  exact Encl.add b5 b2507 (by norm_num) (by norm_num)

def e2518 : ℝ := e2481 / e2517
lemma b2518 : Encl e2518 (382613918919 / 500000000000 : ℝ) (765227837847 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2519 : ℝ := e2518 ^ 2
lemma b2519 : Encl e2519 (292786821901 / 500000000000 : ℝ) (73196705477 / 125000000000 : ℝ) := by
  exact Encl.pow b2518 (by norm_num) 2 (by norm_num) (by norm_num)

def e2520 : ℝ := e5 + e2519
lemma b2520 : Encl e2520 (792786821901 / 500000000000 : ℝ) (198196705477 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2519 (by norm_num) (by norm_num)

def e2521 : ℝ := Real.sqrt e2520
lemma b2521 : Encl e2521 (1259195633649 / 1000000000000 : ℝ) (157399454207 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2520 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2522 : ℝ := e5 + e2521
lemma b2522 : Encl e2522 (2259195633649 / 1000000000000 : ℝ) (282399454207 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2521 (by norm_num) (by norm_num)

def e2523 : ℝ := e2518 / e2522
lemma b2523 : Encl e2523 (338716942631 / 1000000000000 : ℝ) (338716942637 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2518 b2522 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2524 : ℝ := Real.arcsin e2481
lemma b2524 : Encl e2524 (326587952167 / 250000000000 : ℝ) (326587952179 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e2481) (a := (338716942631 / 1000000000000 : ℝ)) (b := (338716942637 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (482618918919 / 500000000000 : ℝ) by norm_num).trans b2481.1
        exact b2481.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2481) (338716942631 / 1000000000000 : ℝ) (338716942637 / 1000000000000 : ℝ) from b2523) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2525 : ℝ := e59 * e2524
lemma b2525 : Encl e2525 (33311971121 / 50000000000 : ℝ) (333119711223 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2526 : ℝ := e61 * e2481
lemma b2526 : Encl e2526 (23648327027 / 50000000000 : ℝ) (236483270271 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2481 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2527 : ℝ := e2526 * e2507
lemma b2527 : Encl e2527 (24724149617 / 200000000000 : ℝ) (30905187023 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2526 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2528 : ℝ := e2525 - e2527
lemma b2528 : Encl e2528 (67827334291 / 125000000000 : ℝ) (542618674361 / 1000000000000 : ℝ) := by
  exact Encl.sub b2525 b2527 (by norm_num) (by norm_num)

def e2529 : ℝ := e43 * e2507
lemma b2529 : Encl e2529 (261373136341 / 20000000000 : ℝ) (8167910511 / 625000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2507 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2530 : ℝ := e2481 / e2529
lemma b2530 : Encl e2530 (14771798683 / 200000000000 : ℝ) (73858993419 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2481 b2529 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2531 : ℝ := e2528 - e2530
lemma b2531 : Encl e2531 (468759680909 / 1000000000000 : ℝ) (234379840473 / 500000000000 : ℝ) := by
  exact Encl.sub b2528 b2530 (by norm_num) (by norm_num)

def e2532 : ℝ := e2531 - e2461
lemma b2532 : Encl e2532 (27965128457 / 500000000000 : ℝ) (55930256973 / 1000000000000 : ℝ) := by
  exact Encl.sub b2531 b2461 (by norm_num) (by norm_num)

def e2533 : ℝ := e2516 * e2532
lemma b2533 : Encl e2533 (471584439 / 1000000000000 : ℝ) (235792221 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2516 b2532 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2534 : ℝ := e2515 + e2533
lemma b2534 : Encl e2534 (986337283 / 1000000000000 : ℝ) (98633729 / 100000000000 : ℝ) := by
  exact Encl.add b2515 b2533 (by norm_num) (by norm_num)

def e2535 : ℝ := e2481 - e2414
lemma b2535 : Encl e2535 (2450548077 / 100000000000 : ℝ) (12252740387 / 500000000000 : ℝ) := by
  exact Encl.sub b2481 b2414 (by norm_num) (by norm_num)

def e2536 : ℝ := e2534 / e2535
lemma b2536 : Encl e2536 (40249660559 / 1000000000000 : ℝ) (10062415213 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2534 b2535 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2537 : ℝ := e2479 + e2536
lemma b2537 : Encl e2537 (-2423583837 / 62500000000 : ℝ) (-19388670529 / 500000000000 : ℝ) := by
  exact Encl.add b2479 b2536 (by norm_num) (by norm_num)

def e2538 : ℝ := e4 * e2500
lemma b2538 : Encl e2538 (683043406341 / 1000000000000 : ℝ) (683043406359 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2500 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2539 : ℝ := e4 / e2412
lemma b2539 : Encl e2539 (35860265167 / 50000000000 : ℝ) (358602651671 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2540 : ℝ := e89 * e2539
lemma b2540 : Encl e2540 (635606650897 / 500000000000 : ℝ) (1271213301799 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2541 : ℝ := e2539 ^ 2
lemma b2541 : Encl e2541 (514383447139 / 1000000000000 : ℝ) (257191723571 / 500000000000 : ℝ) := by
  exact Encl.pow b2539 (by norm_num) 2 (by norm_num) (by norm_num)

def e2542 : ℝ := e91 * e2541
lemma b2542 : Encl e2542 (50499476833 / 125000000000 : ℝ) (100998953667 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2543 : ℝ := e5 + e2542
lemma b2543 : Encl e2543 (175499476833 / 125000000000 : ℝ) (350998953667 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2542 (by norm_num) (by norm_num)

def e2544 : ℝ := Real.sqrt e2543
lemma b2544 : Encl e2544 (59245164669 / 50000000000 : ℝ) (1184903293383 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2543 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2545 : ℝ := e2540 * e2544
lemma b2545 : Encl e2545 (376566206971 / 250000000000 : ℝ) (753132413947 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2540 b2544 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2546 : ℝ := e97 * e2541
lemma b2546 : Encl e2546 (807991629329 / 1000000000000 : ℝ) (161598325867 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2547 : ℝ := e2545 - e2546
lemma b2547 : Encl e2547 (698273198549 / 1000000000000 : ℝ) (139654639713 / 200000000000 : ℝ) := by
  exact Encl.sub b2545 b2546 (by norm_num) (by norm_num)

def e2548 : ℝ := e2481 * e2547
lemma b2548 : Encl e2548 (673999712387 / 1000000000000 : ℝ) (134799942481 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2481 b2547 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2549 : ℝ := e2538 - e2548
lemma b2549 : Encl e2549 (565230871 / 62500000000 : ℝ) (2260923493 / 250000000000 : ℝ) := by
  exact Encl.sub b2538 b2548 (by norm_num) (by norm_num)

def e2550 : ℝ := e165 - e2509
lemma b2550 : Encl e2550 (52664631411 / 1000000000000 : ℝ) (26332315751 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2509 (by norm_num) (by norm_num)

def e2551 : ℝ := e2549 * e2550
lemma b2551 : Encl e2551 (476282807 / 1000000000000 : ℝ) (476282811 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2549 b2550 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2552 : ℝ := e2547 - e2500
lemma b2552 : Encl e2552 (8151433123 / 1000000000000 : ℝ) (1630286631 / 200000000000 : ℝ) := by
  exact Encl.sub b2547 b2500 (by norm_num) (by norm_num)

def e2553 : ℝ := e183 - e2531
lemma b2553 : Encl e2553 (25696544283 / 500000000000 : ℝ) (25696544367 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b2531 (by norm_num) (by norm_num)

def e2554 : ℝ := e2552 * e2553
lemma b2554 : Encl e2554 (104731831 / 250000000000 : ℝ) (13091479 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b2552 b2553 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2555 : ℝ := e2551 + e2554
lemma b2555 : Encl e2555 (895210131 / 1000000000000 : ℝ) (895210139 / 1000000000000 : ℝ) := by
  exact Encl.add b2551 b2554 (by norm_num) (by norm_num)

def e2556 : ℝ := e4 - e2481
lemma b2556 : Encl e2556 (2450548077 / 100000000000 : ℝ) (24505480773 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b2481 (by norm_num) (by norm_num)

def e2557 : ℝ := e2555 / e2556
lemma b2557 : Encl e2557 (2283188553 / 62500000000 : ℝ) (1826550859 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b2555 b2556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2558 : ℝ := e2537 + e2557
lemma b2558 : Encl e2558 (-35098821 / 15625000000 : ℝ) (-1123161939 / 500000000000 : ℝ) := by
  exact Encl.add b2537 b2557 (by norm_num) (by norm_num)

def e2559 : ℝ := e924 / e2412
lemma b2559 : Encl e2559 (695652173913 / 1000000000000 : ℝ) (347826086957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2560 : ℝ := min e7 e2559
lemma b2560 : Encl e2560 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2559 (by norm_num) (by norm_num)

def e2561 : ℝ := e2560 - e5
lemma b2561 : Encl e2561 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2560 b5 (by norm_num) (by norm_num)

def e2562 : ℝ := e23 * e2412
lemma b2562 : Encl e2562 (69 / 25 : ℝ) (69 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2412 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2563 : ℝ := e2562 * e2423
lemma b2563 : Encl e2563 (1936427638701 / 1000000000000 : ℝ) (387285527741 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2562 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2564 : ℝ := e2563 / e0
lemma b2564 : Encl e2564 (308192030639 / 500000000000 : ℝ) (3852400383 / 6250000000 : ℝ) := by
  exact Encl.div_nonneg b2563 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2565 : ℝ := e2561 + e2564
lemma b2565 : Encl e2565 (149037087547 / 500000000000 : ℝ) (298074175097 / 1000000000000 : ℝ) := by
  exact Encl.add b2561 b2564 (by norm_num) (by norm_num)

def e2566 : ℝ := e23 * e2417
lemma b2566 : Encl e2566 (4761 / 1250 : ℝ) (4761 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2417 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2567 : ℝ := e2566 * e2423
lemma b2567 : Encl e2567 (83508441919 / 31250000000 : ℝ) (2672270141413 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2566 b2423 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2568 : ℝ := e0 + e2567
lemma b2568 : Encl e2568 (5813862794997 / 1000000000000 : ℝ) (5813862795003 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2567 (by norm_num) (by norm_num)

def e2569 : ℝ := Real.sqrt e2568
lemma b2569 : Encl e2569 (12055976521 / 5000000000 : ℝ) (1205597652101 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2568 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2570 : ℝ := e932 * e2569
lemma b2570 : Encl e2570 (383753651423 / 250000000000 : ℝ) (11992301607 / 7812500000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2571 : ℝ := e2412 ^ 3
lemma b2571 : Encl e2571 (328509 / 125000 : ℝ) (328509 / 125000 : ℝ) := by
  exact Encl.pow b2412 (by norm_num) 3 (by norm_num) (by norm_num)

def e2572 : ℝ := e939 * e2571
lemma b2572 : Encl e2572 (22010103 / 62500000 : ℝ) (22010103 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2571 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2573 : ℝ := min e2572 e941
lemma b2573 : Encl e2573 (22010103 / 62500000 : ℝ) (22010103 / 62500000 : ℝ) := by
  exact Encl.min b2572 b941 (by norm_num) (by norm_num)

def e2574 : ℝ := e23 * e2565
lemma b2574 : Encl e2574 (149037087547 / 250000000000 : ℝ) (298074175097 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2565 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2575 : ℝ := e944 * e2573
lemma b2575 : Encl e2575 (66030309 / 31250000 : ℝ) (66030309 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2573 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2576 : ℝ := e2570 ^ 2
lemma b2576 : Encl e2576 (2356269839687 / 1000000000000 : ℝ) (2356269839701 / 1000000000000 : ℝ) := by
  exact Encl.pow b2570 (by norm_num) 2 (by norm_num) (by norm_num)

def e2577 : ℝ := e2575 * e2576
lemma b2577 : Encl e2577 (4978727219261 / 1000000000000 : ℝ) (4978727219291 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2575 b2576 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2578 : ℝ := e2577 * e2565
lemma b2578 : Encl e2578 (1484030008899 / 1000000000000 : ℝ) (371007502231 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b2577 b2565 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2579 : ℝ := e2578 / e9
lemma b2579 : Encl e2579 (5300107174639 / 1000000000000 : ℝ) (5300107174729 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2578 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2580 : ℝ := e5 + e2579
lemma b2580 : Encl e2580 (6300107174639 / 1000000000000 : ℝ) (6300107174729 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2579 (by norm_num) (by norm_num)

def e2581 : ℝ := Real.sqrt e2580
lemma b2581 : Encl e2581 (251000142921 / 100000000000 : ℝ) (2510001429229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2580 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2582 : ℝ := e5 + e2581
lemma b2582 : Encl e2582 (351000142921 / 100000000000 : ℝ) (3510001429229 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2581 (by norm_num) (by norm_num)

def e2583 : ℝ := e2574 / e2582
lemma b2583 : Encl e2583 (169842765653 / 1000000000000 : ℝ) (169842765657 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2574 b2582 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2584 : ℝ := e2573 * e954
lemma b2584 : Encl e2584 (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2573 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2585 : ℝ := e2565 - e2583
lemma b2585 : Encl e2585 (128231409437 / 1000000000000 : ℝ) (32057852361 / 250000000000 : ℝ) := by
  exact Encl.sub b2565 b2583 (by norm_num) (by norm_num)

def e2586 : ℝ := e2585 / e2570
lemma b2586 : Encl e2586 (83537582613 / 1000000000000 : ℝ) (83537582619 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2585 b2570 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2587 : ℝ := e2586 ^ 2
lemma b2587 : Encl e2587 (1744631927 / 250000000000 : ℝ) (697852771 / 100000000000 : ℝ) := by
  exact Encl.pow b2586 (by norm_num) 2 (by norm_num) (by norm_num)

def e2588 : ℝ := e9 * e2587
lemma b2588 : Encl e2588 (976993879 / 500000000000 : ℝ) (1953987759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2587 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2589 : ℝ := e2583 ^ 3
lemma b2589 : Encl e2589 (2449690193 / 500000000000 : ℝ) (1224845097 / 250000000000 : ℝ) := by
  exact Encl.pow b2583 (by norm_num) 3 (by norm_num) (by norm_num)

def e2590 : ℝ := e2573 * e2589
lemma b2590 : Encl e2590 (172537387 / 100000000000 : ℝ) (107835867 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2573 b2589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2591 : ℝ := e2588 + e2590
lemma b2591 : Encl e2591 (919840407 / 250000000000 : ℝ) (3679361631 / 1000000000000 : ℝ) := by
  exact Encl.add b2588 b2590 (by norm_num) (by norm_num)

def e2592 : ℝ := min e2584 e2591
lemma b2592 : Encl e2592 (1630684511 / 500000000000 : ℝ) (3261369023 / 1000000000000 : ℝ) := by
  exact Encl.min b2584 b2591 (by norm_num) (by norm_num)

def e2593 : ℝ := (71 / 50 : ℝ)
lemma b2593 : Encl e2593 (71 / 50 : ℝ) (71 / 50 : ℝ) := by
  exact Encl.exact (71 / 50 : ℝ)

def e2594 : ℝ := e2593 / e0
lemma b2594 : Encl e2594 (22600001919 / 50000000000 : ℝ) (452000038381 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2593 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2595 : ℝ := e2593 * e7
lemma b2595 : Encl e2595 (483999980809 / 500000000000 : ℝ) (967999961621 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2593 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2596 : ℝ := e8 * e2593
lemma b2596 : Encl e2596 (3479 / 2500 : ℝ) (3479 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2597 : ℝ := e2596 / e0
lemma b2597 : Encl e2597 (442960037613 / 1000000000000 : ℝ) (221480018807 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2596 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2598 : ℝ := e2593 ^ 2
lemma b2598 : Encl e2598 (5041 / 2500 : ℝ) (5041 / 2500 : ℝ) := by
  exact Encl.pow b2593 (by norm_num) 2 (by norm_num) (by norm_num)

def e2599 : ℝ := e17 * e2598
lemma b2599 : Encl e2599 (5041 / 625 : ℝ) (5041 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2600 : ℝ := e2599 / e0
lemma b2600 : Encl e2600 (2567360218003 / 1000000000000 : ℝ) (641840054501 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2599 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2601 : ℝ := e5 + e2600
lemma b2601 : Encl e2601 (3567360218003 / 1000000000000 : ℝ) (891840054501 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2600 (by norm_num) (by norm_num)

def e2602 : ℝ := Real.sqrt e2601
lemma b2602 : Encl e2602 (236093209149 / 125000000000 : ℝ) (1888745673193 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2603 : ℝ := e5 + e2602
lemma b2603 : Encl e2603 (361093209149 / 125000000000 : ℝ) (2888745673193 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2602 (by norm_num) (by norm_num)

def e2604 : ℝ := e23 / e2603
lemma b2604 : Encl e2604 (69234201493 / 100000000000 : ℝ) (692342014931 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2603 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2605 : ℝ := e9 * e2604
lemma b2605 : Encl e2605 (9692788209 / 50000000000 : ℝ) (193855764181 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2606 : ℝ := e2597 + e2605
lemma b2606 : Encl e2606 (636815801793 / 1000000000000 : ℝ) (127363160359 / 200000000000 : ℝ) := by
  exact Encl.add b2597 b2605 (by norm_num) (by norm_num)

def e2607 : ℝ := e2606 - e5
lemma b2607 : Encl e2607 (-363184198207 / 1000000000000 : ℝ) (-72636839641 / 200000000000 : ℝ) := by
  exact Encl.sub b2606 b5 (by norm_num) (by norm_num)

def e2608 : ℝ := e0 / e2598
lemma b2608 : Encl e2608 (1558020558217 / 1000000000000 : ℝ) (779010279109 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2609 : ℝ := e2594 ^ 2
lemma b2609 : Encl e2609 (40860806939 / 200000000000 : ℝ) (204304034697 / 1000000000000 : ℝ) := by
  exact Encl.pow b2594 (by norm_num) 2 (by norm_num) (by norm_num)

def e2610 : ℝ := e5 - e2609
lemma b2610 : Encl e2610 (795695965303 / 1000000000000 : ℝ) (159139193061 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b2609 (by norm_num) (by norm_num)

def e2611 : ℝ := Real.sqrt e2610
lemma b2611 : Encl e2611 (89201791759 / 100000000000 : ℝ) (111502239699 / 125000000000 : ℝ) := by
  exact Encl.sqrt b2610 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2612 : ℝ := e29 - e2611
lemma b2612 : Encl e2612 (-112675625463 / 500000000000 : ℝ) (-225351250923 / 1000000000000 : ℝ) := by
  exact Encl.sub b29 b2611 (by norm_num) (by norm_num)

def e2613 : ℝ := e2611 ^ 3
lemma b2613 : Encl e2613 (709775058003 / 1000000000000 : ℝ) (88721882251 / 125000000000 : ℝ) := by
  exact Encl.pow b2611 (by norm_num) 3 (by norm_num) (by norm_num)

def e2614 : ℝ := e2613 / e35
lemma b2614 : Encl e2614 (236591686001 / 1000000000000 : ℝ) (236591686003 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2613 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2615 : ℝ := e2612 + e2614
lemma b2615 : Encl e2615 (449617403 / 40000000000 : ℝ) (281010877 / 25000000000 : ℝ) := by
  exact Encl.add b2612 b2614 (by norm_num) (by norm_num)

def e2616 : ℝ := e8 * e2615
lemma b2616 : Encl e2616 (11015626373 / 1000000000000 : ℝ) (11015626379 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2617 : ℝ := e2609 / e2611
lemma b2617 : Encl e2617 (229035797001 / 1000000000000 : ℝ) (57258949251 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2609 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2618 : ℝ := e2617 - e23
lemma b2618 : Encl e2618 (-1770964202999 / 1000000000000 : ℝ) (-442741050749 / 250000000000 : ℝ) := by
  exact Encl.sub b2617 b23 (by norm_num) (by norm_num)

def e2619 : ℝ := e23 * e2611
lemma b2619 : Encl e2619 (89201791759 / 50000000000 : ℝ) (111502239699 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2620 : ℝ := e2618 + e2619
lemma b2620 : Encl e2620 (13071632181 / 1000000000000 : ℝ) (3267908047 / 250000000000 : ℝ) := by
  exact Encl.add b2618 b2619 (by norm_num) (by norm_num)

def e2621 : ℝ := e2620 / e43
lemma b2621 : Encl e2621 (261432643 / 1000000000000 : ℝ) (65358161 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2620 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2622 : ℝ := e2616 - e2621
lemma b2622 : Encl e2622 (10754193729 / 1000000000000 : ℝ) (1344274217 / 125000000000 : ℝ) := by
  exact Encl.sub b2616 b2621 (by norm_num) (by norm_num)

def e2623 : ℝ := e2608 * e2622
lemma b2623 : Encl e2623 (4188813729 / 250000000000 : ℝ) (1047203433 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2608 b2622 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2624 : ℝ := e2607 + e2623
lemma b2624 : Encl e2624 (-346428943291 / 1000000000000 : ℝ) (-346428943277 / 1000000000000 : ℝ) := by
  exact Encl.add b2607 b2623 (by norm_num) (by norm_num)

def e2625 : ℝ := e2595 ^ 2
lemma b2625 : Encl e2625 (234255981423 / 250000000000 : ℝ) (937023925699 / 1000000000000 : ℝ) := by
  exact Encl.pow b2595 (by norm_num) 2 (by norm_num) (by norm_num)

def e2626 : ℝ := e5 - e2625
lemma b2626 : Encl e2626 (62976074301 / 1000000000000 : ℝ) (15744018577 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b2625 (by norm_num) (by norm_num)

def e2627 : ℝ := Real.sqrt e2626
lemma b2627 : Encl e2627 (250950342301 / 1000000000000 : ℝ) (50190068463 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2626 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2628 : ℝ := e5 + e2627
lemma b2628 : Encl e2628 (1250950342301 / 1000000000000 : ℝ) (250190068463 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2627 (by norm_num) (by norm_num)

def e2629 : ℝ := e2595 / e2628
lemma b2629 : Encl e2629 (386905830261 / 500000000000 : ℝ) (386905830267 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2628 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2630 : ℝ := e2629 ^ 2
lemma b2630 : Encl e2630 (598784485959 / 1000000000000 : ℝ) (598784485979 / 1000000000000 : ℝ) := by
  exact Encl.pow b2629 (by norm_num) 2 (by norm_num) (by norm_num)

def e2631 : ℝ := e5 + e2630
lemma b2631 : Encl e2631 (1598784485959 / 1000000000000 : ℝ) (1598784485979 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2630 (by norm_num) (by norm_num)

def e2632 : ℝ := Real.sqrt e2631
lemma b2632 : Encl e2632 (632215249333 / 500000000000 : ℝ) (50577219947 / 40000000000 : ℝ) := by
  exact Encl.sqrt b2631 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2633 : ℝ := e5 + e2632
lemma b2633 : Encl e2633 (1132215249333 / 500000000000 : ℝ) (90577219947 / 40000000000 : ℝ) := by
  exact Encl.add b5 b2632 (by norm_num) (by norm_num)

def e2634 : ℝ := e2629 / e2633
lemma b2634 : Encl e2634 (170862311953 / 500000000000 : ℝ) (170862311957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2629 b2633 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2635 : ℝ := Real.arcsin e2595
lemma b2635 : Encl e2635 (1317134437737 / 1000000000000 : ℝ) (658567218899 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e2595) (a := (170862311953 / 500000000000 : ℝ)) (b := (170862311957 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (483999980809 / 500000000000 : ℝ) by norm_num).trans b2595.1
        exact b2595.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2595) (170862311953 / 500000000000 : ℝ) (170862311957 / 500000000000 : ℝ) from b2634) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2636 : ℝ := e59 * e2635
lemma b2636 : Encl e2636 (134347712649 / 200000000000 : ℝ) (671738563277 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2637 : ℝ := e61 * e2595
lemma b2637 : Encl e2637 (59289997649 / 125000000000 : ℝ) (94863996239 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2595 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2638 : ℝ := e2637 * e2627
lemma b2638 : Encl e2638 (2975769041 / 25000000000 : ℝ) (7439422603 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2637 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2639 : ℝ := e2636 - e2638
lemma b2639 : Encl e2639 (552707801597 / 1000000000000 : ℝ) (552707801637 / 1000000000000 : ℝ) := by
  exact Encl.sub b2636 b2638 (by norm_num) (by norm_num)

def e2640 : ℝ := e43 * e2627
lemma b2640 : Encl e2640 (250950342301 / 20000000000 : ℝ) (50190068463 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2641 : ℝ := e2595 / e2640
lemma b2641 : Encl e2641 (77146733707 / 1000000000000 : ℝ) (4821670857 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2640 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2642 : ℝ := e2639 - e2641
lemma b2642 : Encl e2642 (95112213577 / 200000000000 : ℝ) (47556106793 / 100000000000 : ℝ) := by
  exact Encl.sub b2639 b2641 (by norm_num) (by norm_num)

def e2643 : ℝ := e5 + e2611
lemma b2643 : Encl e2643 (189201791759 / 100000000000 : ℝ) (236502239699 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2611 (by norm_num) (by norm_num)

def e2644 : ℝ := e2594 / e2643
lemma b2644 : Encl e2644 (119449196061 / 500000000000 : ℝ) (59724598031 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2594 b2643 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2645 : ℝ := e2644 ^ 2
lemma b2645 : Encl e2645 (28536220879 / 500000000000 : ℝ) (356702761 / 6250000000 : ℝ) := by
  exact Encl.pow b2644 (by norm_num) 2 (by norm_num) (by norm_num)

def e2646 : ℝ := e5 + e2645
lemma b2646 : Encl e2646 (528536220879 / 500000000000 : ℝ) (6606702761 / 6250000000 : ℝ) := by
  exact Encl.add b5 b2645 (by norm_num) (by norm_num)

def e2647 : ℝ := Real.sqrt e2646
lemma b2647 : Encl e2647 (128517535389 / 125000000000 : ℝ) (514070141557 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2646 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2648 : ℝ := e5 + e2647
lemma b2648 : Encl e2648 (253517535389 / 125000000000 : ℝ) (1014070141557 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2647 (by norm_num) (by norm_num)

def e2649 : ℝ := e2644 / e2648
lemma b2649 : Encl e2649 (29447962021 / 250000000000 : ℝ) (58895924043 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2644 b2648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2650 : ℝ := Real.arcsin e2594
lemma b2650 : Encl e2650 (234503109563 / 500000000000 : ℝ) (93801243827 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e2594) (a := (29447962021 / 250000000000 : ℝ)) (b := (58895924043 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (22600001919 / 50000000000 : ℝ) by norm_num).trans b2594.1
        exact b2594.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2594) (29447962021 / 250000000000 : ℝ) (58895924043 / 500000000000 : ℝ) from b2649) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2651 : ℝ := e59 * e2650
lemma b2651 : Encl e2651 (119596585877 / 500000000000 : ℝ) (239193171759 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2650 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2652 : ℝ := e61 * e2594
lemma b2652 : Encl e2652 (110740009403 / 500000000000 : ℝ) (221480018807 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2594 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2653 : ℝ := e2652 * e2611
lemma b2653 : Encl e2653 (197564145163 / 1000000000000 : ℝ) (39512829033 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2652 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2654 : ℝ := e2651 - e2653
lemma b2654 : Encl e2654 (41629026589 / 1000000000000 : ℝ) (10407256649 / 250000000000 : ℝ) := by
  exact Encl.sub b2651 b2653 (by norm_num) (by norm_num)

def e2655 : ℝ := e43 * e2611
lemma b2655 : Encl e2655 (89201791759 / 2000000000 : ℝ) (111502239699 / 2500000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2656 : ℝ := e2594 / e2655
lemma b2656 : Encl e2656 (253358161 / 25000000000 : ℝ) (10134326441 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2594 b2655 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2657 : ℝ := e2654 - e2656
lemma b2657 : Encl e2657 (7873675037 / 250000000000 : ℝ) (7873675039 / 250000000000 : ℝ) := by
  exact Encl.sub b2654 b2656 (by norm_num) (by norm_num)

def e2658 : ℝ := e2642 - e2657
lemma b2658 : Encl e2658 (444066367729 / 1000000000000 : ℝ) (222033183891 / 500000000000 : ℝ) := by
  exact Encl.sub b2642 b2657 (by norm_num) (by norm_num)

def e2659 : ℝ := e2658 / e2593
lemma b2659 : Encl e2659 (12508911767 / 40000000000 : ℝ) (312722794213 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2658 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2660 : ℝ := e2624 + e2659
lemma b2660 : Encl e2660 (-8426537279 / 250000000000 : ℝ) (-4213268633 / 125000000000 : ℝ) := by
  exact Encl.add b2624 b2659 (by norm_num) (by norm_num)

def e2661 : ℝ := e2595 + e4
lemma b2661 : Encl e2661 (489435820057 / 250000000000 : ℝ) (244717910029 / 125000000000 : ℝ) := by
  exact Encl.add b2595 b4 (by norm_num) (by norm_num)

def e2662 : ℝ := e2661 / e23
lemma b2662 : Encl e2662 (489435820057 / 500000000000 : ℝ) (244717910029 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2661 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2663 : ℝ := e2595 / e2593
lemma b2663 : Encl e2663 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2595 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2664 : ℝ := e89 * e2663
lemma b2664 : Encl e2664 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2665 : ℝ := e2663 ^ 2
lemma b2665 : Encl e2665 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b2663 (by norm_num) 2 (by norm_num) (by norm_num)

def e2666 : ℝ := e91 * e2665
lemma b2666 : Encl e2666 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2667 : ℝ := e5 + e2666
lemma b2667 : Encl e2667 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2666 (by norm_num) (by norm_num)

def e2668 : ℝ := Real.sqrt e2667
lemma b2668 : Encl e2668 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2667 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2669 : ℝ := e2664 * e2668
lemma b2669 : Encl e2669 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2664 b2668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2670 : ℝ := e97 * e2665
lemma b2670 : Encl e2670 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2671 : ℝ := e2669 - e2670
lemma b2671 : Encl e2671 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b2669 b2670 (by norm_num) (by norm_num)

def e2672 : ℝ := e2662 * e2671
lemma b2672 : Encl e2672 (667287119749 / 1000000000000 : ℝ) (333643559887 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2662 b2671 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2673 : ℝ := e2662 / e2593
lemma b2673 : Encl e2673 (86168278179 / 125000000000 : ℝ) (344673112717 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2674 : ℝ := e89 * e2673
lemma b2674 : Encl e2674 (1221834371873 / 1000000000000 : ℝ) (1221834371879 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2673 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2675 : ℝ := e2673 ^ 2
lemma b2675 : Encl e2675 (475198218517 / 1000000000000 : ℝ) (475198218521 / 1000000000000 : ℝ) := by
  exact Encl.pow b2673 (by norm_num) 2 (by norm_num) (by norm_num)

def e2676 : ℝ := e91 * e2675
lemma b2676 : Encl e2676 (46652476009 / 125000000000 : ℝ) (373219808077 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2677 : ℝ := e5 + e2676
lemma b2677 : Encl e2677 (171652476009 / 125000000000 : ℝ) (1373219808077 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2676 (by norm_num) (by norm_num)

def e2678 : ℝ := Real.sqrt e2677
lemma b2678 : Encl e2678 (292961154429 / 250000000000 : ℝ) (29296115443 / 25000000000 : ℝ) := by
  exact Encl.sqrt b2677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2679 : ℝ := e2674 * e2678
lemma b2679 : Encl e2679 (1431800032419 / 1000000000000 : ℝ) (89487502027 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2674 b2678 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2680 : ℝ := e97 * e2675
lemma b2680 : Encl e2680 (149287923229 / 200000000000 : ℝ) (746439616153 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2675 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2681 : ℝ := e2679 - e2680
lemma b2681 : Encl e2681 (342680208133 / 500000000000 : ℝ) (685360416287 / 1000000000000 : ℝ) := by
  exact Encl.sub b2679 b2680 (by norm_num) (by norm_num)

def e2682 : ℝ := e2595 * e2681
lemma b2682 : Encl e2682 (663428856639 / 1000000000000 : ℝ) (663428856663 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2595 b2681 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2683 : ℝ := e2672 - e2682
lemma b2683 : Encl e2683 (1929131543 / 500000000000 : ℝ) (771652627 / 200000000000 : ℝ) := by
  exact Encl.sub b2672 b2682 (by norm_num) (by norm_num)

def e2684 : ℝ := e2662 ^ 2
lemma b2684 : Encl e2684 (958189687819 / 1000000000000 : ℝ) (59886855489 / 62500000000 : ℝ) := by
  exact Encl.pow b2662 (by norm_num) 2 (by norm_num) (by norm_num)

def e2685 : ℝ := e8 * e2684
lemma b2685 : Encl e2685 (469512947031 / 500000000000 : ℝ) (234756473517 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2684 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2686 : ℝ := e5 - e2685
lemma b2686 : Encl e2686 (15243526483 / 250000000000 : ℝ) (30487052969 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2685 (by norm_num) (by norm_num)

def e2687 : ℝ := e5 - e2684
lemma b2687 : Encl e2687 (2613144511 / 62500000000 : ℝ) (41810312181 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2684 (by norm_num) (by norm_num)

def e2688 : ℝ := Real.sqrt e2687
lemma b2688 : Encl e2688 (102237850349 / 500000000000 : ℝ) (204475700711 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2687 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2689 : ℝ := e2686 / e2688
lemma b2689 : Encl e2689 (298197319877 / 1000000000000 : ℝ) (149098659963 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2686 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2690 : ℝ := e5 - e2689
lemma b2690 : Encl e2690 (350901340037 / 500000000000 : ℝ) (701802680123 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2689 (by norm_num) (by norm_num)

def e2691 : ℝ := e8 * e2625
lemma b2691 : Encl e2691 (459141723589 / 500000000000 : ℝ) (459141723593 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2625 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2692 : ℝ := e5 - e2691
lemma b2692 : Encl e2692 (40858276407 / 500000000000 : ℝ) (40858276411 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2691 (by norm_num) (by norm_num)

def e2693 : ℝ := e2692 / e2627
lemma b2693 : Encl e2693 (325628377551 / 1000000000000 : ℝ) (162814188801 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2692 b2627 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2694 : ℝ := e5 - e2693
lemma b2694 : Encl e2694 (337185811199 / 500000000000 : ℝ) (674371622449 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2693 (by norm_num) (by norm_num)

def e2695 : ℝ := e2690 - e2694
lemma b2695 : Encl e2695 (219448461 / 8000000000 : ℝ) (1097242309 / 40000000000 : ℝ) := by
  exact Encl.sub b2690 b2694 (by norm_num) (by norm_num)

def e2696 : ℝ := e2683 * e2695
lemma b2696 : Encl e2696 (105836237 / 1000000000000 : ℝ) (105836239 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2683 b2695 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2697 : ℝ := e2681 - e2671
lemma b2697 : Encl e2697 (1835151219 / 500000000000 : ℝ) (1835151241 / 500000000000 : ℝ) := by
  exact Encl.sub b2681 b2671 (by norm_num) (by norm_num)

def e2698 : ℝ := e5 + e2688
lemma b2698 : Encl e2698 (602237850349 / 500000000000 : ℝ) (1204475700711 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2688 (by norm_num) (by norm_num)

def e2699 : ℝ := e2662 / e2698
lemma b2699 : Encl e2699 (812695216297 / 1000000000000 : ℝ) (203173804077 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2698 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2700 : ℝ := e2699 ^ 2

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
