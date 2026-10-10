import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures289To507

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

def e508 : ℝ := e500 / e502
lemma b508 : Encl e508 (17938056183 / 200000000000 : ℝ) (44845140459 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b500 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e509 : ℝ := e508 - e23
lemma b509 : Encl e509 (-382061943817 / 200000000000 : ℝ) (-955154859541 / 500000000000 : ℝ) := by
  exact Encl.sub b508 b23 (by norm_num) (by norm_num)

def e510 : ℝ := e23 * e502
lemma b510 : Encl e510 (956159897801 / 500000000000 : ℝ) (956159897803 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e511 : ℝ := e509 + e510
lemma b511 : Encl e511 (2010076517 / 1000000000000 : ℝ) (502519131 / 250000000000 : ℝ) := by
  exact Encl.add b509 b510 (by norm_num) (by norm_num)

def e512 : ℝ := e511 / e43
lemma b512 : Encl e512 (4020153 / 100000000000 : ℝ) (40201531 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b511 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e513 : ℝ := e507 - e512
lemma b513 : Encl e513 (226973679 / 125000000000 : ℝ) (1815789439 / 1000000000000 : ℝ) := by
  exact Encl.sub b507 b512 (by norm_num) (by norm_num)

def e514 : ℝ := e499 * e513
lemma b514 : Encl e514 (3369843301 / 500000000000 : ℝ) (6739686629 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b499 b513 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e515 : ℝ := e498 + e514
lemma b515 : Encl e515 (-476896705767 / 1000000000000 : ℝ) (-476896705737 / 1000000000000 : ℝ) := by
  exact Encl.add b498 b514 (by norm_num) (by norm_num)

def e516 : ℝ := e486 ^ 2
lemma b516 : Encl e516 (393323274501 / 1000000000000 : ℝ) (78664654901 / 200000000000 : ℝ) := by
  exact Encl.pow b486 (by norm_num) 2 (by norm_num) (by norm_num)

def e517 : ℝ := e5 - e516
lemma b517 : Encl e517 (121335345099 / 200000000000 : ℝ) (606676725499 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b516 (by norm_num) (by norm_num)

def e518 : ℝ := Real.sqrt e517
lemma b518 : Encl e518 (389447276757 / 500000000000 : ℝ) (389447276759 / 500000000000 : ℝ) := by
  exact Encl.sqrt b517 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e519 : ℝ := e5 + e518
lemma b519 : Encl e519 (889447276757 / 500000000000 : ℝ) (889447276759 / 500000000000 : ℝ) := by
  exact Encl.add b5 b518 (by norm_num) (by norm_num)

def e520 : ℝ := e486 / e519
lemma b520 : Encl e520 (88138291203 / 250000000000 : ℝ) (70510632963 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b519 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e521 : ℝ := e520 ^ 2
lemma b521 : Encl e521 (62146867009 / 500000000000 : ℝ) (62146867011 / 500000000000 : ℝ) := by
  exact Encl.pow b520 (by norm_num) 2 (by norm_num) (by norm_num)

def e522 : ℝ := e5 + e521
lemma b522 : Encl e522 (562146867009 / 500000000000 : ℝ) (562146867011 / 500000000000 : ℝ) := by
  exact Encl.add b5 b521 (by norm_num) (by norm_num)

def e523 : ℝ := Real.sqrt e522
lemma b523 : Encl e523 (265081795633 / 250000000000 : ℝ) (212065436507 / 200000000000 : ℝ) := by
  exact Encl.sqrt b522 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e524 : ℝ := e5 + e523
lemma b524 : Encl e524 (515081795633 / 250000000000 : ℝ) (412065436507 / 200000000000 : ℝ) := by
  exact Encl.add b5 b523 (by norm_num) (by norm_num)

def e525 : ℝ := e520 / e524
lemma b525 : Encl e525 (85557567701 / 500000000000 : ℝ) (42778783851 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b520 b524 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e526 : ℝ := Real.arcsin e486
lemma b526 : Encl e526 (16947377027 / 25000000000 : ℝ) (5296055321 / 7812500000 : ℝ) := by
  apply Encl.arcsin (z := e486) (a := (85557567701 / 500000000000 : ℝ)) (b := (42778783851 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (62715490471 / 100000000000 : ℝ) by norm_num).trans b486.1
        exact b486.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e486) (85557567701 / 500000000000 : ℝ) (42778783851 / 250000000000 : ℝ) from b525) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e527 : ℝ := e59 * e526
lemma b527 : Encl e527 (6914529827 / 20000000000 : ℝ) (69145298271 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b526 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e528 : ℝ := e61 * e486
lemma b528 : Encl e528 (307305903307 / 1000000000000 : ℝ) (307305903309 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b486 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e529 : ℝ := e528 * e518
lemma b529 : Encl e529 (59839723587 / 250000000000 : ℝ) (14959930897 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b528 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e530 : ℝ := e527 - e529
lemma b530 : Encl e530 (53183798499 / 500000000000 : ℝ) (106367597007 / 1000000000000 : ℝ) := by
  exact Encl.sub b527 b529 (by norm_num) (by norm_num)

def e531 : ℝ := e43 * e518
lemma b531 : Encl e531 (389447276757 / 10000000000 : ℝ) (389447276759 / 10000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e532 : ℝ := e486 / e531
lemma b532 : Encl e532 (1610371781 / 100000000000 : ℝ) (16103717811 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b531 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e533 : ℝ := e530 - e532
lemma b533 : Encl e533 (90263879187 / 1000000000000 : ℝ) (90263879197 / 1000000000000 : ℝ) := by
  exact Encl.sub b530 b532 (by norm_num) (by norm_num)

def e534 : ℝ := e5 + e502
lemma b534 : Encl e534 (1956159897801 / 1000000000000 : ℝ) (1956159897803 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b502 (by norm_num) (by norm_num)

def e535 : ℝ := e485 / e534
lemma b535 : Encl e535 (5988162739 / 40000000000 : ℝ) (37426017119 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b485 b534 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e536 : ℝ := e535 ^ 2
lemma b536 : Encl e536 (22411308117 / 1000000000000 : ℝ) (22411308119 / 1000000000000 : ℝ) := by
  exact Encl.pow b535 (by norm_num) 2 (by norm_num) (by norm_num)

def e537 : ℝ := e5 + e536
lemma b537 : Encl e537 (1022411308117 / 1000000000000 : ℝ) (1022411308119 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b536 (by norm_num) (by norm_num)

def e538 : ℝ := Real.sqrt e537
lemma b538 : Encl e538 (1011143564543 / 1000000000000 : ℝ) (202228712909 / 200000000000 : ℝ) := by
  exact Encl.sqrt b537 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e539 : ℝ := e5 + e538
lemma b539 : Encl e539 (2011143564543 / 1000000000000 : ℝ) (402228712909 / 200000000000 : ℝ) := by
  exact Encl.add b5 b538 (by norm_num) (by norm_num)

def e540 : ℝ := e535 / e539
lemma b540 : Encl e540 (74437285887 / 1000000000000 : ℝ) (74437285889 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b535 b539 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e541 : ℝ := Real.arcsin e485
lemma b541 : Encl e541 (297201030933 / 1000000000000 : ℝ) (148600515471 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e485) (a := (74437285887 / 1000000000000 : ℝ)) (b := (74437285889 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (292845095289 / 1000000000000 : ℝ) by norm_num).trans b485.1
        exact b485.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e485) (74437285887 / 1000000000000 : ℝ) (74437285889 / 1000000000000 : ℝ) from b540) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e542 : ℝ := e59 * e541
lemma b542 : Encl e542 (6062901031 / 40000000000 : ℝ) (151572525781 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b541 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e543 : ℝ := e61 * e485
lemma b543 : Encl e543 (143494096691 / 1000000000000 : ℝ) (143494096693 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b485 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e544 : ℝ := e543 * e502
lemma b544 : Encl e544 (137203300827 / 1000000000000 : ℝ) (13720330083 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b543 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e545 : ℝ := e542 - e544
lemma b545 : Encl e545 (2873844989 / 200000000000 : ℝ) (7184612477 / 500000000000 : ℝ) := by
  exact Encl.sub b542 b544 (by norm_num) (by norm_num)

def e546 : ℝ := e43 * e502
lemma b546 : Encl e546 (956159897801 / 20000000000 : ℝ) (956159897803 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b502 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e547 : ℝ := e485 / e546
lemma b547 : Encl e547 (382840119 / 62500000000 : ℝ) (1225088381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b485 b546 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e548 : ℝ := e545 - e547
lemma b548 : Encl e548 (12880911 / 1562500000 : ℝ) (164875661 / 20000000000 : ℝ) := by
  exact Encl.sub b545 b547 (by norm_num) (by norm_num)

def e549 : ℝ := e533 - e548
lemma b549 : Encl e549 (82020096137 / 1000000000000 : ℝ) (82020096157 / 1000000000000 : ℝ) := by
  exact Encl.sub b533 b548 (by norm_num) (by norm_num)

def e550 : ℝ := e549 / e484
lemma b550 : Encl e550 (89152278409 / 1000000000000 : ℝ) (2786008701 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b549 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e551 : ℝ := e515 + e550
lemma b551 : Encl e551 (-193872213679 / 500000000000 : ℝ) (-77548885461 / 200000000000 : ℝ) := by
  exact Encl.add b515 b550 (by norm_num) (by norm_num)

def e552 : ℝ := e486 + e4
lemma b552 : Encl e552 (40422455583 / 25000000000 : ℝ) (1616898223323 / 1000000000000 : ℝ) := by
  exact Encl.add b486 b4 (by norm_num) (by norm_num)

def e553 : ℝ := e552 / e23
lemma b553 : Encl e553 (40422455583 / 50000000000 : ℝ) (404224555831 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b552 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e554 : ℝ := e486 / e484
lemma b554 : Encl e554 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b486 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e555 : ℝ := e89 * e554
lemma b555 : Encl e555 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b554 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e556 : ℝ := e554 ^ 2
lemma b556 : Encl e556 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b554 (by norm_num) 2 (by norm_num) (by norm_num)

def e557 : ℝ := e91 * e556
lemma b557 : Encl e557 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e558 : ℝ := e5 + e557
lemma b558 : Encl e558 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b557 (by norm_num) (by norm_num)

def e559 : ℝ := Real.sqrt e558
lemma b559 : Encl e559 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b558 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e560 : ℝ := e555 * e559
lemma b560 : Encl e560 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b555 b559 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e561 : ℝ := e97 * e556
lemma b561 : Encl e561 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b556 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e562 : ℝ := e560 - e561
lemma b562 : Encl e562 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b560 b561 (by norm_num) (by norm_num)

def e563 : ℝ := e553 * e562
lemma b563 : Encl e563 (551111766933 / 1000000000000 : ℝ) (275555883477 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b553 b562 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e564 : ℝ := e553 / e484
lemma b564 : Encl e564 (878749034413 / 1000000000000 : ℝ) (54921814651 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b553 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e565 : ℝ := e89 * e564
lemma b565 : Encl e565 (194692763753 / 125000000000 : ℝ) (1557542110031 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b564 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e566 : ℝ := e564 ^ 2
lemma b566 : Encl e566 (772199865481 / 1000000000000 : ℝ) (48262491593 / 62500000000 : ℝ) := by
  exact Encl.pow b564 (by norm_num) 2 (by norm_num) (by norm_num)

def e567 : ℝ := e91 * e566
lemma b567 : Encl e567 (151621089031 / 250000000000 : ℝ) (606484356131 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b566 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e568 : ℝ := e5 + e567
lemma b568 : Encl e568 (401621089031 / 250000000000 : ℝ) (1606484356131 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b567 (by norm_num) (by norm_num)

def e569 : ℝ := Real.sqrt e568
lemma b569 : Encl e569 (1267471639179 / 1000000000000 : ℝ) (1267471639183 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b568 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e570 : ℝ := e565 * e569
lemma b570 : Encl e570 (987070225641 / 500000000000 : ℝ) (987070225649 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b565 b569 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e571 : ℝ := e97 * e566
lemma b571 : Encl e571 (151621089031 / 125000000000 : ℝ) (1212968712261 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b566 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e572 : ℝ := e570 - e571
lemma b572 : Encl e572 (761171739021 / 1000000000000 : ℝ) (15223434781 / 20000000000 : ℝ) := by
  exact Encl.sub b570 b571 (by norm_num) (by norm_num)

def e573 : ℝ := e486 * e572
lemma b573 : Encl e573 (477372589453 / 1000000000000 : ℝ) (238686294737 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b486 b572 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e574 : ℝ := e563 - e573
lemma b574 : Encl e574 (73739177459 / 1000000000000 : ℝ) (73739177501 / 1000000000000 : ℝ) := by
  exact Encl.sub b563 b573 (by norm_num) (by norm_num)

def e575 : ℝ := e553 ^ 2
lemma b575 : Encl e575 (653589966143 / 1000000000000 : ℝ) (163397491537 / 250000000000 : ℝ) := by
  exact Encl.pow b553 (by norm_num) 2 (by norm_num) (by norm_num)

def e576 : ℝ := e8 * e575
lemma b576 : Encl e576 (32025908341 / 50000000000 : ℝ) (320259083413 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b575 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e577 : ℝ := e5 - e576
lemma b577 : Encl e577 (179740916587 / 500000000000 : ℝ) (17974091659 / 50000000000 : ℝ) := by
  exact Encl.sub b5 b576 (by norm_num) (by norm_num)

def e578 : ℝ := e5 - e575
lemma b578 : Encl e578 (86602508463 / 250000000000 : ℝ) (346410033857 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b575 (by norm_num) (by norm_num)

def e579 : ℝ := Real.sqrt e578
lemma b579 : Encl e579 (23542643313 / 40000000000 : ℝ) (58856608283 / 100000000000 : ℝ) := by
  exact Encl.sqrt b578 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e580 : ℝ := e577 / e579
lemma b580 : Encl e580 (3817347827 / 6250000000 : ℝ) (38173478271 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b577 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e581 : ℝ := e5 - e580
lemma b581 : Encl e581 (24326521729 / 62500000000 : ℝ) (2432652173 / 6250000000 : ℝ) := by
  exact Encl.sub b5 b580 (by norm_num) (by norm_num)

def e582 : ℝ := e8 * e516
lemma b582 : Encl e582 (38545680901 / 100000000000 : ℝ) (77091361803 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b516 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e583 : ℝ := e5 - e582
lemma b583 : Encl e583 (122908638197 / 200000000000 : ℝ) (61454319099 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b582 (by norm_num) (by norm_num)

def e584 : ℝ := e583 / e518
lemma b584 : Encl e584 (9862425989 / 12500000000 : ℝ) (197248519783 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b583 b518 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e585 : ℝ := e5 - e584
lemma b585 : Encl e585 (52751480217 / 250000000000 : ℝ) (2637574011 / 12500000000 : ℝ) := by
  exact Encl.sub b5 b584 (by norm_num) (by norm_num)

def e586 : ℝ := e581 - e585
lemma b586 : Encl e586 (5569325837 / 31250000000 : ℝ) (44554606703 / 250000000000 : ℝ) := by
  exact Encl.sub b581 b585 (by norm_num) (by norm_num)

def e587 : ℝ := e574 * e586
lemma b587 : Encl e587 (13141680199 / 1000000000000 : ℝ) (13141680209 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b574 b586 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e588 : ℝ := e572 - e562
lemma b588 : Encl e588 (79481625193 / 1000000000000 : ℝ) (15896325049 / 200000000000 : ℝ) := by
  exact Encl.sub b572 b562 (by norm_num) (by norm_num)

def e589 : ℝ := e5 + e579
lemma b589 : Encl e589 (63542643313 / 40000000000 : ℝ) (158856608283 / 100000000000 : ℝ) := by
  exact Encl.add b5 b579 (by norm_num) (by norm_num)

def e590 : ℝ := e553 / e589
lemma b590 : Encl e590 (50891752027 / 100000000000 : ℝ) (254458760137 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b553 b589 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e591 : ℝ := e590 ^ 2
lemma b591 : Encl e591 (258997042437 / 1000000000000 : ℝ) (129498521221 / 500000000000 : ℝ) := by
  exact Encl.pow b590 (by norm_num) 2 (by norm_num) (by norm_num)

def e592 : ℝ := e5 + e591
lemma b592 : Encl e592 (1258997042437 / 1000000000000 : ℝ) (629498521221 / 500000000000 : ℝ) := by
  exact Encl.add b5 b591 (by norm_num) (by norm_num)

def e593 : ℝ := Real.sqrt e592
lemma b593 : Encl e593 (561025187143 / 500000000000 : ℝ) (1122050374289 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b592 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e594 : ℝ := e5 + e593
lemma b594 : Encl e594 (1061025187143 / 500000000000 : ℝ) (2122050374289 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b593 (by norm_num) (by norm_num)

def e595 : ℝ := e590 / e594
lemma b595 : Encl e595 (239823486961 / 1000000000000 : ℝ) (59955871741 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b590 b594 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e596 : ℝ := Real.arcsin e553
lemma b596 : Encl e596 (941512297663 / 1000000000000 : ℝ) (235378074419 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e553) (a := (239823486961 / 1000000000000 : ℝ)) (b := (59955871741 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (40422455583 / 50000000000 : ℝ) by norm_num).trans b553.1
        exact b553.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e553) (239823486961 / 1000000000000 : ℝ) (59955871741 / 250000000000 : ℝ) from b595) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e597 : ℝ := e59 * e596
lemma b597 : Encl e597 (3751338061 / 7812500000 : ℝ) (96034254363 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b596 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e598 : ℝ := e61 * e553
lemma b598 : Encl e598 (396140064713 / 1000000000000 : ℝ) (79228012943 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b553 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e599 : ℝ := e598 * e579
lemma b599 : Encl e599 (116577303069 / 500000000000 : ℝ) (116577303071 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b598 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e600 : ℝ := e597 - e599
lemma b600 : Encl e600 (123508332833 / 500000000000 : ℝ) (247016665677 / 1000000000000 : ℝ) := by
  exact Encl.sub b597 b599 (by norm_num) (by norm_num)

def e601 : ℝ := e43 * e579
lemma b601 : Encl e601 (23542643313 / 800000000 : ℝ) (58856608283 / 2000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b579 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e602 : ℝ := e553 / e601
lemma b602 : Encl e602 (2747182127 / 100000000000 : ℝ) (27471821271 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b553 b601 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e603 : ℝ := e600 - e602
lemma b603 : Encl e603 (43908968879 / 200000000000 : ℝ) (219544844407 / 1000000000000 : ℝ) := by
  exact Encl.sub b600 b602 (by norm_num) (by norm_num)

def e604 : ℝ := e603 - e533
lemma b604 : Encl e604 (64640482599 / 500000000000 : ℝ) (6464048261 / 50000000000 : ℝ) := by
  exact Encl.sub b603 b533 (by norm_num) (by norm_num)

def e605 : ℝ := e588 * e604
lemma b605 : Encl e605 (513773061 / 50000000000 : ℝ) (10275461229 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b588 b604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e606 : ℝ := e587 + e605
lemma b606 : Encl e606 (23417141419 / 1000000000000 : ℝ) (11708570719 / 500000000000 : ℝ) := by
  exact Encl.add b587 b605 (by norm_num) (by norm_num)

def e607 : ℝ := e553 - e486
lemma b607 : Encl e607 (45323551737 / 250000000000 : ℝ) (22661775869 / 125000000000 : ℝ) := by
  exact Encl.sub b553 b486 (by norm_num) (by norm_num)

def e608 : ℝ := e606 / e607
lemma b608 : Encl e608 (129166517853 / 1000000000000 : ℝ) (64583258981 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b606 b607 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e609 : ℝ := e551 + e608
lemma b609 : Encl e609 (-51715581901 / 200000000000 : ℝ) (-258577909343 / 1000000000000 : ℝ) := by
  exact Encl.add b551 b608 (by norm_num) (by norm_num)

def e610 : ℝ := e4 * e572
lemma b610 : Encl e610 (75336464301 / 100000000000 : ℝ) (753364643041 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b572 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e611 : ℝ := e4 / e484
lemma b611 : Encl e611 (107580795501 / 100000000000 : ℝ) (268951988753 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b484 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e612 : ℝ := e89 * e611
lemma b612 : Encl e612 (1906819952691 / 1000000000000 : ℝ) (1906819952697 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b611 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e613 : ℝ := e611 ^ 2
lemma b613 : Encl e613 (578681378031 / 500000000000 : ℝ) (289340689017 / 250000000000 : ℝ) := by
  exact Encl.pow b611 (by norm_num) 2 (by norm_num) (by norm_num)

def e614 : ℝ := e91 * e613
lemma b614 : Encl e614 (181798116599 / 200000000000 : ℝ) (454495291501 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b613 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e615 : ℝ := e5 + e614
lemma b615 : Encl e615 (381798116599 / 200000000000 : ℝ) (954495291501 / 500000000000 : ℝ) := by
  exact Encl.add b5 b614 (by norm_num) (by norm_num)

def e616 : ℝ := Real.sqrt e615
lemma b616 : Encl e616 (1381662253589 / 1000000000000 : ℝ) (1381662253593 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b615 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e617 : ℝ := e612 * e616
lemma b617 : Encl e617 (2634581153023 / 1000000000000 : ℝ) (32932264413 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b612 b616 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e618 : ℝ := e97 * e613
lemma b618 : Encl e618 (181798116599 / 100000000000 : ℝ) (1817981166001 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b613 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e619 : ℝ := e617 - e618
lemma b619 : Encl e619 (408299993511 / 500000000000 : ℝ) (16331999741 / 20000000000 : ℝ) := by
  exact Encl.sub b617 b618 (by norm_num) (by norm_num)

def e620 : ℝ := e553 * e619
lemma b620 : Encl e620 (660179534089 / 1000000000000 : ℝ) (330089767057 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b553 b619 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e621 : ℝ := e610 - e620
lemma b621 : Encl e621 (2912034653 / 31250000000 : ℝ) (11648138619 / 125000000000 : ℝ) := by
  exact Encl.sub b610 b620 (by norm_num) (by norm_num)

def e622 : ℝ := e165 - e581
lemma b622 : Encl e622 (66155130459 / 200000000000 : ℝ) (82693913091 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b581 (by norm_num) (by norm_num)

def e623 : ℝ := e621 * e622
lemma b623 : Encl e623 (30823365179 / 1000000000000 : ℝ) (6164673041 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b621 b622 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e624 : ℝ := e619 - e572
lemma b624 : Encl e624 (13857061993 / 250000000000 : ℝ) (55428248029 / 1000000000000 : ℝ) := by
  exact Encl.sub b619 b572 (by norm_num) (by norm_num)

def e625 : ℝ := e183 - e603
lemma b625 : Encl e625 (60121585021 / 200000000000 : ℝ) (293562427 / 976562500 : ℝ) := by
  exact Encl.sub b183 b603 (by norm_num) (by norm_num)

def e626 : ℝ := e624 * e625
lemma b626 : Encl e626 (3332434123 / 200000000000 : ℝ) (16662170641 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b624 b625 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e627 : ℝ := e623 + e626
lemma b627 : Encl e627 (23742767897 / 500000000000 : ℝ) (23742767923 / 500000000000 : ℝ) := by
  exact Encl.add b623 b626 (by norm_num) (by norm_num)

def e628 : ℝ := e4 - e553
lemma b628 : Encl e628 (45323551737 / 250000000000 : ℝ) (181294206951 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b553 (by norm_num) (by norm_num)

def e629 : ℝ := e627 / e628
lemma b629 : Encl e629 (52385055863 / 200000000000 : ℝ) (32740659951 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b627 b628 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e630 : ℝ := e609 + e629
lemma b630 : Encl e630 (334736981 / 100000000000 : ℝ) (669474053 / 200000000000 : ℝ) := by
  exact Encl.add b609 b629 (by norm_num) (by norm_num)

def e631 : ℝ := e8 / e0
lemma b631 : Encl e631 (15597184423 / 50000000000 : ℝ) (311943688461 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b8 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e632 : ℝ := e8 * e7
lemma b632 : Encl e632 (668056311539 / 1000000000000 : ℝ) (668056311541 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e633 : ℝ := e8 * e8
lemma b633 : Encl e633 (2401 / 2500 : ℝ) (2401 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e634 : ℝ := e633 / e0
lemma b634 : Encl e634 (30570481469 / 100000000000 : ℝ) (305704814691 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b633 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e635 : ℝ := e8 ^ 2
lemma b635 : Encl e635 (2401 / 2500 : ℝ) (2401 / 2500 : ℝ) := by
  exact Encl.pow b8 (by norm_num) 2 (by norm_num) (by norm_num)

def e636 : ℝ := e17 * e635
lemma b636 : Encl e636 (2401 / 625 : ℝ) (2401 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e637 : ℝ := e636 / e0
lemma b637 : Encl e637 (1222819258763 / 1000000000000 : ℝ) (305704814691 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b636 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e638 : ℝ := e5 + e637
lemma b638 : Encl e638 (2222819258763 / 1000000000000 : ℝ) (555704814691 / 250000000000 : ℝ) := by
  exact Encl.add b5 b637 (by norm_num) (by norm_num)

def e639 : ℝ := Real.sqrt e638
lemma b639 : Encl e639 (745456111847 / 500000000000 : ℝ) (93182013981 / 62500000000 : ℝ) := by
  exact Encl.sqrt b638 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e640 : ℝ := e5 + e639
lemma b640 : Encl e640 (1245456111847 / 500000000000 : ℝ) (155682013981 / 62500000000 : ℝ) := by
  exact Encl.add b5 b639 (by norm_num) (by norm_num)

def e641 : ℝ := e23 / e640
lemma b641 : Encl e641 (802918698207 / 1000000000000 : ℝ) (802918698209 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b640 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e642 : ℝ := e9 * e641
lemma b642 : Encl e642 (224817235497 / 1000000000000 : ℝ) (224817235499 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b641 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e643 : ℝ := e634 + e642
lemma b643 : Encl e643 (530522050187 / 1000000000000 : ℝ) (53052205019 / 100000000000 : ℝ) := by
  exact Encl.add b634 b642 (by norm_num) (by norm_num)

def e644 : ℝ := e643 - e5
lemma b644 : Encl e644 (-469477949813 / 1000000000000 : ℝ) (-46947794981 / 100000000000 : ℝ) := by
  exact Encl.sub b643 b5 (by norm_num) (by norm_num)

def e645 : ℝ := e0 / e635
lemma b645 : Encl e645 (654225875383 / 200000000000 : ℝ) (817782344229 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b635 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e646 : ℝ := e631 ^ 2
lemma b646 : Encl e646 (9730886477 / 100000000000 : ℝ) (97308864771 / 1000000000000 : ℝ) := by
  exact Encl.pow b631 (by norm_num) 2 (by norm_num) (by norm_num)

def e647 : ℝ := e5 - e646
lemma b647 : Encl e647 (902691135229 / 1000000000000 : ℝ) (90269113523 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b646 (by norm_num) (by norm_num)

def e648 : ℝ := Real.sqrt e647
lemma b648 : Encl e648 (950100592163 / 1000000000000 : ℝ) (237525148041 / 250000000000 : ℝ) := by
  exact Encl.sqrt b647 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e649 : ℝ := e29 - e648
lemma b649 : Encl e649 (-141716962749 / 500000000000 : ℝ) (-35429240687 / 125000000000 : ℝ) := by
  exact Encl.sub b29 b648 (by norm_num) (by norm_num)

def e650 : ℝ := e648 ^ 3
lemma b650 : Encl e650 (21441184553 / 25000000000 : ℝ) (214411845531 / 250000000000 : ℝ) := by
  exact Encl.pow b648 (by norm_num) 3 (by norm_num) (by norm_num)

def e651 : ℝ := e650 / e35
lemma b651 : Encl e651 (142941230353 / 500000000000 : ℝ) (71470615177 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b650 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e652 : ℝ := e649 + e651
lemma b652 : Encl e652 (306066901 / 125000000000 : ℝ) (612133803 / 250000000000 : ℝ) := by
  exact Encl.add b649 b651 (by norm_num) (by norm_num)

def e653 : ℝ := e8 * e652
lemma b653 : Encl e653 (2399564503 / 1000000000000 : ℝ) (599891127 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b652 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e654 : ℝ := e646 / e648
lemma b654 : Encl e654 (102419539123 / 1000000000000 : ℝ) (819356313 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b646 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e655 : ℝ := e654 - e23
lemma b655 : Encl e655 (-1897580460877 / 1000000000000 : ℝ) (-15180643687 / 8000000000 : ℝ) := by
  exact Encl.sub b654 b23 (by norm_num) (by norm_num)

def e656 : ℝ := e23 * e648
lemma b656 : Encl e656 (950100592163 / 500000000000 : ℝ) (237525148041 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e657 : ℝ := e655 + e656
lemma b657 : Encl e657 (2620723449 / 1000000000000 : ℝ) (2620723453 / 1000000000000 : ℝ) := by
  exact Encl.add b655 b656 (by norm_num) (by norm_num)

def e658 : ℝ := e657 / e43
lemma b658 : Encl e658 (13103617 / 250000000000 : ℝ) (5241447 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b657 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e659 : ℝ := e653 - e658
lemma b659 : Encl e659 (2347150033 / 1000000000000 : ℝ) (58678751 / 25000000000 : ℝ) := by
  exact Encl.sub b653 b658 (by norm_num) (by norm_num)

def e660 : ℝ := e645 * e659
lemma b660 : Encl e660 (29991529 / 3906250000 : ℝ) (959728931 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b645 b659 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e661 : ℝ := e644 + e660
lemma b661 : Encl e661 (-461800118389 / 1000000000000 : ℝ) (-230900059181 / 500000000000 : ℝ) := by
  exact Encl.add b644 b660 (by norm_num) (by norm_num)

def e662 : ℝ := e632 ^ 2
lemma b662 : Encl e662 (446299235387 / 1000000000000 : ℝ) (44629923539 / 100000000000 : ℝ) := by
  exact Encl.pow b632 (by norm_num) 2 (by norm_num) (by norm_num)

def e663 : ℝ := e5 - e662
lemma b663 : Encl e663 (55370076461 / 100000000000 : ℝ) (553700764613 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b662 (by norm_num) (by norm_num)

def e664 : ℝ := Real.sqrt e663
lemma b664 : Encl e664 (148822144133 / 200000000000 : ℝ) (186027680167 / 250000000000 : ℝ) := by
  exact Encl.sqrt b663 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e665 : ℝ := e5 + e664
lemma b665 : Encl e665 (348822144133 / 200000000000 : ℝ) (436027680167 / 250000000000 : ℝ) := by
  exact Encl.add b5 b664 (by norm_num) (by norm_num)

def e666 : ℝ := e632 / e665
lemma b666 : Encl e666 (23939718377 / 62500000000 : ℝ) (76607098807 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b665 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e667 : ℝ := e666 ^ 2
lemma b667 : Encl e667 (18339523711 / 125000000000 : ℝ) (146716189691 / 1000000000000 : ℝ) := by
  exact Encl.pow b666 (by norm_num) 2 (by norm_num) (by norm_num)

def e668 : ℝ := e5 + e667
lemma b668 : Encl e668 (143339523711 / 125000000000 : ℝ) (1146716189691 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b667 (by norm_num) (by norm_num)

def e669 : ℝ := Real.sqrt e668
lemma b669 : Encl e669 (535424175231 / 500000000000 : ℝ) (4183001369 / 3906250000 : ℝ) := by
  exact Encl.sqrt b668 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e670 : ℝ := e5 + e669
lemma b670 : Encl e670 (1035424175231 / 500000000000 : ℝ) (8089251369 / 3906250000 : ℝ) := by
  exact Encl.add b5 b669 (by norm_num) (by norm_num)

def e671 : ℝ := e666 / e670
lemma b671 : Encl e671 (184965496843 / 1000000000000 : ℝ) (92482748423 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b666 b670 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e672 : ℝ := Real.arcsin e632
lemma b672 : Encl e672 (365796809329 / 500000000000 : ℝ) (731593618671 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e632) (a := (184965496843 / 1000000000000 : ℝ)) (b := (92482748423 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (668056311539 / 1000000000000 : ℝ) by norm_num).trans b632.1
        exact b632.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e632) (184965496843 / 1000000000000 : ℝ) (92482748423 / 500000000000 : ℝ) from b671) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e673 : ℝ := e59 * e672
lemma b673 : Encl e673 (74622549103 / 200000000000 : ℝ) (373112745523 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b672 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e674 : ℝ := e61 * e632
lemma b674 : Encl e674 (163673796327 / 500000000000 : ℝ) (20459224541 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b632 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e675 : ℝ := e674 * e664
lemma b675 : Encl e675 (243582853077 / 1000000000000 : ℝ) (243582853081 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b674 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e676 : ℝ := e673 - e675
lemma b676 : Encl e676 (64764946217 / 500000000000 : ℝ) (64764946223 / 500000000000 : ℝ) := by
  exact Encl.sub b673 b675 (by norm_num) (by norm_num)

def e677 : ℝ := e43 * e664
lemma b677 : Encl e677 (148822144133 / 4000000000 : ℝ) (186027680167 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e678 : ℝ := e632 / e677
lemma b678 : Encl e678 (3591166169 / 200000000000 : ℝ) (8977915423 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b677 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e679 : ℝ := e676 - e678
lemma b679 : Encl e679 (27893515397 / 250000000000 : ℝ) (111574061601 / 1000000000000 : ℝ) := by
  exact Encl.sub b676 b678 (by norm_num) (by norm_num)

def e680 : ℝ := e5 + e648
lemma b680 : Encl e680 (1950100592163 / 1000000000000 : ℝ) (487525148041 / 250000000000 : ℝ) := by
  exact Encl.add b5 b648 (by norm_num) (by norm_num)

def e681 : ℝ := e631 / e680
lemma b681 : Encl e681 (79981435243 / 500000000000 : ℝ) (19995358811 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b631 b680 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e682 : ℝ := e681 ^ 2
lemma b682 : Encl e682 (12794059967 / 500000000000 : ℝ) (5117623987 / 200000000000 : ℝ) := by
  exact Encl.pow b681 (by norm_num) 2 (by norm_num) (by norm_num)

def e683 : ℝ := e5 + e682
lemma b683 : Encl e683 (512794059967 / 500000000000 : ℝ) (205117623987 / 200000000000 : ℝ) := by
  exact Encl.add b5 b682 (by norm_num) (by norm_num)

def e684 : ℝ := Real.sqrt e683
lemma b684 : Encl e684 (506356623323 / 500000000000 : ℝ) (126589155831 / 125000000000 : ℝ) := by
  exact Encl.sqrt b683 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e685 : ℝ := e5 + e684
lemma b685 : Encl e685 (1006356623323 / 500000000000 : ℝ) (251589155831 / 125000000000 : ℝ) := by
  exact Encl.add b5 b684 (by norm_num) (by norm_num)

def e686 : ℝ := e681 / e685
lemma b686 : Encl e686 (15895246951 / 200000000000 : ℝ) (79476234757 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b681 b685 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e687 : ℝ := Real.arcsin e631
lemma b687 : Encl e687 (158619059251 / 500000000000 : ℝ) (317238118511 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e631) (a := (15895246951 / 200000000000 : ℝ)) (b := (79476234757 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (15597184423 / 50000000000 : ℝ) by norm_num).trans b631.1
        exact b631.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e631) (15895246951 / 200000000000 : ℝ) (79476234757 / 1000000000000 : ℝ) from b686) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e688 : ℝ := e59 * e687
lemma b688 : Encl e688 (40447860109 / 250000000000 : ℝ) (161791440441 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b687 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e689 : ℝ := e61 * e631
lemma b689 : Encl e689 (30570481469 / 200000000000 : ℝ) (76426203673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b631 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e690 : ℝ := e689 * e648
lemma b690 : Encl e690 (36306290683 / 250000000000 : ℝ) (72612581367 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b689 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e691 : ℝ := e688 - e690
lemma b691 : Encl e691 (8283138851 / 500000000000 : ℝ) (16566277709 / 1000000000000 : ℝ) := by
  exact Encl.sub b688 b690 (by norm_num) (by norm_num)

def e692 : ℝ := e43 * e648
lemma b692 : Encl e692 (950100592163 / 20000000000 : ℝ) (237525148041 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b648 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e693 : ℝ := e631 / e692
lemma b693 : Encl e693 (3283270119 / 500000000000 : ℝ) (6566540239 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b631 b692 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e694 : ℝ := e691 - e693
lemma b694 : Encl e694 (9999737463 / 1000000000000 : ℝ) (9999737471 / 1000000000000 : ℝ) := by
  exact Encl.sub b691 b693 (by norm_num) (by norm_num)

def e695 : ℝ := e679 - e694
lemma b695 : Encl e695 (101574324117 / 1000000000000 : ℝ) (50787162069 / 500000000000 : ℝ) := by
  exact Encl.sub b679 b694 (by norm_num) (by norm_num)

def e696 : ℝ := e695 / e8
lemma b696 : Encl e696 (103647269507 / 1000000000000 : ℝ) (103647269529 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b695 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e697 : ℝ := e661 + e696
lemma b697 : Encl e697 (-179076424441 / 500000000000 : ℝ) (-358152848833 / 1000000000000 : ℝ) := by
  exact Encl.add b661 b696 (by norm_num) (by norm_num)

def e698 : ℝ := e632 + e4
lemma b698 : Encl e698 (1657799630149 / 1000000000000 : ℝ) (207224953769 / 125000000000 : ℝ) := by
  exact Encl.add b632 b4 (by norm_num) (by norm_num)

def e699 : ℝ := e698 / e23
lemma b699 : Encl e699 (414449907537 / 500000000000 : ℝ) (207224953769 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b698 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e700 : ℝ := e632 / e8
lemma b700 : Encl e700 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b632 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e701 : ℝ := e89 * e700
lemma b701 : Encl e701 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b700 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e702 : ℝ := e700 ^ 2
lemma b702 : Encl e702 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b700 (by norm_num) 2 (by norm_num) (by norm_num)

def e703 : ℝ := e91 * e702
lemma b703 : Encl e703 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b702 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e704 : ℝ := e5 + e703
lemma b704 : Encl e704 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b703 (by norm_num) (by norm_num)

def e705 : ℝ := Real.sqrt e704
lemma b705 : Encl e705 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b704 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e706 : ℝ := e701 * e705
lemma b706 : Encl e706 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b701 b705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e707 : ℝ := e97 * e702
lemma b707 : Encl e707 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b702 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e708 : ℝ := e706 - e707
lemma b708 : Encl e708 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b706 b707 (by norm_num) (by norm_num)

def e709 : ℝ := e699 * e708
lemma b709 : Encl e709 (56505280927 / 100000000000 : ℝ) (141263202323 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b699 b708 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e710 : ℝ := e699 / e8
lemma b710 : Encl e710 (84581613783 / 100000000000 : ℝ) (845816137833 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e711 : ℝ := e89 * e710
lemma b711 : Encl e711 (749585035327 / 500000000000 : ℝ) (1499170070661 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e712 : ℝ := e710 ^ 2
lemma b712 : Encl e712 (715404939013 / 1000000000000 : ℝ) (715404939019 / 1000000000000 : ℝ) := by
  exact Encl.pow b710 (by norm_num) 2 (by norm_num) (by norm_num)

def e713 : ℝ := e91 * e712
lemma b713 : Encl e713 (112375545037 / 200000000000 : ℝ) (70234715649 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b712 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e714 : ℝ := e5 + e713
lemma b714 : Encl e714 (312375545037 / 200000000000 : ℝ) (195234715649 / 125000000000 : ℝ) := by
  exact Encl.add b5 b713 (by norm_num) (by norm_num)

def e715 : ℝ := Real.sqrt e714
lemma b715 : Encl e715 (624875532643 / 500000000000 : ℝ) (124975106529 / 100000000000 : ℝ) := by
  exact Encl.sqrt b714 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e716 : ℝ := e711 * e715
lemma b716 : Encl e716 (468397348211 / 250000000000 : ℝ) (93679469643 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b711 b715 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e717 : ℝ := e97 * e712
lemma b717 : Encl e717 (1123755450371 / 1000000000000 : ℝ) (1123755450383 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b712 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e718 : ℝ := e716 - e717
lemma b718 : Encl e718 (749833942461 / 1000000000000 : ℝ) (749833942489 / 1000000000000 : ℝ) := by
  exact Encl.sub b716 b717 (by norm_num) (by norm_num)

def e719 : ℝ := e632 * e718
lemma b719 : Encl e719 (500931297867 / 1000000000000 : ℝ) (15654103059 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b632 b718 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e720 : ℝ := e709 - e719
lemma b720 : Encl e720 (32060755691 / 500000000000 : ℝ) (2564860457 / 40000000000 : ℝ) := by
  exact Encl.sub b709 b719 (by norm_num) (by norm_num)

def e721 : ℝ := e699 ^ 2
lemma b721 : Encl e721 (687074903429 / 1000000000000 : ℝ) (343537451717 / 500000000000 : ℝ) := by
  exact Encl.pow b699 (by norm_num) 2 (by norm_num) (by norm_num)

def e722 : ℝ := e8 * e721
lemma b722 : Encl e722 (8416667567 / 12500000000 : ℝ) (336666702683 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b721 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e723 : ℝ := e5 - e722
lemma b723 : Encl e723 (163333297317 / 500000000000 : ℝ) (4083332433 / 12500000000 : ℝ) := by
  exact Encl.sub b5 b722 (by norm_num) (by norm_num)

def e724 : ℝ := e5 - e721
lemma b724 : Encl e724 (156462548283 / 500000000000 : ℝ) (312925096571 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b721 (by norm_num) (by norm_num)

def e725 : ℝ := Real.sqrt e724

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
