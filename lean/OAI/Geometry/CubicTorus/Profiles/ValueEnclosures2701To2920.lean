import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures2480To2700

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
lemma b2700 : Encl e2700 (20639797331 / 31250000000 : ℝ) (66047351461 / 100000000000 : ℝ) := by
  exact Encl.pow b2699 (by norm_num) 2 (by norm_num) (by norm_num)

def e2701 : ℝ := e5 + e2700
lemma b2701 : Encl e2701 (51889797331 / 31250000000 : ℝ) (166047351461 / 100000000000 : ℝ) := by
  exact Encl.add b5 b2700 (by norm_num) (by norm_num)

def e2702 : ℝ := Real.sqrt e2701
lemma b2702 : Encl e2702 (1288593618869 / 1000000000000 : ℝ) (1288593618877 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2701 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2703 : ℝ := e5 + e2702
lemma b2703 : Encl e2703 (2288593618869 / 1000000000000 : ℝ) (2288593618877 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2702 (by norm_num) (by norm_num)

def e2704 : ℝ := e2699 / e2703
lemma b2704 : Encl e2704 (22194176633 / 62500000000 : ℝ) (71021365227 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2699 b2703 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2705 : ℝ := Real.arcsin e2662
lemma b2705 : Encl e2705 (272973653087 / 200000000000 : ℝ) (136486826553 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e2662) (a := (22194176633 / 62500000000 : ℝ)) (b := (71021365227 / 200000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (489435820057 / 500000000000 : ℝ) by norm_num).trans b2662.1
        exact b2662.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2662) (22194176633 / 62500000000 : ℝ) (71021365227 / 200000000000 : ℝ) from b2704) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2706 : ℝ := e59 * e2705
lemma b2706 : Encl e2706 (696082815371 / 1000000000000 : ℝ) (696082815421 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2705 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2707 : ℝ := e61 * e2662
lemma b2707 : Encl e2707 (95929420731 / 200000000000 : ℝ) (479647103657 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2662 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2708 : ℝ := e2707 * e2688
lemma b2708 : Encl e2708 (98076177607 / 1000000000000 : ℝ) (19615235523 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2707 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2709 : ℝ := e2706 - e2708
lemma b2709 : Encl e2709 (149501659439 / 250000000000 : ℝ) (299003318907 / 500000000000 : ℝ) := by
  exact Encl.sub b2706 b2708 (by norm_num) (by norm_num)

def e2710 : ℝ := e43 * e2688
lemma b2710 : Encl e2710 (102237850349 / 10000000000 : ℝ) (204475700711 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2711 : ℝ := e2662 / e2710
lemma b2711 : Encl e2711 (748004253 / 7812500000 : ℝ) (95744544391 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2662 b2710 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2712 : ℝ := e2709 - e2711
lemma b2712 : Encl e2712 (100452418673 / 200000000000 : ℝ) (50226209343 / 100000000000 : ℝ) := by
  exact Encl.sub b2709 b2711 (by norm_num) (by norm_num)

def e2713 : ℝ := e2712 - e2642
lemma b2713 : Encl e2713 (5340205087 / 200000000000 : ℝ) (5340205109 / 200000000000 : ℝ) := by
  exact Encl.sub b2712 b2642 (by norm_num) (by norm_num)

def e2714 : ℝ := e2697 * e2713
lemma b2714 : Encl e2714 (49000419 / 500000000000 : ℝ) (98000841 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2697 b2713 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2715 : ℝ := e2696 + e2714
lemma b2715 : Encl e2715 (8153483 / 40000000000 : ℝ) (5095927 / 25000000000 : ℝ) := by
  exact Encl.add b2696 b2714 (by norm_num) (by norm_num)

def e2716 : ℝ := e2662 - e2595
lemma b2716 : Encl e2716 (10871678493 / 1000000000000 : ℝ) (5435839249 / 500000000000 : ℝ) := by
  exact Encl.sub b2662 b2595 (by norm_num) (by norm_num)

def e2717 : ℝ := e2715 / e2716
lemma b2717 : Encl e2717 (9374682807 / 500000000000 : ℝ) (18749366083 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2715 b2716 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2718 : ℝ := e2660 + e2717
lemma b2718 : Encl e2718 (-7478391751 / 500000000000 : ℝ) (-14956782981 / 1000000000000 : ℝ) := by
  exact Encl.add b2660 b2717 (by norm_num) (by norm_num)

def e2719 : ℝ := e4 * e2681
lemma b2719 : Encl e2719 (678330892839 / 1000000000000 : ℝ) (678330892861 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b2681 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2720 : ℝ := e4 / e2593
lemma b2720 : Encl e2720 (697002337049 / 1000000000000 : ℝ) (13940046741 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2721 : ℝ := e89 * e2720
lemma b2721 : Encl e2721 (154425559549 / 125000000000 : ℝ) (247080895279 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b2720 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2722 : ℝ := e2720 ^ 2
lemma b2722 : Encl e2722 (485812257851 / 1000000000000 : ℝ) (242906128927 / 500000000000 : ℝ) := by
  exact Encl.pow b2720 (by norm_num) 2 (by norm_num) (by norm_num)

def e2723 : ℝ := e91 * e2722
lemma b2723 : Encl e2723 (381556055071 / 1000000000000 : ℝ) (15262242203 / 40000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b2722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2724 : ℝ := e5 + e2723
lemma b2724 : Encl e2724 (1381556055071 / 1000000000000 : ℝ) (55262242203 / 40000000000 : ℝ) := by
  exact Encl.add b5 b2723 (by norm_num) (by norm_num)

def e2725 : ℝ := Real.sqrt e2724
lemma b2725 : Encl e2725 (587698063437 / 500000000000 : ℝ) (293849031719 / 250000000000 : ℝ) := by
  exact Encl.sqrt b2724 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2726 : ℝ := e2721 * e2725
lemma b2726 : Encl e2726 (1452089636673 / 1000000000000 : ℝ) (36302240917 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b2721 b2725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2727 : ℝ := e97 * e2722
lemma b2727 : Encl e2727 (763112110143 / 1000000000000 : ℝ) (15262242203 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b2722 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2728 : ℝ := e2726 - e2727
lemma b2728 : Encl e2728 (688977526523 / 1000000000000 : ℝ) (688977526537 / 1000000000000 : ℝ) := by
  exact Encl.sub b2726 b2727 (by norm_num) (by norm_num)

def e2729 : ℝ := e2662 * e2728
lemma b2729 : Encl e2729 (674420561389 / 1000000000000 : ℝ) (134884112281 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2662 b2728 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2730 : ℝ := e2719 - e2729
lemma b2730 : Encl e2730 (1955165717 / 500000000000 : ℝ) (244395717 / 62500000000 : ℝ) := by
  exact Encl.sub b2719 b2729 (by norm_num) (by norm_num)

def e2731 : ℝ := e165 - e2690
lemma b2731 : Encl e2731 (4549329963 / 250000000000 : ℝ) (9098659977 / 500000000000 : ℝ) := by
  exact Encl.sub b165 b2690 (by norm_num) (by norm_num)

def e2732 : ℝ := e2730 * e2731
lemma b2732 : Encl e2732 (71157551 / 1000000000000 : ℝ) (71157553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2730 b2731 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2733 : ℝ := e2728 - e2681
lemma b2733 : Encl e2733 (904277559 / 250000000000 : ℝ) (3617110271 / 1000000000000 : ℝ) := by
  exact Encl.sub b2728 b2681 (by norm_num) (by norm_num)

def e2734 : ℝ := e183 - e2712
lemma b2734 : Encl e2734 (8945338041 / 500000000000 : ℝ) (8945338139 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b2712 (by norm_num) (by norm_num)

def e2735 : ℝ := e2733 * e2734
lemma b2735 : Encl e2735 (64712547 / 1000000000000 : ℝ) (64712549 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2733 b2734 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2736 : ℝ := e2732 + e2735
lemma b2736 : Encl e2736 (67935049 / 500000000000 : ℝ) (67935051 / 500000000000 : ℝ) := by
  exact Encl.add b2732 b2735 (by norm_num) (by norm_num)

def e2737 : ℝ := e4 - e2662
lemma b2737 : Encl e2737 (5435839247 / 500000000000 : ℝ) (10871678497 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b2662 (by norm_num) (by norm_num)

def e2738 : ℝ := e2736 / e2737
lemma b2738 : Encl e2738 (12497619207 / 1000000000000 : ℝ) (12497619579 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2736 b2737 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2739 : ℝ := e2718 + e2738
lemma b2739 : Encl e2739 (-491832859 / 200000000000 : ℝ) (-1229581701 / 500000000000 : ℝ) := by
  exact Encl.add b2718 b2738 (by norm_num) (by norm_num)

def e2740 : ℝ := e924 / e2593
lemma b2740 : Encl e2740 (169014084507 / 250000000000 : ℝ) (676056338029 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2741 : ℝ := min e7 e2740
lemma b2741 : Encl e2741 (169014084507 / 250000000000 : ℝ) (676056338029 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2740 (by norm_num) (by norm_num)

def e2742 : ℝ := e2741 - e5
lemma b2742 : Encl e2742 (-80985915493 / 250000000000 : ℝ) (-323943661971 / 1000000000000 : ℝ) := by
  exact Encl.sub b2741 b5 (by norm_num) (by norm_num)

def e2743 : ℝ := e23 * e2593
lemma b2743 : Encl e2743 (71 / 25 : ℝ) (71 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2593 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2744 : ℝ := e2743 * e2604
lemma b2744 : Encl e2744 (1966251322401 / 1000000000000 : ℝ) (393250264481 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2743 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2745 : ℝ := e2744 / e0
lemma b2745 : Encl e2745 (312938617321 / 500000000000 : ℝ) (156469308661 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2744 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2746 : ℝ := e2742 + e2745
lemma b2746 : Encl e2746 (30193357267 / 100000000000 : ℝ) (301933572673 / 1000000000000 : ℝ) := by
  exact Encl.add b2742 b2745 (by norm_num) (by norm_num)

def e2747 : ℝ := e23 * e2598
lemma b2747 : Encl e2747 (5041 / 1250 : ℝ) (5041 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2598 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2748 : ℝ := e2747 * e2604
lemma b2748 : Encl e2748 (2792076877809 / 1000000000000 : ℝ) (1396038438907 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2747 b2604 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2749 : ℝ := e0 + e2748
lemma b2749 : Encl e2749 (2966834765699 / 500000000000 : ℝ) (1483417382851 / 250000000000 : ℝ) := by
  exact Encl.add b0 b2748 (by norm_num) (by norm_num)

def e2750 : ℝ := Real.sqrt e2749
lemma b2750 : Encl e2750 (121795623191 / 50000000000 : ℝ) (2435912463823 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2749 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2751 : ℝ := e932 * e2750
lemma b2751 : Encl e2751 (1550750038223 / 1000000000000 : ℝ) (387687509557 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2752 : ℝ := e2593 ^ 3
lemma b2752 : Encl e2752 (357911 / 125000 : ℝ) (357911 / 125000 : ℝ) := by
  exact Encl.pow b2593 (by norm_num) 3 (by norm_num) (by norm_num)

def e2753 : ℝ := e939 * e2752
lemma b2753 : Encl e2753 (23980037 / 62500000 : ℝ) (23980037 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2752 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2754 : ℝ := min e2753 e941
lemma b2754 : Encl e2754 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2753 b941 (by norm_num) (by norm_num)

def e2755 : ℝ := e23 * e2746
lemma b2755 : Encl e2755 (30193357267 / 50000000000 : ℝ) (301933572673 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2746 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2756 : ℝ := e944 * e2754
lemma b2756 : Encl e2756 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2754 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2757 : ℝ := e2751 ^ 2
lemma b2757 : Encl e2757 (300603210131 / 125000000000 : ℝ) (480965136213 / 200000000000 : ℝ) := by
  exact Encl.pow b2751 (by norm_num) 2 (by norm_num) (by norm_num)

def e2758 : ℝ := e2756 * e2757
lemma b2758 : Encl e2758 (5194423471063 / 1000000000000 : ℝ) (5194423471101 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2756 b2757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2759 : ℝ := e2758 * e2746
lemma b2759 : Encl e2759 (784185418289 / 500000000000 : ℝ) (1568370836607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2758 b2746 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2760 : ℝ := e2759 / e9
lemma b2760 : Encl e2760 (112026488327 / 20000000000 : ℝ) (2800662208227 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2759 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2761 : ℝ := e5 + e2760
lemma b2761 : Encl e2761 (132026488327 / 20000000000 : ℝ) (3300662208227 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2760 (by norm_num) (by norm_num)

def e2762 : ℝ := Real.sqrt e2761
lemma b2762 : Encl e2762 (513860853397 / 200000000000 : ℝ) (1284652133503 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2761 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2763 : ℝ := e5 + e2762
lemma b2763 : Encl e2763 (713860853397 / 200000000000 : ℝ) (1784652133503 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2762 (by norm_num) (by norm_num)

def e2764 : ℝ := e2755 / e2763
lemma b2764 : Encl e2764 (84591715943 / 500000000000 : ℝ) (16918343189 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2755 b2763 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2765 : ℝ := e2754 * e954
lemma b2765 : Encl e2765 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2754 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2766 : ℝ := e2746 - e2764
lemma b2766 : Encl e2766 (6637507039 / 50000000000 : ℝ) (132750140787 / 1000000000000 : ℝ) := by
  exact Encl.sub b2746 b2764 (by norm_num) (by norm_num)

def e2767 : ℝ := e2766 / e2751
lemma b2767 : Encl e2767 (85603828797 / 1000000000000 : ℝ) (85603828803 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2766 b2751 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2768 : ℝ := e2767 ^ 2
lemma b2768 : Encl e2768 (458000969 / 62500000000 : ℝ) (3664007753 / 500000000000 : ℝ) := by
  exact Encl.pow b2767 (by norm_num) 2 (by norm_num) (by norm_num)

def e2769 : ℝ := e9 * e2768
lemma b2769 : Encl e2769 (2051844341 / 1000000000000 : ℝ) (1025922171 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2770 : ℝ := e2764 ^ 3
lemma b2770 : Encl e2770 (4842543059 / 1000000000000 : ℝ) (242127153 / 50000000000 : ℝ) := by
  exact Encl.pow b2764 (by norm_num) 3 (by norm_num) (by norm_num)

def e2771 : ℝ := e2754 * e2770
lemma b2771 : Encl e2771 (1743315501 / 1000000000000 : ℝ) (871657751 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2754 b2770 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2772 : ℝ := e2769 + e2771
lemma b2772 : Encl e2772 (1897579921 / 500000000000 : ℝ) (948789961 / 250000000000 : ℝ) := by
  exact Encl.add b2769 b2771 (by norm_num) (by norm_num)

def e2773 : ℝ := min e2765 e2772
lemma b2773 : Encl e2773 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.min b2765 b2772 (by norm_num) (by norm_num)

def e2774 : ℝ := (73 / 50 : ℝ)
lemma b2774 : Encl e2774 (73 / 50 : ℝ) (73 / 50 : ℝ) := by
  exact Encl.exact (73 / 50 : ℝ)

def e2775 : ℝ := e2774 / e0
lemma b2775 : Encl e2775 (116183108457 / 250000000000 : ℝ) (464732433829 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2774 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2776 : ℝ := e8 * e2774
lemma b2776 : Encl e2776 (3577 / 2500 : ℝ) (3577 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2777 : ℝ := e2776 / e0
lemma b2777 : Encl e2777 (455437785151 / 1000000000000 : ℝ) (7116215393 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b2776 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2778 : ℝ := e2774 ^ 2
lemma b2778 : Encl e2778 (5329 / 2500 : ℝ) (5329 / 2500 : ℝ) := by
  exact Encl.pow b2774 (by norm_num) 2 (by norm_num) (by norm_num)

def e2779 : ℝ := e17 * e2778
lemma b2779 : Encl e2779 (5329 / 625 : ℝ) (5329 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2780 : ℝ := e2779 / e0
lemma b2780 : Encl e2780 (2714037413557 / 1000000000000 : ℝ) (1357018706779 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2779 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2781 : ℝ := e5 + e2780
lemma b2781 : Encl e2781 (3714037413557 / 1000000000000 : ℝ) (1857018706779 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2780 (by norm_num) (by norm_num)

def e2782 : ℝ := Real.sqrt e2781
lemma b2782 : Encl e2782 (1927183803781 / 1000000000000 : ℝ) (963591901891 / 500000000000 : ℝ) := by
  exact Encl.sqrt b2781 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2783 : ℝ := e5 + e2782
lemma b2783 : Encl e2783 (2927183803781 / 1000000000000 : ℝ) (1463591901891 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2782 (by norm_num) (by norm_num)

def e2784 : ℝ := e23 / e2783
lemma b2784 : Encl e2784 (68325056917 / 100000000000 : ℝ) (683250569171 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2783 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2785 : ℝ := e9 * e2784
lemma b2785 : Encl e2785 (191310159367 / 1000000000000 : ℝ) (23913769921 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2786 : ℝ := e2777 + e2785
lemma b2786 : Encl e2786 (323373972259 / 500000000000 : ℝ) (16168698613 / 25000000000 : ℝ) := by
  exact Encl.add b2777 b2785 (by norm_num) (by norm_num)

def e2787 : ℝ := e2786 - e5
lemma b2787 : Encl e2787 (-176626027741 / 500000000000 : ℝ) (-8831301387 / 25000000000 : ℝ) := by
  exact Encl.sub b2786 b5 (by norm_num) (by norm_num)

def e2788 : ℝ := e0 / e2778
lemma b2788 : Encl e2788 (294763806867 / 200000000000 : ℝ) (46056844823 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2789 : ℝ := e2775 ^ 2
lemma b2789 : Encl e2789 (215976235051 / 1000000000000 : ℝ) (215976235053 / 1000000000000 : ℝ) := by
  exact Encl.pow b2775 (by norm_num) 2 (by norm_num) (by norm_num)

def e2790 : ℝ := e5 - e2789
lemma b2790 : Encl e2790 (784023764947 / 1000000000000 : ℝ) (784023764949 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b2789 (by norm_num) (by norm_num)

def e2791 : ℝ := Real.sqrt e2790
lemma b2791 : Encl e2791 (885451164631 / 1000000000000 : ℝ) (885451164633 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2790 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2792 : ℝ := e29 - e2791
lemma b2792 : Encl e2792 (-218784497967 / 1000000000000 : ℝ) (-54696124491 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b2791 (by norm_num) (by norm_num)

def e2793 : ℝ := e2791 ^ 3
lemma b2793 : Encl e2793 (69421475577 / 100000000000 : ℝ) (27768590231 / 40000000000 : ℝ) := by
  exact Encl.pow b2791 (by norm_num) 3 (by norm_num) (by norm_num)

def e2794 : ℝ := e2793 / e35
lemma b2794 : Encl e2794 (23140491859 / 100000000000 : ℝ) (3615701853 / 15625000000 : ℝ) := by
  exact Encl.div_nonneg b2793 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2795 : ℝ := e2792 + e2794
lemma b2795 : Encl e2795 (12620420623 / 1000000000000 : ℝ) (3155105157 / 250000000000 : ℝ) := by
  exact Encl.add b2792 b2794 (by norm_num) (by norm_num)

def e2796 : ℝ := e8 * e2795
lemma b2796 : Encl e2796 (1236801221 / 100000000000 : ℝ) (1546001527 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2797 : ℝ := e2789 / e2791
lemma b2797 : Encl e2797 (48783319437 / 200000000000 : ℝ) (243916597189 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2789 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2798 : ℝ := e2797 - e23
lemma b2798 : Encl e2798 (-351216680563 / 200000000000 : ℝ) (-1756083402811 / 1000000000000 : ℝ) := by
  exact Encl.sub b2797 b23 (by norm_num) (by norm_num)

def e2799 : ℝ := e23 * e2791
lemma b2799 : Encl e2799 (885451164631 / 500000000000 : ℝ) (885451164633 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2800 : ℝ := e2798 + e2799
lemma b2800 : Encl e2800 (14818926447 / 1000000000000 : ℝ) (2963785291 / 200000000000 : ℝ) := by
  exact Encl.add b2798 b2799 (by norm_num) (by norm_num)

def e2801 : ℝ := e2800 / e43
lemma b2801 : Encl e2801 (9261829 / 31250000000 : ℝ) (29637853 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2800 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2802 : ℝ := e2796 - e2801
lemma b2802 : Encl e2802 (150895421 / 12500000000 : ℝ) (1508954211 / 125000000000 : ℝ) := by
  exact Encl.sub b2796 b2801 (by norm_num) (by norm_num)

def e2803 : ℝ := e2788 * e2802
lemma b2803 : Encl e2803 (17791403493 / 1000000000000 : ℝ) (3558280701 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2788 b2802 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2804 : ℝ := e2787 + e2803
lemma b2804 : Encl e2804 (-335460651989 / 1000000000000 : ℝ) (-13418426079 / 40000000000 : ℝ) := by
  exact Encl.add b2787 b2803 (by norm_num) (by norm_num)

def e2805 : ℝ := e5 + e2791
lemma b2805 : Encl e2805 (1885451164631 / 1000000000000 : ℝ) (1885451164633 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2791 (by norm_num) (by norm_num)

def e2806 : ℝ := e2775 / e2805
lemma b2806 : Encl e2806 (61620852683 / 250000000000 : ℝ) (123241705367 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2775 b2805 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2807 : ℝ := e2806 ^ 2
lemma b2807 : Encl e2807 (30377035883 / 500000000000 : ℝ) (7594258971 / 125000000000 : ℝ) := by
  exact Encl.pow b2806 (by norm_num) 2 (by norm_num) (by norm_num)

def e2808 : ℝ := e5 + e2807
lemma b2808 : Encl e2808 (530377035883 / 500000000000 : ℝ) (132594258971 / 125000000000 : ℝ) := by
  exact Encl.add b5 b2807 (by norm_num) (by norm_num)

def e2809 : ℝ := Real.sqrt e2808
lemma b2809 : Encl e2809 (205985831723 / 200000000000 : ℝ) (1029929158617 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2808 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2810 : ℝ := e5 + e2809
lemma b2810 : Encl e2810 (405985831723 / 200000000000 : ℝ) (2029929158617 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2809 (by norm_num) (by norm_num)

def e2811 : ℝ := e2806 / e2810
lemma b2811 : Encl e2811 (121424636759 / 1000000000000 : ℝ) (121424636761 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2806 b2810 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2812 : ℝ := Real.arcsin e2775
lemma b2812 : Encl e2812 (96666481327 / 200000000000 : ℝ) (120833101661 / 250000000000 : ℝ) := by
  apply Encl.arcsin (z := e2775) (a := (121424636759 / 1000000000000 : ℝ)) (b := (121424636761 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (116183108457 / 250000000000 : ℝ) by norm_num).trans b2775.1
        exact b2775.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2775) (121424636759 / 1000000000000 : ℝ) (121424636761 / 1000000000000 : ℝ) from b2811) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2813 : ℝ := e59 * e2812
lemma b2813 : Encl e2813 (246499527383 / 1000000000000 : ℝ) (246499527389 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2812 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2814 : ℝ := e61 * e2775
lemma b2814 : Encl e2814 (9108755703 / 40000000000 : ℝ) (227718892577 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2775 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2815 : ℝ := e2814 * e2791
lemma b2815 : Encl e2815 (201633958639 / 1000000000000 : ℝ) (100816979321 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b2814 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2816 : ℝ := e2813 - e2815
lemma b2816 : Encl e2816 (44865568741 / 1000000000000 : ℝ) (7178491 / 160000000 : ℝ) := by
  exact Encl.sub b2813 b2815 (by norm_num) (by norm_num)

def e2817 : ℝ := e43 * e2791
lemma b2817 : Encl e2817 (885451164631 / 20000000000 : ℝ) (885451164633 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2791 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2818 : ℝ := e2775 / e2817
lemma b2818 : Encl e2818 (2624269143 / 250000000000 : ℝ) (10497076573 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2775 b2817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2819 : ℝ := e2816 - e2818
lemma b2819 : Encl e2819 (4296061521 / 125000000000 : ℝ) (17184246089 / 500000000000 : ℝ) := by
  exact Encl.sub b2816 b2818 (by norm_num) (by norm_num)

def e2820 : ℝ := e183 - e2819
lemma b2820 : Encl e2820 (242892138667 / 500000000000 : ℝ) (19431371099 / 40000000000 : ℝ) := by
  exact Encl.sub b183 b2819 (by norm_num) (by norm_num)

def e2821 : ℝ := e2820 / e2774
lemma b2821 : Encl e2821 (166364478539 / 500000000000 : ℝ) (13309158287 / 40000000000 : ℝ) := by
  exact Encl.div_nonneg b2820 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2822 : ℝ := e2804 + e2821
lemma b2822 : Encl e2822 (-2731694911 / 1000000000000 : ℝ) (-6829237 / 2500000000 : ℝ) := by
  exact Encl.add b2804 b2821 (by norm_num) (by norm_num)

def e2823 : ℝ := e924 / e2774
lemma b2823 : Encl e2823 (26301369863 / 40000000000 : ℝ) (41095890411 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b924 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2824 : ℝ := min e7 e2823
lemma b2824 : Encl e2824 (26301369863 / 40000000000 : ℝ) (41095890411 / 62500000000 : ℝ) := by
  exact Encl.min b7 b2823 (by norm_num) (by norm_num)

def e2825 : ℝ := e2824 - e5
lemma b2825 : Encl e2825 (-13698630137 / 40000000000 : ℝ) (-21404109589 / 62500000000 : ℝ) := by
  exact Encl.sub b2824 b5 (by norm_num) (by norm_num)

def e2826 : ℝ := e23 * e2774
lemma b2826 : Encl e2826 (73 / 25 : ℝ) (73 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b2774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2827 : ℝ := e2826 * e2784
lemma b2827 : Encl e2827 (249386457747 / 125000000000 : ℝ) (99754583099 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b2826 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2828 : ℝ := e2827 / e0
lemma b2828 : Encl e2828 (635057399849 / 1000000000000 : ℝ) (158764349963 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2827 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2829 : ℝ := e2825 + e2828
lemma b2829 : Encl e2829 (36573955803 / 125000000000 : ℝ) (73147911607 / 250000000000 : ℝ) := by
  exact Encl.add b2825 b2828 (by norm_num) (by norm_num)

def e2830 : ℝ := e23 * e2778
lemma b2830 : Encl e2830 (5329 / 1250 : ℝ) (5329 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b2778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2831 : ℝ := e2830 * e2784
lemma b2831 : Encl e2831 (582566765297 / 200000000000 : ℝ) (291283382649 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b2830 b2784 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2832 : ℝ := e0 + e2831
lemma b2832 : Encl e2832 (3027213240037 / 500000000000 : ℝ) (75680331001 / 12500000000 : ℝ) := by
  exact Encl.add b0 b2831 (by norm_num) (by norm_num)

def e2833 : ℝ := Real.sqrt e2832
lemma b2833 : Encl e2833 (492114884151 / 200000000000 : ℝ) (2460574420757 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2834 : ℝ := e932 * e2833
lemma b2834 : Encl e2834 (1566450327633 / 1000000000000 : ℝ) (1566450327637 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2833 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2835 : ℝ := e2774 ^ 3
lemma b2835 : Encl e2835 (389017 / 125000 : ℝ) (389017 / 125000 : ℝ) := by
  exact Encl.pow b2774 (by norm_num) 3 (by norm_num) (by norm_num)

def e2836 : ℝ := e939 * e2835
lemma b2836 : Encl e2836 (26064139 / 62500000 : ℝ) (26064139 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2835 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2837 : ℝ := min e2836 e941
lemma b2837 : Encl e2837 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2836 b941 (by norm_num) (by norm_num)

def e2838 : ℝ := e23 * e2829
lemma b2838 : Encl e2838 (36573955803 / 62500000000 : ℝ) (73147911607 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2839 : ℝ := e944 * e2837
lemma b2839 : Encl e2839 (54 / 25 : ℝ) (54 / 25 : ℝ) := by
  exact Encl.mul_nonneg b944 b2837 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2840 : ℝ := e2834 ^ 2
lemma b2840 : Encl e2840 (2453766628941 / 1000000000000 : ℝ) (490753325791 / 200000000000 : ℝ) := by
  exact Encl.pow b2834 (by norm_num) 2 (by norm_num) (by norm_num)

def e2841 : ℝ := e2839 * e2840
lemma b2841 : Encl e2841 (331258494907 / 62500000000 : ℝ) (5300135918543 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2839 b2840 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2842 : ℝ := e2841 * e2829
lemma b2842 : Encl e2842 (387693873667 / 250000000000 : ℝ) (1550775494699 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2841 b2829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2843 : ℝ := e2842 / e9
lemma b2843 : Encl e2843 (692310488691 / 125000000000 : ℝ) (138462097741 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b2842 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2844 : ℝ := e5 + e2843
lemma b2844 : Encl e2844 (817310488691 / 125000000000 : ℝ) (163462097741 / 25000000000 : ℝ) := by
  exact Encl.add b5 b2843 (by norm_num) (by norm_num)

def e2845 : ℝ := Real.sqrt e2844
lemma b2845 : Encl e2845 (319630741773 / 125000000000 : ℝ) (2557045934207 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2844 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2846 : ℝ := e5 + e2845
lemma b2846 : Encl e2846 (444630741773 / 125000000000 : ℝ) (3557045934207 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2845 (by norm_num) (by norm_num)

def e2847 : ℝ := e2838 / e2846
lemma b2847 : Encl e2847 (164513842011 / 1000000000000 : ℝ) (32902768403 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2838 b2846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2848 : ℝ := e2837 * e954
lemma b2848 : Encl e2848 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.mul_nonneg b2837 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2849 : ℝ := e2829 - e2847
lemma b2849 : Encl e2849 (128077804409 / 1000000000000 : ℝ) (128077804417 / 1000000000000 : ℝ) := by
  exact Encl.sub b2829 b2847 (by norm_num) (by norm_num)

def e2850 : ℝ := e2849 / e2834
lemma b2850 : Encl e2850 (81763080609 / 1000000000000 : ℝ) (16352616123 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2849 b2834 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2851 : ℝ := e2850 ^ 2
lemma b2851 : Encl e2851 (133704027 / 20000000000 : ℝ) (835650169 / 125000000000 : ℝ) := by
  exact Encl.pow b2850 (by norm_num) 2 (by norm_num) (by norm_num)

def e2852 : ℝ := e9 * e2851
lemma b2852 : Encl e2852 (935928189 / 500000000000 : ℝ) (1871856379 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2851 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2853 : ℝ := e2847 ^ 3
lemma b2853 : Encl e2853 (1113133731 / 250000000000 : ℝ) (178101397 / 40000000000 : ℝ) := by
  exact Encl.pow b2847 (by norm_num) 3 (by norm_num) (by norm_num)

def e2854 : ℝ := e2837 * e2853
lemma b2854 : Encl e2854 (400728143 / 250000000000 : ℝ) (1602912573 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2837 b2853 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2855 : ℝ := e2852 + e2854
lemma b2855 : Encl e2855 (69495379 / 20000000000 : ℝ) (434346119 / 125000000000 : ℝ) := by
  exact Encl.add b2852 b2854 (by norm_num) (by norm_num)

def e2856 : ℝ := min e2848 e2855
lemma b2856 : Encl e2856 (83349 / 25000000 : ℝ) (83349 / 25000000 : ℝ) := by
  exact Encl.min b2848 b2855 (by norm_num) (by norm_num)

def e2857 : ℝ := (3 / 2 : ℝ)
lemma b2857 : Encl e2857 (3 / 2 : ℝ) (3 / 2 : ℝ) := by
  exact Encl.exact (3 / 2 : ℝ)

def e2858 : ℝ := e2857 / e0
lemma b2858 : Encl e2858 (19098593171 / 40000000000 : ℝ) (119366207319 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2857 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2859 : ℝ := e8 * e2857
lemma b2859 : Encl e2859 (147 / 100 : ℝ) (147 / 100 : ℝ) := by
  exact Encl.mul_nonneg b8 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2860 : ℝ := e2859 / e0
lemma b2860 : Encl e2860 (46791553269 / 100000000000 : ℝ) (467915532691 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2859 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2861 : ℝ := e2857 ^ 2
lemma b2861 : Encl e2861 (9 / 4 : ℝ) (9 / 4 : ℝ) := by
  exact Encl.pow b2857 (by norm_num) 2 (by norm_num) (by norm_num)

def e2862 : ℝ := e17 * e2861
lemma b2862 : Encl e2862 (9 : ℝ) (9 : ℝ) := by
  exact Encl.mul_nonneg b17 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2863 : ℝ := e2862 / e0
lemma b2863 : Encl e2863 (1432394487827 / 500000000000 : ℝ) (572957795131 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b2862 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2864 : ℝ := e5 + e2863
lemma b2864 : Encl e2864 (1932394487827 / 500000000000 : ℝ) (772957795131 / 200000000000 : ℝ) := by
  exact Encl.add b5 b2863 (by norm_num) (by norm_num)

def e2865 : ℝ := Real.sqrt e2864
lemma b2865 : Encl e2865 (1965906654867 / 1000000000000 : ℝ) (1965906654869 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2864 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2866 : ℝ := e5 + e2865
lemma b2866 : Encl e2866 (2965906654867 / 1000000000000 : ℝ) (2965906654869 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2865 (by norm_num) (by norm_num)

def e2867 : ℝ := e23 / e2866
lemma b2867 : Encl e2867 (337165027887 / 500000000000 : ℝ) (21072814243 / 31250000000 : ℝ) := by
  exact Encl.div_nonneg b23 b2866 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2868 : ℝ := e9 * e2867
lemma b2868 : Encl e2868 (1475096997 / 7812500000 : ℝ) (94406207809 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2869 : ℝ := e2860 + e2868
lemma b2869 : Encl e2869 (328363974153 / 500000000000 : ℝ) (656727948309 / 1000000000000 : ℝ) := by
  exact Encl.add b2860 b2868 (by norm_num) (by norm_num)

def e2870 : ℝ := e2869 - e5
lemma b2870 : Encl e2870 (-171636025847 / 500000000000 : ℝ) (-343272051691 / 1000000000000 : ℝ) := by
  exact Encl.sub b2869 b5 (by norm_num) (by norm_num)

def e2871 : ℝ := e0 / e2861
lemma b2871 : Encl e2871 (279252680319 / 200000000000 : ℝ) (349065850399 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2872 : ℝ := e2858 ^ 2
lemma b2872 : Encl e2872 (113986331597 / 500000000000 : ℝ) (56993165799 / 250000000000 : ℝ) := by
  exact Encl.pow b2858 (by norm_num) 2 (by norm_num) (by norm_num)

def e2873 : ℝ := e5 - e2872
lemma b2873 : Encl e2873 (193006834201 / 250000000000 : ℝ) (386013668403 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b2872 (by norm_num) (by norm_num)

def e2874 : ℝ := Real.sqrt e2873
lemma b2874 : Encl e2874 (878650861721 / 1000000000000 : ℝ) (878650861723 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2873 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2875 : ℝ := e29 - e2874
lemma b2875 : Encl e2875 (-211984195057 / 1000000000000 : ℝ) (-105992097527 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b2874 (by norm_num) (by norm_num)

def e2876 : ℝ := e2874 ^ 3
lemma b2876 : Encl e2876 (339171242377 / 500000000000 : ℝ) (678342484759 / 1000000000000 : ℝ) := by
  exact Encl.pow b2874 (by norm_num) 3 (by norm_num) (by norm_num)

def e2877 : ℝ := e2876 / e35
lemma b2877 : Encl e2877 (14132135099 / 62500000000 : ℝ) (226114161587 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2876 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2878 : ℝ := e2875 + e2877
lemma b2878 : Encl e2878 (14129966527 / 1000000000000 : ℝ) (14129966533 / 1000000000000 : ℝ) := by
  exact Encl.add b2875 b2877 (by norm_num) (by norm_num)

def e2879 : ℝ := e8 * e2878
lemma b2879 : Encl e2879 (3461841799 / 250000000000 : ℝ) (13847367203 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b2878 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2880 : ℝ := e2872 / e2874
lemma b2880 : Encl e2880 (259457622049 / 1000000000000 : ℝ) (64864405513 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2872 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2881 : ℝ := e2880 - e23
lemma b2881 : Encl e2881 (-1740542377951 / 1000000000000 : ℝ) (-435135594487 / 250000000000 : ℝ) := by
  exact Encl.sub b2880 b23 (by norm_num) (by norm_num)

def e2882 : ℝ := e23 * e2874
lemma b2882 : Encl e2882 (878650861721 / 500000000000 : ℝ) (878650861723 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2883 : ℝ := e2881 + e2882
lemma b2883 : Encl e2883 (16759345491 / 1000000000000 : ℝ) (8379672749 / 500000000000 : ℝ) := by
  exact Encl.add b2881 b2882 (by norm_num) (by norm_num)

def e2884 : ℝ := e2883 / e43
lemma b2884 : Encl e2884 (335186909 / 1000000000000 : ℝ) (33518691 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2883 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2885 : ℝ := e2879 - e2884
lemma b2885 : Encl e2885 (6756090143 / 500000000000 : ℝ) (6756090147 / 500000000000 : ℝ) := by
  exact Encl.sub b2879 b2884 (by norm_num) (by norm_num)

def e2886 : ℝ := e2871 * e2885
lemma b2886 : Encl e2886 (18866562809 / 1000000000000 : ℝ) (18866562821 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2871 b2885 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2887 : ℝ := e2870 + e2886
lemma b2887 : Encl e2887 (-64881097777 / 200000000000 : ℝ) (-32440548887 / 100000000000 : ℝ) := by
  exact Encl.add b2870 b2886 (by norm_num) (by norm_num)

def e2888 : ℝ := e5 + e2874
lemma b2888 : Encl e2888 (1878650861721 / 1000000000000 : ℝ) (1878650861723 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2874 (by norm_num) (by norm_num)

def e2889 : ℝ := e2858 / e2888
lemma b2889 : Encl e2889 (31769130111 / 125000000000 : ℝ) (25415304089 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b2858 b2888 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2890 : ℝ := e2889 ^ 2
lemma b2890 : Encl e2890 (252319407 / 3906250000 : ℝ) (32296884097 / 500000000000 : ℝ) := by
  exact Encl.pow b2889 (by norm_num) 2 (by norm_num) (by norm_num)

def e2891 : ℝ := e5 + e2890
lemma b2891 : Encl e2891 (4158569407 / 3906250000 : ℝ) (532296884097 / 500000000000 : ℝ) := by
  exact Encl.add b5 b2890 (by norm_num) (by norm_num)

def e2892 : ℝ := Real.sqrt e2891
lemma b2892 : Encl e2892 (1031791533301 / 1000000000000 : ℝ) (1031791533303 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2893 : ℝ := e5 + e2892
lemma b2893 : Encl e2893 (2031791533301 / 1000000000000 : ℝ) (2031791533303 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2892 (by norm_num) (by norm_num)

def e2894 : ℝ := e2889 / e2893
lemma b2894 : Encl e2894 (5003525937 / 40000000000 : ℝ) (125088148427 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2889 b2893 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2895 : ℝ := Real.arcsin e2858
lemma b2895 : Encl e2895 (497767143601 / 1000000000000 : ℝ) (49776714361 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e2858) (a := (5003525937 / 40000000000 : ℝ)) (b := (125088148427 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (19098593171 / 40000000000 : ℝ) by norm_num).trans b2858.1
        exact b2858.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e2858) (5003525937 / 40000000000 : ℝ) (125088148427 / 1000000000000 : ℝ) from b2894) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e2896 : ℝ := e59 * e2895
lemma b2896 : Encl e2896 (63465310809 / 250000000000 : ℝ) (126930621621 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b2895 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2897 : ℝ := e61 * e2858
lemma b2897 : Encl e2897 (29244720793 / 125000000000 : ℝ) (116978883173 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b2858 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2898 : ℝ := e2897 * e2874
lemma b2898 : Encl e2898 (51391798251 / 250000000000 : ℝ) (205567193007 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2897 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2899 : ℝ := e2896 - e2898
lemma b2899 : Encl e2899 (48294050229 / 1000000000000 : ℝ) (24147025119 / 500000000000 : ℝ) := by
  exact Encl.sub b2896 b2898 (by norm_num) (by norm_num)

def e2900 : ℝ := e43 * e2874
lemma b2900 : Encl e2900 (878650861721 / 20000000000 : ℝ) (878650861723 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b2874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2901 : ℝ := e2858 / e2900
lemma b2901 : Encl e2901 (5434067729 / 500000000000 : ℝ) (10868135459 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2858 b2900 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2902 : ℝ := e2899 - e2901
lemma b2902 : Encl e2902 (3742591477 / 100000000000 : ℝ) (1871295739 / 50000000000 : ℝ) := by
  exact Encl.sub b2899 b2901 (by norm_num) (by norm_num)

def e2903 : ℝ := e183 - e2902
lemma b2903 : Encl e2903 (120681713683 / 250000000000 : ℝ) (482726854873 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b2902 (by norm_num) (by norm_num)

def e2904 : ℝ := e2903 / e2857
lemma b2904 : Encl e2904 (160908951577 / 500000000000 : ℝ) (321817903249 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2903 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2905 : ℝ := e2887 + e2904
lemma b2905 : Encl e2905 (-2587585731 / 1000000000000 : ℝ) (-2587585621 / 1000000000000 : ℝ) := by
  exact Encl.add b2887 b2904 (by norm_num) (by norm_num)

def e2906 : ℝ := e924 / e2857
lemma b2906 : Encl e2906 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.div_nonneg b924 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2907 : ℝ := min e7 e2906
lemma b2907 : Encl e2907 (16 / 25 : ℝ) (16 / 25 : ℝ) := by
  exact Encl.min b7 b2906 (by norm_num) (by norm_num)

def e2908 : ℝ := e2907 - e5
lemma b2908 : Encl e2908 (-9 / 25 : ℝ) (-9 / 25 : ℝ) := by
  exact Encl.sub b2907 b5 (by norm_num) (by norm_num)

def e2909 : ℝ := e23 * e2857
lemma b2909 : Encl e2909 (3 : ℝ) (3 : ℝ) := by
  exact Encl.mul_nonneg b23 b2857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2910 : ℝ := e2909 * e2867
lemma b2910 : Encl e2910 (1011495083661 / 500000000000 : ℝ) (63218442729 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b2909 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2911 : ℝ := e2910 / e0
lemma b2911 : Encl e2911 (643937769911 / 1000000000000 : ℝ) (321968884957 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b2910 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2912 : ℝ := e2908 + e2911
lemma b2912 : Encl e2912 (283937769911 / 1000000000000 : ℝ) (141968884957 / 500000000000 : ℝ) := by
  exact Encl.add b2908 b2911 (by norm_num) (by norm_num)

def e2913 : ℝ := e23 * e2861
lemma b2913 : Encl e2913 (9 / 2 : ℝ) (9 / 2 : ℝ) := by
  exact Encl.mul_nonneg b23 b2861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2914 : ℝ := e2913 * e2867
lemma b2914 : Encl e2914 (3034485250983 / 1000000000000 : ℝ) (189655328187 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2913 b2867 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2915 : ℝ := e0 + e2914
lemma b2915 : Encl e2915 (1544019476143 / 250000000000 : ℝ) (3088038952291 / 500000000000 : ℝ) := by
  exact Encl.add b0 b2914 (by norm_num) (by norm_num)

def e2916 : ℝ := Real.sqrt e2915
lemma b2916 : Encl e2916 (621292901163 / 250000000000 : ℝ) (497034320931 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2915 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2917 : ℝ := e932 * e2916
lemma b2917 : Encl e2917 (791054690623 / 500000000000 : ℝ) (1582109381251 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2916 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2918 : ℝ := e2857 ^ 3
lemma b2918 : Encl e2918 (27 / 8 : ℝ) (27 / 8 : ℝ) := by
  exact Encl.pow b2857 (by norm_num) 3 (by norm_num) (by norm_num)

def e2919 : ℝ := e939 * e2918
lemma b2919 : Encl e2919 (1809 / 4000 : ℝ) (1809 / 4000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2918 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2920 : ℝ := min e2919 e941
lemma b2920 : Encl e2920 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.min b2919 b941 (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
