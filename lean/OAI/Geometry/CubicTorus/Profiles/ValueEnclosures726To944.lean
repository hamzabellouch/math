import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures508To725

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
lemma b725 : Encl e725 (279698541543 / 500000000000 : ℝ) (139849270773 / 250000000000 : ℝ) := by
  exact Encl.sqrt b724 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e726 : ℝ := e723 / e725
lemma b726 : Encl e726 (583961919909 / 1000000000000 : ℝ) (583961919927 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b723 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e727 : ℝ := e5 - e726
lemma b727 : Encl e727 (416038080073 / 1000000000000 : ℝ) (416038080091 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b726 (by norm_num) (by norm_num)

def e728 : ℝ := e8 * e662
lemma b728 : Encl e728 (437373250679 / 1000000000000 : ℝ) (437373250683 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b662 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e729 : ℝ := e5 - e728
lemma b729 : Encl e729 (562626749317 / 1000000000000 : ℝ) (562626749321 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b728 (by norm_num) (by norm_num)

def e730 : ℝ := e729 / e664
lemma b730 : Encl e730 (189026556697 / 250000000000 : ℝ) (756106226797 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b729 b664 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e731 : ℝ := e5 - e730
lemma b731 : Encl e731 (243893773203 / 1000000000000 : ℝ) (60973443303 / 250000000000 : ℝ) := by
  exact Encl.sub b5 b730 (by norm_num) (by norm_num)

def e732 : ℝ := e727 - e731
lemma b732 : Encl e732 (172144306861 / 1000000000000 : ℝ) (21518038361 / 125000000000 : ℝ) := by
  exact Encl.sub b727 b731 (by norm_num) (by norm_num)

def e733 : ℝ := e720 * e732
lemma b733 : Encl e733 (11038153131 / 1000000000000 : ℝ) (11038153141 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b720 b732 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e734 : ℝ := e718 - e708
lemma b734 : Encl e734 (68143828633 / 1000000000000 : ℝ) (17035957171 / 250000000000 : ℝ) := by
  exact Encl.sub b718 b708 (by norm_num) (by norm_num)

def e735 : ℝ := e5 + e725
lemma b735 : Encl e735 (779698541543 / 500000000000 : ℝ) (389849270773 / 250000000000 : ℝ) := by
  exact Encl.add b5 b725 (by norm_num) (by norm_num)

def e736 : ℝ := e699 / e735
lemma b736 : Encl e736 (531551472079 / 1000000000000 : ℝ) (531551472083 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b735 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e737 : ℝ := e736 ^ 2
lemma b737 : Encl e737 (282546967469 / 1000000000000 : ℝ) (141273483737 / 500000000000 : ℝ) := by
  exact Encl.pow b736 (by norm_num) 2 (by norm_num) (by norm_num)

def e738 : ℝ := e5 + e737
lemma b738 : Encl e738 (1282546967469 / 1000000000000 : ℝ) (641273483737 / 500000000000 : ℝ) := by
  exact Encl.add b5 b737 (by norm_num) (by norm_num)

def e739 : ℝ := Real.sqrt e738
lemma b739 : Encl e739 (70780993859 / 62500000000 : ℝ) (283123975437 / 250000000000 : ℝ) := by
  exact Encl.sqrt b738 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e740 : ℝ := e5 + e739
lemma b740 : Encl e740 (133280993859 / 62500000000 : ℝ) (533123975437 / 250000000000 : ℝ) := by
  exact Encl.add b5 b739 (by norm_num) (by norm_num)

def e741 : ℝ := e736 / e740
lemma b741 : Encl e741 (249262599587 / 1000000000000 : ℝ) (24926259959 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b736 b740 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e742 : ℝ := Real.arcsin e699
lemma b742 : Encl e742 (122142259441 / 125000000000 : ℝ) (48856903777 / 50000000000 : ℝ) := by
  apply Encl.arcsin (z := e699) (a := (249262599587 / 1000000000000 : ℝ)) (b := (24926259959 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (414449907537 / 500000000000 : ℝ) by norm_num).trans b699.1
        exact b699.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e699) (249262599587 / 1000000000000 : ℝ) (24926259959 / 100000000000 : ℝ) from b741) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e743 : ℝ := e59 * e742
lemma b743 : Encl e743 (498340418519 / 1000000000000 : ℝ) (249170209263 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b742 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e744 : ℝ := e61 * e699
lemma b744 : Encl e744 (203080454693 / 500000000000 : ℝ) (101540227347 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e745 : ℝ := e744 * e725
lemma b745 : Encl e745 (113602613987 / 500000000000 : ℝ) (113602613989 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b744 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e746 : ℝ := e743 - e745
lemma b746 : Encl e746 (271135190541 / 1000000000000 : ℝ) (33891898819 / 125000000000 : ℝ) := by
  exact Encl.sub b743 b745 (by norm_num) (by norm_num)

def e747 : ℝ := e43 * e725
lemma b747 : Encl e747 (279698541543 / 10000000000 : ℝ) (139849270773 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b725 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e748 : ℝ := e699 / e747
lemma b748 : Encl e748 (29635471479 / 1000000000000 : ℝ) (740886787 / 25000000000 : ℝ) := by
  exact Encl.div_nonneg b699 b747 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e749 : ℝ := e746 - e748
lemma b749 : Encl e749 (241499719061 / 1000000000000 : ℝ) (241499719073 / 1000000000000 : ℝ) := by
  exact Encl.sub b746 b748 (by norm_num) (by norm_num)

def e750 : ℝ := e749 - e679
lemma b750 : Encl e750 (6496282873 / 50000000000 : ℝ) (25985131497 / 200000000000 : ℝ) := by
  exact Encl.sub b749 b679 (by norm_num) (by norm_num)

def e751 : ℝ := e734 * e750
lemma b751 : Encl e751 (1106703967 / 125000000000 : ℝ) (4426815873 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b734 b750 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e752 : ℝ := e733 + e751
lemma b752 : Encl e752 (19891784867 / 1000000000000 : ℝ) (19891784887 / 1000000000000 : ℝ) := by
  exact Encl.add b733 b751 (by norm_num) (by norm_num)

def e753 : ℝ := e699 - e632
lemma b753 : Encl e753 (160843503533 / 1000000000000 : ℝ) (160843503537 / 1000000000000 : ℝ) := by
  exact Encl.sub b699 b632 (by norm_num) (by norm_num)

def e754 : ℝ := e752 / e753
lemma b754 : Encl e754 (123671671093 / 1000000000000 : ℝ) (61835835611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b752 b753 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e755 : ℝ := e697 + e754
lemma b755 : Encl e755 (-234481177789 / 1000000000000 : ℝ) (-234481177611 / 1000000000000 : ℝ) := by
  exact Encl.add b697 b754 (by norm_num) (by norm_num)

def e756 : ℝ := e4 * e718
lemma b756 : Encl e756 (742143134617 / 1000000000000 : ℝ) (742143134647 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b718 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e757 : ℝ := e4 / e8
lemma b757 : Encl e757 (504971080923 / 500000000000 : ℝ) (126242770231 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b8 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e758 : ℝ := e89 * e757
lemma b758 : Encl e758 (358015174791 / 200000000000 : ℝ) (44751896849 / 25000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b757 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e759 : ℝ := e757 ^ 2
lemma b759 : Encl e759 (509991585137 / 500000000000 : ℝ) (1019983170279 / 1000000000000 : ℝ) := by
  exact Encl.pow b757 (by norm_num) 2 (by norm_num) (by norm_num)

def e760 : ℝ := e91 * e759
lemma b760 : Encl e760 (801092908629 / 1000000000000 : ℝ) (400546454317 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b759 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e761 : ℝ := e5 + e760
lemma b761 : Encl e761 (1801092908629 / 1000000000000 : ℝ) (900546454317 / 500000000000 : ℝ) := by
  exact Encl.add b5 b760 (by norm_num) (by norm_num)

def e762 : ℝ := Real.sqrt e761
lemma b762 : Encl e762 (134204802769 / 100000000000 : ℝ) (1342048027693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b761 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e763 : ℝ := e758 * e762
lemma b763 : Encl e763 (300295974507 / 125000000000 : ℝ) (2402367796069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b758 b762 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e764 : ℝ := e97 * e759
lemma b764 : Encl e764 (801092908629 / 500000000000 : ℝ) (1602185817267 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b759 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e765 : ℝ := e763 - e764
lemma b765 : Encl e765 (800181978789 / 1000000000000 : ℝ) (800181978811 / 1000000000000 : ℝ) := by
  exact Encl.sub b763 b764 (by norm_num) (by norm_num)

def e766 : ℝ := e699 * e765
lemma b766 : Encl e766 (663270694243 / 1000000000000 : ℝ) (82908836783 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b699 b765 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e767 : ℝ := e756 - e766
lemma b767 : Encl e767 (78872440353 / 1000000000000 : ℝ) (19718110101 / 250000000000 : ℝ) := by
  exact Encl.sub b756 b766 (by norm_num) (by norm_num)

def e768 : ℝ := e165 - e727
lemma b768 : Encl e768 (75990479971 / 250000000000 : ℝ) (60792383991 / 200000000000 : ℝ) := by
  exact Encl.sub b165 b727 (by norm_num) (by norm_num)

def e769 : ℝ := e767 * e768
lemma b769 : Encl e769 (4794843679 / 200000000000 : ℝ) (23974218417 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b767 b768 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e770 : ℝ := e765 - e718
lemma b770 : Encl e770 (503480363 / 10000000000 : ℝ) (1006960727 / 20000000000 : ℝ) := by
  exact Encl.sub b765 b718 (by norm_num) (by norm_num)

def e771 : ℝ := e183 - e749
lemma b771 : Encl e771 (278653050439 / 1000000000000 : ℝ) (139326525291 / 500000000000 : ℝ) := by
  exact Encl.sub b183 b749 (by norm_num) (by norm_num)

def e772 : ℝ := e770 * e771
lemma b772 : Encl e772 (7014816949 / 500000000000 : ℝ) (21921303 / 1562500000 : ℝ) := by
  exact Encl.mul_nonneg b770 b771 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e773 : ℝ := e769 + e772
lemma b773 : Encl e773 (38003852293 / 1000000000000 : ℝ) (38003852337 / 1000000000000 : ℝ) := by
  exact Encl.add b769 b772 (by norm_num) (by norm_num)

def e774 : ℝ := e4 - e699
lemma b774 : Encl e774 (80421751767 / 500000000000 : ℝ) (160843503537 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b699 (by norm_num) (by norm_num)

def e775 : ℝ := e773 / e774
lemma b775 : Encl e775 (590696103 / 2500000000 : ℝ) (236278441479 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b773 b774 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e776 : ℝ := e755 + e775
lemma b776 : Encl e776 (1797263411 / 1000000000000 : ℝ) (449315967 / 250000000000 : ℝ) := by
  exact Encl.add b755 b775 (by norm_num) (by norm_num)

def e777 : ℝ := (51 / 50 : ℝ)
lemma b777 : Encl e777 (51 / 50 : ℝ) (51 / 50 : ℝ) := by
  exact Encl.exact (51 / 50 : ℝ)

def e778 : ℝ := e777 / e0
lemma b778 : Encl e778 (324676083907 / 1000000000000 : ℝ) (81169020977 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b777 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e779 : ℝ := e777 * e7
lemma b779 : Encl e779 (173830979023 / 250000000000 : ℝ) (347661958047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b777 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e780 : ℝ := e8 * e777
lemma b780 : Encl e780 (2499 / 2500 : ℝ) (2499 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e781 : ℝ := e780 / e0
lemma b781 : Encl e781 (318182562229 / 1000000000000 : ℝ) (31818256223 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b780 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e782 : ℝ := e777 ^ 2
lemma b782 : Encl e782 (2601 / 2500 : ℝ) (2601 / 2500 : ℝ) := by
  exact Encl.pow b777 (by norm_num) 2 (by norm_num) (by norm_num)

def e783 : ℝ := e17 * e782
lemma b783 : Encl e783 (2601 / 625 : ℝ) (2601 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e784 : ℝ := e783 / e0
lemma b784 : Encl e784 (662339211171 / 500000000000 : ℝ) (1324678422343 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b783 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e785 : ℝ := e5 + e784
lemma b785 : Encl e785 (1162339211171 / 500000000000 : ℝ) (2324678422343 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b784 (by norm_num) (by norm_num)

def e786 : ℝ := Real.sqrt e785
lemma b786 : Encl e786 (1524689615083 / 1000000000000 : ℝ) (381172403771 / 250000000000 : ℝ) := by
  exact Encl.sqrt b785 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e787 : ℝ := e5 + e786
lemma b787 : Encl e787 (2524689615083 / 1000000000000 : ℝ) (631172403771 / 250000000000 : ℝ) := by
  exact Encl.add b5 b786 (by norm_num) (by norm_num)

def e788 : ℝ := e23 / e787
lemma b788 : Encl e788 (158435317201 / 200000000000 : ℝ) (396088293003 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b787 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e789 : ℝ := e9 * e788
lemma b789 : Encl e789 (221809444081 / 1000000000000 : ℝ) (110904722041 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e790 : ℝ := e781 + e789
lemma b790 : Encl e790 (53999200631 / 100000000000 : ℝ) (67499000789 / 125000000000 : ℝ) := by
  exact Encl.add b781 b789 (by norm_num) (by norm_num)

def e791 : ℝ := e790 - e5
lemma b791 : Encl e791 (-46000799369 / 100000000000 : ℝ) (-57500999211 / 125000000000 : ℝ) := by
  exact Encl.sub b790 b5 (by norm_num) (by norm_num)

def e792 : ℝ := e0 / e782
lemma b792 : Encl e792 (3019600781997 / 1000000000000 : ℝ) (1509800390999 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e793 : ℝ := e778 ^ 2
lemma b793 : Encl e793 (105414559461 / 1000000000000 : ℝ) (52707279731 / 500000000000 : ℝ) := by
  exact Encl.pow b778 (by norm_num) 2 (by norm_num) (by norm_num)

def e794 : ℝ := e5 - e793
lemma b794 : Encl e794 (447292720269 / 500000000000 : ℝ) (894585440539 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b793 (by norm_num) (by norm_num)

def e795 : ℝ := Real.sqrt e794
lemma b795 : Encl e795 (945825269559 / 1000000000000 : ℝ) (945825269561 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b794 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e796 : ℝ := e29 - e795
lemma b796 : Encl e796 (-55831720579 / 200000000000 : ℝ) (-69789650723 / 250000000000 : ℝ) := by
  exact Encl.sub b29 b795 (by norm_num) (by norm_num)

def e797 : ℝ := e795 ^ 3
lemma b797 : Encl e797 (423060757719 / 500000000000 : ℝ) (169224303089 / 200000000000 : ℝ) := by
  exact Encl.pow b795 (by norm_num) 3 (by norm_num) (by norm_num)

def e798 : ℝ := e797 / e35
lemma b798 : Encl e798 (141020252573 / 500000000000 : ℝ) (282040505149 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b797 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e799 : ℝ := e796 + e798
lemma b799 : Encl e799 (2881902251 / 1000000000000 : ℝ) (2881902257 / 1000000000000 : ℝ) := by
  exact Encl.add b796 b798 (by norm_num) (by norm_num)

def e800 : ℝ := e8 * e799
lemma b800 : Encl e800 (564852841 / 200000000000 : ℝ) (706066053 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b799 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e801 : ℝ := e793 / e795
lemma b801 : Encl e801 (111452466807 / 1000000000000 : ℝ) (111452466809 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b793 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e802 : ℝ := e801 - e23
lemma b802 : Encl e802 (-1888547533193 / 1000000000000 : ℝ) (-1888547533191 / 1000000000000 : ℝ) := by
  exact Encl.sub b801 b23 (by norm_num) (by norm_num)

def e803 : ℝ := e23 * e795
lemma b803 : Encl e803 (945825269559 / 500000000000 : ℝ) (945825269561 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e804 : ℝ := e802 + e803
lemma b804 : Encl e804 (124120237 / 40000000000 : ℝ) (3103005931 / 1000000000000 : ℝ) := by
  exact Encl.add b802 b803 (by norm_num) (by norm_num)

def e805 : ℝ := e804 / e43
lemma b805 : Encl e805 (31030059 / 500000000000 : ℝ) (62060119 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b804 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e806 : ℝ := e800 - e805
lemma b806 : Encl e806 (1381102043 / 500000000000 : ℝ) (1381102047 / 500000000000 : ℝ) := by
  exact Encl.sub b800 b805 (by norm_num) (by norm_num)

def e807 : ℝ := e792 * e806
lemma b807 : Encl e807 (4170376809 / 500000000000 : ℝ) (8340753643 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b792 b806 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e808 : ℝ := e791 + e807
lemma b808 : Encl e808 (-56458405009 / 125000000000 : ℝ) (-90333448009 / 200000000000 : ℝ) := by
  exact Encl.add b791 b807 (by norm_num) (by norm_num)

def e809 : ℝ := e779 ^ 2
lemma b809 : Encl e809 (483475348289 / 1000000000000 : ℝ) (483475348293 / 1000000000000 : ℝ) := by
  exact Encl.pow b779 (by norm_num) 2 (by norm_num) (by norm_num)

def e810 : ℝ := e5 - e809
lemma b810 : Encl e810 (516524651707 / 1000000000000 : ℝ) (516524651711 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b809 (by norm_num) (by norm_num)

def e811 : ℝ := Real.sqrt e810
lemma b811 : Encl e811 (2807408183 / 3906250000 : ℝ) (718696494851 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b810 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e812 : ℝ := e5 + e811
lemma b812 : Encl e812 (6713658183 / 3906250000 : ℝ) (1718696494851 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b811 (by norm_num) (by norm_num)

def e813 : ℝ := e779 / e812
lemma b813 : Encl e813 (202282345421 / 500000000000 : ℝ) (80912938169 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b812 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e814 : ℝ := e813 ^ 2
lemma b814 : Encl e814 (40918147269 / 250000000000 : ℝ) (163672589079 / 1000000000000 : ℝ) := by
  exact Encl.pow b813 (by norm_num) 2 (by norm_num) (by norm_num)

def e815 : ℝ := e5 + e814
lemma b815 : Encl e815 (290918147269 / 250000000000 : ℝ) (1163672589079 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b814 (by norm_num) (by norm_num)

def e816 : ℝ := Real.sqrt e815
lemma b816 : Encl e816 (1078736570751 / 1000000000000 : ℝ) (1078736570753 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b815 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e817 : ℝ := e5 + e816
lemma b817 : Encl e817 (2078736570751 / 1000000000000 : ℝ) (2078736570753 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b816 (by norm_num) (by norm_num)

def e818 : ℝ := e813 / e817
lemma b818 : Encl e818 (194620471171 / 1000000000000 : ℝ) (97310235587 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b813 b817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e819 : ℝ := Real.arcsin e779
lemma b819 : Encl e819 (768870502009 / 1000000000000 : ℝ) (768870502021 / 1000000000000 : ℝ) := by
  apply Encl.arcsin (z := e779) (a := (194620471171 / 1000000000000 : ℝ)) (b := (97310235587 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (173830979023 / 250000000000 : ℝ) by norm_num).trans b779.1
        exact b779.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e779) (194620471171 / 1000000000000 : ℝ) (97310235587 / 500000000000 : ℝ) from b818) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e820 : ℝ := e59 * e819
lemma b820 : Encl e820 (49015494503 / 125000000000 : ℝ) (392123956031 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b819 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e821 : ℝ := e61 * e779
lemma b821 : Encl e821 (68141743777 / 200000000000 : ℝ) (340708718887 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b779 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e822 : ℝ := e821 * e811
lemma b822 : Encl e822 (122433081013 / 500000000000 : ℝ) (24486616203 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b821 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e823 : ℝ := e820 - e822
lemma b823 : Encl e823 (73628896997 / 500000000000 : ℝ) (29451558801 / 200000000000 : ℝ) := by
  exact Encl.sub b820 b822 (by norm_num) (by norm_num)

def e824 : ℝ := e43 * e811
lemma b824 : Encl e824 (2807408183 / 78125000 : ℝ) (718696494851 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e825 : ℝ := e779 / e824
lemma b825 : Encl e825 (4837396043 / 250000000000 : ℝ) (19349584173 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b824 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e826 : ℝ := e823 - e825
lemma b826 : Encl e826 (127908209821 / 1000000000000 : ℝ) (127908209833 / 1000000000000 : ℝ) := by
  exact Encl.sub b823 b825 (by norm_num) (by norm_num)

def e827 : ℝ := e5 + e795
lemma b827 : Encl e827 (1945825269559 / 1000000000000 : ℝ) (1945825269561 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b795 (by norm_num) (by norm_num)

def e828 : ℝ := e778 / e827
lemma b828 : Encl e828 (10428611223 / 62500000000 : ℝ) (16685777957 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b778 b827 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e829 : ℝ := e828 ^ 2
lemma b829 : Encl e829 (13920759301 / 500000000000 : ℝ) (6960379651 / 250000000000 : ℝ) := by
  exact Encl.pow b828 (by norm_num) 2 (by norm_num) (by norm_num)

def e830 : ℝ := e5 + e829
lemma b830 : Encl e830 (513920759301 / 500000000000 : ℝ) (256960379651 / 250000000000 : ℝ) := by
  exact Encl.add b5 b829 (by norm_num) (by norm_num)

def e831 : ℝ := Real.sqrt e830
lemma b831 : Encl e831 (1013825191343 / 1000000000000 : ℝ) (202765038269 / 200000000000 : ℝ) := by
  exact Encl.sqrt b830 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e832 : ℝ := e5 + e831
lemma b832 : Encl e832 (2013825191343 / 1000000000000 : ℝ) (402765038269 / 200000000000 : ℝ) := by
  exact Encl.add b5 b831 (by norm_num) (by norm_num)

def e833 : ℝ := e828 / e832
lemma b833 : Encl e833 (82856138797 / 1000000000000 : ℝ) (82856138799 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b828 b832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e834 : ℝ := Real.arcsin e778
lemma b834 : Encl e834 (330669238673 / 1000000000000 : ℝ) (165334619341 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e778) (a := (82856138797 / 1000000000000 : ℝ)) (b := (82856138799 / 1000000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (324676083907 / 1000000000000 : ℝ) by norm_num).trans b778.1
        exact b778.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e778) (82856138797 / 1000000000000 : ℝ) (82856138799 / 1000000000000 : ℝ) from b833) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e835 : ℝ := e59 * e834
lemma b835 : Encl e835 (168641311723 / 1000000000000 : ℝ) (10540081983 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b834 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e836 : ℝ := e61 * e778
lemma b836 : Encl e836 (79545640557 / 500000000000 : ℝ) (31818256223 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b778 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e837 : ℝ := e836 * e795
lemma b837 : Encl e837 (37618138461 / 250000000000 : ℝ) (75236276923 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b836 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e838 : ℝ := e835 - e837
lemma b838 : Encl e838 (18168757877 / 1000000000000 : ℝ) (4542189471 / 250000000000 : ℝ) := by
  exact Encl.sub b835 b837 (by norm_num) (by norm_num)

def e839 : ℝ := e43 * e795
lemma b839 : Encl e839 (945825269559 / 20000000000 : ℝ) (945825269561 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b795 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e840 : ℝ := e778 / e839
lemma b840 : Encl e840 (68654559 / 10000000000 : ℝ) (6865455901 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b778 b839 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e841 : ℝ := e838 - e840
lemma b841 : Encl e841 (1412912747 / 125000000000 : ℝ) (353228187 / 31250000000 : ℝ) := by
  exact Encl.sub b838 b840 (by norm_num) (by norm_num)

def e842 : ℝ := e826 - e841
lemma b842 : Encl e842 (116604907837 / 1000000000000 : ℝ) (116604907857 / 1000000000000 : ℝ) := by
  exact Encl.sub b826 b841 (by norm_num) (by norm_num)

def e843 : ℝ := e842 / e777
lemma b843 : Encl e843 (22863707419 / 200000000000 : ℝ) (22863707423 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b842 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e844 : ℝ := e808 + e843
lemma b844 : Encl e844 (-337348702977 / 1000000000000 : ℝ) (-33734870293 / 100000000000 : ℝ) := by
  exact Encl.add b808 b843 (by norm_num) (by norm_num)

def e845 : ℝ := e779 + e4
lemma b845 : Encl e845 (842533617351 / 500000000000 : ℝ) (337013446941 / 200000000000 : ℝ) := by
  exact Encl.add b779 b4 (by norm_num) (by norm_num)

def e846 : ℝ := e845 / e23
lemma b846 : Encl e846 (842533617351 / 1000000000000 : ℝ) (842533617353 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b845 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e847 : ℝ := e779 / e777
lemma b847 : Encl e847 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b779 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e848 : ℝ := e89 * e847
lemma b848 : Encl e848 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b847 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e849 : ℝ := e847 ^ 2
lemma b849 : Encl e849 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b847 (by norm_num) 2 (by norm_num) (by norm_num)

def e850 : ℝ := e91 * e849
lemma b850 : Encl e850 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e851 : ℝ := e5 + e850
lemma b851 : Encl e851 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b850 (by norm_num) (by norm_num)

def e852 : ℝ := Real.sqrt e851
lemma b852 : Encl e852 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b851 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e853 : ℝ := e848 * e852
lemma b853 : Encl e853 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b848 b852 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e854 : ℝ := e97 * e849
lemma b854 : Encl e854 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e855 : ℝ := e853 - e854
lemma b855 : Encl e855 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b853 b854 (by norm_num) (by norm_num)

def e856 : ℝ := e846 * e855
lemma b856 : Encl e856 (71793354687 / 125000000000 : ℝ) (287173418759 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b846 b855 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e857 : ℝ := e846 / e777
lemma b857 : Encl e857 (103251668793 / 125000000000 : ℝ) (826013350347 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e858 : ℝ := e89 * e857
lemma b858 : Encl e858 (366017635929 / 250000000000 : ℝ) (1464070543723 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b857 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e859 : ℝ := e857 ^ 2
lemma b859 : Encl e859 (341149027473 / 500000000000 : ℝ) (85287256869 / 125000000000 : ℝ) := by
  exact Encl.pow b857 (by norm_num) 2 (by norm_num) (by norm_num)

def e860 : ℝ := e91 * e859
lemma b860 : Encl e860 (535875639243 / 1000000000000 : ℝ) (2143502557 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b859 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e861 : ℝ := e5 + e860
lemma b861 : Encl e861 (1535875639243 / 1000000000000 : ℝ) (6143502557 / 4000000000 : ℝ) := by
  exact Encl.add b5 b860 (by norm_num) (by norm_num)

def e862 : ℝ := Real.sqrt e861
lemma b862 : Encl e862 (1239304498193 / 1000000000000 : ℝ) (1239304498197 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b861 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e863 : ℝ := e858 * e862
lemma b863 : Encl e863 (1814429210499 / 1000000000000 : ℝ) (907214605257 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b858 b862 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e864 : ℝ := e97 * e859
lemma b864 : Encl e864 (1071751278487 / 1000000000000 : ℝ) (535875639249 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b859 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e865 : ℝ := e863 - e864
lemma b865 : Encl e865 (742677932001 / 1000000000000 : ℝ) (742677932027 / 1000000000000 : ℝ) := by
  exact Encl.sub b863 b864 (by norm_num) (by norm_num)

def e866 : ℝ := e779 * e865
lemma b866 : Encl e866 (258200864037 / 500000000000 : ℝ) (258200864047 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b779 b865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e867 : ℝ := e856 - e866
lemma b867 : Encl e867 (28972554701 / 500000000000 : ℝ) (14486277361 / 250000000000 : ℝ) := by
  exact Encl.sub b856 b866 (by norm_num) (by norm_num)

def e868 : ℝ := e846 ^ 2
lemma b868 : Encl e868 (354931448183 / 500000000000 : ℝ) (70986289637 / 100000000000 : ℝ) := by
  exact Encl.pow b846 (by norm_num) 2 (by norm_num) (by norm_num)

def e869 : ℝ := e8 * e868
lemma b869 : Encl e869 (347832819219 / 500000000000 : ℝ) (695665638443 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b868 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e870 : ℝ := e5 - e869
lemma b870 : Encl e870 (304334361557 / 1000000000000 : ℝ) (152167180781 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b869 (by norm_num) (by norm_num)

def e871 : ℝ := e5 - e868
lemma b871 : Encl e871 (29013710363 / 100000000000 : ℝ) (145068551817 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b868 (by norm_num) (by norm_num)

def e872 : ℝ := Real.sqrt e871
lemma b872 : Encl e872 (134660940799 / 250000000000 : ℝ) (5260193 / 9765625 : ℝ) := by
  exact Encl.sqrt b871 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e873 : ℝ := e870 / e872
lemma b873 : Encl e873 (282500589767 / 500000000000 : ℝ) (565001179549 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b870 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e874 : ℝ := e5 - e873
lemma b874 : Encl e874 (434998820451 / 1000000000000 : ℝ) (217499410233 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b873 (by norm_num) (by norm_num)

def e875 : ℝ := e8 * e809
lemma b875 : Encl e875 (473805841323 / 1000000000000 : ℝ) (29612865083 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b809 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e876 : ℝ := e5 - e875
lemma b876 : Encl e876 (32887134917 / 62500000000 : ℝ) (526194158677 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b875 (by norm_num) (by norm_num)

def e877 : ℝ := e876 / e811
lemma b877 : Encl e877 (146430144697 / 200000000000 : ℝ) (91518840437 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b876 b811 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e878 : ℝ := e5 - e877
lemma b878 : Encl e878 (33481159563 / 125000000000 : ℝ) (53569855303 / 200000000000 : ℝ) := by
  exact Encl.sub b5 b877 (by norm_num) (by norm_num)

def e879 : ℝ := e874 - e878
lemma b879 : Encl e879 (326463953 / 1953125000 : ℝ) (83574771981 / 500000000000 : ℝ) := by
  exact Encl.sub b874 b878 (by norm_num) (by norm_num)

def e880 : ℝ := e867 * e879
lemma b880 : Encl e880 (9685498609 / 1000000000000 : ℝ) (9685498619 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b867 b879 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e881 : ℝ := e865 - e855
lemma b881 : Encl e881 (60987818173 / 1000000000000 : ℝ) (30493909111 / 500000000000 : ℝ) := by
  exact Encl.sub b865 b855 (by norm_num) (by norm_num)

def e882 : ℝ := e5 + e872
lemma b882 : Encl e882 (384660940799 / 250000000000 : ℝ) (15025818 / 9765625 : ℝ) := by
  exact Encl.add b5 b872 (by norm_num) (by norm_num)

def e883 : ℝ := e846 / e882
lemma b883 : Encl e883 (547581992337 / 1000000000000 : ℝ) (547581992341 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b882 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e884 : ℝ := e883 ^ 2
lemma b884 : Encl e884 (299846038331 / 1000000000000 : ℝ) (299846038337 / 1000000000000 : ℝ) := by
  exact Encl.pow b883 (by norm_num) 2 (by norm_num) (by norm_num)

def e885 : ℝ := e5 + e884
lemma b885 : Encl e885 (1299846038331 / 1000000000000 : ℝ) (1299846038337 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b884 (by norm_num) (by norm_num)

def e886 : ℝ := Real.sqrt e885
lemma b886 : Encl e886 (1140107906441 / 1000000000000 : ℝ) (228021581289 / 200000000000 : ℝ) := by
  exact Encl.sqrt b885 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e887 : ℝ := e5 + e886
lemma b887 : Encl e887 (2140107906441 / 1000000000000 : ℝ) (428021581289 / 200000000000 : ℝ) := by
  exact Encl.add b5 b886 (by norm_num) (by norm_num)

def e888 : ℝ := e883 / e887
lemma b888 : Encl e888 (127933266983 / 500000000000 : ℝ) (25586653397 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b883 b887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e889 : ℝ := Real.arcsin e846
lemma b889 : Encl e889 (500984879807 / 500000000000 : ℝ) (100196975963 / 100000000000 : ℝ) := by
  apply Encl.arcsin (z := e846) (a := (127933266983 / 500000000000 : ℝ)) (b := (25586653397 / 100000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (842533617351 / 1000000000000 : ℝ) by norm_num).trans b846.1
        exact b846.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e846) (127933266983 / 500000000000 : ℝ) (25586653397 / 100000000000 : ℝ) from b888) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e890 : ℝ := e59 * e889
lemma b890 : Encl e890 (511004577403 / 1000000000000 : ℝ) (127751144353 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b889 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e891 : ℝ := e61 * e846
lemma b891 : Encl e891 (412841472501 / 1000000000000 : ℝ) (412841472503 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e892 : ℝ := e891 * e872
lemma b892 : Encl e892 (222374484351 / 1000000000000 : ℝ) (44474896871 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b891 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e893 : ℝ := e890 - e892
lemma b893 : Encl e893 (36078761631 / 125000000000 : ℝ) (288630093061 / 1000000000000 : ℝ) := by
  exact Encl.sub b890 b892 (by norm_num) (by norm_num)

def e894 : ℝ := e43 * e872
lemma b894 : Encl e894 (134660940799 / 5000000000 : ℝ) (10520386 / 390625 : ℝ) := by
  exact Encl.mul_nonneg b43 b872 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e895 : ℝ := e846 / e894
lemma b895 : Encl e895 (31283518901 / 1000000000000 : ℝ) (15641759451 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b846 b894 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e896 : ℝ := e893 - e895
lemma b896 : Encl e896 (128673287073 / 500000000000 : ℝ) (3216832177 / 12500000000 : ℝ) := by
  exact Encl.sub b893 b895 (by norm_num) (by norm_num)

def e897 : ℝ := e896 - e826
lemma b897 : Encl e897 (129438364313 / 1000000000000 : ℝ) (129438364339 / 1000000000000 : ℝ) := by
  exact Encl.sub b896 b826 (by norm_num) (by norm_num)

def e898 : ℝ := e881 * e897
lemma b898 : Encl e898 (7894163427 / 1000000000000 : ℝ) (1973540859 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b881 b897 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e899 : ℝ := e880 + e898
lemma b899 : Encl e899 (4394915509 / 250000000000 : ℝ) (3515932411 / 200000000000 : ℝ) := by
  exact Encl.add b880 b898 (by norm_num) (by norm_num)

def e900 : ℝ := e846 - e779
lemma b900 : Encl e900 (147209701257 / 1000000000000 : ℝ) (147209701261 / 1000000000000 : ℝ) := by
  exact Encl.sub b846 b779 (by norm_num) (by norm_num)

def e901 : ℝ := e899 / e900
lemma b901 : Encl e901 (119419181517 / 1000000000000 : ℝ) (2388383633 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b899 b900 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e902 : ℝ := e844 + e901
lemma b902 : Encl e902 (-10896476073 / 50000000000 : ℝ) (-340514877 / 1562500000 : ℝ) := by
  exact Encl.add b844 b901 (by norm_num) (by norm_num)

def e903 : ℝ := e4 * e865
lemma b903 : Encl e903 (735060521077 / 1000000000000 : ℝ) (45941282569 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e904 : ℝ := e4 / e777
lemma b904 : Encl e904 (121292073359 / 125000000000 : ℝ) (485168293437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e905 : ℝ := e89 * e904
lemma b905 : Encl e905 (68795072803 / 40000000000 : ℝ) (21498460251 / 12500000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b904 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e906 : ℝ := e904 ^ 2
lemma b906 : Encl e906 (470776545911 / 500000000000 : ℝ) (941553091827 / 1000000000000 : ℝ) := by
  exact Encl.pow b904 (by norm_num) 2 (by norm_num) (by norm_num)

def e907 : ℝ := e91 * e906
lemma b907 : Encl e907 (739494069057 / 1000000000000 : ℝ) (739494069063 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b906 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e908 : ℝ := e5 + e907
lemma b908 : Encl e908 (1739494069057 / 1000000000000 : ℝ) (1739494069063 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b907 (by norm_num) (by norm_num)

def e909 : ℝ := Real.sqrt e908
lemma b909 : Encl e909 (164862351157 / 125000000000 : ℝ) (1318898809259 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b908 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e910 : ℝ := e905 * e909
lemma b910 : Encl e910 (2268343490063 / 1000000000000 : ℝ) (567085872519 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b905 b909 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e911 : ℝ := e97 * e906
lemma b911 : Encl e911 (295797627623 / 200000000000 : ℝ) (2366381021 / 1600000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b906 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e912 : ℝ := e910 - e911
lemma b912 : Encl e912 (394677675969 / 500000000000 : ℝ) (789355351961 / 1000000000000 : ℝ) := by
  exact Encl.sub b910 b911 (by norm_num) (by norm_num)

def e913 : ℝ := e846 * e912
lemma b913 : Encl e913 (665058420043 / 1000000000000 : ℝ) (133011684013 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b846 b912 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e914 : ℝ := e903 - e913
lemma b914 : Encl e914 (17500525253 / 250000000000 : ℝ) (70002101061 / 1000000000000 : ℝ) := by
  exact Encl.sub b903 b913 (by norm_num) (by norm_num)

def e915 : ℝ := e165 - e874
lemma b915 : Encl e915 (285001179509 / 1000000000000 : ℝ) (285001179577 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b874 (by norm_num) (by norm_num)

def e916 : ℝ := e914 * e915
lemma b916 : Encl e916 (4987670339 / 250000000000 : ℝ) (623458793 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b914 b915 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e917 : ℝ := e912 - e865
lemma b917 : Encl e917 (46677419911 / 1000000000000 : ℝ) (1166935499 / 25000000000 : ℝ) := by
  exact Encl.sub b912 b865 (by norm_num) (by norm_num)

def e918 : ℝ := e183 - e896
lemma b918 : Encl e918 (32850774419 / 125000000000 : ℝ) (262806195497 / 1000000000000 : ℝ) := by
  exact Encl.sub b183 b896 (by norm_num) (by norm_num)

def e919 : ℝ := e917 * e918
lemma b919 : Encl e919 (2453423027 / 200000000000 : ℝ) (3066778789 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b917 b918 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e920 : ℝ := e916 + e919
lemma b920 : Encl e920 (32217796491 / 1000000000000 : ℝ) (8054449133 / 250000000000 : ℝ) := by
  exact Encl.add b916 b919 (by norm_num) (by norm_num)

def e921 : ℝ := e4 - e846
lemma b921 : Encl e921 (147209701257 / 1000000000000 : ℝ) (7360485063 / 50000000000 : ℝ) := by
  exact Encl.sub b4 b846 (by norm_num) (by norm_num)

def e922 : ℝ := e920 / e921
lemma b922 : Encl e922 (218856476273 / 1000000000000 : ℝ) (218856476557 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b920 b921 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e923 : ℝ := e902 + e922
lemma b923 : Encl e923 (926954813 / 1000000000000 : ℝ) (926955277 / 1000000000000 : ℝ) := by
  exact Encl.add b902 b922 (by norm_num) (by norm_num)

def e924 : ℝ := (24 / 25 : ℝ)
lemma b924 : Encl e924 (24 / 25 : ℝ) (24 / 25 : ℝ) := by
  exact Encl.exact (24 / 25 : ℝ)

def e925 : ℝ := e924 / e777
lemma b925 : Encl e925 (235294117647 / 250000000000 : ℝ) (941176470589 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e926 : ℝ := min e7 e925
lemma b926 : Encl e926 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b925 (by norm_num) (by norm_num)

def e927 : ℝ := e926 - e5
lemma b927 : Encl e927 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b926 b5 (by norm_num) (by norm_num)

def e928 : ℝ := e23 * e777
lemma b928 : Encl e928 (51 / 25 : ℝ) (51 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b777 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e929 : ℝ := e928 * e788
lemma b929 : Encl e929 (32320804709 / 20000000000 : ℝ) (1616040235453 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b928 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e930 : ℝ := e929 / e0
lemma b930 : Encl e930 (257200791707 / 500000000000 : ℝ) (64300197927 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b929 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e931 : ℝ := e927 + e930
lemma b931 : Encl e931 (19609169723 / 100000000000 : ℝ) (196091697233 / 1000000000000 : ℝ) := by
  exact Encl.add b927 b930 (by norm_num) (by norm_num)

def e932 : ℝ := e23 / e0
lemma b932 : Encl e932 (636619772367 / 1000000000000 : ℝ) (39788735773 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b23 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e933 : ℝ := e23 * e782
lemma b933 : Encl e933 (2601 / 1250 : ℝ) (2601 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b782 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e934 : ℝ := e933 * e788
lemma b934 : Encl e934 (1648361040159 / 1000000000000 : ℝ) (824180520081 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b933 b788 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e935 : ℝ := e0 + e934
lemma b935 : Encl e935 (1197488423437 / 250000000000 : ℝ) (598744211719 / 125000000000 : ℝ) := by
  exact Encl.add b0 b934 (by norm_num) (by norm_num)

def e936 : ℝ := Real.sqrt e935
lemma b936 : Encl e936 (437719256773 / 200000000000 : ℝ) (1094298141933 / 500000000000 : ℝ) := by
  exact Encl.sqrt b935 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e937 : ℝ := e932 * e936
lemma b937 : Encl e937 (1393303668037 / 1000000000000 : ℝ) (1393303668041 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b936 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e938 : ℝ := e777 ^ 3
lemma b938 : Encl e938 (132651 / 125000 : ℝ) (132651 / 125000 : ℝ) := by
  exact Encl.pow b777 (by norm_num) 3 (by norm_num) (by norm_num)

def e939 : ℝ := (67 / 500 : ℝ)
lemma b939 : Encl e939 (67 / 500 : ℝ) (67 / 500 : ℝ) := by
  exact Encl.exact (67 / 500 : ℝ)

def e940 : ℝ := e939 * e938
lemma b940 : Encl e940 (8887617 / 62500000 : ℝ) (8887617 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b938 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e941 : ℝ := (9 / 25 : ℝ)
lemma b941 : Encl e941 (9 / 25 : ℝ) (9 / 25 : ℝ) := by
  exact Encl.exact (9 / 25 : ℝ)

def e942 : ℝ := min e940 e941
lemma b942 : Encl e942 (8887617 / 62500000 : ℝ) (8887617 / 62500000 : ℝ) := by
  exact Encl.min b940 b941 (by norm_num) (by norm_num)

def e943 : ℝ := e23 * e931
lemma b943 : Encl e943 (19609169723 / 50000000000 : ℝ) (196091697233 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e944 : ℝ := (6 : ℝ)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
