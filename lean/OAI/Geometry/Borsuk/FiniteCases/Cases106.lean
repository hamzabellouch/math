import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases023
import OAI.Geometry.Borsuk.FiniteCases.Cases037
import OAI.Geometry.Borsuk.FiniteCases.Cases038
import OAI.Geometry.Borsuk.FiniteCases.Cases039
import OAI.Geometry.Borsuk.FiniteCases.Cases040
import OAI.Geometry.Borsuk.FiniteCases.Cases041
import OAI.Geometry.Borsuk.FiniteCases.Cases076

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31742 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 8, 9} → T {5, 6, 9} → T {6, 7, 9} → False := by
  classical
  intro a119 a113 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1917 h u0_121 a113 a118 a119

theorem c31744 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {4, 7, 8} → T {5, 7, 8} → False := by
  classical
  intro a117 a108 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1919 h u0_121 a108 a114 a117

theorem c31745 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {7, 8, 9} → ¬ T {5, 7, 8} → False := by
  classical
  intro n108 n120 n114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1920 h u0_121 n108 n114 n120

theorem c31747 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {7, 8, 9} → ¬ T {4, 7, 8} → False := by
  classical
  intro n117 n120 n108
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1922 h u0_121 n108 n117 n120

theorem c31748 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {7, 8, 9} → T {6, 7, 8} → False := by
  classical
  intro a108 a120 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1923 h u0_121 a108 a117 a120

theorem c31750 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {7, 8, 9} → T {5, 7, 8} → False := by
  classical
  intro a117 a120 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1925 h u0_121 a114 a117 a120

theorem c31751 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 9} → ¬ T {5, 7, 9} → ¬ T {4, 7, 9} → False := by
  classical
  intro n118 n115 n109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1926 h u0_121 n109 n115 n118

theorem c31752 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 9} → T {6, 7, 9} → T {4, 7, 9} → False := by
  classical
  intro a115 a118 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1927 h u0_121 a109 a115 a118

theorem c31755 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 9} → ¬ T {4, 7, 9} → ¬ T {7, 8, 9} → False := by
  classical
  intro n118 n109 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1930 h u0_121 n109 n118 n120

theorem c31756 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {7, 8, 9} → T {6, 7, 9} → T {4, 7, 9} → False := by
  classical
  intro a120 a118 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1931 h u0_121 a109 a118 a120

theorem c31757 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 9} → ¬ T {7, 8, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n115 n120 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1932 h u0_121 n115 n118 n120

theorem c31764 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {7, 8, 9} → T {4, 8, 9} → T {6, 8, 9} → False := by
  classical
  intro a120 a110 a119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1939 h u0_121 a110 a119 a120

theorem c31765 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {7, 8, 9} → ¬ T {5, 8, 9} → False := by
  classical
  intro n119 n120 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1940 h u0_121 n116 n119 n120

theorem c31767 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a185 a120
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10763 h a185 u0_37 a120

theorem c31769 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {0, 4, 5, 6} → T {1, 2, 9} → False := by
  classical
  intro a41 a185 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10785 h a185 u0_37 a41 a43

theorem c31777 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 7} → T {6, 8, 9} → False := by
  classical
  intro a186 a119
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10903 h a186 u0_37 a119

theorem c31779 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 7} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a186 a43 a40
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10925 h a186 u0_37 a40 a43

theorem c31785 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 7} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a186 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c10965 h a186 u0_37 a67 a70

theorem c31787 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {6, 7, 9} → False := by
  classical
  intro a187 a118
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11043 h a187 u0_37 a118

theorem c31789 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {1, 2, 6} → T {1, 2, 9} → False := by
  classical
  intro a187 a40 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11065 h a187 u0_37 a40 a43

theorem c31790 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 8} → T {1, 2, 7} → T {1, 2, 9} → False := by
  classical
  intro a187 a41 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11067 h a187 u0_37 a41 a43

theorem c31797 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a188 a117
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11183 h a188 u0_37 a117

theorem c31807 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a189 a116
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11323 h a189 u0_37 a116

theorem c31809 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {1, 2, 5} → T {1, 2, 9} → False := by
  classical
  intro a189 a39 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11345 h a189 u0_37 a39 a43

theorem c31810 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {1, 2, 8} → T {1, 2, 9} → False := by
  classical
  intro a189 a42 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11347 h a189 u0_37 a42 a43

theorem c31815 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {2, 3, 5} → T {2, 3, 9} → False := by
  classical
  intro a189 a66 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11385 h a189 u0_37 a66 a70

theorem c31816 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 7} → T {2, 3, 8} → T {2, 3, 9} → False := by
  classical
  intro a189 a69 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11387 h a189 u0_37 a69 a70

theorem c31817 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 6, 8} → T {5, 7, 9} → False := by
  classical
  intro a190 a115
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11463 h a190 u0_37 a115

theorem c31819 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a39 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11485 h a190 u0_37 a39 a43

theorem c31820 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → Q {0, 4, 6, 8} → T {1, 2, 9} → False := by
  classical
  intro a41 a190 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11487 h a190 u0_37 a41 a43

theorem c31837 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 8} → T {5, 6, 9} → False := by
  classical
  intro a192 a113
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11743 h a192 u0_37 a113

theorem c31840 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 8} → T {1, 2, 9} → T {1, 2, 6} → False := by
  classical
  intro a192 a43 a40
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11767 h a192 u0_37 a40 a43

theorem c31846 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 8} → T {2, 3, 6} → T {2, 3, 9} → False := by
  classical
  intro a192 a67 a70
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11807 h a192 u0_37 a67 a70

theorem c31847 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a193 a112
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11883 h a193 u0_37 a112

theorem c31848 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 5} → Q {0, 4, 7, 9} → T {1, 2, 6} → False := by
  classical
  intro a39 a193 a40
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11903 h a193 u0_37 a39 a40

theorem c31851 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {1, 3, 5} → T {1, 3, 6} → False := by
  classical
  intro a193 a45 a46
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11911 h a193 u0_37 a45 a46

theorem c31853 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 7, 9} → T {1, 3, 8} → T {1, 3, 6} → False := by
  classical
  intro a193 a48 a46
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c11915 h a193 u0_37 a46 a48

theorem c31857 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 4, 8, 9} → T {5, 6, 7} → False := by
  classical
  intro a194 a111
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12023 h a194 u0_37 a111

theorem c31869 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 7} → T {1, 2, 4} → T {1, 2, 9} → False := by
  classical
  intro a195 a38 a43
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12185 h a195 u0_37 a38 a43

theorem c31877 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 8} → T {4, 7, 9} → False := by
  classical
  intro a196 a109
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12303 h a196 u0_37 a109

theorem c31880 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 2, 7} → T {1, 2, 9} → Q {0, 5, 6, 8} → False := by
  classical
  intro a41 a43 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12327 h a196 u0_37 a41 a43

theorem c31881 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {1, 3, 4} → T {1, 3, 7} → Q {0, 5, 6, 8} → False := by
  classical
  intro a44 a47 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12331 h a196 u0_37 a44 a47

theorem c31884 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 4} → Q {0, 5, 6, 8} → T {2, 3, 7} → False := by
  classical
  intro a65 a196 a68
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12363 h a196 u0_37 a65 a68

theorem c31885 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 4} → T {2, 3, 9} → Q {0, 5, 6, 8} → False := by
  classical
  intro a65 a70 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12365 h a196 u0_37 a65 a70

theorem c31886 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {2, 3, 7} → T {2, 3, 9} → Q {0, 5, 6, 8} → False := by
  classical
  intro a68 a70 a196
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12367 h a196 u0_37 a68 a70

theorem c31887 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 6, 9} → T {4, 7, 8} → False := by
  classical
  intro a197 a108
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12443 h a197 u0_37 a108

theorem c31897 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 7, 8} → T {4, 6, 9} → False := by
  classical
  intro a198 a107
  have u0_37 : T {1, 2, 3} := by
    by_contra hv
    exact c31206 h h0 hv
  exact c12583 h a198 u0_37 a107

end BorsukNine.FiniteObstruction

end OAI
