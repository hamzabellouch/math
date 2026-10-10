import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases021
import OAI.Geometry.Borsuk.FiniteCases.Cases022
import OAI.Geometry.Borsuk.FiniteCases.Cases023
import OAI.Geometry.Borsuk.FiniteCases.Cases076

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31667 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → False := by
  classical
  intro n102 n108 n109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1842 h u0_121 n102 n108 n109

theorem c31668 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {4, 7, 8} → T {4, 7, 9} → False := by
  classical
  intro a102 a108 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1843 h u0_121 a102 a108 a109

theorem c31669 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {4, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n108 n109 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1844 h u0_121 n105 n108 n109

theorem c31670 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {4, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a108 a105 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1845 h u0_121 a105 a108 a109

theorem c31671 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n106 n108 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1846 h u0_121 n103 n106 n108

theorem c31672 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {4, 6, 8} → T {4, 5, 8} → False := by
  classical
  intro a108 a106 a103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1847 h u0_121 a103 a106 a108

theorem c31673 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 6, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n110 n106 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1848 h u0_121 n103 n106 n110

theorem c31675 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → ¬ T {4, 5, 8} → False := by
  classical
  intro n108 n110 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1850 h u0_121 n103 n108 n110

theorem c31677 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {4, 7, 8} → ¬ T {4, 8, 9} → False := by
  classical
  intro n106 n108 n110
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1852 h u0_121 n106 n108 n110

theorem c31678 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {4, 8, 9} → T {4, 6, 8} → False := by
  classical
  intro a108 a110 a106
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1853 h u0_121 a106 a108 a110

theorem c31680 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 9} → T {4, 6, 9} → T {4, 7, 9} → False := by
  classical
  intro a104 a107 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1855 h u0_121 a104 a107 a109

theorem c31681 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {4, 8, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n104 n110 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1856 h u0_121 n104 n107 n110

theorem c31683 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 5, 9} → ¬ T {4, 7, 9} → False := by
  classical
  intro n110 n104 n109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1858 h u0_121 n104 n109 n110

theorem c31685 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {4, 7, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n110 n109 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1860 h u0_121 n107 n109 n110

theorem c31690 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {5, 6, 9} → T {5, 6, 7} → False := by
  classical
  intro a101 a113 a111
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1865 h u0_121 a101 a111 a113

theorem c31691 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 9} → ¬ T {4, 5, 6} → ¬ T {5, 6, 8} → False := by
  classical
  intro n113 n101 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1866 h u0_121 n101 n112 n113

theorem c31692 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → T {5, 6, 8} → T {4, 5, 6} → False := by
  classical
  intro a113 a112 a101
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1867 h u0_121 a101 a112 a113

theorem c31693 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 7} → ¬ T {5, 6, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n111 n113 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1868 h u0_121 n111 n112 n113

theorem c31703 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 7, 8} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n114 n103 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1878 h u0_121 n103 n112 n114

theorem c31704 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 5, 8} → T {5, 7, 8} → False := by
  classical
  intro a112 a103 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1879 h u0_121 a103 a112 a114

theorem c31705 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {4, 5, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n116 n103 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1880 h u0_121 n103 n112 n116

theorem c31706 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {4, 5, 8} → T {5, 8, 9} → False := by
  classical
  intro a112 a103 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1881 h u0_121 a103 a112 a116

theorem c31707 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {4, 5, 8} → False := by
  classical
  intro n116 n114 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1882 h u0_121 n103 n114 n116

theorem c31708 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 8} → T {5, 8, 9} → T {4, 5, 8} → False := by
  classical
  intro a114 a116 a103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1883 h u0_121 a103 a114 a116

theorem c31709 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 8, 9} → ¬ T {5, 7, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n116 n114 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1884 h u0_121 n112 n114 n116

theorem c31710 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 8} → T {5, 7, 8} → T {5, 8, 9} → False := by
  classical
  intro a112 a114 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1885 h u0_121 a112 a114 a116

theorem c31711 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 9} → ¬ T {5, 7, 9} → ¬ T {4, 5, 9} → False := by
  classical
  intro n113 n115 n104
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1886 h u0_121 n104 n113 n115

theorem c31712 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 7, 9} → T {4, 5, 9} → T {5, 6, 9} → False := by
  classical
  intro a115 a104 a113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1887 h u0_121 a104 a113 a115

theorem c31714 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → T {4, 5, 9} → T {5, 8, 9} → False := by
  classical
  intro a113 a104 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1889 h u0_121 a104 a113 a116

theorem c31715 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {5, 7, 9} → ¬ T {5, 8, 9} → False := by
  classical
  intro n104 n115 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1890 h u0_121 n104 n115 n116

theorem c31718 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 9} → T {5, 7, 9} → T {5, 8, 9} → False := by
  classical
  intro a113 a115 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1893 h u0_121 a113 a115 a116

theorem c31720 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {5, 6, 7} → T {4, 6, 7} → False := by
  classical
  intro a117 a111 a105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1895 h u0_121 a105 a111 a117

theorem c31721 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 7} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n111 n105 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1896 h u0_121 n105 n111 n118

theorem c31722 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 7} → T {4, 6, 7} → T {6, 7, 9} → False := by
  classical
  intro a111 a105 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1897 h u0_121 a105 a111 a118

theorem c31723 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {4, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n117 n105 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1898 h u0_121 n105 n117 n118

theorem c31724 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 7, 8} → T {4, 6, 7} → T {6, 7, 9} → False := by
  classical
  intro a117 a105 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1899 h u0_121 a105 a117 a118

theorem c31725 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {5, 6, 7} → ¬ T {6, 7, 9} → False := by
  classical
  intro n117 n111 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1900 h u0_121 n111 n117 n118

theorem c31726 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {5, 6, 7} → T {6, 7, 8} → T {6, 7, 9} → False := by
  classical
  intro a111 a117 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1901 h u0_121 a111 a117 a118

theorem c31727 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {6, 7, 8} → ¬ T {5, 6, 8} → False := by
  classical
  intro n106 n117 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1902 h u0_121 n106 n112 n117

theorem c31731 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {4, 6, 8} → ¬ T {6, 7, 8} → False := by
  classical
  intro n119 n106 n117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1906 h u0_121 n106 n117 n119

theorem c31732 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 8} → T {6, 8, 9} → T {6, 7, 8} → False := by
  classical
  intro a106 a119 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1907 h u0_121 a106 a117 a119

theorem c31733 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 7, 8} → ¬ T {6, 8, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n117 n119 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1908 h u0_121 n112 n117 n119

theorem c31735 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {5, 6, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n113 n107 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1910 h u0_121 n107 n113 n118

theorem c31737 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {5, 6, 9} → ¬ T {4, 6, 9} → False := by
  classical
  intro n119 n113 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1912 h u0_121 n107 n113 n119

theorem c31738 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {6, 8, 9} → T {5, 6, 9} → T {4, 6, 9} → False := by
  classical
  intro a119 a113 a107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1913 h u0_121 a107 a113 a119

theorem c31739 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {4, 6, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n119 n107 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1914 h u0_121 n107 n118 n119

theorem c31741 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {6, 8, 9} → ¬ T {5, 6, 9} → ¬ T {6, 7, 9} → False := by
  classical
  intro n119 n113 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1916 h u0_121 n113 n118 n119

end BorsukNine.FiniteObstruction

end OAI
