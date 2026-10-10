import Mathlib
import OAI.Geometry.Borsuk.FiniteCases.Cases019
import OAI.Geometry.Borsuk.FiniteCases.Cases021
import OAI.Geometry.Borsuk.FiniteCases.Cases077

namespace OAI

open Set MeasureTheory
namespace BorsukNine.FiniteObstruction
attribute [local instance] Classical.propDecidable
variable {T Q : Family}

theorem c31601 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 5, 7, 9} → ¬ Q {3, 5, 7, 9} → ¬ Q {2, 5, 7, 9} → ¬ Q {0, 5, 7, 9} → False := by
  classical
  intro a255 n310 n290 n199
  have u0_320 : ¬ Q {4, 5, 7, 9} := by
    intro hv
    exact c31217 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1716 h a255 n199 n290 n310 u0_320 u1_327 u2_329

theorem c31604 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {0, 5, 8, 9} → ¬ Q {2, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → False := by
  classical
  intro a200 n291 n256 n311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1729 h a200 n256 n291 n311 u0_321 u1_328 u2_329

theorem c31606 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {3, 5, 8, 9} → False := by
  classical
  intro a291 n256 n200 n311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1733 h a291 n200 n256 n311 u0_321 u1_328 u2_329

theorem c31607 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 5, 8, 9} → ¬ Q {0, 5, 8, 9} → ¬ Q {1, 5, 8, 9} → Q {3, 5, 8, 9} → False := by
  classical
  intro n291 n200 n256 a311
  have u0_321 : ¬ Q {4, 5, 8, 9} := by
    intro hv
    exact c31216 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  exact c1735 h a311 n200 n256 n291 u0_321 u1_328 u2_329

theorem c31614 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {2, 6, 7, 9} → ¬ Q {0, 6, 7, 9} → ¬ Q {3, 6, 7, 9} → Q {1, 6, 7, 9} → False := by
  classical
  intro n293 n202 n313 a258
  have u0_323 : ¬ Q {4, 6, 7, 9} := by
    intro hv
    exact c31214 h h0 hv
  have u1_327 : ¬ Q {5, 6, 7, 9} := by
    intro hv
    exact c31210 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1761 h a258 n202 n293 n313 u0_323 u1_327 u2_330

theorem c31621 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {3, 6, 8, 9} → ¬ Q {1, 6, 8, 9} → ¬ Q {0, 6, 8, 9} → ¬ Q {2, 6, 8, 9} → False := by
  classical
  intro a314 n259 n203 n294
  have u0_324 : ¬ Q {4, 6, 8, 9} := by
    intro hv
    exact c31213 h h0 hv
  have u1_328 : ¬ Q {5, 6, 8, 9} := by
    intro hv
    exact c31209 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1780 h a314 n203 n259 n294 u0_324 u1_328 u2_330

theorem c31622 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ Q {1, 7, 8, 9} → T {7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → False := by
  classical
  intro n260 a120 n204 n315 n295
  have u0_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1787 h a120 n204 n260 n295 n315 u0_325 u1_329 u2_330

theorem c31624 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {1, 7, 8, 9} → ¬ Q {2, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → False := by
  classical
  intro a260 n295 n204 n315
  have u0_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1791 h a260 n204 n295 n315 u0_325 u1_329 u2_330

theorem c31625 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    Q {2, 7, 8, 9} → ¬ Q {3, 7, 8, 9} → ¬ Q {0, 7, 8, 9} → ¬ Q {1, 7, 8, 9} → False := by
  classical
  intro a295 n315 n204 n260
  have u0_325 : ¬ Q {4, 7, 8, 9} := by
    intro hv
    exact c31212 h h0 hv
  have u1_329 : ¬ Q {5, 7, 8, 9} := by
    intro hv
    exact c31208 h h0 hv
  have u2_330 : ¬ Q {6, 7, 8, 9} := by
    intro hv
    exact c31207 h h0 hv
  exact c1793 h a295 n204 n260 n315 u0_325 u1_329 u2_330

theorem c31627 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {7, 8, 9} → False := by
  classical
  intro n101 n120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1802 h u0_121 n101 n120

theorem c31628 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {7, 8, 9} → False := by
  classical
  intro a101 a120
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1803 h u0_121 a101 a120

theorem c31629 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {6, 8, 9} → False := by
  classical
  intro n102 n119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1804 h u0_121 n102 n119

theorem c31630 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {6, 8, 9} → False := by
  classical
  intro a102 a119
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1805 h u0_121 a102 a119

theorem c31631 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 8} → ¬ T {6, 7, 9} → False := by
  classical
  intro n103 n118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1806 h u0_121 n103 n118

theorem c31632 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 8} → T {6, 7, 9} → False := by
  classical
  intro a103 a118
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1807 h u0_121 a103 a118

theorem c31633 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {6, 7, 8} → False := by
  classical
  intro n104 n117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1808 h u0_121 n104 n117

theorem c31634 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 9} → T {6, 7, 8} → False := by
  classical
  intro a104 a117
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1809 h u0_121 a104 a117

theorem c31635 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 7} → ¬ T {5, 8, 9} → False := by
  classical
  intro n105 n116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1810 h u0_121 n105 n116

theorem c31636 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 7} → T {5, 8, 9} → False := by
  classical
  intro a105 a116
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1811 h u0_121 a105 a116

theorem c31637 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {5, 7, 9} → False := by
  classical
  intro n106 n115
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1812 h u0_121 n106 n115

theorem c31639 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 9} → ¬ T {5, 7, 8} → False := by
  classical
  intro n107 n114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1814 h u0_121 n107 n114

theorem c31640 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 9} → T {5, 7, 8} → False := by
  classical
  intro a107 a114
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1815 h u0_121 a107 a114

theorem c31641 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 8} → ¬ T {5, 6, 9} → False := by
  classical
  intro n108 n113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1816 h u0_121 n108 n113

theorem c31642 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 8} → T {5, 6, 9} → False := by
  classical
  intro a108 a113
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1817 h u0_121 a108 a113

theorem c31643 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 7, 9} → ¬ T {5, 6, 8} → False := by
  classical
  intro n109 n112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1818 h u0_121 n109 n112

theorem c31644 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 7, 9} → T {5, 6, 8} → False := by
  classical
  intro a109 a112
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1819 h u0_121 a109 a112

theorem c31645 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 8, 9} → ¬ T {5, 6, 7} → False := by
  classical
  intro n110 n111
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1820 h u0_121 n110 n111

theorem c31646 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 8, 9} → T {5, 6, 7} → False := by
  classical
  intro a110 a111
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1821 h u0_121 a110 a111

theorem c31647 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 5, 6} → ¬ T {4, 5, 8} → False := by
  classical
  intro n102 n101 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1822 h u0_121 n101 n102 n103

theorem c31649 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → False := by
  classical
  intro n101 n102 n104
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1824 h u0_121 n101 n102 n104

theorem c31651 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 9} → ¬ T {4, 5, 6} → ¬ T {4, 5, 8} → False := by
  classical
  intro n104 n101 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1826 h u0_121 n101 n103 n104

theorem c31653 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 5, 9} → ¬ T {4, 5, 8} → False := by
  classical
  intro n102 n104 n103
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1828 h u0_121 n102 n103 n104

theorem c31655 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {4, 6, 8} → ¬ T {4, 6, 7} → False := by
  classical
  intro n101 n106 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1830 h u0_121 n101 n105 n106

theorem c31657 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 6} → ¬ T {4, 6, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n101 n107 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1832 h u0_121 n101 n105 n107

theorem c31658 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {4, 6, 9} → T {4, 6, 7} → False := by
  classical
  intro a101 a107 a105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1833 h u0_121 a101 a105 a107

theorem c31659 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 6, 8} → ¬ T {4, 5, 6} → ¬ T {4, 6, 9} → False := by
  classical
  intro n106 n101 n107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1834 h u0_121 n101 n106 n107

theorem c31660 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 6} → T {4, 6, 8} → T {4, 6, 9} → False := by
  classical
  intro a101 a106 a107
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1835 h u0_121 a101 a106 a107

theorem c31662 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 6, 9} → T {4, 6, 8} → T {4, 6, 7} → False := by
  classical
  intro a107 a106 a105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1837 h u0_121 a105 a106 a107

theorem c31663 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 7, 8} → ¬ T {4, 6, 7} → False := by
  classical
  intro n102 n108 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1838 h u0_121 n102 n105 n108

theorem c31665 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    ¬ T {4, 5, 7} → ¬ T {4, 7, 9} → ¬ T {4, 6, 7} → False := by
  classical
  intro n102 n109 n105
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1840 h u0_121 n102 n105 n109

theorem c31666 (h : TenSystem T Q) (h0 : Q {0, 1, 2, 3}) :
    T {4, 5, 7} → T {4, 6, 7} → T {4, 7, 9} → False := by
  classical
  intro a102 a105 a109
  have u0_121 : Q {0, 1, 2, 3} := by
    by_contra hv
    exact c31202 h0 hv
  exact c1841 h u0_121 a102 a105 a109

end BorsukNine.FiniteObstruction

end OAI
