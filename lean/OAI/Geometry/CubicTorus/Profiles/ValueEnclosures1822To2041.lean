import Mathlib
import OAI.Geometry.CubicTorus.Profiles.ValueEnclosures1603To1821

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
lemma b1821 : Encl e1821 (177099635389 / 100000000000 : ℝ) (1770996353899 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1816 b1820 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1822 : ℝ := e97 * e1817
lemma b1822 : Encl e1822 (516910527713 / 500000000000 : ℝ) (1033821055431 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1817 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1823 : ℝ := e1821 - e1822
lemma b1823 : Encl e1823 (737175298459 / 1000000000000 : ℝ) (737175298473 / 1000000000000 : ℝ) := by
  exact Encl.sub b1821 b1822 (by norm_num) (by norm_num)

def e1824 : ℝ := e1757 * e1823
lemma b1824 : Encl e1824 (335673741071 / 500000000000 : ℝ) (335673741079 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1757 b1823 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1825 : ℝ := e1814 - e1824
lemma b1825 : Encl e1825 (812106609 / 25000000000 : ℝ) (8121066101 / 250000000000 : ℝ) := by
  exact Encl.sub b1814 b1824 (by norm_num) (by norm_num)

def e1826 : ℝ := e165 - e1785
lemma b1826 : Encl e1826 (21652521253 / 125000000000 : ℝ) (173220170101 / 1000000000000 : ℝ) := by
  exact Encl.sub b165 b1785 (by norm_num) (by norm_num)

def e1827 : ℝ := e1825 * e1826
lemma b1827 : Encl e1827 (1125385959 / 200000000000 : ℝ) (2813464903 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1825 b1826 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1828 : ℝ := e1823 - e1776
lemma b1828 : Encl e1828 (13024881939 / 500000000000 : ℝ) (13024881959 / 500000000000 : ℝ) := by
  exact Encl.sub b1823 b1776 (by norm_num) (by norm_num)

def e1829 : ℝ := e183 - e1807
lemma b1829 : Encl e1829 (41158491389 / 250000000000 : ℝ) (20579245713 / 125000000000 : ℝ) := by
  exact Encl.sub b183 b1807 (by norm_num) (by norm_num)

def e1830 : ℝ := e1828 * e1829
lemma b1830 : Encl e1830 (4288675929 / 1000000000000 : ℝ) (214433797 / 50000000000 : ℝ) := by
  exact Encl.mul_nonneg b1828 b1829 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1831 : ℝ := e1827 + e1830
lemma b1831 : Encl e1831 (2478901431 / 250000000000 : ℝ) (4957802873 / 500000000000 : ℝ) := by
  exact Encl.add b1827 b1830 (by norm_num) (by norm_num)

def e1832 : ℝ := e4 - e1757
lemma b1832 : Encl e1832 (19760172469 / 250000000000 : ℝ) (79040689879 / 1000000000000 : ℝ) := by
  exact Encl.sub b4 b1757 (by norm_num) (by norm_num)

def e1833 : ℝ := e1831 / e1832
lemma b1833 : Encl e1833 (62724691163 / 500000000000 : ℝ) (12544938261 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1831 b1832 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1834 : ℝ := e1813 + e1833
lemma b1834 : Encl e1834 (-1602774927 / 1000000000000 : ℝ) (-400693599 / 250000000000 : ℝ) := by
  exact Encl.add b1813 b1833 (by norm_num) (by norm_num)

def e1835 : ℝ := e924 / e1688
lemma b1835 : Encl e1835 (786885245901 / 1000000000000 : ℝ) (393442622951 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1836 : ℝ := min e7 e1835
lemma b1836 : Encl e1836 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b1835 (by norm_num) (by norm_num)

def e1837 : ℝ := e1836 - e5
lemma b1837 : Encl e1837 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b1836 b5 (by norm_num) (by norm_num)

def e1838 : ℝ := e23 * e1688
lemma b1838 : Encl e1838 (61 / 25 : ℝ) (61 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1688 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1839 : ℝ := e1838 * e1699
lemma b1839 : Encl e1839 (1806406308167 / 1000000000000 : ℝ) (180640630817 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1838 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1840 : ℝ := e1839 / e0
lemma b1840 : Encl e1840 (287498493177 / 500000000000 : ℝ) (143749246589 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1839 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1841 : ℝ := e1837 + e1840
lemma b1841 : Encl e1841 (25668710017 / 100000000000 : ℝ) (256687100173 / 1000000000000 : ℝ) := by
  exact Encl.add b1837 b1840 (by norm_num) (by norm_num)

def e1842 : ℝ := e23 * e1693
lemma b1842 : Encl e1842 (3721 / 1250 : ℝ) (3721 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1693 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1843 : ℝ := e1842 * e1699
lemma b1843 : Encl e1843 (550953923991 / 250000000000 : ℝ) (68869240499 / 31250000000 : ℝ) := by
  exact Encl.mul_nonneg b1842 b1699 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1844 : ℝ := e0 + e1843
lemma b1844 : Encl e1844 (5345408349553 / 1000000000000 : ℝ) (2672704174779 / 500000000000 : ℝ) := by
  exact Encl.add b0 b1843 (by norm_num) (by norm_num)

def e1845 : ℝ := Real.sqrt e1844
lemma b1845 : Encl e1845 (2312013916383 / 1000000000000 : ℝ) (1156006958193 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1844 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1846 : ℝ := e932 * e1845
lemma b1846 : Encl e1846 (1471873773157 / 1000000000000 : ℝ) (735936886581 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b1845 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1847 : ℝ := e1688 ^ 3
lemma b1847 : Encl e1847 (226981 / 125000 : ℝ) (226981 / 125000 : ℝ) := by
  exact Encl.pow b1688 (by norm_num) 3 (by norm_num) (by norm_num)

def e1848 : ℝ := e939 * e1847
lemma b1848 : Encl e1848 (15207727 / 62500000 : ℝ) (15207727 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b1847 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1849 : ℝ := min e1848 e941
lemma b1849 : Encl e1849 (15207727 / 62500000 : ℝ) (15207727 / 62500000 : ℝ) := by
  exact Encl.min b1848 b941 (by norm_num) (by norm_num)

def e1850 : ℝ := e23 * e1841
lemma b1850 : Encl e1850 (25668710017 / 50000000000 : ℝ) (256687100173 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1841 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1851 : ℝ := e944 * e1849
lemma b1851 : Encl e1851 (45623181 / 31250000 : ℝ) (45623181 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b1849 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1852 : ℝ := e1846 ^ 2
lemma b1852 : Encl e1852 (2166412404107 / 1000000000000 : ℝ) (2166412404123 / 1000000000000 : ℝ) := by
  exact Encl.pow b1846 (by norm_num) 2 (by norm_num) (by norm_num)

def e1853 : ℝ := e1851 * e1852
lemma b1853 : Encl e1853 (3162836007463 / 1000000000000 : ℝ) (3162836007487 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1851 b1852 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1854 : ℝ := e1853 * e1841
lemma b1854 : Encl e1854 (202964800767 / 250000000000 : ℝ) (162371840617 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b1853 b1841 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1855 : ℝ := e1854 / e9
lemma b1855 : Encl e1855 (1449748576907 / 500000000000 : ℝ) (23195977231 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b1854 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1856 : ℝ := e5 + e1855
lemma b1856 : Encl e1856 (1949748576907 / 500000000000 : ℝ) (31195977231 / 8000000000 : ℝ) := by
  exact Encl.add b5 b1855 (by norm_num) (by norm_num)

def e1857 : ℝ := Real.sqrt e1856
lemma b1857 : Encl e1857 (1974714448677 / 1000000000000 : ℝ) (1974714448693 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1856 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1858 : ℝ := e5 + e1857
lemma b1858 : Encl e1858 (2974714448677 / 1000000000000 : ℝ) (2974714448693 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1857 (by norm_num) (by norm_num)

def e1859 : ℝ := e1850 / e1858
lemma b1859 : Encl e1859 (86289660603 / 500000000000 : ℝ) (17257932121 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1850 b1858 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1860 : ℝ := e1849 * e954
lemma b1860 : Encl e1860 (450684031 / 200000000000 : ℝ) (563355039 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1849 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1861 : ℝ := e1841 - e1859
lemma b1861 : Encl e1861 (1051347237 / 12500000000 : ℝ) (84107778967 / 1000000000000 : ℝ) := by
  exact Encl.sub b1841 b1859 (by norm_num) (by norm_num)

def e1862 : ℝ := e1861 / e1846
lemma b1862 : Encl e1862 (3571458559 / 62500000000 : ℝ) (1142866739 / 20000000000 : ℝ) := by
  exact Encl.div_nonneg b1861 b1846 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1863 : ℝ := e1862 ^ 2
lemma b1863 : Encl e1863 (3265360957 / 1000000000000 : ℝ) (1632680479 / 500000000000 : ℝ) := by
  exact Encl.pow b1862 (by norm_num) 2 (by norm_num) (by norm_num)

def e1864 : ℝ := e9 * e1863
lemma b1864 : Encl e1864 (914301067 / 1000000000000 : ℝ) (914301069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1863 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1865 : ℝ := e1859 ^ 3
lemma b1865 : Encl e1865 (2570018643 / 500000000000 : ℝ) (5140037287 / 1000000000000 : ℝ) := by
  exact Encl.pow b1859 (by norm_num) 3 (by norm_num) (by norm_num)

def e1866 : ℝ := e1849 * e1865
lemma b1866 : Encl e1866 (1250692541 / 1000000000000 : ℝ) (625346271 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1849 b1865 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1867 : ℝ := e1864 + e1866
lemma b1867 : Encl e1867 (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  exact Encl.add b1864 b1866 (by norm_num) (by norm_num)

def e1868 : ℝ := min e1860 e1867
lemma b1868 : Encl e1868 (270624201 / 125000000000 : ℝ) (2164993611 / 1000000000000 : ℝ) := by
  exact Encl.min b1860 b1867 (by norm_num) (by norm_num)

def e1869 : ℝ := (63 / 50 : ℝ)
lemma b1869 : Encl e1869 (63 / 50 : ℝ) (63 / 50 : ℝ) := by
  exact Encl.exact (63 / 50 : ℝ)

def e1870 : ℝ := e1869 / e0
lemma b1870 : Encl e1870 (401070456591 / 1000000000000 : ℝ) (25066903537 / 62500000000 : ℝ) := by
  exact Encl.div_nonneg b1869 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1871 : ℝ := e1869 * e7
lemma b1871 : Encl e1871 (53683096463 / 62500000000 : ℝ) (85892954341 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b1869 b7 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1872 : ℝ := e8 * e1869
lemma b1872 : Encl e1872 (3087 / 2500 : ℝ) (3087 / 2500 : ℝ) := by
  exact Encl.mul_nonneg b8 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1873 : ℝ := e1872 / e0
lemma b1873 : Encl e1873 (393049047459 / 1000000000000 : ℝ) (19652452373 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1872 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1874 : ℝ := e1869 ^ 2
lemma b1874 : Encl e1874 (3969 / 2500 : ℝ) (3969 / 2500 : ℝ) := by
  exact Encl.pow b1869 (by norm_num) 2 (by norm_num) (by norm_num)

def e1875 : ℝ := e17 * e1874
lemma b1875 : Encl e1875 (3969 / 625 : ℝ) (3969 / 625 : ℝ) := by
  exact Encl.mul_nonneg b17 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1876 : ℝ := e1875 / e0
lemma b1876 : Encl e1876 (2021395101221 / 1000000000000 : ℝ) (1010697550611 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1875 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1877 : ℝ := e5 + e1876
lemma b1877 : Encl e1877 (3021395101221 / 1000000000000 : ℝ) (1510697550611 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1876 (by norm_num) (by norm_num)

def e1878 : ℝ := Real.sqrt e1877
lemma b1878 : Encl e1878 (1738216068623 / 1000000000000 : ℝ) (108638504289 / 62500000000 : ℝ) := by
  exact Encl.sqrt b1877 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1879 : ℝ := e5 + e1878
lemma b1879 : Encl e1879 (2738216068623 / 1000000000000 : ℝ) (171138504289 / 62500000000 : ℝ) := by
  exact Encl.add b5 b1878 (by norm_num) (by norm_num)

def e1880 : ℝ := e23 / e1879
lemma b1880 : Encl e1880 (365201275187 / 500000000000 : ℝ) (5843220403 / 8000000000 : ℝ) := by
  exact Encl.div_nonneg b23 b1879 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1881 : ℝ := e9 * e1880
lemma b1881 : Encl e1881 (25564089263 / 125000000000 : ℝ) (40902542821 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b9 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1882 : ℝ := e1873 + e1881
lemma b1882 : Encl e1882 (597561761563 / 1000000000000 : ℝ) (119512352313 / 200000000000 : ℝ) := by
  exact Encl.add b1873 b1881 (by norm_num) (by norm_num)

def e1883 : ℝ := e1882 - e5
lemma b1883 : Encl e1883 (-402438238437 / 1000000000000 : ℝ) (-80487647687 / 200000000000 : ℝ) := by
  exact Encl.sub b1882 b5 (by norm_num) (by norm_num)

def e1884 : ℝ := e0 / e1874
lemma b1884 : Encl e1884 (1978831351467 / 1000000000000 : ℝ) (494707837867 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b0 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1885 : ℝ := e1870 ^ 2
lemma b1885 : Encl e1885 (3217150223 / 20000000000 : ℝ) (160857511151 / 1000000000000 : ℝ) := by
  exact Encl.pow b1870 (by norm_num) 2 (by norm_num) (by norm_num)

def e1886 : ℝ := e5 - e1885
lemma b1886 : Encl e1886 (839142488849 / 1000000000000 : ℝ) (16782849777 / 20000000000 : ℝ) := by
  exact Encl.sub b5 b1885 (by norm_num) (by norm_num)

def e1887 : ℝ := Real.sqrt e1886
lemma b1887 : Encl e1887 (916047208853 / 1000000000000 : ℝ) (183209441771 / 200000000000 : ℝ) := by
  exact Encl.sqrt b1886 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1888 : ℝ := e29 - e1887
lemma b1888 : Encl e1888 (-249380542189 / 1000000000000 : ℝ) (-124690271093 / 500000000000 : ℝ) := by
  exact Encl.sub b29 b1887 (by norm_num) (by norm_num)

def e1889 : ℝ := e1887 ^ 3
lemma b1889 : Encl e1889 (384347067369 / 500000000000 : ℝ) (96086766843 / 125000000000 : ℝ) := by
  exact Encl.pow b1887 (by norm_num) 3 (by norm_num) (by norm_num)

def e1890 : ℝ := e1889 / e35
lemma b1890 : Encl e1890 (128115689123 / 500000000000 : ℝ) (32028922281 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1889 b35 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1891 : ℝ := e1888 + e1890
lemma b1891 : Encl e1891 (6850836057 / 1000000000000 : ℝ) (3425418031 / 500000000000 : ℝ) := by
  exact Encl.add b1888 b1890 (by norm_num) (by norm_num)

def e1892 : ℝ := e8 * e1891
lemma b1892 : Encl e1892 (1342763867 / 200000000000 : ℝ) (6713819341 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1891 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1893 : ℝ := e1885 / e1887
lemma b1893 : Encl e1893 (87799793283 / 500000000000 : ℝ) (21949948321 / 125000000000 : ℝ) := by
  exact Encl.div_nonneg b1885 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1894 : ℝ := e1893 - e23
lemma b1894 : Encl e1894 (-912200206717 / 500000000000 : ℝ) (-228050051679 / 125000000000 : ℝ) := by
  exact Encl.sub b1893 b23 (by norm_num) (by norm_num)

def e1895 : ℝ := e23 * e1887
lemma b1895 : Encl e1895 (916047208853 / 500000000000 : ℝ) (183209441771 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1896 : ℝ := e1894 + e1895
lemma b1896 : Encl e1896 (480875267 / 62500000000 : ℝ) (3847002139 / 500000000000 : ℝ) := by
  exact Encl.add b1894 b1895 (by norm_num) (by norm_num)

def e1897 : ℝ := e1896 / e43
lemma b1897 : Encl e1897 (30776017 / 200000000000 : ℝ) (76940043 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1896 b43 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1898 : ℝ := e1892 - e1897
lemma b1898 : Encl e1898 (6559939249 / 1000000000000 : ℝ) (819992407 / 125000000000 : ℝ) := by
  exact Encl.sub b1892 b1897 (by norm_num) (by norm_num)

def e1899 : ℝ := e1884 * e1898
lemma b1899 : Encl e1899 (12981013449 / 1000000000000 : ℝ) (1622626683 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1884 b1898 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1900 : ℝ := e1883 + e1899
lemma b1900 : Encl e1900 (-97364306247 / 250000000000 : ℝ) (-389457224971 / 1000000000000 : ℝ) := by
  exact Encl.add b1883 b1899 (by norm_num) (by norm_num)

def e1901 : ℝ := e1871 ^ 2
lemma b1901 : Encl e1901 (737759960539 / 1000000000000 : ℝ) (737759960543 / 1000000000000 : ℝ) := by
  exact Encl.pow b1871 (by norm_num) 2 (by norm_num) (by norm_num)

def e1902 : ℝ := e5 - e1901
lemma b1902 : Encl e1902 (262240039457 / 1000000000000 : ℝ) (262240039461 / 1000000000000 : ℝ) := by
  exact Encl.sub b5 b1901 (by norm_num) (by norm_num)

def e1903 : ℝ := Real.sqrt e1902
lemma b1903 : Encl e1903 (512093779943 / 1000000000000 : ℝ) (128023444987 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1902 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1904 : ℝ := e5 + e1903
lemma b1904 : Encl e1904 (1512093779943 / 1000000000000 : ℝ) (378023444987 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1903 (by norm_num) (by norm_num)

def e1905 : ℝ := e1871 / e1904
lemma b1905 : Encl e1905 (568039862869 / 1000000000000 : ℝ) (284019931437 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1904 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1906 : ℝ := e1905 ^ 2
lemma b1906 : Encl e1906 (20166830363 / 62500000000 : ℝ) (161334642907 / 500000000000 : ℝ) := by
  exact Encl.pow b1905 (by norm_num) 2 (by norm_num) (by norm_num)

def e1907 : ℝ := e5 + e1906
lemma b1907 : Encl e1907 (82666830363 / 62500000000 : ℝ) (661334642907 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1906 (by norm_num) (by norm_num)

def e1908 : ℝ := Real.sqrt e1907
lemma b1908 : Encl e1908 (115007360017 / 100000000000 : ℝ) (1150073600173 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1907 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1909 : ℝ := e5 + e1908
lemma b1909 : Encl e1909 (215007360017 / 100000000000 : ℝ) (2150073600173 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1908 (by norm_num) (by norm_num)

def e1910 : ℝ := e1905 / e1909
lemma b1910 : Encl e1910 (26419554327 / 100000000000 : ℝ) (132097771637 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1905 b1909 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1911 : ℝ := Real.arcsin e1871
lemma b1911 : Encl e1911 (516587820431 / 500000000000 : ℝ) (516587820439 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1871) (a := (26419554327 / 100000000000 : ℝ)) (b := (132097771637 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (53683096463 / 62500000000 : ℝ) by norm_num).trans b1871.1
        exact b1871.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1871) (26419554327 / 100000000000 : ℝ) (132097771637 / 500000000000 : ℝ) from b1910) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1912 : ℝ := e59 * e1911
lemma b1912 : Encl e1912 (526919576839 / 1000000000000 : ℝ) (32932473553 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1911 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1913 : ℝ := e61 * e1871
lemma b1913 : Encl e1913 (420875476269 / 1000000000000 : ℝ) (420875476271 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1871 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1914 : ℝ := e1913 * e1903
lemma b1914 : Encl e1914 (215527713527 / 1000000000000 : ℝ) (53881928383 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1913 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1915 : ℝ := e1912 - e1914
lemma b1915 : Encl e1915 (311391863307 / 1000000000000 : ℝ) (311391863321 / 1000000000000 : ℝ) := by
  exact Encl.sub b1912 b1914 (by norm_num) (by norm_num)

def e1916 : ℝ := e43 * e1903
lemma b1916 : Encl e1916 (512093779943 / 20000000000 : ℝ) (128023444987 / 5000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1917 : ℝ := e1871 / e1916
lemma b1917 : Encl e1917 (33545790909 / 1000000000000 : ℝ) (3354579091 / 100000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1916 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1918 : ℝ := e1915 - e1917
lemma b1918 : Encl e1918 (277846072397 / 1000000000000 : ℝ) (69461518103 / 250000000000 : ℝ) := by
  exact Encl.sub b1915 b1917 (by norm_num) (by norm_num)

def e1919 : ℝ := e5 + e1887
lemma b1919 : Encl e1919 (1916047208853 / 1000000000000 : ℝ) (383209441771 / 200000000000 : ℝ) := by
  exact Encl.add b5 b1887 (by norm_num) (by norm_num)

def e1920 : ℝ := e1870 / e1919
lemma b1920 : Encl e1920 (6541306347 / 31250000000 : ℝ) (104660901553 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1870 b1919 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1921 : ℝ := e1920 ^ 2
lemma b1921 : Encl e1921 (21907808627 / 500000000000 : ℝ) (5476952157 / 125000000000 : ℝ) := by
  exact Encl.pow b1920 (by norm_num) 2 (by norm_num) (by norm_num)

def e1922 : ℝ := e5 + e1921
lemma b1922 : Encl e1922 (521907808627 / 500000000000 : ℝ) (130476952157 / 125000000000 : ℝ) := by
  exact Encl.add b5 b1921 (by norm_num) (by norm_num)

def e1923 : ℝ := Real.sqrt e1922
lemma b1923 : Encl e1923 (6385455939 / 6250000000 : ℝ) (510836475121 / 500000000000 : ℝ) := by
  exact Encl.sqrt b1922 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1924 : ℝ := e5 + e1923
lemma b1924 : Encl e1924 (12635455939 / 6250000000 : ℝ) (1010836475121 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1923 (by norm_num) (by norm_num)

def e1925 : ℝ := e1920 / e1924
lemma b1925 : Encl e1925 (51769452393 / 500000000000 : ℝ) (25884726197 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1920 b1924 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1926 : ℝ := Real.arcsin e1870
lemma b1926 : Encl e1926 (51585638507 / 125000000000 : ℝ) (82537021613 / 200000000000 : ℝ) := by
  apply Encl.arcsin (z := e1870) (a := (51769452393 / 500000000000 : ℝ)) (b := (25884726197 / 250000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (401070456591 / 1000000000000 : ℝ) by norm_num).trans b1870.1
        exact b1870.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1870) (51769452393 / 500000000000 : ℝ) (25884726197 / 250000000000 : ℝ) from b1925) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1927 : ℝ := e59 * e1926
lemma b1927 : Encl e1927 (52617351277 / 250000000000 : ℝ) (105234702557 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1926 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1928 : ℝ := e61 * e1870
lemma b1928 : Encl e1928 (196524523729 / 1000000000000 : ℝ) (196524523731 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1870 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1929 : ℝ := e1928 * e1887
lemma b1929 : Encl e1929 (180025741433 / 1000000000000 : ℝ) (45006435359 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1928 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1930 : ℝ := e1927 - e1929
lemma b1930 : Encl e1930 (3805457959 / 125000000000 : ℝ) (30443663681 / 1000000000000 : ℝ) := by
  exact Encl.sub b1927 b1929 (by norm_num) (by norm_num)

def e1931 : ℝ := e43 * e1887
lemma b1931 : Encl e1931 (916047208853 / 20000000000 : ℝ) (183209441771 / 4000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1887 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1932 : ℝ := e1870 / e1931
lemma b1932 : Encl e1932 (8756545573 / 1000000000000 : ℝ) (4378272787 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1870 b1931 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1933 : ℝ := e1930 - e1932
lemma b1933 : Encl e1933 (10843559049 / 500000000000 : ℝ) (5421779527 / 250000000000 : ℝ) := by
  exact Encl.sub b1930 b1932 (by norm_num) (by norm_num)

def e1934 : ℝ := e1918 - e1933
lemma b1934 : Encl e1934 (256158954289 / 1000000000000 : ℝ) (128079477157 / 500000000000 : ℝ) := by
  exact Encl.sub b1918 b1933 (by norm_num) (by norm_num)

def e1935 : ℝ := e1934 / e1869
lemma b1935 : Encl e1935 (50825189343 / 250000000000 : ℝ) (203300757393 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1934 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1936 : ℝ := e1900 + e1935
lemma b1936 : Encl e1936 (-5817389613 / 31250000000 : ℝ) (-93078233789 / 500000000000 : ℝ) := by
  exact Encl.add b1900 b1935 (by norm_num) (by norm_num)

def e1937 : ℝ := e1871 + e4
lemma b1937 : Encl e1937 (924336431009 / 500000000000 : ℝ) (1848672862021 / 1000000000000 : ℝ) := by
  exact Encl.add b1871 b4 (by norm_num) (by norm_num)

def e1938 : ℝ := e1937 / e23
lemma b1938 : Encl e1938 (924336431009 / 1000000000000 : ℝ) (924336431011 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1937 b23 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1939 : ℝ := e1871 / e1869
lemma b1939 : Encl e1939 (136338022763 / 200000000000 : ℝ) (340845056909 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1871 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1940 : ℝ := e89 * e1939
lemma b1940 : Encl e1940 (241652853471 / 200000000000 : ℝ) (604132133681 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1939 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1941 : ℝ := e1939 ^ 2
lemma b1941 : Encl e1941 (464701411273 / 1000000000000 : ℝ) (232350705639 / 500000000000 : ℝ) := by
  exact Encl.pow b1939 (by norm_num) 2 (by norm_num) (by norm_num)

def e1942 : ℝ := e91 * e1941
lemma b1942 : Encl e1942 (364975634941 / 1000000000000 : ℝ) (364975634947 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1943 : ℝ := e5 + e1942
lemma b1943 : Encl e1943 (1364975634941 / 1000000000000 : ℝ) (1364975634947 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1942 (by norm_num) (by norm_num)

def e1944 : ℝ := Real.sqrt e1943
lemma b1944 : Encl e1944 (46732868689 / 40000000000 : ℝ) (1168321717229 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1943 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1945 : ℝ := e1940 * e1944
lemma b1945 : Encl e1945 (1411641383697 / 1000000000000 : ℝ) (1411641383711 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1940 b1944 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1946 : ℝ := e97 * e1941
lemma b1946 : Encl e1946 (729951269883 / 1000000000000 : ℝ) (182487817473 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1941 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1947 : ℝ := e1945 - e1946
lemma b1947 : Encl e1947 (136338022761 / 200000000000 : ℝ) (170422528457 / 250000000000 : ℝ) := by
  exact Encl.sub b1945 b1946 (by norm_num) (by norm_num)

def e1948 : ℝ := e1938 * e1947
lemma b1948 : Encl e1948 (4922742241 / 7812500000 : ℝ) (78763875859 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1938 b1947 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1949 : ℝ := e1938 / e1869
lemma b1949 : Encl e1949 (73360034207 / 100000000000 : ℝ) (733600342073 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1950 : ℝ := e89 * e1949
lemma b1950 : Encl e1950 (1300272751327 / 1000000000000 : ℝ) (650136375667 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1949 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1951 : ℝ := e1949 ^ 2
lemma b1951 : Encl e1951 (107633892377 / 200000000000 : ℝ) (53816946189 / 100000000000 : ℝ) := by
  exact Encl.pow b1949 (by norm_num) 2 (by norm_num) (by norm_num)

def e1952 : ℝ := e91 * e1951
lemma b1952 : Encl e1952 (5283466337 / 12500000000 : ℝ) (211338653483 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1951 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1953 : ℝ := e5 + e1952
lemma b1953 : Encl e1953 (17783466337 / 12500000000 : ℝ) (711338653483 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1952 (by norm_num) (by norm_num)

def e1954 : ℝ := Real.sqrt e1953
lemma b1954 : Encl e1954 (238552074563 / 200000000000 : ℝ) (1192760372819 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1953 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1955 : ℝ := e1950 * e1954
lemma b1955 : Encl e1955 (1550913811633 / 1000000000000 : ℝ) (24233028307 / 15625000000 : ℝ) := by
  exact Encl.mul_nonneg b1950 b1954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1956 : ℝ := e97 * e1951
lemma b1956 : Encl e1956 (845354613921 / 1000000000000 : ℝ) (845354613931 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1951 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1957 : ℝ := e1955 - e1956
lemma b1957 : Encl e1957 (352779598851 / 500000000000 : ℝ) (705559197727 / 1000000000000 : ℝ) := by
  exact Encl.sub b1955 b1956 (by norm_num) (by norm_num)

def e1958 : ℝ := e1871 * e1957
lemma b1958 : Encl e1958 (606025639529 / 1000000000000 : ℝ) (606025639553 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1871 b1957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1959 : ℝ := e1948 - e1958
lemma b1959 : Encl e1959 (4817073459 / 200000000000 : ℝ) (24085367343 / 1000000000000 : ℝ) := by
  exact Encl.sub b1948 b1958 (by norm_num) (by norm_num)

def e1960 : ℝ := e1938 ^ 2
lemma b1960 : Encl e1960 (85439783769 / 100000000000 : ℝ) (170879567539 / 200000000000 : ℝ) := by
  exact Encl.pow b1938 (by norm_num) 2 (by norm_num) (by norm_num)

def e1961 : ℝ := e8 * e1960
lemma b1961 : Encl e1961 (104663735117 / 125000000000 : ℝ) (418654940471 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1960 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1962 : ℝ := e5 - e1961
lemma b1962 : Encl e1962 (81345059529 / 500000000000 : ℝ) (20336264883 / 125000000000 : ℝ) := by
  exact Encl.sub b5 b1961 (by norm_num) (by norm_num)

def e1963 : ℝ := e5 - e1960
lemma b1963 : Encl e1963 (29120432461 / 200000000000 : ℝ) (14560216231 / 100000000000 : ℝ) := by
  exact Encl.sub b5 b1960 (by norm_num) (by norm_num)

def e1964 : ℝ := Real.sqrt e1963
lemma b1964 : Encl e1964 (76315702789 / 200000000000 : ℝ) (381578513953 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b1963 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1965 : ℝ := e1962 / e1964
lemma b1965 : Encl e1965 (213180398147 / 500000000000 : ℝ) (2664754977 / 6250000000 : ℝ) := by
  exact Encl.div_nonneg b1962 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1966 : ℝ := e5 - e1965
lemma b1966 : Encl e1966 (3585245023 / 6250000000 : ℝ) (286819601853 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1965 (by norm_num) (by norm_num)

def e1967 : ℝ := e8 * e1901
lemma b1967 : Encl e1967 (45187797583 / 62500000000 : ℝ) (723004761333 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b8 b1901 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1968 : ℝ := e5 - e1967
lemma b1968 : Encl e1968 (276995238667 / 1000000000000 : ℝ) (17312202417 / 62500000000 : ℝ) := by
  exact Encl.sub b5 b1967 (by norm_num) (by norm_num)

def e1969 : ℝ := e1968 / e1903
lemma b1969 : Encl e1969 (270453625403 / 500000000000 : ℝ) (270453625411 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1968 b1903 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1970 : ℝ := e5 - e1969
lemma b1970 : Encl e1970 (229546374589 / 500000000000 : ℝ) (229546374597 / 500000000000 : ℝ) := by
  exact Encl.sub b5 b1969 (by norm_num) (by norm_num)

def e1971 : ℝ := e1966 - e1970
lemma b1971 : Encl e1971 (57273227243 / 500000000000 : ℝ) (27965443 / 244140625 : ℝ) := by
  exact Encl.sub b1966 b1970 (by norm_num) (by norm_num)

def e1972 : ℝ := e1959 * e1971
lemma b1972 : Encl e1972 (689723357 / 250000000000 : ℝ) (689723359 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1959 b1971 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1973 : ℝ := e1957 - e1947
lemma b1973 : Encl e1973 (11934541937 / 500000000000 : ℝ) (11934541961 / 500000000000 : ℝ) := by
  exact Encl.sub b1957 b1947 (by norm_num) (by norm_num)

def e1974 : ℝ := e5 + e1964
lemma b1974 : Encl e1974 (276315702789 / 200000000000 : ℝ) (1381578513953 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1964 (by norm_num) (by norm_num)

def e1975 : ℝ := e1938 / e1974
lemma b1975 : Encl e1975 (334521860927 / 500000000000 : ℝ) (33452186093 / 50000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1974 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1976 : ℝ := e1975 ^ 2
lemma b1976 : Encl e1976 (55952437719 / 125000000000 : ℝ) (447619501761 / 1000000000000 : ℝ) := by
  exact Encl.pow b1975 (by norm_num) 2 (by norm_num) (by norm_num)

def e1977 : ℝ := e5 + e1976
lemma b1977 : Encl e1977 (180952437719 / 125000000000 : ℝ) (1447619501761 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b1976 (by norm_num) (by norm_num)

def e1978 : ℝ := Real.sqrt e1977
lemma b1978 : Encl e1978 (1203170603759 / 1000000000000 : ℝ) (300792650941 / 250000000000 : ℝ) := by
  exact Encl.sqrt b1977 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1979 : ℝ := e5 + e1978
lemma b1979 : Encl e1979 (2203170603759 / 1000000000000 : ℝ) (550792650941 / 250000000000 : ℝ) := by
  exact Encl.add b5 b1978 (by norm_num) (by norm_num)

def e1980 : ℝ := e1975 / e1979
lemma b1980 : Encl e1980 (151836566971 / 500000000000 : ℝ) (151836566973 / 500000000000 : ℝ) := by
  exact Encl.div_nonneg b1975 b1979 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1981 : ℝ := Real.arcsin e1938
lemma b1981 : Encl e1981 (1179292904367 / 1000000000000 : ℝ) (589646452193 / 500000000000 : ℝ) := by
  apply Encl.arcsin (z := e1938) (a := (151836566971 / 500000000000 : ℝ)) (b := (151836566973 / 500000000000 : ℝ))
    (by constructor; exact (show (0 : ℝ) ≤ (924336431009 / 1000000000000 : ℝ) by norm_num).trans b1938.1
        exact b1938.2.trans_lt (by norm_num))
    (by constructor <;> norm_num) (by constructor <;> norm_num)
    (show Encl (asinQuarterArg e1938) (151836566971 / 500000000000 : ℝ) (151836566973 / 500000000000 : ℝ) from b1980) 5
  · norm_num [atanPoly, Finset.sum_range_succ]
  · norm_num [atanPoly, Finset.sum_range_succ]

def e1982 : ℝ := e59 * e1981
lemma b1982 : Encl e1982 (601439381227 / 1000000000000 : ℝ) (601439381237 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b59 b1981 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1983 : ℝ := e61 * e1938
lemma b1983 : Encl e1983 (226462425597 / 500000000000 : ℝ) (113231212799 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b61 b1938 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1984 : ℝ := e1983 * e1964
lemma b1984 : Encl e1984 (172826391647 / 1000000000000 : ℝ) (43206597913 / 250000000000 : ℝ) := by
  exact Encl.mul_nonneg b1983 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1985 : ℝ := e1982 - e1984
lemma b1985 : Encl e1985 (17144519583 / 40000000000 : ℝ) (42861298959 / 100000000000 : ℝ) := by
  exact Encl.sub b1982 b1984 (by norm_num) (by norm_num)

def e1986 : ℝ := e43 * e1964
lemma b1986 : Encl e1986 (76315702789 / 4000000000 : ℝ) (381578513953 / 20000000000 : ℝ) := by
  exact Encl.mul_nonneg b43 b1964 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1987 : ℝ := e1938 / e1986
lemma b1987 : Encl e1987 (24224016741 / 500000000000 : ℝ) (12112008371 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1938 b1986 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1988 : ℝ := e1985 - e1987
lemma b1988 : Encl e1988 (380164956091 / 1000000000000 : ℝ) (95041239027 / 250000000000 : ℝ) := by
  exact Encl.sub b1985 b1987 (by norm_num) (by norm_num)

def e1989 : ℝ := e1988 - e1918
lemma b1989 : Encl e1989 (102318883679 / 1000000000000 : ℝ) (102318883711 / 1000000000000 : ℝ) := by
  exact Encl.sub b1988 b1918 (by norm_num) (by norm_num)

def e1990 : ℝ := e1973 * e1989
lemma b1990 : Encl e1990 (76320563 / 31250000000 : ℝ) (2442258023 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b1973 b1989 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1991 : ℝ := e1972 + e1990
lemma b1991 : Encl e1991 (1300287861 / 250000000000 : ℝ) (5201151459 / 1000000000000 : ℝ) := by
  exact Encl.add b1972 b1990 (by norm_num) (by norm_num)

def e1992 : ℝ := e1938 - e1871
lemma b1992 : Encl e1992 (65406887599 / 1000000000000 : ℝ) (65406887603 / 1000000000000 : ℝ) := by
  exact Encl.sub b1938 b1871 (by norm_num) (by norm_num)

def e1993 : ℝ := e1991 / e1992
lemma b1993 : Encl e1993 (4969995931 / 62500000000 : ℝ) (19879983783 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b1991 b1992 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1994 : ℝ := e1936 + e1993
lemma b1994 : Encl e1994 (-1332956659 / 12500000000 : ℝ) (-53318266223 / 500000000000 : ℝ) := by
  exact Encl.add b1936 b1993 (by norm_num) (by norm_num)

def e1995 : ℝ := e4 * e1957
lemma b1995 : Encl e1995 (698322501809 / 1000000000000 : ℝ) (139664500367 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b4 b1957 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1996 : ℝ := e4 / e1869
lemma b1996 : Encl e1996 (31420422813 / 40000000000 : ℝ) (785510570327 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b4 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1997 : ℝ := e89 * e1996
lemma b1997 : Encl e1997 (1392281235299 / 1000000000000 : ℝ) (174035154413 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b89 b1996 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e1998 : ℝ := e1996 ^ 2
lemma b1998 : Encl e1998 (154256714023 / 250000000000 : ℝ) (19282089253 / 31250000000 : ℝ) := by
  exact Encl.pow b1996 (by norm_num) 2 (by norm_num) (by norm_num)

def e1999 : ℝ := e91 * e1998
lemma b1999 : Encl e1999 (484611759541 / 1000000000000 : ℝ) (242305879773 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b91 b1998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2000 : ℝ := e5 + e1999
lemma b2000 : Encl e2000 (1484611759541 / 1000000000000 : ℝ) (742305879773 / 500000000000 : ℝ) := by
  exact Encl.add b5 b1999 (by norm_num) (by norm_num)

def e2001 : ℝ := Real.sqrt e2000
lemma b2001 : Encl e2001 (304611613323 / 250000000000 : ℝ) (243689290659 / 200000000000 : ℝ) := by
  exact Encl.sqrt b2000 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2002 : ℝ := e1997 * e2001
lemma b2002 : Encl e2002 (339284026627 / 200000000000 : ℝ) (848210066573 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b1997 b2001 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2003 : ℝ := e97 * e1998
lemma b2003 : Encl e2003 (484611759541 / 500000000000 : ℝ) (96922351909 / 100000000000 : ℝ) := by
  exact Encl.mul_nonneg b97 b1998 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2004 : ℝ := e2002 - e2003
lemma b2004 : Encl e2004 (145439322809 / 200000000000 : ℝ) (45449788379 / 62500000000 : ℝ) := by
  exact Encl.sub b2002 b2003 (by norm_num) (by norm_num)

def e2005 : ℝ := e1938 * e2004
lemma b2005 : Encl e2005 (168043580717 / 250000000000 : ℝ) (84021790361 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b1938 b2004 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2006 : ℝ := e1995 - e2005
lemma b2006 : Encl e2006 (26148178921 / 1000000000000 : ℝ) (26148178967 / 1000000000000 : ℝ) := by
  exact Encl.sub b1995 b2005 (by norm_num) (by norm_num)

def e2007 : ℝ := e165 - e1966
lemma b2007 : Encl e2007 (146360796269 / 1000000000000 : ℝ) (36590199087 / 250000000000 : ℝ) := by
  exact Encl.sub b165 b1966 (by norm_num) (by norm_num)

def e2008 : ℝ := e2006 * e2007
lemma b2008 : Encl e2008 (3827068287 / 1000000000000 : ℝ) (3827068297 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2006 b2007 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2009 : ℝ := e2004 - e1957
lemma b2009 : Encl e2009 (10818708159 / 500000000000 : ℝ) (10818708181 / 500000000000 : ℝ) := by
  exact Encl.sub b2004 b1957 (by norm_num) (by norm_num)

def e2010 : ℝ := e183 - e1988
lemma b2010 : Encl e2010 (34996953351 / 250000000000 : ℝ) (8749238347 / 62500000000 : ℝ) := by
  exact Encl.sub b183 b1988 (by norm_num) (by norm_num)

def e2011 : ℝ := e2009 * e2010
lemma b2011 : Encl e2011 (1514487299 / 500000000000 : ℝ) (189310913 / 62500000000 : ℝ) := by
  exact Encl.mul_nonneg b2009 b2010 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2012 : ℝ := e2008 + e2011
lemma b2012 : Encl e2012 (1371208577 / 200000000000 : ℝ) (1371208581 / 200000000000 : ℝ) := by
  exact Encl.add b2008 b2011 (by norm_num) (by norm_num)

def e2013 : ℝ := e4 - e1938
lemma b2013 : Encl e2013 (65406887599 / 1000000000000 : ℝ) (32703443801 / 500000000000 : ℝ) := by
  exact Encl.sub b4 b1938 (by norm_num) (by norm_num)

def e2014 : ℝ := e2012 / e2013
lemma b2014 : Encl e2014 (20964284149 / 200000000000 : ℝ) (104821421057 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2012 b2013 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2015 : ℝ := e1994 + e2014
lemma b2015 : Encl e2015 (-72604479 / 40000000000 : ℝ) (-1815111389 / 1000000000000 : ℝ) := by
  exact Encl.add b1994 b2014 (by norm_num) (by norm_num)

def e2016 : ℝ := e924 / e1869
lemma b2016 : Encl e2016 (47619047619 / 62500000000 : ℝ) (152380952381 / 200000000000 : ℝ) := by
  exact Encl.div_nonneg b924 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2017 : ℝ := min e7 e2016
lemma b2017 : Encl e2017 (85211264227 / 125000000000 : ℝ) (681690113817 / 1000000000000 : ℝ) := by
  exact Encl.min b7 b2016 (by norm_num) (by norm_num)

def e2018 : ℝ := e2017 - e5
lemma b2018 : Encl e2018 (-39788735773 / 125000000000 : ℝ) (-318309886183 / 1000000000000 : ℝ) := by
  exact Encl.sub b2017 b5 (by norm_num) (by norm_num)

def e2019 : ℝ := e23 * e1869
lemma b2019 : Encl e2019 (63 / 25 : ℝ) (63 / 25 : ℝ) := by
  exact Encl.mul_nonneg b23 b1869 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2020 : ℝ := e2019 * e1880
lemma b2020 : Encl e2020 (920307213471 / 500000000000 : ℝ) (368122885389 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2019 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2021 : ℝ := e2020 / e0
lemma b2021 : Encl e2021 (146471442187 / 250000000000 : ℝ) (93741723 / 160000000 : ℝ) := by
  exact Encl.div_nonneg b2020 b0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2022 : ℝ := e2018 + e2021
lemma b2022 : Encl e2022 (66893970641 / 250000000000 : ℝ) (267575882567 / 1000000000000 : ℝ) := by
  exact Encl.add b2018 b2021 (by norm_num) (by norm_num)

def e2023 : ℝ := e23 * e1874
lemma b2023 : Encl e2023 (3969 / 1250 : ℝ) (3969 / 1250 : ℝ) := by
  exact Encl.mul_nonneg b23 b1874 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2024 : ℝ := e2023 * e1880
lemma b2024 : Encl e2024 (2319174177947 / 1000000000000 : ℝ) (2319174177951 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2023 b1880 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2025 : ℝ := e0 + e2024
lemma b2025 : Encl e2025 (341297926971 / 62500000000 : ℝ) (5460766831541 / 1000000000000 : ℝ) := by
  exact Encl.add b0 b2024 (by norm_num) (by norm_num)

def e2026 : ℝ := Real.sqrt e2025
lemma b2026 : Encl e2026 (2336828370149 / 1000000000000 : ℝ) (2336828370151 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2025 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2027 : ℝ := e932 * e2026
lemma b2027 : Encl e2027 (297534229013 / 200000000000 : ℝ) (1487671145069 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b932 b2026 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2028 : ℝ := e1869 ^ 3
lemma b2028 : Encl e2028 (250047 / 125000 : ℝ) (250047 / 125000 : ℝ) := by
  exact Encl.pow b1869 (by norm_num) 3 (by norm_num) (by norm_num)

def e2029 : ℝ := e939 * e2028
lemma b2029 : Encl e2029 (16753149 / 62500000 : ℝ) (16753149 / 62500000 : ℝ) := by
  exact Encl.mul_nonneg b939 b2028 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2030 : ℝ := min e2029 e941
lemma b2030 : Encl e2030 (16753149 / 62500000 : ℝ) (16753149 / 62500000 : ℝ) := by
  exact Encl.min b2029 b941 (by norm_num) (by norm_num)

def e2031 : ℝ := e23 * e2022
lemma b2031 : Encl e2031 (66893970641 / 125000000000 : ℝ) (267575882567 / 500000000000 : ℝ) := by
  exact Encl.mul_nonneg b23 b2022 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2032 : ℝ := e944 * e2030
lemma b2032 : Encl e2032 (50259447 / 31250000 : ℝ) (50259447 / 31250000 : ℝ) := by
  exact Encl.mul_nonneg b944 b2030 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2033 : ℝ := e2027 ^ 2
lemma b2033 : Encl e2033 (2213165435859 / 1000000000000 : ℝ) (2213165435871 / 1000000000000 : ℝ) := by
  exact Encl.pow b2027 (by norm_num) 2 (by norm_num) (by norm_num)

def e2034 : ℝ := e2032 * e2033
lemma b2034 : Encl e2034 (28475512557 / 8000000000 : ℝ) (711887813929 / 200000000000 : ℝ) := by
  exact Encl.mul_nonneg b2032 b2033 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2035 : ℝ := e2034 * e2022
lemma b2035 : Encl e2035 (952420050487 / 1000000000000 : ℝ) (119052506313 / 125000000000 : ℝ) := by
  exact Encl.mul_nonneg b2034 b2022 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2036 : ℝ := e2035 / e9
lemma b2036 : Encl e2036 (340150018031 / 100000000000 : ℝ) (850375045093 / 250000000000 : ℝ) := by
  exact Encl.div_nonneg b2035 b9 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2037 : ℝ := e5 + e2036
lemma b2037 : Encl e2037 (440150018031 / 100000000000 : ℝ) (1100375045093 / 250000000000 : ℝ) := by
  exact Encl.add b5 b2036 (by norm_num) (by norm_num)

def e2038 : ℝ := Real.sqrt e2037
lemma b2038 : Encl e2038 (419595051463 / 200000000000 : ℝ) (2097975257331 / 1000000000000 : ℝ) := by
  exact Encl.sqrt b2037 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2039 : ℝ := e5 + e2038
lemma b2039 : Encl e2039 (619595051463 / 200000000000 : ℝ) (3097975257331 / 1000000000000 : ℝ) := by
  exact Encl.add b5 b2038 (by norm_num) (by norm_num)

def e2040 : ℝ := e2031 / e2039
lemma b2040 : Encl e2040 (86371213563 / 500000000000 : ℝ) (172742427129 / 1000000000000 : ℝ) := by
  exact Encl.div_nonneg b2031 b2039 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def e2041 : ℝ := e2030 * e954
lemma b2041 : Encl e2041 (1241207303 / 500000000000 : ℝ) (2482414607 / 1000000000000 : ℝ) := by
  exact Encl.mul_nonneg b2030 b954 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
