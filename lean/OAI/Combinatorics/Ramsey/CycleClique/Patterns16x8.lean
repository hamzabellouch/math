import Mathlib
import OAI.Combinatorics.Ramsey.CycleClique.BallPacking
import OAI.Combinatorics.Ramsey.CycleClique.CachedDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CertificateModel
import OAI.Combinatorics.Ramsey.CycleClique.Certificates055
import OAI.Combinatorics.Ramsey.CycleClique.Certificates056
import OAI.Combinatorics.Ramsey.CycleClique.Certificates057
import OAI.Combinatorics.Ramsey.CycleClique.Certificates058
import OAI.Combinatorics.Ramsey.CycleClique.Certificates059
import OAI.Combinatorics.Ramsey.CycleClique.Certificates060
import OAI.Combinatorics.Ramsey.CycleClique.Certificates061
import OAI.Combinatorics.Ramsey.CycleClique.Certificates062
import OAI.Combinatorics.Ramsey.CycleClique.Certificates063
import OAI.Combinatorics.Ramsey.CycleClique.Certificates064
import OAI.Combinatorics.Ramsey.CycleClique.Certificates065
import OAI.Combinatorics.Ramsey.CycleClique.Certificates066
import OAI.Combinatorics.Ramsey.CycleClique.Certificates067
import OAI.Combinatorics.Ramsey.CycleClique.Certificates068
import OAI.Combinatorics.Ramsey.CycleClique.Certificates069
import OAI.Combinatorics.Ramsey.CycleClique.Certificates070
import OAI.Combinatorics.Ramsey.CycleClique.CliqueBits
import OAI.Combinatorics.Ramsey.CycleClique.CompactDecisions
import OAI.Combinatorics.Ramsey.CycleClique.CompactLabels
import OAI.Combinatorics.Ramsey.CycleClique.EdgeBits
import OAI.Combinatorics.Ramsey.CycleClique.EdgeDecisions
import OAI.Combinatorics.Ramsey.CycleClique.FiniteGraphs
import OAI.Combinatorics.Ramsey.CycleClique.LabelDecisions
import OAI.Combinatorics.Ramsey.CycleClique.MatrixBits
import OAI.Combinatorics.Ramsey.CycleClique.PatternReduction

namespace OAI

namespace CycleClique
open scoped SimpleGraph

noncomputable def patterns_16_8_0 : List (List (List ℕ)) := [[[],[],[],[],[],[],[],[]],[[],[],[],[],[],[],[1]],[[],[],[],[],[],[],[2]],[[],[],[],[],[],[],[3]],[[],[],[],[],[],[],[4]],[[],[],[],[],[],[],[5]],[[],[],[],[],[],[],[6]],[[],[],[],[],[],[],[7]],[[],[],[],[],[],[],[8]],[[],[],[],[],[],[1,1]],[[],[],[],[],[],[1,2]],[[],[],[],[],[],[1,3]],[[],[],[],[],[],[1,4]],[[],[],[],[],[],[1,5]],[[],[],[],[],[],[1,6]],[[],[],[],[],[],[1,7]]]

theorem patterns_16_8_0_verified : ∀ D ∈ patterns_16_8_0, PatternVerified 16 8 D := by

  simp only [patterns_16_8_0, List.forall_mem_cons]

  exact ⟨⟨certificate_1752, certificate_1752_valid⟩, ⟨⟨certificate_1753, certificate_1753_valid⟩, ⟨⟨certificate_1754, certificate_1754_valid⟩, ⟨⟨certificate_1755, certificate_1755_valid⟩, ⟨⟨certificate_1756, certificate_1756_valid⟩, ⟨⟨certificate_1757, certificate_1757_valid⟩, ⟨⟨certificate_1758, certificate_1758_valid⟩, ⟨⟨certificate_1759, certificate_1759_valid⟩, ⟨⟨certificate_1760, certificate_1760_valid⟩, ⟨⟨certificate_1761, certificate_1761_valid⟩, ⟨⟨certificate_1762, certificate_1762_valid⟩, ⟨⟨certificate_1763, certificate_1763_valid⟩, ⟨⟨certificate_1764, certificate_1764_valid⟩, ⟨⟨certificate_1765, certificate_1765_valid⟩, ⟨⟨certificate_1766, certificate_1766_valid⟩, ⟨⟨certificate_1767, certificate_1767_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_1 : List (List (List ℕ)) := [[[],[],[],[],[],[2,2]],[[],[],[],[],[],[2,3]],[[],[],[],[],[],[2,4]],[[],[],[],[],[],[2,5]],[[],[],[],[],[],[2,6]],[[],[],[],[],[],[3,3]],[[],[],[],[],[],[3,4]],[[],[],[],[],[],[3,5]],[[],[],[],[],[],[4,4]],[[],[],[],[],[1],[1]],[[],[],[],[],[1],[2]],[[],[],[],[],[1],[3]],[[],[],[],[],[1],[4]],[[],[],[],[],[1],[5]],[[],[],[],[],[1],[6]],[[],[],[],[],[1],[7]]]

theorem patterns_16_8_1_verified : ∀ D ∈ patterns_16_8_1, PatternVerified 16 8 D := by

  simp only [patterns_16_8_1, List.forall_mem_cons]

  exact ⟨⟨certificate_1768, certificate_1768_valid⟩, ⟨⟨certificate_1769, certificate_1769_valid⟩, ⟨⟨certificate_1770, certificate_1770_valid⟩, ⟨⟨certificate_1771, certificate_1771_valid⟩, ⟨⟨certificate_1772, certificate_1772_valid⟩, ⟨⟨certificate_1773, certificate_1773_valid⟩, ⟨⟨certificate_1774, certificate_1774_valid⟩, ⟨⟨certificate_1775, certificate_1775_valid⟩, ⟨⟨certificate_1776, certificate_1776_valid⟩, ⟨⟨certificate_1777, certificate_1777_valid⟩, ⟨⟨certificate_1778, certificate_1778_valid⟩, ⟨⟨certificate_1779, certificate_1779_valid⟩, ⟨⟨certificate_1780, certificate_1780_valid⟩, ⟨⟨certificate_1781, certificate_1781_valid⟩, ⟨⟨certificate_1782, certificate_1782_valid⟩, ⟨⟨certificate_1783, certificate_1783_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_2 : List (List (List ℕ)) := [[[],[],[],[],[1,1,1]],[[],[],[],[],[1,1,2]],[[],[],[],[],[1,1,3]],[[],[],[],[],[1,1,4]],[[],[],[],[],[1,1,5]],[[],[],[],[],[1,1,6]],[[],[],[],[],[1,2,1]],[[],[],[],[],[1,2,2]],[[],[],[],[],[1,2,3]],[[],[],[],[],[1,2,4]],[[],[],[],[],[1,2,5]],[[],[],[],[],[1,3,1]],[[],[],[],[],[1,3,2]],[[],[],[],[],[1,3,3]],[[],[],[],[],[1,3,4]],[[],[],[],[],[1,4,1]]]

theorem patterns_16_8_2_verified : ∀ D ∈ patterns_16_8_2, PatternVerified 16 8 D := by

  simp only [patterns_16_8_2, List.forall_mem_cons]

  exact ⟨⟨certificate_1784, certificate_1784_valid⟩, ⟨⟨certificate_1785, certificate_1785_valid⟩, ⟨⟨certificate_1786, certificate_1786_valid⟩, ⟨⟨certificate_1787, certificate_1787_valid⟩, ⟨⟨certificate_1788, certificate_1788_valid⟩, ⟨⟨certificate_1789, certificate_1789_valid⟩, ⟨⟨certificate_1790, certificate_1790_valid⟩, ⟨⟨certificate_1791, certificate_1791_valid⟩, ⟨⟨certificate_1792, certificate_1792_valid⟩, ⟨⟨certificate_1793, certificate_1793_valid⟩, ⟨⟨certificate_1794, certificate_1794_valid⟩, ⟨⟨certificate_1795, certificate_1795_valid⟩, ⟨⟨certificate_1796, certificate_1796_valid⟩, ⟨⟨certificate_1797, certificate_1797_valid⟩, ⟨⟨certificate_1798, certificate_1798_valid⟩, ⟨⟨certificate_1799, certificate_1799_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_3 : List (List (List ℕ)) := [[[],[],[],[],[1,4,2]],[[],[],[],[],[1,4,3]],[[],[],[],[],[1,5,1]],[[],[],[],[],[1,5,2]],[[],[],[],[],[1,6,1]],[[],[],[],[],[2],[2]],[[],[],[],[],[2],[3]],[[],[],[],[],[2],[4]],[[],[],[],[],[2],[5]],[[],[],[],[],[2],[6]],[[],[],[],[],[2,1,2]],[[],[],[],[],[2,1,3]],[[],[],[],[],[2,1,4]],[[],[],[],[],[2,1,5]],[[],[],[],[],[2,2,2]],[[],[],[],[],[2,2,3]]]

theorem patterns_16_8_3_verified : ∀ D ∈ patterns_16_8_3, PatternVerified 16 8 D := by

  simp only [patterns_16_8_3, List.forall_mem_cons]

  exact ⟨⟨certificate_1800, certificate_1800_valid⟩, ⟨⟨certificate_1801, certificate_1801_valid⟩, ⟨⟨certificate_1802, certificate_1802_valid⟩, ⟨⟨certificate_1803, certificate_1803_valid⟩, ⟨⟨certificate_1804, certificate_1804_valid⟩, ⟨⟨certificate_1805, certificate_1805_valid⟩, ⟨⟨certificate_1806, certificate_1806_valid⟩, ⟨⟨certificate_1807, certificate_1807_valid⟩, ⟨⟨certificate_1808, certificate_1808_valid⟩, ⟨⟨certificate_1809, certificate_1809_valid⟩, ⟨⟨certificate_1810, certificate_1810_valid⟩, ⟨⟨certificate_1811, certificate_1811_valid⟩, ⟨⟨certificate_1812, certificate_1812_valid⟩, ⟨⟨certificate_1813, certificate_1813_valid⟩, ⟨⟨certificate_1814, certificate_1814_valid⟩, ⟨⟨certificate_1815, certificate_1815_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_4 : List (List (List ℕ)) := [[[],[],[],[],[2,2,4]],[[],[],[],[],[2,3,2]],[[],[],[],[],[2,3,3]],[[],[],[],[],[2,4,2]],[[],[],[],[],[3],[3]],[[],[],[],[],[3],[4]],[[],[],[],[],[3],[5]],[[],[],[],[],[3,1,3]],[[],[],[],[],[3,1,4]],[[],[],[],[],[3,2,3]],[[],[],[],[],[4],[4]],[[],[],[],[1],[1,1]],[[],[],[],[1],[1,2]],[[],[],[],[1],[1,3]],[[],[],[],[1],[1,4]],[[],[],[],[1],[1,5]]]

theorem patterns_16_8_4_verified : ∀ D ∈ patterns_16_8_4, PatternVerified 16 8 D := by

  simp only [patterns_16_8_4, List.forall_mem_cons]

  exact ⟨⟨certificate_1816, certificate_1816_valid⟩, ⟨⟨certificate_1817, certificate_1817_valid⟩, ⟨⟨certificate_1818, certificate_1818_valid⟩, ⟨⟨certificate_1819, certificate_1819_valid⟩, ⟨⟨certificate_1820, certificate_1820_valid⟩, ⟨⟨certificate_1821, certificate_1821_valid⟩, ⟨⟨certificate_1822, certificate_1822_valid⟩, ⟨⟨certificate_1823, certificate_1823_valid⟩, ⟨⟨certificate_1824, certificate_1824_valid⟩, ⟨⟨certificate_1825, certificate_1825_valid⟩, ⟨⟨certificate_1826, certificate_1826_valid⟩, ⟨⟨certificate_1827, certificate_1827_valid⟩, ⟨⟨certificate_1828, certificate_1828_valid⟩, ⟨⟨certificate_1829, certificate_1829_valid⟩, ⟨⟨certificate_1830, certificate_1830_valid⟩, ⟨⟨certificate_1831, certificate_1831_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_5 : List (List (List ℕ)) := [[[],[],[],[1],[1,6]],[[],[],[],[1],[2,2]],[[],[],[],[1],[2,3]],[[],[],[],[1],[2,4]],[[],[],[],[1],[2,5]],[[],[],[],[1],[3,3]],[[],[],[],[1],[3,4]],[[],[],[],[1,1],[2]],[[],[],[],[1,1],[3]],[[],[],[],[1,1],[4]],[[],[],[],[1,1],[5]],[[],[],[],[1,1],[6]],[[],[],[],[1,1,1,1]],[[],[],[],[1,1,1,2]],[[],[],[],[1,1,1,3]],[[],[],[],[1,1,1,4]]]

theorem patterns_16_8_5_verified : ∀ D ∈ patterns_16_8_5, PatternVerified 16 8 D := by

  simp only [patterns_16_8_5, List.forall_mem_cons]

  exact ⟨⟨certificate_1832, certificate_1832_valid⟩, ⟨⟨certificate_1833, certificate_1833_valid⟩, ⟨⟨certificate_1834, certificate_1834_valid⟩, ⟨⟨certificate_1835, certificate_1835_valid⟩, ⟨⟨certificate_1836, certificate_1836_valid⟩, ⟨⟨certificate_1837, certificate_1837_valid⟩, ⟨⟨certificate_1838, certificate_1838_valid⟩, ⟨⟨certificate_1839, certificate_1839_valid⟩, ⟨⟨certificate_1840, certificate_1840_valid⟩, ⟨⟨certificate_1841, certificate_1841_valid⟩, ⟨⟨certificate_1842, certificate_1842_valid⟩, ⟨⟨certificate_1843, certificate_1843_valid⟩, ⟨⟨certificate_1844, certificate_1844_valid⟩, ⟨⟨certificate_1845, certificate_1845_valid⟩, ⟨⟨certificate_1846, certificate_1846_valid⟩, ⟨⟨certificate_1847, certificate_1847_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_6 : List (List (List ℕ)) := [[[],[],[],[1,1,1,5]],[[],[],[],[1,1,2,1]],[[],[],[],[1,1,2,2]],[[],[],[],[1,1,2,3]],[[],[],[],[1,1,2,4]],[[],[],[],[1,1,3,1]],[[],[],[],[1,1,3,2]],[[],[],[],[1,1,3,3]],[[],[],[],[1,1,4,1]],[[],[],[],[1,1,4,2]],[[],[],[],[1,1,5,1]],[[],[],[],[1,2],[2]],[[],[],[],[1,2],[3]],[[],[],[],[1,2],[4]],[[],[],[],[1,2],[5]],[[],[],[],[1,2,1,2]]]

theorem patterns_16_8_6_verified : ∀ D ∈ patterns_16_8_6, PatternVerified 16 8 D := by

  simp only [patterns_16_8_6, List.forall_mem_cons]

  exact ⟨⟨certificate_1848, certificate_1848_valid⟩, ⟨⟨certificate_1849, certificate_1849_valid⟩, ⟨⟨certificate_1850, certificate_1850_valid⟩, ⟨⟨certificate_1851, certificate_1851_valid⟩, ⟨⟨certificate_1852, certificate_1852_valid⟩, ⟨⟨certificate_1853, certificate_1853_valid⟩, ⟨⟨certificate_1854, certificate_1854_valid⟩, ⟨⟨certificate_1855, certificate_1855_valid⟩, ⟨⟨certificate_1856, certificate_1856_valid⟩, ⟨⟨certificate_1857, certificate_1857_valid⟩, ⟨⟨certificate_1858, certificate_1858_valid⟩, ⟨⟨certificate_1859, certificate_1859_valid⟩, ⟨⟨certificate_1860, certificate_1860_valid⟩, ⟨⟨certificate_1861, certificate_1861_valid⟩, ⟨⟨certificate_1862, certificate_1862_valid⟩, ⟨⟨certificate_1863, certificate_1863_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_7 : List (List (List ℕ)) := [[[],[],[],[1,2,1,3]],[[],[],[],[1,2,1,4]],[[],[],[],[1,2,2,1]],[[],[],[],[1,2,2,2]],[[],[],[],[1,2,2,3]],[[],[],[],[1,2,3,1]],[[],[],[],[1,2,3,2]],[[],[],[],[1,2,4,1]],[[],[],[],[1,3],[2]],[[],[],[],[1,3],[3]],[[],[],[],[1,3],[4]],[[],[],[],[1,3,1,2]],[[],[],[],[1,3,1,3]],[[],[],[],[1,3,2,2]],[[],[],[],[1,3,3,1]],[[],[],[],[1,4],[2]]]

theorem patterns_16_8_7_verified : ∀ D ∈ patterns_16_8_7, PatternVerified 16 8 D := by

  simp only [patterns_16_8_7, List.forall_mem_cons]

  exact ⟨⟨certificate_1864, certificate_1864_valid⟩, ⟨⟨certificate_1865, certificate_1865_valid⟩, ⟨⟨certificate_1866, certificate_1866_valid⟩, ⟨⟨certificate_1867, certificate_1867_valid⟩, ⟨⟨certificate_1868, certificate_1868_valid⟩, ⟨⟨certificate_1869, certificate_1869_valid⟩, ⟨⟨certificate_1870, certificate_1870_valid⟩, ⟨⟨certificate_1871, certificate_1871_valid⟩, ⟨⟨certificate_1872, certificate_1872_valid⟩, ⟨⟨certificate_1873, certificate_1873_valid⟩, ⟨⟨certificate_1874, certificate_1874_valid⟩, ⟨⟨certificate_1875, certificate_1875_valid⟩, ⟨⟨certificate_1876, certificate_1876_valid⟩, ⟨⟨certificate_1877, certificate_1877_valid⟩, ⟨⟨certificate_1878, certificate_1878_valid⟩, ⟨⟨certificate_1879, certificate_1879_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_8 : List (List (List ℕ)) := [[[],[],[],[1,4],[3]],[[],[],[],[1,4,1,2]],[[],[],[],[1,5],[2]],[[],[],[],[2],[2,2]],[[],[],[],[2],[2,3]],[[],[],[],[2],[2,4]],[[],[],[],[2],[3,3]],[[],[],[],[2,1,1,2]],[[],[],[],[2,1,1,3]],[[],[],[],[2,1,1,4]],[[],[],[],[2,1,2,2]],[[],[],[],[2,1,2,3]],[[],[],[],[2,1,3,2]],[[],[],[],[2,2],[3]],[[],[],[],[2,2],[4]],[[],[],[],[2,2,1,3]]]

theorem patterns_16_8_8_verified : ∀ D ∈ patterns_16_8_8, PatternVerified 16 8 D := by

  simp only [patterns_16_8_8, List.forall_mem_cons]

  exact ⟨⟨certificate_1880, certificate_1880_valid⟩, ⟨⟨certificate_1881, certificate_1881_valid⟩, ⟨⟨certificate_1882, certificate_1882_valid⟩, ⟨⟨certificate_1883, certificate_1883_valid⟩, ⟨⟨certificate_1884, certificate_1884_valid⟩, ⟨⟨certificate_1885, certificate_1885_valid⟩, ⟨⟨certificate_1886, certificate_1886_valid⟩, ⟨⟨certificate_1887, certificate_1887_valid⟩, ⟨⟨certificate_1888, certificate_1888_valid⟩, ⟨⟨certificate_1889, certificate_1889_valid⟩, ⟨⟨certificate_1890, certificate_1890_valid⟩, ⟨⟨certificate_1891, certificate_1891_valid⟩, ⟨⟨certificate_1892, certificate_1892_valid⟩, ⟨⟨certificate_1893, certificate_1893_valid⟩, ⟨⟨certificate_1894, certificate_1894_valid⟩, ⟨⟨certificate_1895, certificate_1895_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_9 : List (List (List ℕ)) := [[[],[],[],[2,2,2,2]],[[],[],[],[2,3],[3]],[[],[],[],[3,1,1,3]],[[],[],[1],[1],[1]],[[],[],[1],[1],[2]],[[],[],[1],[1],[3]],[[],[],[1],[1],[4]],[[],[],[1],[1],[5]],[[],[],[1],[1],[6]],[[],[],[1],[1,1,1]],[[],[],[1],[1,1,2]],[[],[],[1],[1,1,3]],[[],[],[1],[1,1,4]],[[],[],[1],[1,1,5]],[[],[],[1],[1,2,1]],[[],[],[1],[1,2,2]]]

theorem patterns_16_8_9_verified : ∀ D ∈ patterns_16_8_9, PatternVerified 16 8 D := by

  simp only [patterns_16_8_9, List.forall_mem_cons]

  exact ⟨⟨certificate_1896, certificate_1896_valid⟩, ⟨⟨certificate_1897, certificate_1897_valid⟩, ⟨⟨certificate_1898, certificate_1898_valid⟩, ⟨⟨certificate_1899, certificate_1899_valid⟩, ⟨⟨certificate_1900, certificate_1900_valid⟩, ⟨⟨certificate_1901, certificate_1901_valid⟩, ⟨⟨certificate_1902, certificate_1902_valid⟩, ⟨⟨certificate_1903, certificate_1903_valid⟩, ⟨⟨certificate_1904, certificate_1904_valid⟩, ⟨⟨certificate_1905, certificate_1905_valid⟩, ⟨⟨certificate_1906, certificate_1906_valid⟩, ⟨⟨certificate_1907, certificate_1907_valid⟩, ⟨⟨certificate_1908, certificate_1908_valid⟩, ⟨⟨certificate_1909, certificate_1909_valid⟩, ⟨⟨certificate_1910, certificate_1910_valid⟩, ⟨⟨certificate_1911, certificate_1911_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_10 : List (List (List ℕ)) := [[[],[],[1],[1,2,3]],[[],[],[1],[1,2,4]],[[],[],[1],[1,3,1]],[[],[],[1],[1,3,2]],[[],[],[1],[1,3,3]],[[],[],[1],[1,4,1]],[[],[],[1],[1,4,2]],[[],[],[1],[1,5,1]],[[],[],[1],[2],[2]],[[],[],[1],[2],[3]],[[],[],[1],[2],[4]],[[],[],[1],[2],[5]],[[],[],[1],[2,1,2]],[[],[],[1],[2,1,3]],[[],[],[1],[2,1,4]],[[],[],[1],[2,2,2]]]

theorem patterns_16_8_10_verified : ∀ D ∈ patterns_16_8_10, PatternVerified 16 8 D := by

  simp only [patterns_16_8_10, List.forall_mem_cons]

  exact ⟨⟨certificate_1912, certificate_1912_valid⟩, ⟨⟨certificate_1913, certificate_1913_valid⟩, ⟨⟨certificate_1914, certificate_1914_valid⟩, ⟨⟨certificate_1915, certificate_1915_valid⟩, ⟨⟨certificate_1916, certificate_1916_valid⟩, ⟨⟨certificate_1917, certificate_1917_valid⟩, ⟨⟨certificate_1918, certificate_1918_valid⟩, ⟨⟨certificate_1919, certificate_1919_valid⟩, ⟨⟨certificate_1920, certificate_1920_valid⟩, ⟨⟨certificate_1921, certificate_1921_valid⟩, ⟨⟨certificate_1922, certificate_1922_valid⟩, ⟨⟨certificate_1923, certificate_1923_valid⟩, ⟨⟨certificate_1924, certificate_1924_valid⟩, ⟨⟨certificate_1925, certificate_1925_valid⟩, ⟨⟨certificate_1926, certificate_1926_valid⟩, ⟨⟨certificate_1927, certificate_1927_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_11 : List (List (List ℕ)) := [[[],[],[1],[2,2,3]],[[],[],[1],[2,3,2]],[[],[],[1],[3],[3]],[[],[],[1],[3],[4]],[[],[],[1],[3,1,3]],[[],[],[1,1],[1,1]],[[],[],[1,1],[1,2]],[[],[],[1,1],[1,3]],[[],[],[1,1],[1,4]],[[],[],[1,1],[1,5]],[[],[],[1,1],[2,2]],[[],[],[1,1],[2,3]],[[],[],[1,1],[2,4]],[[],[],[1,1],[3,3]],[[],[],[1,1,1],[2]],[[],[],[1,1,1],[3]]]

theorem patterns_16_8_11_verified : ∀ D ∈ patterns_16_8_11, PatternVerified 16 8 D := by

  simp only [patterns_16_8_11, List.forall_mem_cons]

  exact ⟨⟨certificate_1928, certificate_1928_valid⟩, ⟨⟨certificate_1929, certificate_1929_valid⟩, ⟨⟨certificate_1930, certificate_1930_valid⟩, ⟨⟨certificate_1931, certificate_1931_valid⟩, ⟨⟨certificate_1932, certificate_1932_valid⟩, ⟨⟨certificate_1933, certificate_1933_valid⟩, ⟨⟨certificate_1934, certificate_1934_valid⟩, ⟨⟨certificate_1935, certificate_1935_valid⟩, ⟨⟨certificate_1936, certificate_1936_valid⟩, ⟨⟨certificate_1937, certificate_1937_valid⟩, ⟨⟨certificate_1938, certificate_1938_valid⟩, ⟨⟨certificate_1939, certificate_1939_valid⟩, ⟨⟨certificate_1940, certificate_1940_valid⟩, ⟨⟨certificate_1941, certificate_1941_valid⟩, ⟨⟨certificate_1942, certificate_1942_valid⟩, ⟨⟨certificate_1943, certificate_1943_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_12 : List (List (List ℕ)) := [[[],[],[1,1,1],[4]],[[],[],[1,1,1],[5]],[[],[],[1,1,1,1,1]],[[],[],[1,1,1,1,2]],[[],[],[1,1,1,1,3]],[[],[],[1,1,1,1,4]],[[],[],[1,1,1,2,1]],[[],[],[1,1,1,2,2]],[[],[],[1,1,1,2,3]],[[],[],[1,1,1,3,1]],[[],[],[1,1,1,3,2]],[[],[],[1,1,1,4,1]],[[],[],[1,1,2],[2]],[[],[],[1,1,2],[3]],[[],[],[1,1,2],[4]],[[],[],[1,1,2,1,1]]]

theorem patterns_16_8_12_verified : ∀ D ∈ patterns_16_8_12, PatternVerified 16 8 D := by

  simp only [patterns_16_8_12, List.forall_mem_cons]

  exact ⟨⟨certificate_1944, certificate_1944_valid⟩, ⟨⟨certificate_1945, certificate_1945_valid⟩, ⟨⟨certificate_1946, certificate_1946_valid⟩, ⟨⟨certificate_1947, certificate_1947_valid⟩, ⟨⟨certificate_1948, certificate_1948_valid⟩, ⟨⟨certificate_1949, certificate_1949_valid⟩, ⟨⟨certificate_1950, certificate_1950_valid⟩, ⟨⟨certificate_1951, certificate_1951_valid⟩, ⟨⟨certificate_1952, certificate_1952_valid⟩, ⟨⟨certificate_1953, certificate_1953_valid⟩, ⟨⟨certificate_1954, certificate_1954_valid⟩, ⟨⟨certificate_1955, certificate_1955_valid⟩, ⟨⟨certificate_1956, certificate_1956_valid⟩, ⟨⟨certificate_1957, certificate_1957_valid⟩, ⟨⟨certificate_1958, certificate_1958_valid⟩, ⟨⟨certificate_1959, certificate_1959_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_13 : List (List (List ℕ)) := [[[],[],[1,1,2,1,2]],[[],[],[1,1,2,1,3]],[[],[],[1,1,2,2,1]],[[],[],[1,1,2,2,2]],[[],[],[1,1,2,3,1]],[[],[],[1,1,3],[2]],[[],[],[1,1,3],[3]],[[],[],[1,1,3,1,1]],[[],[],[1,1,3,1,2]],[[],[],[1,1,3,2,1]],[[],[],[1,1,4],[2]],[[],[],[1,1,4,1,1]],[[],[],[1,2],[1,2]],[[],[],[1,2],[1,3]],[[],[],[1,2],[1,4]],[[],[],[1,2],[2,2]]]

theorem patterns_16_8_13_verified : ∀ D ∈ patterns_16_8_13, PatternVerified 16 8 D := by

  simp only [patterns_16_8_13, List.forall_mem_cons]

  exact ⟨⟨certificate_1960, certificate_1960_valid⟩, ⟨⟨certificate_1961, certificate_1961_valid⟩, ⟨⟨certificate_1962, certificate_1962_valid⟩, ⟨⟨certificate_1963, certificate_1963_valid⟩, ⟨⟨certificate_1964, certificate_1964_valid⟩, ⟨⟨certificate_1965, certificate_1965_valid⟩, ⟨⟨certificate_1966, certificate_1966_valid⟩, ⟨⟨certificate_1967, certificate_1967_valid⟩, ⟨⟨certificate_1968, certificate_1968_valid⟩, ⟨⟨certificate_1969, certificate_1969_valid⟩, ⟨⟨certificate_1970, certificate_1970_valid⟩, ⟨⟨certificate_1971, certificate_1971_valid⟩, ⟨⟨certificate_1972, certificate_1972_valid⟩, ⟨⟨certificate_1973, certificate_1973_valid⟩, ⟨⟨certificate_1974, certificate_1974_valid⟩, ⟨⟨certificate_1975, certificate_1975_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_14 : List (List (List ℕ)) := [[[],[],[1,2],[2,3]],[[],[],[1,2,1],[2]],[[],[],[1,2,1],[3]],[[],[],[1,2,1],[4]],[[],[],[1,2,1,1,2]],[[],[],[1,2,1,1,3]],[[],[],[1,2,1,2,1]],[[],[],[1,2,1,2,2]],[[],[],[1,2,1,3,1]],[[],[],[1,2,2],[2]],[[],[],[1,2,2],[3]],[[],[],[1,2,2,1,2]],[[],[],[1,2,2,2,1]],[[],[],[1,2,3],[2]],[[],[],[1,3],[1,3]],[[],[],[1,3],[2,2]]]

theorem patterns_16_8_14_verified : ∀ D ∈ patterns_16_8_14, PatternVerified 16 8 D := by

  simp only [patterns_16_8_14, List.forall_mem_cons]

  exact ⟨⟨certificate_1976, certificate_1976_valid⟩, ⟨⟨certificate_1977, certificate_1977_valid⟩, ⟨⟨certificate_1978, certificate_1978_valid⟩, ⟨⟨certificate_1979, certificate_1979_valid⟩, ⟨⟨certificate_1980, certificate_1980_valid⟩, ⟨⟨certificate_1981, certificate_1981_valid⟩, ⟨⟨certificate_1982, certificate_1982_valid⟩, ⟨⟨certificate_1983, certificate_1983_valid⟩, ⟨⟨certificate_1984, certificate_1984_valid⟩, ⟨⟨certificate_1985, certificate_1985_valid⟩, ⟨⟨certificate_1986, certificate_1986_valid⟩, ⟨⟨certificate_1987, certificate_1987_valid⟩, ⟨⟨certificate_1988, certificate_1988_valid⟩, ⟨⟨certificate_1989, certificate_1989_valid⟩, ⟨⟨certificate_1990, certificate_1990_valid⟩, ⟨⟨certificate_1991, certificate_1991_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_15 : List (List (List ℕ)) := [[[],[],[1,3,1],[2]],[[],[],[1,3,1],[3]],[[],[],[1,3,1,1,2]],[[],[],[1,3,2],[2]],[[],[],[1,4,1],[2]],[[],[],[2],[2],[2]],[[],[],[2],[2],[3]],[[],[],[2],[2],[4]],[[],[],[2],[2,1,2]],[[],[],[2],[2,1,3]],[[],[],[2],[2,2,2]],[[],[],[2],[3],[3]],[[],[],[2,1,1,1,2]],[[],[],[2,1,1,1,3]],[[],[],[2,1,1,2,2]],[[],[],[2,1,2],[3]]]

theorem patterns_16_8_15_verified : ∀ D ∈ patterns_16_8_15, PatternVerified 16 8 D := by

  simp only [patterns_16_8_15, List.forall_mem_cons]

  exact ⟨⟨certificate_1992, certificate_1992_valid⟩, ⟨⟨certificate_1993, certificate_1993_valid⟩, ⟨⟨certificate_1994, certificate_1994_valid⟩, ⟨⟨certificate_1995, certificate_1995_valid⟩, ⟨⟨certificate_1996, certificate_1996_valid⟩, ⟨⟨certificate_1997, certificate_1997_valid⟩, ⟨⟨certificate_1998, certificate_1998_valid⟩, ⟨⟨certificate_1999, certificate_1999_valid⟩, ⟨⟨certificate_2000, certificate_2000_valid⟩, ⟨⟨certificate_2001, certificate_2001_valid⟩, ⟨⟨certificate_2002, certificate_2002_valid⟩, ⟨⟨certificate_2003, certificate_2003_valid⟩, ⟨⟨certificate_2004, certificate_2004_valid⟩, ⟨⟨certificate_2005, certificate_2005_valid⟩, ⟨⟨certificate_2006, certificate_2006_valid⟩, ⟨⟨certificate_2007, certificate_2007_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_16 : List (List (List ℕ)) := [[[],[],[2,1,2,1,2]],[[],[],[2,2],[2,2]],[[],[1],[1],[1,1]],[[],[1],[1],[1,2]],[[],[1],[1],[1,3]],[[],[1],[1],[1,4]],[[],[1],[1],[1,5]],[[],[1],[1],[2,2]],[[],[1],[1],[2,3]],[[],[1],[1],[2,4]],[[],[1],[1],[3,3]],[[],[1],[1,1],[2]],[[],[1],[1,1],[3]],[[],[1],[1,1],[4]],[[],[1],[1,1],[5]],[[],[1],[1,1,1,1]]]

theorem patterns_16_8_16_verified : ∀ D ∈ patterns_16_8_16, PatternVerified 16 8 D := by

  simp only [patterns_16_8_16, List.forall_mem_cons]

  exact ⟨⟨certificate_2008, certificate_2008_valid⟩, ⟨⟨certificate_2009, certificate_2009_valid⟩, ⟨⟨certificate_2010, certificate_2010_valid⟩, ⟨⟨certificate_2011, certificate_2011_valid⟩, ⟨⟨certificate_2012, certificate_2012_valid⟩, ⟨⟨certificate_2013, certificate_2013_valid⟩, ⟨⟨certificate_2014, certificate_2014_valid⟩, ⟨⟨certificate_2015, certificate_2015_valid⟩, ⟨⟨certificate_2016, certificate_2016_valid⟩, ⟨⟨certificate_2017, certificate_2017_valid⟩, ⟨⟨certificate_2018, certificate_2018_valid⟩, ⟨⟨certificate_2019, certificate_2019_valid⟩, ⟨⟨certificate_2020, certificate_2020_valid⟩, ⟨⟨certificate_2021, certificate_2021_valid⟩, ⟨⟨certificate_2022, certificate_2022_valid⟩, ⟨⟨certificate_2023, certificate_2023_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_17 : List (List (List ℕ)) := [[[],[1],[1,1,1,2]],[[],[1],[1,1,1,3]],[[],[1],[1,1,1,4]],[[],[1],[1,1,2,1]],[[],[1],[1,1,2,2]],[[],[1],[1,1,2,3]],[[],[1],[1,1,3,1]],[[],[1],[1,1,3,2]],[[],[1],[1,1,4,1]],[[],[1],[1,2],[2]],[[],[1],[1,2],[3]],[[],[1],[1,2],[4]],[[],[1],[1,2,1,2]],[[],[1],[1,2,1,3]],[[],[1],[1,2,2,1]],[[],[1],[1,2,2,2]]]

theorem patterns_16_8_17_verified : ∀ D ∈ patterns_16_8_17, PatternVerified 16 8 D := by

  simp only [patterns_16_8_17, List.forall_mem_cons]

  exact ⟨⟨certificate_2024, certificate_2024_valid⟩, ⟨⟨certificate_2025, certificate_2025_valid⟩, ⟨⟨certificate_2026, certificate_2026_valid⟩, ⟨⟨certificate_2027, certificate_2027_valid⟩, ⟨⟨certificate_2028, certificate_2028_valid⟩, ⟨⟨certificate_2029, certificate_2029_valid⟩, ⟨⟨certificate_2030, certificate_2030_valid⟩, ⟨⟨certificate_2031, certificate_2031_valid⟩, ⟨⟨certificate_2032, certificate_2032_valid⟩, ⟨⟨certificate_2033, certificate_2033_valid⟩, ⟨⟨certificate_2034, certificate_2034_valid⟩, ⟨⟨certificate_2035, certificate_2035_valid⟩, ⟨⟨certificate_2036, certificate_2036_valid⟩, ⟨⟨certificate_2037, certificate_2037_valid⟩, ⟨⟨certificate_2038, certificate_2038_valid⟩, ⟨⟨certificate_2039, certificate_2039_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_18 : List (List (List ℕ)) := [[[],[1],[1,2,3,1]],[[],[1],[1,3],[2]],[[],[1],[1,3],[3]],[[],[1],[1,3,1,2]],[[],[1],[1,4],[2]],[[],[1],[2],[2,2]],[[],[1],[2],[2,3]],[[],[1],[2,1,1,2]],[[],[1],[2,1,1,3]],[[],[1],[2,1,2,2]],[[],[1],[2,2],[3]],[[],[1,1],[1,1,1]],[[],[1,1],[1,1,2]],[[],[1,1],[1,1,3]],[[],[1,1],[1,1,4]],[[],[1,1],[1,2,1]]]

theorem patterns_16_8_18_verified : ∀ D ∈ patterns_16_8_18, PatternVerified 16 8 D := by

  simp only [patterns_16_8_18, List.forall_mem_cons]

  exact ⟨⟨certificate_2040, certificate_2040_valid⟩, ⟨⟨certificate_2041, certificate_2041_valid⟩, ⟨⟨certificate_2042, certificate_2042_valid⟩, ⟨⟨certificate_2043, certificate_2043_valid⟩, ⟨⟨certificate_2044, certificate_2044_valid⟩, ⟨⟨certificate_2045, certificate_2045_valid⟩, ⟨⟨certificate_2046, certificate_2046_valid⟩, ⟨⟨certificate_2047, certificate_2047_valid⟩, ⟨⟨certificate_2048, certificate_2048_valid⟩, ⟨⟨certificate_2049, certificate_2049_valid⟩, ⟨⟨certificate_2050, certificate_2050_valid⟩, ⟨⟨certificate_2051, certificate_2051_valid⟩, ⟨⟨certificate_2052, certificate_2052_valid⟩, ⟨⟨certificate_2053, certificate_2053_valid⟩, ⟨⟨certificate_2054, certificate_2054_valid⟩, ⟨⟨certificate_2055, certificate_2055_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_19 : List (List (List ℕ)) := [[[],[1,1],[1,2,2]],[[],[1,1],[1,2,3]],[[],[1,1],[1,3,1]],[[],[1,1],[1,3,2]],[[],[1,1],[1,4,1]],[[],[1,1],[2],[2]],[[],[1,1],[2],[3]],[[],[1,1],[2],[4]],[[],[1,1],[2,1,2]],[[],[1,1],[2,1,3]],[[],[1,1],[2,2,2]],[[],[1,1],[3],[3]],[[],[1,1,1],[1,2]],[[],[1,1,1],[1,3]],[[],[1,1,1],[1,4]],[[],[1,1,1],[2,2]]]

theorem patterns_16_8_19_verified : ∀ D ∈ patterns_16_8_19, PatternVerified 16 8 D := by

  simp only [patterns_16_8_19, List.forall_mem_cons]

  exact ⟨⟨certificate_2056, certificate_2056_valid⟩, ⟨⟨certificate_2057, certificate_2057_valid⟩, ⟨⟨certificate_2058, certificate_2058_valid⟩, ⟨⟨certificate_2059, certificate_2059_valid⟩, ⟨⟨certificate_2060, certificate_2060_valid⟩, ⟨⟨certificate_2061, certificate_2061_valid⟩, ⟨⟨certificate_2062, certificate_2062_valid⟩, ⟨⟨certificate_2063, certificate_2063_valid⟩, ⟨⟨certificate_2064, certificate_2064_valid⟩, ⟨⟨certificate_2065, certificate_2065_valid⟩, ⟨⟨certificate_2066, certificate_2066_valid⟩, ⟨⟨certificate_2067, certificate_2067_valid⟩, ⟨⟨certificate_2068, certificate_2068_valid⟩, ⟨⟨certificate_2069, certificate_2069_valid⟩, ⟨⟨certificate_2070, certificate_2070_valid⟩, ⟨⟨certificate_2071, certificate_2071_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_20 : List (List (List ℕ)) := [[[],[1,1,1],[2,3]],[[],[1,1,1,1],[2]],[[],[1,1,1,1],[3]],[[],[1,1,1,1],[4]],[[],[1,1,1,1,1,1]],[[],[1,1,1,1,1,2]],[[],[1,1,1,1,1,3]],[[],[1,1,1,1,2,1]],[[],[1,1,1,1,2,2]],[[],[1,1,1,1,3,1]],[[],[1,1,1,2],[2]],[[],[1,1,1,2],[3]],[[],[1,1,1,2,1,1]],[[],[1,1,1,2,1,2]],[[],[1,1,1,2,2,1]],[[],[1,1,1,3],[2]]]

theorem patterns_16_8_20_verified : ∀ D ∈ patterns_16_8_20, PatternVerified 16 8 D := by

  simp only [patterns_16_8_20, List.forall_mem_cons]

  exact ⟨⟨certificate_2072, certificate_2072_valid⟩, ⟨⟨certificate_2073, certificate_2073_valid⟩, ⟨⟨certificate_2074, certificate_2074_valid⟩, ⟨⟨certificate_2075, certificate_2075_valid⟩, ⟨⟨certificate_2076, certificate_2076_valid⟩, ⟨⟨certificate_2077, certificate_2077_valid⟩, ⟨⟨certificate_2078, certificate_2078_valid⟩, ⟨⟨certificate_2079, certificate_2079_valid⟩, ⟨⟨certificate_2080, certificate_2080_valid⟩, ⟨⟨certificate_2081, certificate_2081_valid⟩, ⟨⟨certificate_2082, certificate_2082_valid⟩, ⟨⟨certificate_2083, certificate_2083_valid⟩, ⟨⟨certificate_2084, certificate_2084_valid⟩, ⟨⟨certificate_2085, certificate_2085_valid⟩, ⟨⟨certificate_2086, certificate_2086_valid⟩, ⟨⟨certificate_2087, certificate_2087_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_21 : List (List (List ℕ)) := [[[],[1,1,1,3,1,1]],[[],[1,1,2],[1,2]],[[],[1,1,2],[1,3]],[[],[1,1,2],[2,2]],[[],[1,1,2,1],[2]],[[],[1,1,2,1],[3]],[[],[1,1,2,1,1,2]],[[],[1,1,2,1,2,1]],[[],[1,1,2,2],[2]],[[],[1,1,2,2,1,1]],[[],[1,1,3],[1,2]],[[],[1,1,3,1],[2]],[[],[1,2],[1,2,1]],[[],[1,2],[1,2,2]],[[],[1,2],[1,3,1]],[[],[1,2],[2],[2]]]

theorem patterns_16_8_21_verified : ∀ D ∈ patterns_16_8_21, PatternVerified 16 8 D := by

  simp only [patterns_16_8_21, List.forall_mem_cons]

  exact ⟨⟨certificate_2088, certificate_2088_valid⟩, ⟨⟨certificate_2089, certificate_2089_valid⟩, ⟨⟨certificate_2090, certificate_2090_valid⟩, ⟨⟨certificate_2091, certificate_2091_valid⟩, ⟨⟨certificate_2092, certificate_2092_valid⟩, ⟨⟨certificate_2093, certificate_2093_valid⟩, ⟨⟨certificate_2094, certificate_2094_valid⟩, ⟨⟨certificate_2095, certificate_2095_valid⟩, ⟨⟨certificate_2096, certificate_2096_valid⟩, ⟨⟨certificate_2097, certificate_2097_valid⟩, ⟨⟨certificate_2098, certificate_2098_valid⟩, ⟨⟨certificate_2099, certificate_2099_valid⟩, ⟨⟨certificate_2100, certificate_2100_valid⟩, ⟨⟨certificate_2101, certificate_2101_valid⟩, ⟨⟨certificate_2102, certificate_2102_valid⟩, ⟨⟨certificate_2103, certificate_2103_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_22 : List (List (List ℕ)) := [[[],[1,2],[2],[3]],[[],[1,2],[2,1,2]],[[],[1,2,1],[1,3]],[[],[1,2,1],[2,2]],[[],[1,2,1,1,1,2]],[[],[1,2,1,1,2,1]],[[],[1,2,1,2],[2]],[[],[1,2,2,1],[2]],[[],[1,3],[2],[2]],[[],[2],[2],[2,2]],[[],[2],[2,1,1,2]],[[],[2,1,1,1,1,2]],[[1],[1],[1],[1]],[[1],[1],[1],[2]],[[1],[1],[1],[3]],[[1],[1],[1],[4]]]

theorem patterns_16_8_22_verified : ∀ D ∈ patterns_16_8_22, PatternVerified 16 8 D := by

  simp only [patterns_16_8_22, List.forall_mem_cons]

  exact ⟨⟨certificate_2104, certificate_2104_valid⟩, ⟨⟨certificate_2105, certificate_2105_valid⟩, ⟨⟨certificate_2106, certificate_2106_valid⟩, ⟨⟨certificate_2107, certificate_2107_valid⟩, ⟨⟨certificate_2108, certificate_2108_valid⟩, ⟨⟨certificate_2109, certificate_2109_valid⟩, ⟨⟨certificate_2110, certificate_2110_valid⟩, ⟨⟨certificate_2111, certificate_2111_valid⟩, ⟨⟨certificate_2112, certificate_2112_valid⟩, ⟨⟨certificate_2113, certificate_2113_valid⟩, ⟨⟨certificate_2114, certificate_2114_valid⟩, ⟨⟨certificate_2115, certificate_2115_valid⟩, ⟨⟨certificate_2116, certificate_2116_valid⟩, ⟨⟨certificate_2117, certificate_2117_valid⟩, ⟨⟨certificate_2118, certificate_2118_valid⟩, ⟨⟨certificate_2119, certificate_2119_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_23 : List (List (List ℕ)) := [[[1],[1],[1],[5]],[[1],[1],[1,1,1]],[[1],[1],[1,1,2]],[[1],[1],[1,1,3]],[[1],[1],[1,1,4]],[[1],[1],[1,2,1]],[[1],[1],[1,2,2]],[[1],[1],[1,2,3]],[[1],[1],[1,3,1]],[[1],[1],[1,3,2]],[[1],[1],[1,4,1]],[[1],[1],[2],[2]],[[1],[1],[2],[3]],[[1],[1],[2],[4]],[[1],[1],[2,1,2]],[[1],[1],[2,1,3]]]

theorem patterns_16_8_23_verified : ∀ D ∈ patterns_16_8_23, PatternVerified 16 8 D := by

  simp only [patterns_16_8_23, List.forall_mem_cons]

  exact ⟨⟨certificate_2120, certificate_2120_valid⟩, ⟨⟨certificate_2121, certificate_2121_valid⟩, ⟨⟨certificate_2122, certificate_2122_valid⟩, ⟨⟨certificate_2123, certificate_2123_valid⟩, ⟨⟨certificate_2124, certificate_2124_valid⟩, ⟨⟨certificate_2125, certificate_2125_valid⟩, ⟨⟨certificate_2126, certificate_2126_valid⟩, ⟨⟨certificate_2127, certificate_2127_valid⟩, ⟨⟨certificate_2128, certificate_2128_valid⟩, ⟨⟨certificate_2129, certificate_2129_valid⟩, ⟨⟨certificate_2130, certificate_2130_valid⟩, ⟨⟨certificate_2131, certificate_2131_valid⟩, ⟨⟨certificate_2132, certificate_2132_valid⟩, ⟨⟨certificate_2133, certificate_2133_valid⟩, ⟨⟨certificate_2134, certificate_2134_valid⟩, ⟨⟨certificate_2135, certificate_2135_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_24 : List (List (List ℕ)) := [[[1],[1],[2,2,2]],[[1],[1],[3],[3]],[[1],[1,1],[1,1]],[[1],[1,1],[1,2]],[[1],[1,1],[1,3]],[[1],[1,1],[1,4]],[[1],[1,1],[2,2]],[[1],[1,1],[2,3]],[[1],[1,1,1],[2]],[[1],[1,1,1],[3]],[[1],[1,1,1],[4]],[[1],[1,1,1,1,1]],[[1],[1,1,1,1,2]],[[1],[1,1,1,1,3]],[[1],[1,1,1,2,1]],[[1],[1,1,1,2,2]]]

theorem patterns_16_8_24_verified : ∀ D ∈ patterns_16_8_24, PatternVerified 16 8 D := by

  simp only [patterns_16_8_24, List.forall_mem_cons]

  exact ⟨⟨certificate_2136, certificate_2136_valid⟩, ⟨⟨certificate_2137, certificate_2137_valid⟩, ⟨⟨certificate_2138, certificate_2138_valid⟩, ⟨⟨certificate_2139, certificate_2139_valid⟩, ⟨⟨certificate_2140, certificate_2140_valid⟩, ⟨⟨certificate_2141, certificate_2141_valid⟩, ⟨⟨certificate_2142, certificate_2142_valid⟩, ⟨⟨certificate_2143, certificate_2143_valid⟩, ⟨⟨certificate_2144, certificate_2144_valid⟩, ⟨⟨certificate_2145, certificate_2145_valid⟩, ⟨⟨certificate_2146, certificate_2146_valid⟩, ⟨⟨certificate_2147, certificate_2147_valid⟩, ⟨⟨certificate_2148, certificate_2148_valid⟩, ⟨⟨certificate_2149, certificate_2149_valid⟩, ⟨⟨certificate_2150, certificate_2150_valid⟩, ⟨⟨certificate_2151, certificate_2151_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_25 : List (List (List ℕ)) := [[[1],[1,1,1,3,1]],[[1],[1,1,2],[2]],[[1],[1,1,2],[3]],[[1],[1,1,2,1,1]],[[1],[1,1,2,1,2]],[[1],[1,1,2,2,1]],[[1],[1,1,3],[2]],[[1],[1,1,3,1,1]],[[1],[1,2],[1,2]],[[1],[1,2],[1,3]],[[1],[1,2],[2,2]],[[1],[1,2,1],[2]],[[1],[1,2,1],[3]],[[1],[1,2,1,1,2]],[[1],[1,2,1,2,1]],[[1],[1,2,2],[2]]]

theorem patterns_16_8_25_verified : ∀ D ∈ patterns_16_8_25, PatternVerified 16 8 D := by

  simp only [patterns_16_8_25, List.forall_mem_cons]

  exact ⟨⟨certificate_2152, certificate_2152_valid⟩, ⟨⟨certificate_2153, certificate_2153_valid⟩, ⟨⟨certificate_2154, certificate_2154_valid⟩, ⟨⟨certificate_2155, certificate_2155_valid⟩, ⟨⟨certificate_2156, certificate_2156_valid⟩, ⟨⟨certificate_2157, certificate_2157_valid⟩, ⟨⟨certificate_2158, certificate_2158_valid⟩, ⟨⟨certificate_2159, certificate_2159_valid⟩, ⟨⟨certificate_2160, certificate_2160_valid⟩, ⟨⟨certificate_2161, certificate_2161_valid⟩, ⟨⟨certificate_2162, certificate_2162_valid⟩, ⟨⟨certificate_2163, certificate_2163_valid⟩, ⟨⟨certificate_2164, certificate_2164_valid⟩, ⟨⟨certificate_2165, certificate_2165_valid⟩, ⟨⟨certificate_2166, certificate_2166_valid⟩, ⟨⟨certificate_2167, certificate_2167_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_26 : List (List (List ℕ)) := [[[1],[1,3,1],[2]],[[1],[2],[2],[2]],[[1],[2],[2],[3]],[[1],[2],[2,1,2]],[[1],[2,1,1,1,2]],[[1,1],[1,1],[2]],[[1,1],[1,1],[3]],[[1,1],[1,1],[4]],[[1,1],[1,1,1,1]],[[1,1],[1,1,1,2]],[[1,1],[1,1,1,3]],[[1,1],[1,1,2,1]],[[1,1],[1,1,2,2]],[[1,1],[1,1,3,1]],[[1,1],[1,2],[2]],[[1,1],[1,2],[3]]]

theorem patterns_16_8_26_verified : ∀ D ∈ patterns_16_8_26, PatternVerified 16 8 D := by

  simp only [patterns_16_8_26, List.forall_mem_cons]

  exact ⟨⟨certificate_2168, certificate_2168_valid⟩, ⟨⟨certificate_2169, certificate_2169_valid⟩, ⟨⟨certificate_2170, certificate_2170_valid⟩, ⟨⟨certificate_2171, certificate_2171_valid⟩, ⟨⟨certificate_2172, certificate_2172_valid⟩, ⟨⟨certificate_2173, certificate_2173_valid⟩, ⟨⟨certificate_2174, certificate_2174_valid⟩, ⟨⟨certificate_2175, certificate_2175_valid⟩, ⟨⟨certificate_2176, certificate_2176_valid⟩, ⟨⟨certificate_2177, certificate_2177_valid⟩, ⟨⟨certificate_2178, certificate_2178_valid⟩, ⟨⟨certificate_2179, certificate_2179_valid⟩, ⟨⟨certificate_2180, certificate_2180_valid⟩, ⟨⟨certificate_2181, certificate_2181_valid⟩, ⟨⟨certificate_2182, certificate_2182_valid⟩, ⟨⟨certificate_2183, certificate_2183_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_27 : List (List (List ℕ)) := [[[1,1],[1,2,1,2]],[[1,1],[1,2,2,1]],[[1,1],[1,3],[2]],[[1,1],[2],[2,2]],[[1,1],[2,1,1,2]],[[1,1,1],[1,1,1]],[[1,1,1],[1,1,2]],[[1,1,1],[1,1,3]],[[1,1,1],[1,2,1]],[[1,1,1],[1,2,2]],[[1,1,1],[1,3,1]],[[1,1,1],[2],[2]],[[1,1,1],[2],[3]],[[1,1,1],[2,1,2]],[[1,1,1,1],[1,2]],[[1,1,1,1],[1,3]]]

theorem patterns_16_8_27_verified : ∀ D ∈ patterns_16_8_27, PatternVerified 16 8 D := by

  simp only [patterns_16_8_27, List.forall_mem_cons]

  exact ⟨⟨certificate_2184, certificate_2184_valid⟩, ⟨⟨certificate_2185, certificate_2185_valid⟩, ⟨⟨certificate_2186, certificate_2186_valid⟩, ⟨⟨certificate_2187, certificate_2187_valid⟩, ⟨⟨certificate_2188, certificate_2188_valid⟩, ⟨⟨certificate_2189, certificate_2189_valid⟩, ⟨⟨certificate_2190, certificate_2190_valid⟩, ⟨⟨certificate_2191, certificate_2191_valid⟩, ⟨⟨certificate_2192, certificate_2192_valid⟩, ⟨⟨certificate_2193, certificate_2193_valid⟩, ⟨⟨certificate_2194, certificate_2194_valid⟩, ⟨⟨certificate_2195, certificate_2195_valid⟩, ⟨⟨certificate_2196, certificate_2196_valid⟩, ⟨⟨certificate_2197, certificate_2197_valid⟩, ⟨⟨certificate_2198, certificate_2198_valid⟩, ⟨⟨certificate_2199, certificate_2199_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_28 : List (List (List ℕ)) := [[[1,1,1,1],[2,2]],[[1,1,1,1,1],[2]],[[1,1,1,1,1],[3]],[[1,1,1,1,1,1,1]],[[1,1,1,1,1,1,2]],[[1,1,1,1,1,2,1]],[[1,1,1,1,2],[2]],[[1,1,1,1,2,1,1]],[[1,1,1,2],[1,2]],[[1,1,1,2,1],[2]],[[1,1,1,2,1,1,1]],[[1,1,2],[1,1,2]],[[1,1,2],[1,2,1]],[[1,1,2],[2],[2]],[[1,1,2,1],[1,2]],[[1,1,2,1,1],[2]]]

theorem patterns_16_8_28_verified : ∀ D ∈ patterns_16_8_28, PatternVerified 16 8 D := by

  simp only [patterns_16_8_28, List.forall_mem_cons]

  exact ⟨⟨certificate_2200, certificate_2200_valid⟩, ⟨⟨certificate_2201, certificate_2201_valid⟩, ⟨⟨certificate_2202, certificate_2202_valid⟩, ⟨⟨certificate_2203, certificate_2203_valid⟩, ⟨⟨certificate_2204, certificate_2204_valid⟩, ⟨⟨certificate_2205, certificate_2205_valid⟩, ⟨⟨certificate_2206, certificate_2206_valid⟩, ⟨⟨certificate_2207, certificate_2207_valid⟩, ⟨⟨certificate_2208, certificate_2208_valid⟩, ⟨⟨certificate_2209, certificate_2209_valid⟩, ⟨⟨certificate_2210, certificate_2210_valid⟩, ⟨⟨certificate_2211, certificate_2211_valid⟩, ⟨⟨certificate_2212, certificate_2212_valid⟩, ⟨⟨certificate_2213, certificate_2213_valid⟩, ⟨⟨certificate_2214, certificate_2214_valid⟩, ⟨⟨certificate_2215, certificate_2215_valid⟩, (by simp)⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

noncomputable def patterns_16_8_29 : List (List (List ℕ)) := [[[1,2],[1,2],[2]],[[1,2,1],[1,2,1]],[[1,2,1],[2],[2]],[[2],[2],[2],[2]]]

theorem patterns_16_8_29_verified : ∀ D ∈ patterns_16_8_29, PatternVerified 16 8 D := by

  simp only [patterns_16_8_29, List.forall_mem_cons]

  exact ⟨⟨certificate_2216, certificate_2216_valid⟩, ⟨⟨certificate_2217, certificate_2217_valid⟩, ⟨⟨certificate_2218, certificate_2218_valid⟩, ⟨⟨certificate_2219, certificate_2219_valid⟩, (by simp)⟩⟩⟩⟩

noncomputable def patterns_16_8 : List (List (List ℕ)) := patterns_16_8_0 ++ (patterns_16_8_1 ++ (patterns_16_8_2 ++ (patterns_16_8_3 ++ (patterns_16_8_4 ++ (patterns_16_8_5 ++ (patterns_16_8_6 ++ (patterns_16_8_7 ++ (patterns_16_8_8 ++ (patterns_16_8_9 ++ (patterns_16_8_10 ++ (patterns_16_8_11 ++ (patterns_16_8_12 ++ (patterns_16_8_13 ++ (patterns_16_8_14 ++ (patterns_16_8_15 ++ (patterns_16_8_16 ++ (patterns_16_8_17 ++ (patterns_16_8_18 ++ (patterns_16_8_19 ++ (patterns_16_8_20 ++ (patterns_16_8_21 ++ (patterns_16_8_22 ++ (patterns_16_8_23 ++ (patterns_16_8_24 ++ (patterns_16_8_25 ++ (patterns_16_8_26 ++ (patterns_16_8_27 ++ (patterns_16_8_28 ++ (patterns_16_8_29 ++ ([]))))))))))))))))))))))))))))))

theorem patterns_16_8_verified : ∀ D ∈ patterns_16_8, PatternVerified 16 8 D := by

  simp only [patterns_16_8, List.forall_mem_append]

  exact ⟨patterns_16_8_0_verified, ⟨patterns_16_8_1_verified, ⟨patterns_16_8_2_verified, ⟨patterns_16_8_3_verified, ⟨patterns_16_8_4_verified, ⟨patterns_16_8_5_verified, ⟨patterns_16_8_6_verified, ⟨patterns_16_8_7_verified, ⟨patterns_16_8_8_verified, ⟨patterns_16_8_9_verified, ⟨patterns_16_8_10_verified, ⟨patterns_16_8_11_verified, ⟨patterns_16_8_12_verified, ⟨patterns_16_8_13_verified, ⟨patterns_16_8_14_verified, ⟨patterns_16_8_15_verified, ⟨patterns_16_8_16_verified, ⟨patterns_16_8_17_verified, ⟨patterns_16_8_18_verified, ⟨patterns_16_8_19_verified, ⟨patterns_16_8_20_verified, ⟨patterns_16_8_21_verified, ⟨patterns_16_8_22_verified, ⟨patterns_16_8_23_verified, ⟨patterns_16_8_24_verified, ⟨patterns_16_8_25_verified, ⟨patterns_16_8_26_verified, ⟨patterns_16_8_27_verified, ⟨patterns_16_8_28_verified, ⟨patterns_16_8_29_verified, by simp⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem patterns_16_8_coverage : patternChoices 8 8 [] = patterns_16_8 := by decide +kernel

theorem finite_patterns_16_8 : ∀ D ∈ patternChoices 8 (16-8) [], PatternVerified 16 8 D := by

  rw [patterns_16_8_coverage]

  exact patterns_16_8_verified

end CycleClique

end OAI
