import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block37
import OAI.Analysis.MutuallyUnbiased.GramRows.Block38

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows10_0 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1764, row1765, row1766, row1767, row1768, row1769, row1770, row1771, row1772, row1773, row1774, row1775, row1776, row1777]

theorem entryCheck10_0 : entry10_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_0 k)) := by decide +kernel

theorem rowsSound10_0 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1764 x
  · exact rowEval1765 x
  · exact rowEval1766 x
  · exact rowEval1767 x
  · exact rowEval1768 x
  · exact rowEval1769 x
  · exact rowEval1770 x
  · exact rowEval1771 x
  · exact rowEval1772 x
  · exact rowEval1773 x
  · exact rowEval1774 x
  · exact rowEval1775 x
  · exact rowEval1776 x
  · exact rowEval1777 x

theorem entryEval10_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_0 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck10_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_0]

def rows10_1 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1778, row1779, row1780, row1781, row1782, row1783, row1784, row1785, row1786, row1787, row1788, row1789, row1790, row1791]

theorem entryCheck10_1 : entry10_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_1 k)) := by decide +kernel

theorem rowsSound10_1 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1778 x
  · exact rowEval1779 x
  · exact rowEval1780 x
  · exact rowEval1781 x
  · exact rowEval1782 x
  · exact rowEval1783 x
  · exact rowEval1784 x
  · exact rowEval1785 x
  · exact rowEval1786 x
  · exact rowEval1787 x
  · exact rowEval1788 x
  · exact rowEval1789 x
  · exact rowEval1790 x
  · exact rowEval1791 x

theorem entryEval10_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_1 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck10_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_1]

def rows10_2 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1792, row1793, row1794, row1795, row1796, row1797, row1798, row1799, row1800, row1801, row1802, row1803, row1804, row1805]

theorem entryCheck10_2 : entry10_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_2 k)) := by decide +kernel

theorem rowsSound10_2 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1792 x
  · exact rowEval1793 x
  · exact rowEval1794 x
  · exact rowEval1795 x
  · exact rowEval1796 x
  · exact rowEval1797 x
  · exact rowEval1798 x
  · exact rowEval1799 x
  · exact rowEval1800 x
  · exact rowEval1801 x
  · exact rowEval1802 x
  · exact rowEval1803 x
  · exact rowEval1804 x
  · exact rowEval1805 x

theorem entryEval10_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_2 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck10_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_2]

def rows10_3 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1806, row1807, row1808, row1809, row1810, row1811, row1812, row1813, row1814, row1815, row1816, row1817, row1818, row1819]

theorem entryCheck10_3 : entry10_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_3 k)) := by decide +kernel

theorem rowsSound10_3 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1806 x
  · exact rowEval1807 x
  · exact rowEval1808 x
  · exact rowEval1809 x
  · exact rowEval1810 x
  · exact rowEval1811 x
  · exact rowEval1812 x
  · exact rowEval1813 x
  · exact rowEval1814 x
  · exact rowEval1815 x
  · exact rowEval1816 x
  · exact rowEval1817 x
  · exact rowEval1818 x
  · exact rowEval1819 x

theorem entryEval10_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_3 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck10_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_3]

def rows10_4 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1820, row1821, row1822, row1823, row1824, row1825, row1826, row1827, row1828, row1829, row1830, row1831, row1832, row1833]

theorem entryCheck10_4 : entry10_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_4 k)) := by decide +kernel

theorem rowsSound10_4 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1820 x
  · exact rowEval1821 x
  · exact rowEval1822 x
  · exact rowEval1823 x
  · exact rowEval1824 x
  · exact rowEval1825 x
  · exact rowEval1826 x
  · exact rowEval1827 x
  · exact rowEval1828 x
  · exact rowEval1829 x
  · exact rowEval1830 x
  · exact rowEval1831 x
  · exact rowEval1832 x
  · exact rowEval1833 x

theorem entryEval10_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_4 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck10_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_4]

def rows10_5 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1834, row1835, row1836, row1837, row1838, row1839, row1840, row1841, row1842, row1843, row1844, row1845, row1846, row1847]

theorem entryCheck10_5 : entry10_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_5 k)) := by decide +kernel

theorem rowsSound10_5 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1834 x
  · exact rowEval1835 x
  · exact rowEval1836 x
  · exact rowEval1837 x
  · exact rowEval1838 x
  · exact rowEval1839 x
  · exact rowEval1840 x
  · exact rowEval1841 x
  · exact rowEval1842 x
  · exact rowEval1843 x
  · exact rowEval1844 x
  · exact rowEval1845 x
  · exact rowEval1846 x
  · exact rowEval1847 x

theorem entryEval10_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_5 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck10_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_5]

def rows10_6 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1848, row1849, row1850, row1851, row1852, row1853, row1854, row1855, row1856, row1857, row1858, row1859, row1860, row1861]

theorem entryCheck10_6 : entry10_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_6 k)) := by decide +kernel

theorem rowsSound10_6 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval1848 x
  · exact rowEval1849 x
  · exact rowEval1850 x
  · exact rowEval1851 x
  · exact rowEval1852 x
  · exact rowEval1853 x
  · exact rowEval1854 x
  · exact rowEval1855 x
  · exact rowEval1856 x
  · exact rowEval1857 x
  · exact rowEval1858 x
  · exact rowEval1859 x
  · exact rowEval1860 x
  · exact rowEval1861 x

theorem entryEval10_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_6 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck10_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_6]

def rows10_7 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1862, row1863, row1864, row1865, row1866, row1867, row1868, row1869, row1870, row1871, row1872, row1873, row1874, row1875]

theorem entryCheck10_7 : entry10_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_7 k)) := by decide +kernel

theorem rowsSound10_7 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval1862 x
  · exact rowEval1863 x
  · exact rowEval1864 x
  · exact rowEval1865 x
  · exact rowEval1866 x
  · exact rowEval1867 x
  · exact rowEval1868 x
  · exact rowEval1869 x
  · exact rowEval1870 x
  · exact rowEval1871 x
  · exact rowEval1872 x
  · exact rowEval1873 x
  · exact rowEval1874 x
  · exact rowEval1875 x

theorem entryEval10_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_7 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck10_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_7]

def rows10_8 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1876, row1877, row1878, row1879, row1880, row1881, row1882, row1883, row1884, row1885, row1886, row1887, row1888, row1889]

theorem entryCheck10_8 : entry10_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_8 k)) := by decide +kernel

theorem rowsSound10_8 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval1876 x
  · exact rowEval1877 x
  · exact rowEval1878 x
  · exact rowEval1879 x
  · exact rowEval1880 x
  · exact rowEval1881 x
  · exact rowEval1882 x
  · exact rowEval1883 x
  · exact rowEval1884 x
  · exact rowEval1885 x
  · exact rowEval1886 x
  · exact rowEval1887 x
  · exact rowEval1888 x
  · exact rowEval1889 x

theorem entryEval10_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_8 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck10_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_8]

def rows10_9 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1890, row1891, row1892, row1893, row1894, row1895, row1896, row1897, row1898, row1899, row1900, row1901, row1902, row1903]

theorem entryCheck10_9 : entry10_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_9 k)) := by decide +kernel

theorem rowsSound10_9 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval1890 x
  · exact rowEval1891 x
  · exact rowEval1892 x
  · exact rowEval1893 x
  · exact rowEval1894 x
  · exact rowEval1895 x
  · exact rowEval1896 x
  · exact rowEval1897 x
  · exact rowEval1898 x
  · exact rowEval1899 x
  · exact rowEval1900 x
  · exact rowEval1901 x
  · exact rowEval1902 x
  · exact rowEval1903 x

theorem entryEval10_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_9 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck10_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_9]

def rows10_10 : Fin GramFunctions.Block1.form10.size → Integer.Sparse Key := ![row1904, row1905, row1906, row1907, row1908, row1909, row1910, row1911, row1912, row1913, row1914, row1915, row1916, row1917]

theorem entryCheck10_10 : entry10_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form10.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form10.terms k).coefficient) (rows10_10 k)) := by decide +kernel

theorem rowsSound10_10 (k : Fin GramFunctions.Block1.form10.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows10_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form10.terms k).tag (GramFunctions.Block1.form10.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval1904 x
  · exact rowEval1905 x
  · exact rowEval1906 x
  · exact rowEval1907 x
  · exact rowEval1908 x
  · exact rowEval1909 x
  · exact rowEval1910 x
  · exact rowEval1911 x
  · exact rowEval1912 x
  · exact rowEval1913 x
  · exact rowEval1914 x
  · exact rowEval1915 x
  · exact rowEval1916 x
  · exact rowEval1917 x

theorem entryEval10_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry10_10 (GramNormalization.eval B) = GramFunctions.Block1.form10.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck10_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form10 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound10_10]

end MUB6.Certificate.GramEntries.Block1

end OAI
