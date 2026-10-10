import OAI.Analysis.MutuallyUnbiased.MixedData.Source12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1600 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue4056 x + ((4 : ℝ) * Sparse.eval nodeValue4057 x + ((4 : ℝ) * Sparse.eval nodeValue4063 x + ((4 : ℝ) * Sparse.eval nodeValue4068 x + ((12 : ℝ) * Sparse.eval nodeValue4069 x + ((1 : ℝ) * Sparse.eval nodeValue4079 x + ((4 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1600 : Integer.Sparse Master := [(Sum.inr 4056, 1), (Sum.inr 4057, 4), (Sum.inr 4063, 4), (Sum.inr 4068, 4), (Sum.inr 4069, 12), (Sum.inr 4079, 1), (Sum.inr 4083, 4)]

theorem reindexCheck1600 : Integer.Sparse.reindex keyMap MixedData.row1600 = numericRow1600 := by decide +kernel

theorem numericCheck1600 (x : Master → ℝ) : Integer.Sparse.eval numericRow1600 x =
    (1 : ℝ) * reducedSource1600 x := by
  norm_num [numericRow1600, reducedSource1600, Integer.Sparse.eval, Sparse.eval, nodeValue4056, nodeValue4057, nodeValue4063, nodeValue4068, nodeValue4069, nodeValue4079, nodeValue4083]

noncomputable def reducedSource1601 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue940 x + ((1 : ℝ) * Sparse.eval nodeValue1820 x + ((2 : ℝ) * Sparse.eval nodeValue1971 x + ((1 : ℝ) * Sparse.eval nodeValue2063 x + ((1 : ℝ) * Sparse.eval nodeValue2065 x + ((-1 : ℝ) * Sparse.eval nodeValue4085 x + 0)))))

def numericRow1601 : Integer.Sparse Master := [(Sum.inr 940, 1), (Sum.inr 1820, 1), (Sum.inr 1971, 2), (Sum.inr 2063, 1), (Sum.inr 2065, 1), (Sum.inr 4085, -1)]

theorem reindexCheck1601 : Integer.Sparse.reindex keyMap MixedData.row1601 = numericRow1601 := by decide +kernel

theorem numericCheck1601 (x : Master → ℝ) : Integer.Sparse.eval numericRow1601 x =
    (1 : ℝ) * reducedSource1601 x := by
  norm_num [numericRow1601, reducedSource1601, Integer.Sparse.eval, Sparse.eval, nodeValue940, nodeValue1820, nodeValue1971, nodeValue2063, nodeValue2065, nodeValue4085]

noncomputable def reducedSource1602 (x : Master → ℝ) : ℝ :=
  (2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2222 x + ((1 : ℝ) * Sparse.eval nodeValue2230 x + ((1 : ℝ) * Sparse.eval nodeValue2282 x + ((1 : ℝ) * Sparse.eval nodeValue2287 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1602 : Integer.Sparse Master := [(Sum.inr 2220, 2), (Sum.inr 2222, 1), (Sum.inr 2230, 1), (Sum.inr 2282, 1), (Sum.inr 2287, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1602 : Integer.Sparse.reindex keyMap MixedData.row1602 = numericRow1602 := by decide +kernel

theorem numericCheck1602 (x : Master → ℝ) : Integer.Sparse.eval numericRow1602 x =
    (1 : ℝ) * reducedSource1602 x := by
  norm_num [numericRow1602, reducedSource1602, Integer.Sparse.eval, Sparse.eval, nodeValue2220, nodeValue2222, nodeValue2230, nodeValue2282, nodeValue2287, nodeValue4081]

noncomputable def reducedSource1603 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue931 x + ((1 : ℝ) * Sparse.eval nodeValue1813 x + ((1 : ℝ) * Sparse.eval nodeValue1965 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2037 x + ((1 : ℝ) * Sparse.eval nodeValue2058 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1603 : Integer.Sparse Master := [(Sum.inr 931, 1), (Sum.inr 1813, 1), (Sum.inr 1965, 1), (Sum.inr 2026, 1), (Sum.inr 2037, 1), (Sum.inr 2058, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1603 : Integer.Sparse.reindex keyMap MixedData.row1603 = numericRow1603 := by decide +kernel

theorem numericCheck1603 (x : Master → ℝ) : Integer.Sparse.eval numericRow1603 x =
    (1 : ℝ) * reducedSource1603 x := by
  norm_num [numericRow1603, reducedSource1603, Integer.Sparse.eval, Sparse.eval, nodeValue931, nodeValue1813, nodeValue1965, nodeValue2026, nodeValue2037, nodeValue2058, nodeValue4084]

noncomputable def reducedSource1604 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue914 x + ((1 : ℝ) * Sparse.eval nodeValue1797 x + ((1 : ℝ) * Sparse.eval nodeValue1957 x + ((1 : ℝ) * Sparse.eval nodeValue1980 x + ((1 : ℝ) * Sparse.eval nodeValue2026 x + ((1 : ℝ) * Sparse.eval nodeValue2028 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1604 : Integer.Sparse Master := [(Sum.inr 914, 1), (Sum.inr 1797, 1), (Sum.inr 1957, 1), (Sum.inr 1980, 1), (Sum.inr 2026, 1), (Sum.inr 2028, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1604 : Integer.Sparse.reindex keyMap MixedData.row1604 = numericRow1604 := by decide +kernel

theorem numericCheck1604 (x : Master → ℝ) : Integer.Sparse.eval numericRow1604 x =
    (1 : ℝ) * reducedSource1604 x := by
  norm_num [numericRow1604, reducedSource1604, Integer.Sparse.eval, Sparse.eval, nodeValue914, nodeValue1797, nodeValue1957, nodeValue1980, nodeValue2026, nodeValue2028, nodeValue4084]

noncomputable def reducedSource1605 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue949 x + ((1 : ℝ) * Sparse.eval nodeValue1828 x + ((1 : ℝ) * Sparse.eval nodeValue1976 x + ((2 : ℝ) * Sparse.eval nodeValue2092 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1605 : Integer.Sparse Master := [(Sum.inr 949, 1), (Sum.inr 1828, 1), (Sum.inr 1976, 1), (Sum.inr 2092, 2), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1605 : Integer.Sparse.reindex keyMap MixedData.row1605 = numericRow1605 := by decide +kernel

theorem numericCheck1605 (x : Master → ℝ) : Integer.Sparse.eval numericRow1605 x =
    (1 : ℝ) * reducedSource1605 x := by
  norm_num [numericRow1605, reducedSource1605, Integer.Sparse.eval, Sparse.eval, nodeValue949, nodeValue1828, nodeValue1976, nodeValue2092, nodeValue2110, nodeValue4083]

noncomputable def reducedSource1606 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2219 x + ((2 : ℝ) * Sparse.eval nodeValue2220 x + ((1 : ℝ) * Sparse.eval nodeValue2221 x + ((2 : ℝ) * Sparse.eval nodeValue2224 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))

def numericRow1606 : Integer.Sparse Master := [(Sum.inr 2219, 1), (Sum.inr 2220, 2), (Sum.inr 2221, 1), (Sum.inr 2224, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1606 : Integer.Sparse.reindex keyMap MixedData.row1606 = numericRow1606 := by decide +kernel

theorem numericCheck1606 (x : Master → ℝ) : Integer.Sparse.eval numericRow1606 x =
    (1 : ℝ) * reducedSource1606 x := by
  norm_num [numericRow1606, reducedSource1606, Integer.Sparse.eval, Sparse.eval, nodeValue2219, nodeValue2220, nodeValue2221, nodeValue2224, nodeValue4081]

noncomputable def reducedSource1607 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue925 x + ((1 : ℝ) * Sparse.eval nodeValue1808 x + ((1 : ℝ) * Sparse.eval nodeValue1961 x + ((1 : ℝ) * Sparse.eval nodeValue2035 x + ((1 : ℝ) * Sparse.eval nodeValue2054 x + ((1 : ℝ) * Sparse.eval nodeValue2062 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1607 : Integer.Sparse Master := [(Sum.inr 925, 1), (Sum.inr 1808, 1), (Sum.inr 1961, 1), (Sum.inr 2035, 1), (Sum.inr 2054, 1), (Sum.inr 2062, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1607 : Integer.Sparse.reindex keyMap MixedData.row1607 = numericRow1607 := by decide +kernel

theorem numericCheck1607 (x : Master → ℝ) : Integer.Sparse.eval numericRow1607 x =
    (1 : ℝ) * reducedSource1607 x := by
  norm_num [numericRow1607, reducedSource1607, Integer.Sparse.eval, Sparse.eval, nodeValue925, nodeValue1808, nodeValue1961, nodeValue2035, nodeValue2054, nodeValue2062, nodeValue4084]

noncomputable def reducedSource1608 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1137 x + ((1 : ℝ) * Sparse.eval nodeValue2340 x + ((1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2486 x + ((1 : ℝ) * Sparse.eval nodeValue2497 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1608 : Integer.Sparse Master := [(Sum.inr 1137, 1), (Sum.inr 2340, 1), (Sum.inr 2430, 1), (Sum.inr 2486, 1), (Sum.inr 2497, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1608 : Integer.Sparse.reindex keyMap MixedData.row1608 = numericRow1608 := by decide +kernel

theorem numericCheck1608 (x : Master → ℝ) : Integer.Sparse.eval numericRow1608 x =
    (1 : ℝ) * reducedSource1608 x := by
  norm_num [numericRow1608, reducedSource1608, Integer.Sparse.eval, Sparse.eval, nodeValue1137, nodeValue2340, nodeValue2430, nodeValue2486, nodeValue2497, nodeValue2515, nodeValue4092]

noncomputable def reducedSource1609 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue3358 x + ((1 : ℝ) * Sparse.eval nodeValue3437 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1609 : Integer.Sparse Master := [(Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3358, 1), (Sum.inr 3437, 1), (Sum.inr 3472, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1609 : Integer.Sparse.reindex keyMap MixedData.row1609 = numericRow1609 := by decide +kernel

theorem numericCheck1609 (x : Master → ℝ) : Integer.Sparse.eval numericRow1609 x =
    (1 : ℝ) * reducedSource1609 x := by
  norm_num [numericRow1609, reducedSource1609, Integer.Sparse.eval, Sparse.eval, nodeValue1948, nodeValue2207, nodeValue3358, nodeValue3437, nodeValue3472, nodeValue3481, nodeValue4081]

noncomputable def reducedSource1610 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1910 x + ((1 : ℝ) * Sparse.eval nodeValue1916 x + ((1 : ℝ) * Sparse.eval nodeValue1917 x + ((1 : ℝ) * Sparse.eval nodeValue1948 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue3472 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1610 : Integer.Sparse Master := [(Sum.inr 1910, 1), (Sum.inr 1916, 1), (Sum.inr 1917, 1), (Sum.inr 1948, 1), (Sum.inr 2207, 1), (Sum.inr 3472, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1610 : Integer.Sparse.reindex keyMap MixedData.row1610 = numericRow1610 := by decide +kernel

theorem numericCheck1610 (x : Master → ℝ) : Integer.Sparse.eval numericRow1610 x =
    (1 : ℝ) * reducedSource1610 x := by
  norm_num [numericRow1610, reducedSource1610, Integer.Sparse.eval, Sparse.eval, nodeValue1910, nodeValue1916, nodeValue1917, nodeValue1948, nodeValue2207, nodeValue3472, nodeValue4081]

noncomputable def reducedSource1611 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue2203 x + ((1 : ℝ) * Sparse.eval nodeValue2207 x + ((1 : ℝ) * Sparse.eval nodeValue2224 x + ((1 : ℝ) * Sparse.eval nodeValue2259 x + ((1 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0))))))

def numericRow1611 : Integer.Sparse Master := [(Sum.inr 2201, 1), (Sum.inr 2203, 1), (Sum.inr 2207, 1), (Sum.inr 2224, 1), (Sum.inr 2259, 1), (Sum.inr 3481, 1), (Sum.inr 4081, -1)]

theorem reindexCheck1611 : Integer.Sparse.reindex keyMap MixedData.row1611 = numericRow1611 := by decide +kernel

theorem numericCheck1611 (x : Master → ℝ) : Integer.Sparse.eval numericRow1611 x =
    (1 : ℝ) * reducedSource1611 x := by
  norm_num [numericRow1611, reducedSource1611, Integer.Sparse.eval, Sparse.eval, nodeValue2201, nodeValue2203, nodeValue2207, nodeValue2224, nodeValue2259, nodeValue3481, nodeValue4081]

noncomputable def reducedSource1612 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue905 x + ((1 : ℝ) * Sparse.eval nodeValue1790 x + ((1 : ℝ) * Sparse.eval nodeValue1973 x + ((1 : ℝ) * Sparse.eval nodeValue2009 x + ((1 : ℝ) * Sparse.eval nodeValue2020 x + ((1 : ℝ) * Sparse.eval nodeValue2025 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0))))))

def numericRow1612 : Integer.Sparse Master := [(Sum.inr 905, 1), (Sum.inr 1790, 1), (Sum.inr 1973, 1), (Sum.inr 2009, 1), (Sum.inr 2020, 1), (Sum.inr 2025, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1612 : Integer.Sparse.reindex keyMap MixedData.row1612 = numericRow1612 := by decide +kernel

theorem numericCheck1612 (x : Master → ℝ) : Integer.Sparse.eval numericRow1612 x =
    (1 : ℝ) * reducedSource1612 x := by
  norm_num [numericRow1612, reducedSource1612, Integer.Sparse.eval, Sparse.eval, nodeValue905, nodeValue1790, nodeValue1973, nodeValue2009, nodeValue2020, nodeValue2025, nodeValue4083]

noncomputable def reducedSource1613 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1116 x + ((1 : ℝ) * Sparse.eval nodeValue2323 x + ((1 : ℝ) * Sparse.eval nodeValue2440 x + ((2 : ℝ) * Sparse.eval nodeValue2471 x + ((1 : ℝ) * Sparse.eval nodeValue2483 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1613 : Integer.Sparse Master := [(Sum.inr 1116, 1), (Sum.inr 2323, 1), (Sum.inr 2440, 1), (Sum.inr 2471, 2), (Sum.inr 2483, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1613 : Integer.Sparse.reindex keyMap MixedData.row1613 = numericRow1613 := by decide +kernel

theorem numericCheck1613 (x : Master → ℝ) : Integer.Sparse.eval numericRow1613 x =
    (1 : ℝ) * reducedSource1613 x := by
  norm_num [numericRow1613, reducedSource1613, Integer.Sparse.eval, Sparse.eval, nodeValue1116, nodeValue2323, nodeValue2440, nodeValue2471, nodeValue2483, nodeValue4091]

noncomputable def reducedSource1614 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1940 x + ((1 : ℝ) * Sparse.eval nodeValue2201 x + ((1 : ℝ) * Sparse.eval nodeValue3350 x + ((1 : ℝ) * Sparse.eval nodeValue3466 x + ((2 : ℝ) * Sparse.eval nodeValue3481 x + ((-1 : ℝ) * Sparse.eval nodeValue4081 x + 0)))))

def numericRow1614 : Integer.Sparse Master := [(Sum.inr 1940, 1), (Sum.inr 2201, 1), (Sum.inr 3350, 1), (Sum.inr 3466, 1), (Sum.inr 3481, 2), (Sum.inr 4081, -1)]

theorem reindexCheck1614 : Integer.Sparse.reindex keyMap MixedData.row1614 = numericRow1614 := by decide +kernel

theorem numericCheck1614 (x : Master → ℝ) : Integer.Sparse.eval numericRow1614 x =
    (1 : ℝ) * reducedSource1614 x := by
  norm_num [numericRow1614, reducedSource1614, Integer.Sparse.eval, Sparse.eval, nodeValue1940, nodeValue2201, nodeValue3350, nodeValue3466, nodeValue3481, nodeValue4081]

noncomputable def reducedSource1615 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue909 x + ((1 : ℝ) * Sparse.eval nodeValue1793 x + ((1 : ℝ) * Sparse.eval nodeValue1976 x + ((2 : ℝ) * Sparse.eval nodeValue2010 x + ((1 : ℝ) * Sparse.eval nodeValue2023 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1615 : Integer.Sparse Master := [(Sum.inr 909, 1), (Sum.inr 1793, 1), (Sum.inr 1976, 1), (Sum.inr 2010, 2), (Sum.inr 2023, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1615 : Integer.Sparse.reindex keyMap MixedData.row1615 = numericRow1615 := by decide +kernel

theorem numericCheck1615 (x : Master → ℝ) : Integer.Sparse.eval numericRow1615 x =
    (1 : ℝ) * reducedSource1615 x := by
  norm_num [numericRow1615, reducedSource1615, Integer.Sparse.eval, Sparse.eval, nodeValue909, nodeValue1793, nodeValue1976, nodeValue2010, nodeValue2023, nodeValue4083]

end MUB6.Certificate.MixedSourceBridge

end OAI
