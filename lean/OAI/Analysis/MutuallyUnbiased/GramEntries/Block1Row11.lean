import OAI.Analysis.MutuallyUnbiased.GramEntries.Block1Data
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block1
import OAI.Analysis.MutuallyUnbiased.GramRows.Block38
import OAI.Analysis.MutuallyUnbiased.GramRows.Block39
import OAI.Analysis.MutuallyUnbiased.GramRows.Block40

namespace OAI

namespace MUB6.Certificate.GramEntries.Block1

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

def rows11_0 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1918, row1919, row1920, row1921, row1922, row1923, row1924, row1925, row1926, row1927, row1928, row1929, row1930, row1931]

theorem entryCheck11_0 : entry11_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_0 k)) := by decide +kernel

theorem rowsSound11_0 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_0 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form0) x := by
  fin_cases k
  · exact rowEval1918 x
  · exact rowEval1919 x
  · exact rowEval1920 x
  · exact rowEval1921 x
  · exact rowEval1922 x
  · exact rowEval1923 x
  · exact rowEval1924 x
  · exact rowEval1925 x
  · exact rowEval1926 x
  · exact rowEval1927 x
  · exact rowEval1928 x
  · exact rowEval1929 x
  · exact rowEval1930 x
  · exact rowEval1931 x

theorem entryEval11_0 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_0 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form0 B := by
  rw [entryCheck11_0, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form0 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_0]

def rows11_1 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1932, row1933, row1934, row1935, row1936, row1937, row1938, row1939, row1940, row1941, row1942, row1943, row1944, row1945]

theorem entryCheck11_1 : entry11_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_1 k)) := by decide +kernel

theorem rowsSound11_1 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_1 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form1) x := by
  fin_cases k
  · exact rowEval1932 x
  · exact rowEval1933 x
  · exact rowEval1934 x
  · exact rowEval1935 x
  · exact rowEval1936 x
  · exact rowEval1937 x
  · exact rowEval1938 x
  · exact rowEval1939 x
  · exact rowEval1940 x
  · exact rowEval1941 x
  · exact rowEval1942 x
  · exact rowEval1943 x
  · exact rowEval1944 x
  · exact rowEval1945 x

theorem entryEval11_1 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_1 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form1 B := by
  rw [entryCheck11_1, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form1 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_1]

def rows11_2 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1946, row1947, row1948, row1949, row1950, row1951, row1952, row1953, row1954, row1955, row1956, row1957, row1958, row1959]

theorem entryCheck11_2 : entry11_2 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_2 k)) := by decide +kernel

theorem rowsSound11_2 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_2 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form2) x := by
  fin_cases k
  · exact rowEval1946 x
  · exact rowEval1947 x
  · exact rowEval1948 x
  · exact rowEval1949 x
  · exact rowEval1950 x
  · exact rowEval1951 x
  · exact rowEval1952 x
  · exact rowEval1953 x
  · exact rowEval1954 x
  · exact rowEval1955 x
  · exact rowEval1956 x
  · exact rowEval1957 x
  · exact rowEval1958 x
  · exact rowEval1959 x

theorem entryEval11_2 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_2 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form2 B := by
  rw [entryCheck11_2, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form2 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_2]

def rows11_3 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1960, row1961, row1962, row1963, row1964, row1965, row1966, row1967, row1968, row1969, row1970, row1971, row1972, row1973]

theorem entryCheck11_3 : entry11_3 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_3 k)) := by decide +kernel

theorem rowsSound11_3 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_3 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form3) x := by
  fin_cases k
  · exact rowEval1960 x
  · exact rowEval1961 x
  · exact rowEval1962 x
  · exact rowEval1963 x
  · exact rowEval1964 x
  · exact rowEval1965 x
  · exact rowEval1966 x
  · exact rowEval1967 x
  · exact rowEval1968 x
  · exact rowEval1969 x
  · exact rowEval1970 x
  · exact rowEval1971 x
  · exact rowEval1972 x
  · exact rowEval1973 x

theorem entryEval11_3 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_3 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form3 B := by
  rw [entryCheck11_3, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form3 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_3]

def rows11_4 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1974, row1975, row1976, row1977, row1978, row1979, row1980, row1981, row1982, row1983, row1984, row1985, row1986, row1987]

theorem entryCheck11_4 : entry11_4 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_4 k)) := by decide +kernel

theorem rowsSound11_4 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_4 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form4) x := by
  fin_cases k
  · exact rowEval1974 x
  · exact rowEval1975 x
  · exact rowEval1976 x
  · exact rowEval1977 x
  · exact rowEval1978 x
  · exact rowEval1979 x
  · exact rowEval1980 x
  · exact rowEval1981 x
  · exact rowEval1982 x
  · exact rowEval1983 x
  · exact rowEval1984 x
  · exact rowEval1985 x
  · exact rowEval1986 x
  · exact rowEval1987 x

theorem entryEval11_4 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_4 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form4 B := by
  rw [entryCheck11_4, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form4 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_4]

def rows11_5 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row1988, row1989, row1990, row1991, row1992, row1993, row1994, row1995, row1996, row1997, row1998, row1999, row2000, row2001]

theorem entryCheck11_5 : entry11_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_5 k)) := by decide +kernel

theorem rowsSound11_5 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_5 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form5) x := by
  fin_cases k
  · exact rowEval1988 x
  · exact rowEval1989 x
  · exact rowEval1990 x
  · exact rowEval1991 x
  · exact rowEval1992 x
  · exact rowEval1993 x
  · exact rowEval1994 x
  · exact rowEval1995 x
  · exact rowEval1996 x
  · exact rowEval1997 x
  · exact rowEval1998 x
  · exact rowEval1999 x
  · exact rowEval2000 x
  · exact rowEval2001 x

theorem entryEval11_5 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_5 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form5 B := by
  rw [entryCheck11_5, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form5 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_5]

def rows11_6 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2002, row2003, row2004, row2005, row2006, row2007, row2008, row2009, row2010, row2011, row2012, row2013, row2014, row2015]

theorem entryCheck11_6 : entry11_6 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_6 k)) := by decide +kernel

theorem rowsSound11_6 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_6 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form6) x := by
  fin_cases k
  · exact rowEval2002 x
  · exact rowEval2003 x
  · exact rowEval2004 x
  · exact rowEval2005 x
  · exact rowEval2006 x
  · exact rowEval2007 x
  · exact rowEval2008 x
  · exact rowEval2009 x
  · exact rowEval2010 x
  · exact rowEval2011 x
  · exact rowEval2012 x
  · exact rowEval2013 x
  · exact rowEval2014 x
  · exact rowEval2015 x

theorem entryEval11_6 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_6 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form6 B := by
  rw [entryCheck11_6, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form6 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_6]

def rows11_7 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2016, row2017, row2018, row2019, row2020, row2021, row2022, row2023, row2024, row2025, row2026, row2027, row2028, row2029]

theorem entryCheck11_7 : entry11_7 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_7 k)) := by decide +kernel

theorem rowsSound11_7 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_7 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form7) x := by
  fin_cases k
  · exact rowEval2016 x
  · exact rowEval2017 x
  · exact rowEval2018 x
  · exact rowEval2019 x
  · exact rowEval2020 x
  · exact rowEval2021 x
  · exact rowEval2022 x
  · exact rowEval2023 x
  · exact rowEval2024 x
  · exact rowEval2025 x
  · exact rowEval2026 x
  · exact rowEval2027 x
  · exact rowEval2028 x
  · exact rowEval2029 x

theorem entryEval11_7 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_7 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form7 B := by
  rw [entryCheck11_7, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form7 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_7]

def rows11_8 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2030, row2031, row2032, row2033, row2034, row2035, row2036, row2037, row2038, row2039, row2040, row2041, row2042, row2043]

theorem entryCheck11_8 : entry11_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_8 k)) := by decide +kernel

theorem rowsSound11_8 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_8 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form8) x := by
  fin_cases k
  · exact rowEval2030 x
  · exact rowEval2031 x
  · exact rowEval2032 x
  · exact rowEval2033 x
  · exact rowEval2034 x
  · exact rowEval2035 x
  · exact rowEval2036 x
  · exact rowEval2037 x
  · exact rowEval2038 x
  · exact rowEval2039 x
  · exact rowEval2040 x
  · exact rowEval2041 x
  · exact rowEval2042 x
  · exact rowEval2043 x

theorem entryEval11_8 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_8 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form8 B := by
  rw [entryCheck11_8, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form8 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_8]

def rows11_9 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2044, row2045, row2046, row2047, row2048, row2049, row2050, row2051, row2052, row2053, row2054, row2055, row2056, row2057]

theorem entryCheck11_9 : entry11_9 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_9 k)) := by decide +kernel

theorem rowsSound11_9 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_9 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form9) x := by
  fin_cases k
  · exact rowEval2044 x
  · exact rowEval2045 x
  · exact rowEval2046 x
  · exact rowEval2047 x
  · exact rowEval2048 x
  · exact rowEval2049 x
  · exact rowEval2050 x
  · exact rowEval2051 x
  · exact rowEval2052 x
  · exact rowEval2053 x
  · exact rowEval2054 x
  · exact rowEval2055 x
  · exact rowEval2056 x
  · exact rowEval2057 x

theorem entryEval11_9 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_9 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form9 B := by
  rw [entryCheck11_9, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form9 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_9]

def rows11_10 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2058, row2059, row2060, row2061, row2062, row2063, row2064, row2065, row2066, row2067, row2068, row2069, row2070, row2071]

theorem entryCheck11_10 : entry11_10 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_10 k)) := by decide +kernel

theorem rowsSound11_10 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_10 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form10) x := by
  fin_cases k
  · exact rowEval2058 x
  · exact rowEval2059 x
  · exact rowEval2060 x
  · exact rowEval2061 x
  · exact rowEval2062 x
  · exact rowEval2063 x
  · exact rowEval2064 x
  · exact rowEval2065 x
  · exact rowEval2066 x
  · exact rowEval2067 x
  · exact rowEval2068 x
  · exact rowEval2069 x
  · exact rowEval2070 x
  · exact rowEval2071 x

theorem entryEval11_10 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_10 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form10 B := by
  rw [entryCheck11_10, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form10 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_10]

def rows11_11 : Fin GramFunctions.Block1.form11.size → Integer.Sparse Key := ![row2072, row2073, row2074, row2075, row2076, row2077, row2078, row2079, row2080, row2081, row2082, row2083, row2084, row2085]

theorem entryCheck11_11 : entry11_11 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block1.form11.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block1.form11.terms k).coefficient) (rows11_11 k)) := by decide +kernel

theorem rowsSound11_11 (k : Fin GramFunctions.Block1.form11.size) (x : Key → ℝ) :
    Integer.Sparse.eval (rows11_11 k) x =
      Integer.Sparse.eval (normalizedRow (GramFunctions.Block1.form11.terms k).tag (GramFunctions.Block1.form11.terms k).charge GramFunctions.Block1.form11) x := by
  fin_cases k
  · exact rowEval2072 x
  · exact rowEval2073 x
  · exact rowEval2074 x
  · exact rowEval2075 x
  · exact rowEval2076 x
  · exact rowEval2077 x
  · exact rowEval2078 x
  · exact rowEval2079 x
  · exact rowEval2080 x
  · exact rowEval2081 x
  · exact rowEval2082 x
  · exact rowEval2083 x
  · exact rowEval2084 x
  · exact rowEval2085 x

theorem entryEval11_11 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval entry11_11 (GramNormalization.eval B) = GramFunctions.Block1.form11.mixedGram GramFunctions.Block1.form11 B := by
  rw [entryCheck11_11, collectWeightedRows_eval, mixedGram_eq_rows GramFunctions.Block1.form11 GramFunctions.Block1.form11 B hB]
  apply Finset.sum_congr rfl
  intro k _
  rw [rowsSound11_11]

end MUB6.Certificate.GramEntries.Block1

end OAI
