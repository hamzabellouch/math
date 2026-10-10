import OAI.Analysis.MutuallyUnbiased.MixedData.Source14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.NumericVector
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values63
import OAI.Analysis.MutuallyUnbiased.MixedSources.Basic

namespace OAI

namespace MUB6.Certificate.MixedSourceBridge

open MixedSemantics

noncomputable def reducedSource1888 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2443 x + ((1 : ℝ) * Sparse.eval nodeValue3033 x + ((1 : ℝ) * Sparse.eval nodeValue3136 x + ((1 : ℝ) * Sparse.eval nodeValue3138 x + ((1 : ℝ) * Sparse.eval nodeValue3180 x + ((1 : ℝ) * Sparse.eval nodeValue3732 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1888 : Integer.Sparse Master := [(Sum.inr 2443, 1), (Sum.inr 3033, 1), (Sum.inr 3136, 1), (Sum.inr 3138, 1), (Sum.inr 3180, 1), (Sum.inr 3732, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1888 : Integer.Sparse.reindex keyMap MixedData.row1888 = numericRow1888 := by decide +kernel

theorem numericCheck1888 (x : Master → ℝ) : Integer.Sparse.eval numericRow1888 x =
    (1 : ℝ) * reducedSource1888 x := by
  norm_num [numericRow1888, reducedSource1888, Integer.Sparse.eval, Sparse.eval, nodeValue2443, nodeValue3033, nodeValue3136, nodeValue3138, nodeValue3180, nodeValue3732, nodeValue4092]

noncomputable def reducedSource1889 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue942 x + ((1 : ℝ) * Sparse.eval nodeValue1822 x + ((1 : ℝ) * Sparse.eval nodeValue2088 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((2 : ℝ) * Sparse.eval nodeValue2107 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1889 : Integer.Sparse Master := [(Sum.inr 942, 1), (Sum.inr 1822, 1), (Sum.inr 2088, 1), (Sum.inr 2105, 1), (Sum.inr 2107, 2), (Sum.inr 4083, -1)]

theorem reindexCheck1889 : Integer.Sparse.reindex keyMap MixedData.row1889 = numericRow1889 := by decide +kernel

theorem numericCheck1889 (x : Master → ℝ) : Integer.Sparse.eval numericRow1889 x =
    (1 : ℝ) * reducedSource1889 x := by
  norm_num [numericRow1889, reducedSource1889, Integer.Sparse.eval, Sparse.eval, nodeValue942, nodeValue1822, nodeValue2088, nodeValue2105, nodeValue2107, nodeValue4083]

noncomputable def reducedSource1890 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2890 x + ((2 : ℝ) * Sparse.eval nodeValue3135 x + ((1 : ℝ) * Sparse.eval nodeValue3137 x + ((1 : ℝ) * Sparse.eval nodeValue3172 x + ((1 : ℝ) * Sparse.eval nodeValue3721 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1890 : Integer.Sparse Master := [(Sum.inr 2890, 1), (Sum.inr 3135, 2), (Sum.inr 3137, 1), (Sum.inr 3172, 1), (Sum.inr 3721, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1890 : Integer.Sparse.reindex keyMap MixedData.row1890 = numericRow1890 := by decide +kernel

theorem numericCheck1890 (x : Master → ℝ) : Integer.Sparse.eval numericRow1890 x =
    (1 : ℝ) * reducedSource1890 x := by
  norm_num [numericRow1890, reducedSource1890, Integer.Sparse.eval, Sparse.eval, nodeValue2890, nodeValue3135, nodeValue3137, nodeValue3172, nodeValue3721, nodeValue4091]

noncomputable def reducedSource1891 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue944 x + ((1 : ℝ) * Sparse.eval nodeValue1824 x + ((2 : ℝ) * Sparse.eval nodeValue2089 x + ((1 : ℝ) * Sparse.eval nodeValue2105 x + ((1 : ℝ) * Sparse.eval nodeValue2110 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1891 : Integer.Sparse Master := [(Sum.inr 944, 1), (Sum.inr 1824, 1), (Sum.inr 2089, 2), (Sum.inr 2105, 1), (Sum.inr 2110, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1891 : Integer.Sparse.reindex keyMap MixedData.row1891 = numericRow1891 := by decide +kernel

theorem numericCheck1891 (x : Master → ℝ) : Integer.Sparse.eval numericRow1891 x =
    (1 : ℝ) * reducedSource1891 x := by
  norm_num [numericRow1891, reducedSource1891, Integer.Sparse.eval, Sparse.eval, nodeValue944, nodeValue1824, nodeValue2089, nodeValue2105, nodeValue2110, nodeValue4083]

noncomputable def reducedSource1892 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2423 x + ((1 : ℝ) * Sparse.eval nodeValue3133 x + ((1 : ℝ) * Sparse.eval nodeValue3134 x + ((1 : ℝ) * Sparse.eval nodeValue3136 x + ((1 : ℝ) * Sparse.eval nodeValue3170 x + ((1 : ℝ) * Sparse.eval nodeValue3719 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1892 : Integer.Sparse Master := [(Sum.inr 2423, 1), (Sum.inr 3133, 1), (Sum.inr 3134, 1), (Sum.inr 3136, 1), (Sum.inr 3170, 1), (Sum.inr 3719, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1892 : Integer.Sparse.reindex keyMap MixedData.row1892 = numericRow1892 := by decide +kernel

theorem numericCheck1892 (x : Master → ℝ) : Integer.Sparse.eval numericRow1892 x =
    (1 : ℝ) * reducedSource1892 x := by
  norm_num [numericRow1892, reducedSource1892, Integer.Sparse.eval, Sparse.eval, nodeValue2423, nodeValue3133, nodeValue3134, nodeValue3136, nodeValue3170, nodeValue3719, nodeValue4092]

noncomputable def reducedSource1893 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2899 x + ((1 : ℝ) * Sparse.eval nodeValue3128 x + ((2 : ℝ) * Sparse.eval nodeValue3132 x + ((1 : ℝ) * Sparse.eval nodeValue3158 x + ((1 : ℝ) * Sparse.eval nodeValue3394 x + ((-1 : ℝ) * Sparse.eval nodeValue4083 x + 0)))))

def numericRow1893 : Integer.Sparse Master := [(Sum.inr 2899, 1), (Sum.inr 3128, 1), (Sum.inr 3132, 2), (Sum.inr 3158, 1), (Sum.inr 3394, 1), (Sum.inr 4083, -1)]

theorem reindexCheck1893 : Integer.Sparse.reindex keyMap MixedData.row1893 = numericRow1893 := by decide +kernel

theorem numericCheck1893 (x : Master → ℝ) : Integer.Sparse.eval numericRow1893 x =
    (1 : ℝ) * reducedSource1893 x := by
  norm_num [numericRow1893, reducedSource1893, Integer.Sparse.eval, Sparse.eval, nodeValue2899, nodeValue3128, nodeValue3132, nodeValue3158, nodeValue3394, nodeValue4083]

noncomputable def reducedSource1894 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2435 x + ((1 : ℝ) * Sparse.eval nodeValue3127 x + ((1 : ℝ) * Sparse.eval nodeValue3129 x + ((1 : ℝ) * Sparse.eval nodeValue3131 x + ((1 : ℝ) * Sparse.eval nodeValue3156 x + ((1 : ℝ) * Sparse.eval nodeValue3391 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0))))))

def numericRow1894 : Integer.Sparse Master := [(Sum.inr 2435, 1), (Sum.inr 3127, 1), (Sum.inr 3129, 1), (Sum.inr 3131, 1), (Sum.inr 3156, 1), (Sum.inr 3391, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1894 : Integer.Sparse.reindex keyMap MixedData.row1894 = numericRow1894 := by decide +kernel

theorem numericCheck1894 (x : Master → ℝ) : Integer.Sparse.eval numericRow1894 x =
    (1 : ℝ) * reducedSource1894 x := by
  norm_num [numericRow1894, reducedSource1894, Integer.Sparse.eval, Sparse.eval, nodeValue2435, nodeValue3127, nodeValue3129, nodeValue3131, nodeValue3156, nodeValue3391, nodeValue4084]

noncomputable def reducedSource1895 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1130 x + ((1 : ℝ) * Sparse.eval nodeValue2333 x + ((1 : ℝ) * Sparse.eval nodeValue2481 x + ((1 : ℝ) * Sparse.eval nodeValue2494 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1895 : Integer.Sparse Master := [(Sum.inr 1130, 1), (Sum.inr 2333, 1), (Sum.inr 2481, 1), (Sum.inr 2494, 1), (Sum.inr 2508, 1), (Sum.inr 2515, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1895 : Integer.Sparse.reindex keyMap MixedData.row1895 = numericRow1895 := by decide +kernel

theorem numericCheck1895 (x : Master → ℝ) : Integer.Sparse.eval numericRow1895 x =
    (1 : ℝ) * reducedSource1895 x := by
  norm_num [numericRow1895, reducedSource1895, Integer.Sparse.eval, Sparse.eval, nodeValue1130, nodeValue2333, nodeValue2481, nodeValue2494, nodeValue2508, nodeValue2515, nodeValue4092]

noncomputable def reducedSource1896 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2437 x + ((1 : ℝ) * Sparse.eval nodeValue2900 x + ((1 : ℝ) * Sparse.eval nodeValue2902 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((1 : ℝ) * Sparse.eval nodeValue2984 x + ((1 : ℝ) * Sparse.eval nodeValue3787 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1896 : Integer.Sparse Master := [(Sum.inr 2437, 1), (Sum.inr 2900, 1), (Sum.inr 2902, 1), (Sum.inr 2954, 1), (Sum.inr 2984, 1), (Sum.inr 3787, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1896 : Integer.Sparse.reindex keyMap MixedData.row1896 = numericRow1896 := by decide +kernel

theorem numericCheck1896 (x : Master → ℝ) : Integer.Sparse.eval numericRow1896 x =
    (1 : ℝ) * reducedSource1896 x := by
  norm_num [numericRow1896, reducedSource1896, Integer.Sparse.eval, Sparse.eval, nodeValue2437, nodeValue2900, nodeValue2902, nodeValue2954, nodeValue2984, nodeValue3787, nodeValue4091]

noncomputable def reducedSource1897 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1127 x + ((1 : ℝ) * Sparse.eval nodeValue2331 x + ((1 : ℝ) * Sparse.eval nodeValue2493 x + ((1 : ℝ) * Sparse.eval nodeValue2508 x + ((2 : ℝ) * Sparse.eval nodeValue2512 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0)))))

def numericRow1897 : Integer.Sparse Master := [(Sum.inr 1127, 1), (Sum.inr 2493, 1), (Sum.inr 2508, 1), (Sum.inr 2512, 2), (Sum.inr 4092, -1)]

theorem reindexCheck1897 : Integer.Sparse.reindex keyMap MixedData.row1897 = numericRow1897 := by decide +kernel

theorem numericCheck1897 (x : Master → ℝ) : Integer.Sparse.eval numericRow1897 x =
    (1 : ℝ) * reducedSource1897 x := by
  norm_num [numericRow1897, reducedSource1897, Integer.Sparse.eval, Sparse.eval, nodeValue1127, nodeValue2331, nodeValue2493, nodeValue2508, nodeValue2512, nodeValue4092]

noncomputable def reducedSource1898 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2847 x + ((2 : ℝ) * Sparse.eval nodeValue2849 x + ((1 : ℝ) * Sparse.eval nodeValue2884 x + ((1 : ℝ) * Sparse.eval nodeValue2976 x + ((1 : ℝ) * Sparse.eval nodeValue3945 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0)))))

def numericRow1898 : Integer.Sparse Master := [(Sum.inr 2847, 1), (Sum.inr 2849, 2), (Sum.inr 2884, 1), (Sum.inr 2976, 1), (Sum.inr 3945, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1898 : Integer.Sparse.reindex keyMap MixedData.row1898 = numericRow1898 := by decide +kernel

theorem numericCheck1898 (x : Master → ℝ) : Integer.Sparse.eval numericRow1898 x =
    (1 : ℝ) * reducedSource1898 x := by
  norm_num [numericRow1898, reducedSource1898, Integer.Sparse.eval, Sparse.eval, nodeValue2847, nodeValue2849, nodeValue2884, nodeValue2976, nodeValue3945, nodeValue4091]

noncomputable def reducedSource1899 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2846 x + ((1 : ℝ) * Sparse.eval nodeValue2848 x + ((1 : ℝ) * Sparse.eval nodeValue2881 x + ((1 : ℝ) * Sparse.eval nodeValue2974 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1899 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2846, 1), (Sum.inr 2848, 1), (Sum.inr 2881, 1), (Sum.inr 2974, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1899 : Integer.Sparse.reindex keyMap MixedData.row1899 = numericRow1899 := by decide +kernel

theorem numericCheck1899 (x : Master → ℝ) : Integer.Sparse.eval numericRow1899 x =
    (1 : ℝ) * reducedSource1899 x := by
  norm_num [numericRow1899, reducedSource1899, Integer.Sparse.eval, Sparse.eval, nodeValue2426, nodeValue2846, nodeValue2848, nodeValue2881, nodeValue2974, nodeValue3781, nodeValue4092]

noncomputable def reducedSource1900 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1960 x + ((2 : ℝ) * Sparse.eval nodeValue2427 x + ((1 : ℝ) * Sparse.eval nodeValue2509 x + ((1 : ℝ) * Sparse.eval nodeValue2552 x + ((1 : ℝ) * Sparse.eval nodeValue3493 x + ((-1 : ℝ) * Sparse.eval nodeValue4084 x + 0)))))

def numericRow1900 : Integer.Sparse Master := [(Sum.inr 1960, 1), (Sum.inr 2427, 2), (Sum.inr 2509, 1), (Sum.inr 3493, 1), (Sum.inr 4084, -1)]

theorem reindexCheck1900 : Integer.Sparse.reindex keyMap MixedData.row1900 = numericRow1900 := by decide +kernel

theorem numericCheck1900 (x : Master → ℝ) : Integer.Sparse.eval numericRow1900 x =
    (1 : ℝ) * reducedSource1900 x := by
  norm_num [numericRow1900, reducedSource1900, Integer.Sparse.eval, Sparse.eval, nodeValue1960, nodeValue2427, nodeValue2509, nodeValue2552, nodeValue3493, nodeValue4084]

noncomputable def reducedSource1901 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2426 x + ((1 : ℝ) * Sparse.eval nodeValue2428 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2512 x + ((1 : ℝ) * Sparse.eval nodeValue2554 x + ((1 : ℝ) * Sparse.eval nodeValue3781 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1901 : Integer.Sparse Master := [(Sum.inr 2426, 1), (Sum.inr 2428, 1), (Sum.inr 2433, 1), (Sum.inr 2512, 1), (Sum.inr 3781, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1901 : Integer.Sparse.reindex keyMap MixedData.row1901 = numericRow1901 := by decide +kernel

theorem numericCheck1901 (x : Master → ℝ) : Integer.Sparse.eval numericRow1901 x =
    (1 : ℝ) * reducedSource1901 x := by
  norm_num [numericRow1901, reducedSource1901, Integer.Sparse.eval, Sparse.eval, nodeValue2426, nodeValue2428, nodeValue2433, nodeValue2512, nodeValue2554, nodeValue3781, nodeValue4092]

noncomputable def reducedSource1902 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue2430 x + ((1 : ℝ) * Sparse.eval nodeValue2431 x + ((1 : ℝ) * Sparse.eval nodeValue2433 x + ((1 : ℝ) * Sparse.eval nodeValue2515 x + ((1 : ℝ) * Sparse.eval nodeValue2557 x + ((1 : ℝ) * Sparse.eval nodeValue3782 x + ((-1 : ℝ) * Sparse.eval nodeValue4092 x + 0))))))

def numericRow1902 : Integer.Sparse Master := [(Sum.inr 2430, 1), (Sum.inr 2431, 1), (Sum.inr 2433, 1), (Sum.inr 2515, 1), (Sum.inr 2557, 1), (Sum.inr 3782, 1), (Sum.inr 4092, -1)]

theorem reindexCheck1902 : Integer.Sparse.reindex keyMap MixedData.row1902 = numericRow1902 := by decide +kernel

theorem numericCheck1902 (x : Master → ℝ) : Integer.Sparse.eval numericRow1902 x =
    (1 : ℝ) * reducedSource1902 x := by
  norm_num [numericRow1902, reducedSource1902, Integer.Sparse.eval, Sparse.eval, nodeValue2430, nodeValue2431, nodeValue2433, nodeValue2515, nodeValue2557, nodeValue3782, nodeValue4092]

noncomputable def reducedSource1903 (x : Master → ℝ) : ℝ :=
  (1 : ℝ) * Sparse.eval nodeValue1335 x + ((1 : ℝ) * Sparse.eval nodeValue2826 x + ((1 : ℝ) * Sparse.eval nodeValue2924 x + ((1 : ℝ) * Sparse.eval nodeValue2933 x + ((1 : ℝ) * Sparse.eval nodeValue2951 x + ((1 : ℝ) * Sparse.eval nodeValue2954 x + ((-1 : ℝ) * Sparse.eval nodeValue4091 x + 0))))))

def numericRow1903 : Integer.Sparse Master := [(Sum.inr 1335, 1), (Sum.inr 2826, 1), (Sum.inr 2924, 1), (Sum.inr 2933, 1), (Sum.inr 2951, 1), (Sum.inr 2954, 1), (Sum.inr 4091, -1)]

theorem reindexCheck1903 : Integer.Sparse.reindex keyMap MixedData.row1903 = numericRow1903 := by decide +kernel

theorem numericCheck1903 (x : Master → ℝ) : Integer.Sparse.eval numericRow1903 x =
    (1 : ℝ) * reducedSource1903 x := by
  norm_num [numericRow1903, reducedSource1903, Integer.Sparse.eval, Sparse.eval, nodeValue1335, nodeValue2826, nodeValue2924, nodeValue2933, nodeValue2951, nodeValue2954, nodeValue4091]

end MUB6.Certificate.MixedSourceBridge

end OAI
