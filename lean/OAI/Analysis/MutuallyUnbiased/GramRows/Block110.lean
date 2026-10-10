import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block3
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block10
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block11
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block12
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block13
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block14
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow11008 : Integer.Sparse Key := [(key1344, -2), (key1338, -2), (key1338, -2), (key1658, -2), (key1656, -2), (key1658, -2), (key1456, -2), (key1656, -2), (key1456, -2), (key1666, -2), (key1666, -2), (key1465, -2), (key1325, 1), (key1317, 1), (key1325, 1), (key1297, 1), (key1317, 1), (key1297, 1), (key1555, 1), (key1547, 1), (key1555, 1), (key1392, 1), (key1547, 1), (key1392, 1), (key1623, 1), (key1574, 1), (key1623, 1), (key1425, 1), (key1574, 1), (key1425, 1), (key1632, 1), (key1592, 1), (key1632, 1), (key1443, 1), (key1592, 1), (key1443, 1)]

theorem rawRowCheck11008 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form8 = rawRow11008 := by decide +kernel

def row11008 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11008 : row11008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11008 := by decide +kernel

theorem rowEval11008 (x : Key → ℝ) : Integer.Sparse.eval row11008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11008, Integer.Sparse.eval_collectBalanced, rawRowCheck11008]

def rawRow11009 : Integer.Sparse Key := [(key1456, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1338, -2), (key1656, -2), (key1656, -2), (key1666, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1658, -2), (key1392, 1), (key1392, 1), (key1425, 1), (key1425, 1), (key1443, 1), (key1443, 1), (key1297, 1), (key1297, 1), (key1574, 1), (key1574, 1), (key1592, 1), (key1592, 1), (key1317, 1), (key1317, 1), (key1547, 1), (key1547, 1), (key1632, 1), (key1632, 1), (key1325, 1), (key1325, 1), (key1555, 1), (key1555, 1), (key1623, 1), (key1623, 1)]

theorem rawRowCheck11009 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form8 = rawRow11009 := by decide +kernel

def row11009 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11009 : row11009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11009 := by decide +kernel

theorem rowEval11009 (x : Key → ℝ) : Integer.Sparse.eval row11009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11009, Integer.Sparse.eval_collectBalanced, rawRowCheck11009]

def rawRow11010 : Integer.Sparse Key := [(key1456, -2), (key1465, -2), (key1456, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1658, -2), (key1344, -2), (key1658, -2), (key1425, 1), (key1443, 1), (key1392, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1623, 1), (key1325, 1), (key1555, 1)]

theorem rawRowCheck11010 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form8 = rawRow11010 := by decide +kernel

def row11010 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11010 : row11010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11010 := by decide +kernel

theorem rowEval11010 (x : Key → ℝ) : Integer.Sparse.eval row11010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11010, Integer.Sparse.eval_collectBalanced, rawRowCheck11010]

def rawRow11011 : Integer.Sparse Key := [(key1465, -2), (key1456, -2), (key1456, -2), (key1666, -2), (key1656, -2), (key1666, -2), (key1338, -2), (key1656, -2), (key1338, -2), (key1658, -2), (key1658, -2), (key1344, -2), (key1443, 1), (key1425, 1), (key1443, 1), (key1392, 1), (key1425, 1), (key1392, 1), (key1592, 1), (key1574, 1), (key1592, 1), (key1297, 1), (key1574, 1), (key1297, 1), (key1632, 1), (key1547, 1), (key1632, 1), (key1317, 1), (key1547, 1), (key1317, 1), (key1623, 1), (key1555, 1), (key1623, 1), (key1325, 1), (key1555, 1), (key1325, 1)]

theorem rawRowCheck11011 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form8 = rawRow11011 := by decide +kernel

def row11011 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11011 : row11011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11011 := by decide +kernel

theorem rowEval11011 (x : Key → ℝ) : Integer.Sparse.eval row11011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11011, Integer.Sparse.eval_collectBalanced, rawRowCheck11011]

def rawRow11012 : Integer.Sparse Key := [(key1656, -2), (key1658, -2), (key1666, -2), (key1338, -2), (key1344, -2), (key1456, -2), (key1658, -2), (key1465, -2), (key1666, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1547, 1), (key1555, 1), (key1574, 1), (key1623, 1), (key1592, 1), (key1632, 1), (key1317, 1), (key1325, 1), (key1425, 1), (key1623, 1), (key1443, 1), (key1632, 1), (key1297, 1), (key1325, 1), (key1392, 1), (key1555, 1), (key1443, 1), (key1592, 1), (key1297, 1), (key1317, 1), (key1392, 1), (key1547, 1), (key1425, 1), (key1574, 1)]

theorem rawRowCheck11012 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form8 = rawRow11012 := by decide +kernel

def row11012 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11012 : row11012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11012 := by decide +kernel

theorem rowEval11012 (x : Key → ℝ) : Integer.Sparse.eval row11012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11012, Integer.Sparse.eval_collectBalanced, rawRowCheck11012]

def rawRow11013 : Integer.Sparse Key := [(key1658, -2), (key1656, -2), (key1666, -2), (key1344, -2), (key1338, -2), (key1658, -2), (key1456, -2), (key1666, -2), (key1465, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1555, 1), (key1547, 1), (key1623, 1), (key1574, 1), (key1632, 1), (key1592, 1), (key1325, 1), (key1317, 1), (key1623, 1), (key1425, 1), (key1632, 1), (key1443, 1), (key1325, 1), (key1297, 1), (key1555, 1), (key1392, 1), (key1592, 1), (key1443, 1), (key1317, 1), (key1297, 1), (key1547, 1), (key1392, 1), (key1574, 1), (key1425, 1)]

theorem rawRowCheck11013 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form8 = rawRow11013 := by decide +kernel

def row11013 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11013 : row11013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11013 := by decide +kernel

theorem rowEval11013 (x : Key → ℝ) : Integer.Sparse.eval row11013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11013, Integer.Sparse.eval_collectBalanced, rawRowCheck11013]

def rawRow11014 : Integer.Sparse Key := [(key1656, -2), (key1666, -2), (key1658, -2), (key1456, -2), (key1465, -2), (key1338, -2), (key1666, -2), (key1344, -2), (key1658, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1574, 1), (key1592, 1), (key1547, 1), (key1632, 1), (key1555, 1), (key1623, 1), (key1425, 1), (key1443, 1), (key1317, 1), (key1632, 1), (key1325, 1), (key1623, 1), (key1392, 1), (key1443, 1), (key1297, 1), (key1592, 1), (key1325, 1), (key1555, 1), (key1392, 1), (key1425, 1), (key1297, 1), (key1574, 1), (key1317, 1), (key1547, 1)]

theorem rawRowCheck11014 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form8 = rawRow11014 := by decide +kernel

def row11014 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11014 : row11014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11014 := by decide +kernel

theorem rowEval11014 (x : Key → ℝ) : Integer.Sparse.eval row11014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form8) x := by
  rw [rowCheck11014, Integer.Sparse.eval_collectBalanced, rawRowCheck11014]

def rawRow11015 : Integer.Sparse Key := [(key1666, -2), (key1656, -2), (key1658, -2), (key1465, -2), (key1456, -2), (key1666, -2), (key1338, -2), (key1658, -2), (key1344, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1592, 1), (key1574, 1), (key1632, 1), (key1547, 1), (key1623, 1), (key1555, 1), (key1443, 1), (key1425, 1), (key1632, 1), (key1317, 1), (key1623, 1), (key1325, 1), (key1443, 1), (key1392, 1), (key1592, 1), (key1297, 1), (key1555, 1), (key1325, 1), (key1425, 1), (key1392, 1), (key1574, 1), (key1297, 1), (key1547, 1), (key1317, 1)]

theorem rawRowCheck11015 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form8 = rawRow11015 := by decide +kernel

def row11015 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11015 : row11015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11015 := by decide +kernel

theorem rowEval11015 (x : Key → ℝ) : Integer.Sparse.eval row11015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11015, Integer.Sparse.eval_collectBalanced, rawRowCheck11015]

def rawRow11016 : Integer.Sparse Key := [(key1658, -2), (key1666, -2), (key1656, -2), (key1658, -2), (key1666, -2), (key1344, -2), (key1465, -2), (key1338, -2), (key1456, -2), (key1656, -2), (key1338, -2), (key1456, -2), (key1623, 1), (key1632, 1), (key1555, 1), (key1592, 1), (key1547, 1), (key1574, 1), (key1623, 1), (key1632, 1), (key1325, 1), (key1443, 1), (key1317, 1), (key1425, 1), (key1555, 1), (key1592, 1), (key1325, 1), (key1443, 1), (key1297, 1), (key1392, 1), (key1547, 1), (key1574, 1), (key1317, 1), (key1425, 1), (key1297, 1), (key1392, 1)]

theorem rawRowCheck11016 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form8 = rawRow11016 := by decide +kernel

def row11016 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11016 : row11016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11016 := by decide +kernel

theorem rowEval11016 (x : Key → ℝ) : Integer.Sparse.eval row11016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form8) x := by
  rw [rowCheck11016, Integer.Sparse.eval_collectBalanced, rawRowCheck11016]

def rawRow11017 : Integer.Sparse Key := [(key1666, -2), (key1658, -2), (key1656, -2), (key1666, -2), (key1658, -2), (key1465, -2), (key1344, -2), (key1456, -2), (key1338, -2), (key1656, -2), (key1456, -2), (key1338, -2), (key1632, 1), (key1623, 1), (key1592, 1), (key1555, 1), (key1574, 1), (key1547, 1), (key1632, 1), (key1623, 1), (key1443, 1), (key1325, 1), (key1425, 1), (key1317, 1), (key1592, 1), (key1555, 1), (key1443, 1), (key1325, 1), (key1392, 1), (key1297, 1), (key1574, 1), (key1547, 1), (key1425, 1), (key1317, 1), (key1392, 1), (key1297, 1)]

theorem rawRowCheck11017 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form8 = rawRow11017 := by decide +kernel

def row11017 : Integer.Sparse Key := [(key1297, 2), (key1317, 2), (key1325, 2), (key1338, -4), (key1344, -2), (key1392, 2), (key1425, 2), (key1443, 2), (key1456, -4), (key1465, -2), (key1547, 2), (key1555, 2), (key1574, 2), (key1592, 2), (key1623, 2), (key1632, 2), (key1656, -4), (key1658, -4), (key1666, -4)]

theorem rowCheck11017 : row11017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11017 := by decide +kernel

theorem rowEval11017 (x : Key → ℝ) : Integer.Sparse.eval row11017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form8) x := by
  rw [rowCheck11017, Integer.Sparse.eval_collectBalanced, rawRowCheck11017]

def rawRow11018 : Integer.Sparse Key := [(key2609, 1), (key2613, 1), (key2625, 1), (key2647, 1), (key2637, 1), (key2652, 1), (key2664, 1), (key2668, 1), (key2779, 1), (key2937, 1), (key2791, 1), (key2942, 1), (key2699, 1), (key2736, 1), (key2802, 1), (key2949, 1), (key2896, 1), (key2975, 1), (key2723, 1), (key2746, 1), (key2826, 1), (key2959, 1), (key2903, 1), (key2982, 1), (key2613, -2), (key2629, -2), (key2647, -2), (key2668, -2), (key2783, -2), (key2937, -2), (key2703, -2), (key2736, -2), (key2806, -2), (key2949, -2), (key2894, -2), (key2973, -2)]

theorem rawRowCheck11018 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form9 = rawRow11018 := by decide +kernel

def row11018 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11018 : row11018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11018 := by decide +kernel

theorem rowEval11018 (x : Key → ℝ) : Integer.Sparse.eval row11018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11018, Integer.Sparse.eval_collectBalanced, rawRowCheck11018]

def rawRow11019 : Integer.Sparse Key := [(key2613, 1), (key2609, 1), (key2647, 1), (key2625, 1), (key2652, 1), (key2637, 1), (key2668, 1), (key2664, 1), (key2937, 1), (key2779, 1), (key2942, 1), (key2791, 1), (key2736, 1), (key2699, 1), (key2949, 1), (key2802, 1), (key2975, 1), (key2896, 1), (key2746, 1), (key2723, 1), (key2959, 1), (key2826, 1), (key2982, 1), (key2903, 1), (key2613, -2), (key2647, -2), (key2629, -2), (key2668, -2), (key2937, -2), (key2783, -2), (key2736, -2), (key2703, -2), (key2949, -2), (key2806, -2), (key2973, -2), (key2894, -2)]

theorem rawRowCheck11019 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form9 = rawRow11019 := by decide +kernel

def row11019 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11019 : row11019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11019 := by decide +kernel

theorem rowEval11019 (x : Key → ℝ) : Integer.Sparse.eval row11019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11019, Integer.Sparse.eval_collectBalanced, rawRowCheck11019]

def rawRow11020 : Integer.Sparse Key := [(key2625, 1), (key2637, 1), (key2609, 1), (key2652, 1), (key2613, 1), (key2647, 1), (key2779, 1), (key2791, 1), (key2664, 1), (key2942, 1), (key2668, 1), (key2937, 1), (key2802, 1), (key2896, 1), (key2699, 1), (key2975, 1), (key2736, 1), (key2949, 1), (key2826, 1), (key2903, 1), (key2723, 1), (key2982, 1), (key2746, 1), (key2959, 1), (key2629, -2), (key2613, -2), (key2647, -2), (key2783, -2), (key2668, -2), (key2937, -2), (key2806, -2), (key2894, -2), (key2703, -2), (key2973, -2), (key2736, -2), (key2949, -2)]

theorem rawRowCheck11020 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form9 = rawRow11020 := by decide +kernel

def row11020 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11020 : row11020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11020 := by decide +kernel

theorem rowEval11020 (x : Key → ℝ) : Integer.Sparse.eval row11020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11020, Integer.Sparse.eval_collectBalanced, rawRowCheck11020]

def rawRow11021 : Integer.Sparse Key := [(key2637, 1), (key2625, 1), (key2652, 1), (key2609, 1), (key2647, 1), (key2613, 1), (key2791, 1), (key2779, 1), (key2942, 1), (key2664, 1), (key2937, 1), (key2668, 1), (key2896, 1), (key2802, 1), (key2975, 1), (key2699, 1), (key2949, 1), (key2736, 1), (key2903, 1), (key2826, 1), (key2982, 1), (key2723, 1), (key2959, 1), (key2746, 1), (key2629, -2), (key2647, -2), (key2613, -2), (key2783, -2), (key2937, -2), (key2668, -2), (key2894, -2), (key2806, -2), (key2973, -2), (key2703, -2), (key2949, -2), (key2736, -2)]

theorem rawRowCheck11021 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form9 = rawRow11021 := by decide +kernel

def row11021 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11021 : row11021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11021 := by decide +kernel

theorem rowEval11021 (x : Key → ℝ) : Integer.Sparse.eval row11021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11021, Integer.Sparse.eval_collectBalanced, rawRowCheck11021]

def rawRow11022 : Integer.Sparse Key := [(key2647, 1), (key2652, 1), (key2613, 1), (key2637, 1), (key2609, 1), (key2625, 1), (key2937, 1), (key2942, 1), (key2668, 1), (key2791, 1), (key2664, 1), (key2779, 1), (key2949, 1), (key2975, 1), (key2736, 1), (key2896, 1), (key2699, 1), (key2802, 1), (key2959, 1), (key2982, 1), (key2746, 1), (key2903, 1), (key2723, 1), (key2826, 1), (key2647, -2), (key2613, -2), (key2629, -2), (key2937, -2), (key2668, -2), (key2783, -2), (key2949, -2), (key2973, -2), (key2736, -2), (key2894, -2), (key2703, -2), (key2806, -2)]

theorem rawRowCheck11022 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form9 = rawRow11022 := by decide +kernel

def row11022 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11022 : row11022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11022 := by decide +kernel

theorem rowEval11022 (x : Key → ℝ) : Integer.Sparse.eval row11022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11022, Integer.Sparse.eval_collectBalanced, rawRowCheck11022]

def rawRow11023 : Integer.Sparse Key := [(key2652, 1), (key2647, 1), (key2637, 1), (key2613, 1), (key2625, 1), (key2609, 1), (key2942, 1), (key2937, 1), (key2791, 1), (key2668, 1), (key2779, 1), (key2664, 1), (key2975, 1), (key2949, 1), (key2896, 1), (key2736, 1), (key2802, 1), (key2699, 1), (key2982, 1), (key2959, 1), (key2903, 1), (key2746, 1), (key2826, 1), (key2723, 1), (key2647, -2), (key2629, -2), (key2613, -2), (key2937, -2), (key2783, -2), (key2668, -2), (key2973, -2), (key2949, -2), (key2894, -2), (key2736, -2), (key2806, -2), (key2703, -2)]

theorem rawRowCheck11023 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form9 = rawRow11023 := by decide +kernel

def row11023 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11023 : row11023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11023 := by decide +kernel

theorem rowEval11023 (x : Key → ℝ) : Integer.Sparse.eval row11023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11023, Integer.Sparse.eval_collectBalanced, rawRowCheck11023]

def rawRow11024 : Integer.Sparse Key := [(key2664, 1), (key2668, 1), (key2699, 1), (key2736, 1), (key2723, 1), (key2746, 1), (key2609, 1), (key2613, 1), (key2802, 1), (key2949, 1), (key2826, 1), (key2959, 1), (key2625, 1), (key2647, 1), (key2779, 1), (key2937, 1), (key2903, 1), (key2982, 1), (key2637, 1), (key2652, 1), (key2791, 1), (key2942, 1), (key2896, 1), (key2975, 1), (key2668, -2), (key2703, -2), (key2736, -2), (key2613, -2), (key2806, -2), (key2949, -2), (key2629, -2), (key2647, -2), (key2783, -2), (key2937, -2), (key2894, -2), (key2973, -2)]

theorem rawRowCheck11024 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form9 = rawRow11024 := by decide +kernel

def row11024 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11024 : row11024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11024 := by decide +kernel

theorem rowEval11024 (x : Key → ℝ) : Integer.Sparse.eval row11024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11024, Integer.Sparse.eval_collectBalanced, rawRowCheck11024]

def rawRow11025 : Integer.Sparse Key := [(key2668, 1), (key2664, 1), (key2736, 1), (key2699, 1), (key2746, 1), (key2723, 1), (key2613, 1), (key2609, 1), (key2949, 1), (key2802, 1), (key2959, 1), (key2826, 1), (key2647, 1), (key2625, 1), (key2937, 1), (key2779, 1), (key2982, 1), (key2903, 1), (key2652, 1), (key2637, 1), (key2942, 1), (key2791, 1), (key2975, 1), (key2896, 1), (key2668, -2), (key2736, -2), (key2703, -2), (key2613, -2), (key2949, -2), (key2806, -2), (key2647, -2), (key2629, -2), (key2937, -2), (key2783, -2), (key2973, -2), (key2894, -2)]

theorem rawRowCheck11025 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form9 = rawRow11025 := by decide +kernel

def row11025 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11025 : row11025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11025 := by decide +kernel

theorem rowEval11025 (x : Key → ℝ) : Integer.Sparse.eval row11025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11025, Integer.Sparse.eval_collectBalanced, rawRowCheck11025]

def rawRow11026 : Integer.Sparse Key := [(key2699, 1), (key2723, 1), (key2664, 1), (key2746, 1), (key2668, 1), (key2736, 1), (key2802, 1), (key2826, 1), (key2609, 1), (key2959, 1), (key2613, 1), (key2949, 1), (key2779, 1), (key2903, 1), (key2625, 1), (key2982, 1), (key2647, 1), (key2937, 1), (key2791, 1), (key2896, 1), (key2637, 1), (key2975, 1), (key2652, 1), (key2942, 1), (key2703, -2), (key2668, -2), (key2736, -2), (key2806, -2), (key2613, -2), (key2949, -2), (key2783, -2), (key2894, -2), (key2629, -2), (key2973, -2), (key2647, -2), (key2937, -2)]

theorem rawRowCheck11026 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form9 = rawRow11026 := by decide +kernel

def row11026 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11026 : row11026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11026 := by decide +kernel

theorem rowEval11026 (x : Key → ℝ) : Integer.Sparse.eval row11026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11026, Integer.Sparse.eval_collectBalanced, rawRowCheck11026]

def rawRow11027 : Integer.Sparse Key := [(key2723, 1), (key2699, 1), (key2746, 1), (key2664, 1), (key2736, 1), (key2668, 1), (key2826, 1), (key2802, 1), (key2959, 1), (key2609, 1), (key2949, 1), (key2613, 1), (key2903, 1), (key2779, 1), (key2982, 1), (key2625, 1), (key2937, 1), (key2647, 1), (key2896, 1), (key2791, 1), (key2975, 1), (key2637, 1), (key2942, 1), (key2652, 1), (key2703, -2), (key2736, -2), (key2668, -2), (key2806, -2), (key2949, -2), (key2613, -2), (key2894, -2), (key2783, -2), (key2973, -2), (key2629, -2), (key2937, -2), (key2647, -2)]

theorem rawRowCheck11027 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form9 = rawRow11027 := by decide +kernel

def row11027 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11027 : row11027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11027 := by decide +kernel

theorem rowEval11027 (x : Key → ℝ) : Integer.Sparse.eval row11027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11027, Integer.Sparse.eval_collectBalanced, rawRowCheck11027]

def rawRow11028 : Integer.Sparse Key := [(key2736, 1), (key2746, 1), (key2668, 1), (key2723, 1), (key2664, 1), (key2699, 1), (key2949, 1), (key2959, 1), (key2613, 1), (key2826, 1), (key2609, 1), (key2802, 1), (key2937, 1), (key2982, 1), (key2647, 1), (key2903, 1), (key2625, 1), (key2779, 1), (key2942, 1), (key2975, 1), (key2652, 1), (key2896, 1), (key2637, 1), (key2791, 1), (key2736, -2), (key2668, -2), (key2703, -2), (key2949, -2), (key2613, -2), (key2806, -2), (key2937, -2), (key2973, -2), (key2647, -2), (key2894, -2), (key2629, -2), (key2783, -2)]

theorem rawRowCheck11028 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form9 = rawRow11028 := by decide +kernel

def row11028 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11028 : row11028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11028 := by decide +kernel

theorem rowEval11028 (x : Key → ℝ) : Integer.Sparse.eval row11028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11028, Integer.Sparse.eval_collectBalanced, rawRowCheck11028]

def rawRow11029 : Integer.Sparse Key := [(key2746, 1), (key2736, 1), (key2723, 1), (key2668, 1), (key2699, 1), (key2664, 1), (key2959, 1), (key2949, 1), (key2826, 1), (key2613, 1), (key2802, 1), (key2609, 1), (key2982, 1), (key2937, 1), (key2903, 1), (key2647, 1), (key2779, 1), (key2625, 1), (key2975, 1), (key2942, 1), (key2896, 1), (key2652, 1), (key2791, 1), (key2637, 1), (key2736, -2), (key2703, -2), (key2668, -2), (key2949, -2), (key2806, -2), (key2613, -2), (key2973, -2), (key2937, -2), (key2894, -2), (key2647, -2), (key2783, -2), (key2629, -2)]

theorem rawRowCheck11029 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form9 = rawRow11029 := by decide +kernel

def row11029 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11029 : row11029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11029 := by decide +kernel

theorem rowEval11029 (x : Key → ℝ) : Integer.Sparse.eval row11029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11029, Integer.Sparse.eval_collectBalanced, rawRowCheck11029]

def rawRow11030 : Integer.Sparse Key := [(key2779, 1), (key2791, 1), (key2802, 1), (key2896, 1), (key2826, 1), (key2903, 1), (key2625, 1), (key2637, 1), (key2699, 1), (key2975, 1), (key2723, 1), (key2982, 1), (key2609, 1), (key2652, 1), (key2664, 1), (key2942, 1), (key2746, 1), (key2959, 1), (key2613, 1), (key2647, 1), (key2668, 1), (key2937, 1), (key2736, 1), (key2949, 1), (key2783, -2), (key2806, -2), (key2894, -2), (key2629, -2), (key2703, -2), (key2973, -2), (key2613, -2), (key2647, -2), (key2668, -2), (key2937, -2), (key2736, -2), (key2949, -2)]

theorem rawRowCheck11030 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form9 = rawRow11030 := by decide +kernel

def row11030 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11030 : row11030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11030 := by decide +kernel

theorem rowEval11030 (x : Key → ℝ) : Integer.Sparse.eval row11030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11030, Integer.Sparse.eval_collectBalanced, rawRowCheck11030]

def rawRow11031 : Integer.Sparse Key := [(key2791, 1), (key2779, 1), (key2896, 1), (key2802, 1), (key2903, 1), (key2826, 1), (key2637, 1), (key2625, 1), (key2975, 1), (key2699, 1), (key2982, 1), (key2723, 1), (key2652, 1), (key2609, 1), (key2942, 1), (key2664, 1), (key2959, 1), (key2746, 1), (key2647, 1), (key2613, 1), (key2937, 1), (key2668, 1), (key2949, 1), (key2736, 1), (key2783, -2), (key2894, -2), (key2806, -2), (key2629, -2), (key2973, -2), (key2703, -2), (key2647, -2), (key2613, -2), (key2937, -2), (key2668, -2), (key2949, -2), (key2736, -2)]

theorem rawRowCheck11031 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form9 = rawRow11031 := by decide +kernel

def row11031 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11031 : row11031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11031 := by decide +kernel

theorem rowEval11031 (x : Key → ℝ) : Integer.Sparse.eval row11031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11031, Integer.Sparse.eval_collectBalanced, rawRowCheck11031]

def rawRow11032 : Integer.Sparse Key := [(key2802, 1), (key2826, 1), (key2779, 1), (key2903, 1), (key2791, 1), (key2896, 1), (key2699, 1), (key2723, 1), (key2625, 1), (key2982, 1), (key2637, 1), (key2975, 1), (key2664, 1), (key2746, 1), (key2609, 1), (key2959, 1), (key2652, 1), (key2942, 1), (key2668, 1), (key2736, 1), (key2613, 1), (key2949, 1), (key2647, 1), (key2937, 1), (key2806, -2), (key2783, -2), (key2894, -2), (key2703, -2), (key2629, -2), (key2973, -2), (key2668, -2), (key2736, -2), (key2613, -2), (key2949, -2), (key2647, -2), (key2937, -2)]

theorem rawRowCheck11032 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form9 = rawRow11032 := by decide +kernel

def row11032 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11032 : row11032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11032 := by decide +kernel

theorem rowEval11032 (x : Key → ℝ) : Integer.Sparse.eval row11032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11032, Integer.Sparse.eval_collectBalanced, rawRowCheck11032]

def rawRow11033 : Integer.Sparse Key := [(key2826, 1), (key2802, 1), (key2903, 1), (key2779, 1), (key2896, 1), (key2791, 1), (key2723, 1), (key2699, 1), (key2982, 1), (key2625, 1), (key2975, 1), (key2637, 1), (key2746, 1), (key2664, 1), (key2959, 1), (key2609, 1), (key2942, 1), (key2652, 1), (key2736, 1), (key2668, 1), (key2949, 1), (key2613, 1), (key2937, 1), (key2647, 1), (key2806, -2), (key2894, -2), (key2783, -2), (key2703, -2), (key2973, -2), (key2629, -2), (key2736, -2), (key2668, -2), (key2949, -2), (key2613, -2), (key2937, -2), (key2647, -2)]

theorem rawRowCheck11033 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form9 = rawRow11033 := by decide +kernel

def row11033 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11033 : row11033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11033 := by decide +kernel

theorem rowEval11033 (x : Key → ℝ) : Integer.Sparse.eval row11033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11033, Integer.Sparse.eval_collectBalanced, rawRowCheck11033]

def rawRow11034 : Integer.Sparse Key := [(key2896, 1), (key2903, 1), (key2791, 1), (key2826, 1), (key2779, 1), (key2802, 1), (key2975, 1), (key2982, 1), (key2637, 1), (key2723, 1), (key2625, 1), (key2699, 1), (key2942, 1), (key2959, 1), (key2652, 1), (key2746, 1), (key2609, 1), (key2664, 1), (key2937, 1), (key2949, 1), (key2647, 1), (key2736, 1), (key2613, 1), (key2668, 1), (key2894, -2), (key2783, -2), (key2806, -2), (key2973, -2), (key2629, -2), (key2703, -2), (key2937, -2), (key2949, -2), (key2647, -2), (key2736, -2), (key2613, -2), (key2668, -2)]

theorem rawRowCheck11034 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form9 = rawRow11034 := by decide +kernel

def row11034 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11034 : row11034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11034 := by decide +kernel

theorem rowEval11034 (x : Key → ℝ) : Integer.Sparse.eval row11034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11034, Integer.Sparse.eval_collectBalanced, rawRowCheck11034]

def rawRow11035 : Integer.Sparse Key := [(key2903, 1), (key2896, 1), (key2826, 1), (key2791, 1), (key2802, 1), (key2779, 1), (key2982, 1), (key2975, 1), (key2723, 1), (key2637, 1), (key2699, 1), (key2625, 1), (key2959, 1), (key2942, 1), (key2746, 1), (key2652, 1), (key2664, 1), (key2609, 1), (key2949, 1), (key2937, 1), (key2736, 1), (key2647, 1), (key2668, 1), (key2613, 1), (key2894, -2), (key2806, -2), (key2783, -2), (key2973, -2), (key2703, -2), (key2629, -2), (key2949, -2), (key2937, -2), (key2736, -2), (key2647, -2), (key2668, -2), (key2613, -2)]

theorem rawRowCheck11035 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form9 = rawRow11035 := by decide +kernel

def row11035 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11035 : row11035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11035 := by decide +kernel

theorem rowEval11035 (x : Key → ℝ) : Integer.Sparse.eval row11035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11035, Integer.Sparse.eval_collectBalanced, rawRowCheck11035]

def rawRow11036 : Integer.Sparse Key := [(key2937, 1), (key2942, 1), (key2949, 1), (key2975, 1), (key2959, 1), (key2982, 1), (key2647, 1), (key2652, 1), (key2736, 1), (key2896, 1), (key2746, 1), (key2903, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2609, 1), (key2625, 1), (key2664, 1), (key2779, 1), (key2699, 1), (key2802, 1), (key2937, -2), (key2949, -2), (key2973, -2), (key2647, -2), (key2736, -2), (key2894, -2), (key2613, -2), (key2629, -2), (key2668, -2), (key2783, -2), (key2703, -2), (key2806, -2)]

theorem rawRowCheck11036 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form9 = rawRow11036 := by decide +kernel

def row11036 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11036 : row11036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11036 := by decide +kernel

theorem rowEval11036 (x : Key → ℝ) : Integer.Sparse.eval row11036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11036, Integer.Sparse.eval_collectBalanced, rawRowCheck11036]

def rawRow11037 : Integer.Sparse Key := [(key2942, 1), (key2937, 1), (key2975, 1), (key2949, 1), (key2982, 1), (key2959, 1), (key2652, 1), (key2647, 1), (key2896, 1), (key2736, 1), (key2903, 1), (key2746, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2625, 1), (key2609, 1), (key2779, 1), (key2664, 1), (key2802, 1), (key2699, 1), (key2937, -2), (key2973, -2), (key2949, -2), (key2647, -2), (key2894, -2), (key2736, -2), (key2629, -2), (key2613, -2), (key2783, -2), (key2668, -2), (key2806, -2), (key2703, -2)]

theorem rawRowCheck11037 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form9 = rawRow11037 := by decide +kernel

def row11037 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11037 : row11037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11037 := by decide +kernel

theorem rowEval11037 (x : Key → ℝ) : Integer.Sparse.eval row11037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11037, Integer.Sparse.eval_collectBalanced, rawRowCheck11037]

def rawRow11038 : Integer.Sparse Key := [(key2949, 1), (key2959, 1), (key2937, 1), (key2982, 1), (key2942, 1), (key2975, 1), (key2736, 1), (key2746, 1), (key2647, 1), (key2903, 1), (key2652, 1), (key2896, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2664, 1), (key2699, 1), (key2609, 1), (key2802, 1), (key2625, 1), (key2779, 1), (key2949, -2), (key2937, -2), (key2973, -2), (key2736, -2), (key2647, -2), (key2894, -2), (key2668, -2), (key2703, -2), (key2613, -2), (key2806, -2), (key2629, -2), (key2783, -2)]

theorem rawRowCheck11038 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form9 = rawRow11038 := by decide +kernel

def row11038 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11038 : row11038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11038 := by decide +kernel

theorem rowEval11038 (x : Key → ℝ) : Integer.Sparse.eval row11038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11038, Integer.Sparse.eval_collectBalanced, rawRowCheck11038]

def rawRow11039 : Integer.Sparse Key := [(key2959, 1), (key2949, 1), (key2982, 1), (key2937, 1), (key2975, 1), (key2942, 1), (key2746, 1), (key2736, 1), (key2903, 1), (key2647, 1), (key2896, 1), (key2652, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2699, 1), (key2664, 1), (key2802, 1), (key2609, 1), (key2779, 1), (key2625, 1), (key2949, -2), (key2973, -2), (key2937, -2), (key2736, -2), (key2894, -2), (key2647, -2), (key2703, -2), (key2668, -2), (key2806, -2), (key2613, -2), (key2783, -2), (key2629, -2)]

theorem rawRowCheck11039 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form9 = rawRow11039 := by decide +kernel

def row11039 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11039 : row11039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11039 := by decide +kernel

theorem rowEval11039 (x : Key → ℝ) : Integer.Sparse.eval row11039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11039, Integer.Sparse.eval_collectBalanced, rawRowCheck11039]

def rawRow11040 : Integer.Sparse Key := [(key2975, 1), (key2982, 1), (key2942, 1), (key2959, 1), (key2937, 1), (key2949, 1), (key2896, 1), (key2903, 1), (key2652, 1), (key2746, 1), (key2647, 1), (key2736, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2779, 1), (key2802, 1), (key2625, 1), (key2699, 1), (key2609, 1), (key2664, 1), (key2973, -2), (key2937, -2), (key2949, -2), (key2894, -2), (key2647, -2), (key2736, -2), (key2783, -2), (key2806, -2), (key2629, -2), (key2703, -2), (key2613, -2), (key2668, -2)]

theorem rawRowCheck11040 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form9 = rawRow11040 := by decide +kernel

def row11040 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11040 : row11040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11040 := by decide +kernel

theorem rowEval11040 (x : Key → ℝ) : Integer.Sparse.eval row11040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11040, Integer.Sparse.eval_collectBalanced, rawRowCheck11040]

def rawRow11041 : Integer.Sparse Key := [(key2982, 1), (key2975, 1), (key2959, 1), (key2942, 1), (key2949, 1), (key2937, 1), (key2903, 1), (key2896, 1), (key2746, 1), (key2652, 1), (key2736, 1), (key2647, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2802, 1), (key2779, 1), (key2699, 1), (key2625, 1), (key2664, 1), (key2609, 1), (key2973, -2), (key2949, -2), (key2937, -2), (key2894, -2), (key2736, -2), (key2647, -2), (key2806, -2), (key2783, -2), (key2703, -2), (key2629, -2), (key2668, -2), (key2613, -2)]

theorem rawRowCheck11041 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form9 = rawRow11041 := by decide +kernel

def row11041 : Integer.Sparse Key := [(key2609, 1), (key2613, -1), (key2625, 1), (key2629, -2), (key2637, 1), (key2647, -1), (key2652, 1), (key2664, 1), (key2668, -1), (key2699, 1), (key2703, -2), (key2723, 1), (key2736, -1), (key2746, 1), (key2779, 1), (key2783, -2), (key2791, 1), (key2802, 1), (key2806, -2), (key2826, 1), (key2894, -2), (key2896, 1), (key2903, 1), (key2937, -1), (key2942, 1), (key2949, -1), (key2959, 1), (key2973, -2), (key2975, 1), (key2982, 1)]

theorem rowCheck11041 : row11041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11041 := by decide +kernel

theorem rowEval11041 (x : Key → ℝ) : Integer.Sparse.eval row11041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11041, Integer.Sparse.eval_collectBalanced, rawRowCheck11041]

def rawRow11042 : Integer.Sparse Key := [(key2613, 1), (key2613, 1), (key2629, 1), (key2629, 1), (key2637, 1), (key2637, 1), (key2668, 1), (key2668, 1), (key2783, 1), (key2783, 1), (key2791, 1), (key2791, 1), (key2703, 1), (key2703, 1), (key2806, 1), (key2806, 1), (key2857, 1), (key2857, 1), (key2723, 1), (key2723, 1), (key2826, 1), (key2826, 1), (key2867, 1), (key2867, 1), (key2609, -2), (key2625, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2779, -2), (key2699, -2), (key2699, -2), (key2802, -2), (key2802, -2), (key2852, -2), (key2852, -2)]

theorem rawRowCheck11042 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form9 = rawRow11042 := by decide +kernel

def row11042 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11042 : row11042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11042 := by decide +kernel

theorem rowEval11042 (x : Key → ℝ) : Integer.Sparse.eval row11042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11042, Integer.Sparse.eval_collectBalanced, rawRowCheck11042]

def rawRow11043 : Integer.Sparse Key := [(key2629, 1), (key2637, 1), (key2613, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2625, -2), (key2609, -2), (key2625, -2), (key2779, -2), (key2664, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2852, -2), (key2699, -2), (key2802, -2)]

theorem rawRowCheck11043 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form9 = rawRow11043 := by decide +kernel

def row11043 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11043 : row11043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11043 := by decide +kernel

theorem rowEval11043 (x : Key → ℝ) : Integer.Sparse.eval row11043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11043, Integer.Sparse.eval_collectBalanced, rawRowCheck11043]

def rawRow11044 : Integer.Sparse Key := [(key2637, 1), (key2629, 1), (key2637, 1), (key2613, 1), (key2629, 1), (key2613, 1), (key2791, 1), (key2783, 1), (key2791, 1), (key2668, 1), (key2783, 1), (key2668, 1), (key2857, 1), (key2806, 1), (key2857, 1), (key2703, 1), (key2806, 1), (key2703, 1), (key2867, 1), (key2826, 1), (key2867, 1), (key2723, 1), (key2826, 1), (key2723, 1), (key2625, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2779, -2), (key2664, -2), (key2852, -2), (key2802, -2), (key2852, -2), (key2699, -2), (key2802, -2), (key2699, -2)]

theorem rawRowCheck11044 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form9 = rawRow11044 := by decide +kernel

def row11044 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11044 : row11044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11044 := by decide +kernel

theorem rowEval11044 (x : Key → ℝ) : Integer.Sparse.eval row11044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11044, Integer.Sparse.eval_collectBalanced, rawRowCheck11044]

def rawRow11045 : Integer.Sparse Key := [(key2668, 1), (key2668, 1), (key2703, 1), (key2703, 1), (key2723, 1), (key2723, 1), (key2613, 1), (key2613, 1), (key2806, 1), (key2806, 1), (key2826, 1), (key2826, 1), (key2629, 1), (key2629, 1), (key2783, 1), (key2783, 1), (key2867, 1), (key2867, 1), (key2637, 1), (key2637, 1), (key2791, 1), (key2791, 1), (key2857, 1), (key2857, 1), (key2664, -2), (key2699, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2802, -2), (key2625, -2), (key2625, -2), (key2779, -2), (key2779, -2), (key2852, -2), (key2852, -2)]

theorem rawRowCheck11045 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form9 = rawRow11045 := by decide +kernel

def row11045 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11045 : row11045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11045 := by decide +kernel

theorem rowEval11045 (x : Key → ℝ) : Integer.Sparse.eval row11045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11045, Integer.Sparse.eval_collectBalanced, rawRowCheck11045]

def rawRow11046 : Integer.Sparse Key := [(key2703, 1), (key2723, 1), (key2668, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2699, -2), (key2664, -2), (key2699, -2), (key2802, -2), (key2609, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2852, -2), (key2625, -2), (key2779, -2)]

theorem rawRowCheck11046 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form9 = rawRow11046 := by decide +kernel

def row11046 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11046 : row11046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11046 := by decide +kernel

theorem rowEval11046 (x : Key → ℝ) : Integer.Sparse.eval row11046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11046, Integer.Sparse.eval_collectBalanced, rawRowCheck11046]

def rawRow11047 : Integer.Sparse Key := [(key2723, 1), (key2703, 1), (key2723, 1), (key2668, 1), (key2703, 1), (key2668, 1), (key2826, 1), (key2806, 1), (key2826, 1), (key2613, 1), (key2806, 1), (key2613, 1), (key2867, 1), (key2783, 1), (key2867, 1), (key2629, 1), (key2783, 1), (key2629, 1), (key2857, 1), (key2791, 1), (key2857, 1), (key2637, 1), (key2791, 1), (key2637, 1), (key2699, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2802, -2), (key2609, -2), (key2852, -2), (key2779, -2), (key2852, -2), (key2625, -2), (key2779, -2), (key2625, -2)]

theorem rawRowCheck11047 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form9 = rawRow11047 := by decide +kernel

def row11047 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11047 : row11047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11047 := by decide +kernel

theorem rowEval11047 (x : Key → ℝ) : Integer.Sparse.eval row11047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11047, Integer.Sparse.eval_collectBalanced, rawRowCheck11047]

def rawRow11048 : Integer.Sparse Key := [(key2783, 1), (key2791, 1), (key2806, 1), (key2857, 1), (key2826, 1), (key2867, 1), (key2629, 1), (key2637, 1), (key2703, 1), (key2857, 1), (key2723, 1), (key2867, 1), (key2613, 1), (key2637, 1), (key2668, 1), (key2791, 1), (key2723, 1), (key2826, 1), (key2613, 1), (key2629, 1), (key2668, 1), (key2783, 1), (key2703, 1), (key2806, 1), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2852, -2), (key2609, -2), (key2625, -2), (key2664, -2), (key2779, -2), (key2699, -2), (key2802, -2)]

theorem rawRowCheck11048 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form9 = rawRow11048 := by decide +kernel

def row11048 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11048 : row11048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11048 := by decide +kernel

theorem rowEval11048 (x : Key → ℝ) : Integer.Sparse.eval row11048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11048, Integer.Sparse.eval_collectBalanced, rawRowCheck11048]

def rawRow11049 : Integer.Sparse Key := [(key2791, 1), (key2783, 1), (key2857, 1), (key2806, 1), (key2867, 1), (key2826, 1), (key2637, 1), (key2629, 1), (key2857, 1), (key2703, 1), (key2867, 1), (key2723, 1), (key2637, 1), (key2613, 1), (key2791, 1), (key2668, 1), (key2826, 1), (key2723, 1), (key2629, 1), (key2613, 1), (key2783, 1), (key2668, 1), (key2806, 1), (key2703, 1), (key2779, -2), (key2852, -2), (key2802, -2), (key2625, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2609, -2), (key2779, -2), (key2664, -2), (key2802, -2), (key2699, -2)]

theorem rawRowCheck11049 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form9 = rawRow11049 := by decide +kernel

def row11049 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11049 : row11049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11049 := by decide +kernel

theorem rowEval11049 (x : Key → ℝ) : Integer.Sparse.eval row11049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11049, Integer.Sparse.eval_collectBalanced, rawRowCheck11049]

def rawRow11050 : Integer.Sparse Key := [(key2806, 1), (key2826, 1), (key2783, 1), (key2867, 1), (key2791, 1), (key2857, 1), (key2703, 1), (key2723, 1), (key2629, 1), (key2867, 1), (key2637, 1), (key2857, 1), (key2668, 1), (key2723, 1), (key2613, 1), (key2826, 1), (key2637, 1), (key2791, 1), (key2668, 1), (key2703, 1), (key2613, 1), (key2806, 1), (key2629, 1), (key2783, 1), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2852, -2), (key2664, -2), (key2699, -2), (key2609, -2), (key2802, -2), (key2625, -2), (key2779, -2)]

theorem rawRowCheck11050 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form9 = rawRow11050 := by decide +kernel

def row11050 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11050 : row11050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11050 := by decide +kernel

theorem rowEval11050 (x : Key → ℝ) : Integer.Sparse.eval row11050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form9) x := by
  rw [rowCheck11050, Integer.Sparse.eval_collectBalanced, rawRowCheck11050]

def rawRow11051 : Integer.Sparse Key := [(key2826, 1), (key2806, 1), (key2867, 1), (key2783, 1), (key2857, 1), (key2791, 1), (key2723, 1), (key2703, 1), (key2867, 1), (key2629, 1), (key2857, 1), (key2637, 1), (key2723, 1), (key2668, 1), (key2826, 1), (key2613, 1), (key2791, 1), (key2637, 1), (key2703, 1), (key2668, 1), (key2806, 1), (key2613, 1), (key2783, 1), (key2629, 1), (key2802, -2), (key2852, -2), (key2779, -2), (key2699, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2664, -2), (key2802, -2), (key2609, -2), (key2779, -2), (key2625, -2)]

theorem rawRowCheck11051 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form9 = rawRow11051 := by decide +kernel

def row11051 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11051 : row11051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11051 := by decide +kernel

theorem rowEval11051 (x : Key → ℝ) : Integer.Sparse.eval row11051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11051, Integer.Sparse.eval_collectBalanced, rawRowCheck11051]

def rawRow11052 : Integer.Sparse Key := [(key2857, 1), (key2867, 1), (key2791, 1), (key2826, 1), (key2783, 1), (key2806, 1), (key2857, 1), (key2867, 1), (key2637, 1), (key2723, 1), (key2629, 1), (key2703, 1), (key2791, 1), (key2826, 1), (key2637, 1), (key2723, 1), (key2613, 1), (key2668, 1), (key2783, 1), (key2806, 1), (key2629, 1), (key2703, 1), (key2613, 1), (key2668, 1), (key2852, -2), (key2779, -2), (key2802, -2), (key2852, -2), (key2625, -2), (key2699, -2), (key2779, -2), (key2802, -2), (key2625, -2), (key2699, -2), (key2609, -2), (key2664, -2)]

theorem rawRowCheck11052 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form9 = rawRow11052 := by decide +kernel

def row11052 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11052 : row11052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11052 := by decide +kernel

theorem rowEval11052 (x : Key → ℝ) : Integer.Sparse.eval row11052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form9) x := by
  rw [rowCheck11052, Integer.Sparse.eval_collectBalanced, rawRowCheck11052]

def rawRow11053 : Integer.Sparse Key := [(key2867, 1), (key2857, 1), (key2826, 1), (key2791, 1), (key2806, 1), (key2783, 1), (key2867, 1), (key2857, 1), (key2723, 1), (key2637, 1), (key2703, 1), (key2629, 1), (key2826, 1), (key2791, 1), (key2723, 1), (key2637, 1), (key2668, 1), (key2613, 1), (key2806, 1), (key2783, 1), (key2703, 1), (key2629, 1), (key2668, 1), (key2613, 1), (key2852, -2), (key2802, -2), (key2779, -2), (key2852, -2), (key2699, -2), (key2625, -2), (key2802, -2), (key2779, -2), (key2699, -2), (key2625, -2), (key2664, -2), (key2609, -2)]

theorem rawRowCheck11053 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form9 = rawRow11053 := by decide +kernel

def row11053 : Integer.Sparse Key := [(key2609, -2), (key2613, 2), (key2625, -4), (key2629, 2), (key2637, 2), (key2664, -2), (key2668, 2), (key2699, -4), (key2703, 2), (key2723, 2), (key2779, -4), (key2783, 2), (key2791, 2), (key2802, -4), (key2806, 2), (key2826, 2), (key2852, -4), (key2857, 2), (key2867, 2)]

theorem rowCheck11053 : row11053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11053 := by decide +kernel

theorem rowEval11053 (x : Key → ℝ) : Integer.Sparse.eval row11053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form9) x := by
  rw [rowCheck11053, Integer.Sparse.eval_collectBalanced, rawRowCheck11053]

def rawRow11054 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1614, -6), (key1810, -6), (key1288, 2), (key1308, 2), (key1334, 2), (key1383, 2), (key1538, 2), (key1769, 2), (key1416, 2), (key1452, 2), (key1565, 2), (key1785, 2), (key1652, 2), (key1810, 2)]

theorem rawRowCheck11054 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form10 = rawRow11054 := by decide +kernel

def row11054 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11054 : row11054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11054 := by decide +kernel

theorem rowEval11054 (x : Key → ℝ) : Integer.Sparse.eval row11054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11054, Integer.Sparse.eval_collectBalanced, rawRowCheck11054]

def rawRow11055 : Integer.Sparse Key := [(key1308, -6), (key1416, -6), (key1810, -6), (key1614, -6), (key1288, 2), (key1334, 2), (key1308, 2), (key1383, 2), (key1769, 2), (key1538, 2), (key1452, 2), (key1416, 2), (key1785, 2), (key1565, 2), (key1810, 2), (key1652, 2)]

theorem rawRowCheck11055 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form10 = rawRow11055 := by decide +kernel

def row11055 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11055 : row11055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11055 := by decide +kernel

theorem rowEval11055 (x : Key → ℝ) : Integer.Sparse.eval row11055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11055, Integer.Sparse.eval_collectBalanced, rawRowCheck11055]

def rawRow11056 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1416, -6), (key1810, -6), (key1308, 2), (key1288, 2), (key1334, 2), (key1538, 2), (key1383, 2), (key1769, 2), (key1565, 2), (key1652, 2), (key1416, 2), (key1810, 2), (key1452, 2), (key1785, 2)]

theorem rawRowCheck11056 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form10 = rawRow11056 := by decide +kernel

def row11056 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11056 : row11056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11056 := by decide +kernel

theorem rowEval11056 (x : Key → ℝ) : Integer.Sparse.eval row11056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11056, Integer.Sparse.eval_collectBalanced, rawRowCheck11056]

def rawRow11057 : Integer.Sparse Key := [(key1308, -6), (key1614, -6), (key1810, -6), (key1416, -6), (key1308, 2), (key1334, 2), (key1288, 2), (key1538, 2), (key1769, 2), (key1383, 2), (key1652, 2), (key1565, 2), (key1810, 2), (key1416, 2), (key1785, 2), (key1452, 2)]

theorem rawRowCheck11057 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form10 = rawRow11057 := by decide +kernel

def row11057 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11057 : row11057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11057 := by decide +kernel

theorem rowEval11057 (x : Key → ℝ) : Integer.Sparse.eval row11057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11057, Integer.Sparse.eval_collectBalanced, rawRowCheck11057]

def rawRow11058 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1416, -6), (key1614, -6), (key1334, 2), (key1288, 2), (key1308, 2), (key1769, 2), (key1383, 2), (key1538, 2), (key1785, 2), (key1810, 2), (key1452, 2), (key1652, 2), (key1416, 2), (key1565, 2)]

theorem rawRowCheck11058 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form10 = rawRow11058 := by decide +kernel

def row11058 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11058 : row11058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11058 := by decide +kernel

theorem rowEval11058 (x : Key → ℝ) : Integer.Sparse.eval row11058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11058, Integer.Sparse.eval_collectBalanced, rawRowCheck11058]

def rawRow11059 : Integer.Sparse Key := [(key1308, -6), (key1810, -6), (key1614, -6), (key1416, -6), (key1334, 2), (key1308, 2), (key1288, 2), (key1769, 2), (key1538, 2), (key1383, 2), (key1810, 2), (key1785, 2), (key1652, 2), (key1452, 2), (key1565, 2), (key1416, 2)]

theorem rawRowCheck11059 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form10 = rawRow11059 := by decide +kernel

def row11059 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11059 : row11059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11059 := by decide +kernel

theorem rowEval11059 (x : Key → ℝ) : Integer.Sparse.eval row11059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11059, Integer.Sparse.eval_collectBalanced, rawRowCheck11059]

def rawRow11060 : Integer.Sparse Key := [(key1416, -6), (key1308, -6), (key1614, -6), (key1810, -6), (key1383, 2), (key1416, 2), (key1452, 2), (key1288, 2), (key1565, 2), (key1785, 2), (key1308, 2), (key1334, 2), (key1538, 2), (key1769, 2), (key1652, 2), (key1810, 2)]

theorem rawRowCheck11060 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form10 = rawRow11060 := by decide +kernel

def row11060 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11060 : row11060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11060 := by decide +kernel

theorem rowEval11060 (x : Key → ℝ) : Integer.Sparse.eval row11060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11060, Integer.Sparse.eval_collectBalanced, rawRowCheck11060]

def rawRow11061 : Integer.Sparse Key := [(key1416, -6), (key1308, -6), (key1810, -6), (key1614, -6), (key1383, 2), (key1452, 2), (key1416, 2), (key1288, 2), (key1785, 2), (key1565, 2), (key1334, 2), (key1308, 2), (key1769, 2), (key1538, 2), (key1810, 2), (key1652, 2)]

theorem rawRowCheck11061 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form10 = rawRow11061 := by decide +kernel

def row11061 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11061 : row11061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11061 := by decide +kernel

theorem rowEval11061 (x : Key → ℝ) : Integer.Sparse.eval row11061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11061, Integer.Sparse.eval_collectBalanced, rawRowCheck11061]

def rawRow11062 : Integer.Sparse Key := [(key1416, -6), (key1614, -6), (key1308, -6), (key1810, -6), (key1416, 2), (key1383, 2), (key1452, 2), (key1565, 2), (key1288, 2), (key1785, 2), (key1538, 2), (key1652, 2), (key1308, 2), (key1810, 2), (key1334, 2), (key1769, 2)]

theorem rawRowCheck11062 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form10 = rawRow11062 := by decide +kernel

def row11062 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11062 : row11062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11062 := by decide +kernel

theorem rowEval11062 (x : Key → ℝ) : Integer.Sparse.eval row11062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11062, Integer.Sparse.eval_collectBalanced, rawRowCheck11062]

def rawRow11063 : Integer.Sparse Key := [(key1416, -6), (key1614, -6), (key1810, -6), (key1308, -6), (key1416, 2), (key1452, 2), (key1383, 2), (key1565, 2), (key1785, 2), (key1288, 2), (key1652, 2), (key1538, 2), (key1810, 2), (key1308, 2), (key1769, 2), (key1334, 2)]

theorem rawRowCheck11063 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form10 = rawRow11063 := by decide +kernel

def row11063 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11063 : row11063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11063 := by decide +kernel

theorem rowEval11063 (x : Key → ℝ) : Integer.Sparse.eval row11063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11063, Integer.Sparse.eval_collectBalanced, rawRowCheck11063]

def rawRow11064 : Integer.Sparse Key := [(key1416, -6), (key1810, -6), (key1308, -6), (key1614, -6), (key1452, 2), (key1383, 2), (key1416, 2), (key1785, 2), (key1288, 2), (key1565, 2), (key1769, 2), (key1810, 2), (key1334, 2), (key1652, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11064 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form10 = rawRow11064 := by decide +kernel

def row11064 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11064 : row11064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11064 := by decide +kernel

theorem rowEval11064 (x : Key → ℝ) : Integer.Sparse.eval row11064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11064, Integer.Sparse.eval_collectBalanced, rawRowCheck11064]

def rawRow11065 : Integer.Sparse Key := [(key1416, -6), (key1810, -6), (key1614, -6), (key1308, -6), (key1452, 2), (key1416, 2), (key1383, 2), (key1785, 2), (key1565, 2), (key1288, 2), (key1810, 2), (key1769, 2), (key1652, 2), (key1334, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11065 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form10 = rawRow11065 := by decide +kernel

def row11065 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11065 : row11065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11065 := by decide +kernel

theorem rowEval11065 (x : Key → ℝ) : Integer.Sparse.eval row11065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11065, Integer.Sparse.eval_collectBalanced, rawRowCheck11065]

def rawRow11066 : Integer.Sparse Key := [(key1614, -6), (key1308, -6), (key1416, -6), (key1810, -6), (key1538, 2), (key1565, 2), (key1652, 2), (key1308, 2), (key1416, 2), (key1810, 2), (key1288, 2), (key1334, 2), (key1383, 2), (key1769, 2), (key1452, 2), (key1785, 2)]

theorem rawRowCheck11066 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form10 = rawRow11066 := by decide +kernel

def row11066 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11066 : row11066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11066 := by decide +kernel

theorem rowEval11066 (x : Key → ℝ) : Integer.Sparse.eval row11066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11066, Integer.Sparse.eval_collectBalanced, rawRowCheck11066]

def rawRow11067 : Integer.Sparse Key := [(key1614, -6), (key1308, -6), (key1810, -6), (key1416, -6), (key1538, 2), (key1652, 2), (key1565, 2), (key1308, 2), (key1810, 2), (key1416, 2), (key1334, 2), (key1288, 2), (key1769, 2), (key1383, 2), (key1785, 2), (key1452, 2)]

theorem rawRowCheck11067 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form10 = rawRow11067 := by decide +kernel

def row11067 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11067 : row11067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11067 := by decide +kernel

theorem rowEval11067 (x : Key → ℝ) : Integer.Sparse.eval row11067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11067, Integer.Sparse.eval_collectBalanced, rawRowCheck11067]

def rawRow11068 : Integer.Sparse Key := [(key1614, -6), (key1416, -6), (key1308, -6), (key1810, -6), (key1565, 2), (key1538, 2), (key1652, 2), (key1416, 2), (key1308, 2), (key1810, 2), (key1383, 2), (key1452, 2), (key1288, 2), (key1785, 2), (key1334, 2), (key1769, 2)]

theorem rawRowCheck11068 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form10 = rawRow11068 := by decide +kernel

def row11068 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11068 : row11068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11068 := by decide +kernel

theorem rowEval11068 (x : Key → ℝ) : Integer.Sparse.eval row11068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11068, Integer.Sparse.eval_collectBalanced, rawRowCheck11068]

def rawRow11069 : Integer.Sparse Key := [(key1614, -6), (key1416, -6), (key1810, -6), (key1308, -6), (key1565, 2), (key1652, 2), (key1538, 2), (key1416, 2), (key1810, 2), (key1308, 2), (key1452, 2), (key1383, 2), (key1785, 2), (key1288, 2), (key1769, 2), (key1334, 2)]

theorem rawRowCheck11069 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form10 = rawRow11069 := by decide +kernel

def row11069 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11069 : row11069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11069 := by decide +kernel

theorem rowEval11069 (x : Key → ℝ) : Integer.Sparse.eval row11069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11069, Integer.Sparse.eval_collectBalanced, rawRowCheck11069]

def rawRow11070 : Integer.Sparse Key := [(key1614, -6), (key1810, -6), (key1308, -6), (key1416, -6), (key1652, 2), (key1538, 2), (key1565, 2), (key1810, 2), (key1308, 2), (key1416, 2), (key1769, 2), (key1785, 2), (key1334, 2), (key1452, 2), (key1288, 2), (key1383, 2)]

theorem rawRowCheck11070 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form10 = rawRow11070 := by decide +kernel

def row11070 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11070 : row11070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11070 := by decide +kernel

theorem rowEval11070 (x : Key → ℝ) : Integer.Sparse.eval row11070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11070, Integer.Sparse.eval_collectBalanced, rawRowCheck11070]

def rawRow11071 : Integer.Sparse Key := [(key1614, -6), (key1810, -6), (key1416, -6), (key1308, -6), (key1652, 2), (key1565, 2), (key1538, 2), (key1810, 2), (key1416, 2), (key1308, 2), (key1785, 2), (key1769, 2), (key1452, 2), (key1334, 2), (key1383, 2), (key1288, 2)]

theorem rawRowCheck11071 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form10 = rawRow11071 := by decide +kernel

def row11071 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11071 : row11071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11071 := by decide +kernel

theorem rowEval11071 (x : Key → ℝ) : Integer.Sparse.eval row11071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11071, Integer.Sparse.eval_collectBalanced, rawRowCheck11071]

def rawRow11072 : Integer.Sparse Key := [(key1810, -6), (key1308, -6), (key1416, -6), (key1614, -6), (key1769, 2), (key1785, 2), (key1810, 2), (key1334, 2), (key1452, 2), (key1652, 2), (key1288, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1416, 2), (key1565, 2)]

theorem rawRowCheck11072 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form10 = rawRow11072 := by decide +kernel

def row11072 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11072 : row11072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11072 := by decide +kernel

theorem rowEval11072 (x : Key → ℝ) : Integer.Sparse.eval row11072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11072, Integer.Sparse.eval_collectBalanced, rawRowCheck11072]

def rawRow11073 : Integer.Sparse Key := [(key1810, -6), (key1308, -6), (key1614, -6), (key1416, -6), (key1769, 2), (key1810, 2), (key1785, 2), (key1334, 2), (key1652, 2), (key1452, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1383, 2), (key1565, 2), (key1416, 2)]

theorem rawRowCheck11073 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form10 = rawRow11073 := by decide +kernel

def row11073 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11073 : row11073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11073 := by decide +kernel

theorem rowEval11073 (x : Key → ℝ) : Integer.Sparse.eval row11073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11073, Integer.Sparse.eval_collectBalanced, rawRowCheck11073]

def rawRow11074 : Integer.Sparse Key := [(key1810, -6), (key1416, -6), (key1308, -6), (key1614, -6), (key1785, 2), (key1769, 2), (key1810, 2), (key1452, 2), (key1334, 2), (key1652, 2), (key1383, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11074 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form10 = rawRow11074 := by decide +kernel

def row11074 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11074 : row11074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11074 := by decide +kernel

theorem rowEval11074 (x : Key → ℝ) : Integer.Sparse.eval row11074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11074, Integer.Sparse.eval_collectBalanced, rawRowCheck11074]

def rawRow11075 : Integer.Sparse Key := [(key1810, -6), (key1416, -6), (key1614, -6), (key1308, -6), (key1785, 2), (key1810, 2), (key1769, 2), (key1452, 2), (key1652, 2), (key1334, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1288, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11075 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form10 = rawRow11075 := by decide +kernel

def row11075 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11075 : row11075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11075 := by decide +kernel

theorem rowEval11075 (x : Key → ℝ) : Integer.Sparse.eval row11075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11075, Integer.Sparse.eval_collectBalanced, rawRowCheck11075]

def rawRow11076 : Integer.Sparse Key := [(key1810, -6), (key1614, -6), (key1308, -6), (key1416, -6), (key1810, 2), (key1769, 2), (key1785, 2), (key1652, 2), (key1334, 2), (key1452, 2), (key1538, 2), (key1565, 2), (key1308, 2), (key1416, 2), (key1288, 2), (key1383, 2)]

theorem rawRowCheck11076 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form10 = rawRow11076 := by decide +kernel

def row11076 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11076 : row11076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11076 := by decide +kernel

theorem rowEval11076 (x : Key → ℝ) : Integer.Sparse.eval row11076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11076, Integer.Sparse.eval_collectBalanced, rawRowCheck11076]

def rawRow11077 : Integer.Sparse Key := [(key1810, -6), (key1614, -6), (key1416, -6), (key1308, -6), (key1810, 2), (key1785, 2), (key1769, 2), (key1652, 2), (key1452, 2), (key1334, 2), (key1565, 2), (key1538, 2), (key1416, 2), (key1308, 2), (key1383, 2), (key1288, 2)]

theorem rawRowCheck11077 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form10 = rawRow11077 := by decide +kernel

def row11077 : Integer.Sparse Key := [(key1288, 2), (key1308, -4), (key1334, 2), (key1383, 2), (key1416, -4), (key1452, 2), (key1538, 2), (key1565, 2), (key1614, -6), (key1652, 2), (key1769, 2), (key1785, 2), (key1810, -4)]

theorem rowCheck11077 : row11077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11077 := by decide +kernel

theorem rowEval11077 (x : Key → ℝ) : Integer.Sparse.eval row11077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11077, Integer.Sparse.eval_collectBalanced, rawRowCheck11077]

def rawRow11078 : Integer.Sparse Key := [(key1334, -6), (key1452, -6), (key1652, -6), (key1652, -6), (key1288, 2), (key1308, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1538, 2), (key1416, 2), (key1416, 2), (key1565, 2), (key1565, 2), (key1614, 2), (key1614, 2)]

theorem rawRowCheck11078 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form10 = rawRow11078 := by decide +kernel

def row11078 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11078 : row11078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11078 := by decide +kernel

theorem rowEval11078 (x : Key → ℝ) : Integer.Sparse.eval row11078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11078, Integer.Sparse.eval_collectBalanced, rawRowCheck11078]

def rawRow11079 : Integer.Sparse Key := [(key1334, -6), (key1652, -6), (key1452, -6), (key1652, -6), (key1308, 2), (key1288, 2), (key1308, 2), (key1538, 2), (key1383, 2), (key1538, 2), (key1565, 2), (key1614, 2), (key1416, 2), (key1614, 2), (key1416, 2), (key1565, 2)]

theorem rawRowCheck11079 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form10 = rawRow11079 := by decide +kernel

def row11079 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11079 : row11079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11079 := by decide +kernel

theorem rowEval11079 (x : Key → ℝ) : Integer.Sparse.eval row11079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11079, Integer.Sparse.eval_collectBalanced, rawRowCheck11079]

def rawRow11080 : Integer.Sparse Key := [(key1334, -6), (key1652, -6), (key1652, -6), (key1452, -6), (key1308, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1538, 2), (key1383, 2), (key1614, 2), (key1565, 2), (key1614, 2), (key1416, 2), (key1565, 2), (key1416, 2)]

theorem rawRowCheck11080 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form10 = rawRow11080 := by decide +kernel

def row11080 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11080 : row11080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11080 := by decide +kernel

theorem rowEval11080 (x : Key → ℝ) : Integer.Sparse.eval row11080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11080, Integer.Sparse.eval_collectBalanced, rawRowCheck11080]

def rawRow11081 : Integer.Sparse Key := [(key1452, -6), (key1334, -6), (key1652, -6), (key1652, -6), (key1383, 2), (key1416, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1565, 2), (key1308, 2), (key1308, 2), (key1538, 2), (key1538, 2), (key1614, 2), (key1614, 2)]

theorem rawRowCheck11081 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form10 = rawRow11081 := by decide +kernel

def row11081 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11081 : row11081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11081 := by decide +kernel

theorem rowEval11081 (x : Key → ℝ) : Integer.Sparse.eval row11081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11081, Integer.Sparse.eval_collectBalanced, rawRowCheck11081]

def rawRow11082 : Integer.Sparse Key := [(key1452, -6), (key1652, -6), (key1334, -6), (key1652, -6), (key1416, 2), (key1383, 2), (key1416, 2), (key1565, 2), (key1288, 2), (key1565, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1614, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11082 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form10 = rawRow11082 := by decide +kernel

def row11082 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11082 : row11082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11082 := by decide +kernel

theorem rowEval11082 (x : Key → ℝ) : Integer.Sparse.eval row11082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11082, Integer.Sparse.eval_collectBalanced, rawRowCheck11082]

def rawRow11083 : Integer.Sparse Key := [(key1452, -6), (key1652, -6), (key1652, -6), (key1334, -6), (key1416, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1565, 2), (key1288, 2), (key1614, 2), (key1538, 2), (key1614, 2), (key1308, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11083 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form10 = rawRow11083 := by decide +kernel

def row11083 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11083 : row11083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11083 := by decide +kernel

theorem rowEval11083 (x : Key → ℝ) : Integer.Sparse.eval row11083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11083, Integer.Sparse.eval_collectBalanced, rawRowCheck11083]

def rawRow11084 : Integer.Sparse Key := [(key1652, -6), (key1334, -6), (key1452, -6), (key1652, -6), (key1538, 2), (key1565, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1614, 2), (key1288, 2), (key1308, 2), (key1383, 2), (key1538, 2), (key1416, 2), (key1565, 2)]

theorem rawRowCheck11084 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form10 = rawRow11084 := by decide +kernel

def row11084 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11084 : row11084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11084 := by decide +kernel

theorem rowEval11084 (x : Key → ℝ) : Integer.Sparse.eval row11084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11084, Integer.Sparse.eval_collectBalanced, rawRowCheck11084]

def rawRow11085 : Integer.Sparse Key := [(key1652, -6), (key1334, -6), (key1652, -6), (key1452, -6), (key1538, 2), (key1614, 2), (key1565, 2), (key1308, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1288, 2), (key1538, 2), (key1383, 2), (key1565, 2), (key1416, 2)]

theorem rawRowCheck11085 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form10 = rawRow11085 := by decide +kernel

def row11085 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11085 : row11085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11085 := by decide +kernel

theorem rowEval11085 (x : Key → ℝ) : Integer.Sparse.eval row11085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11085, Integer.Sparse.eval_collectBalanced, rawRowCheck11085]

def rawRow11086 : Integer.Sparse Key := [(key1652, -6), (key1452, -6), (key1334, -6), (key1652, -6), (key1565, 2), (key1538, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1614, 2), (key1383, 2), (key1416, 2), (key1288, 2), (key1565, 2), (key1308, 2), (key1538, 2)]

theorem rawRowCheck11086 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form10 = rawRow11086 := by decide +kernel

def row11086 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11086 : row11086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11086 := by decide +kernel

theorem rowEval11086 (x : Key → ℝ) : Integer.Sparse.eval row11086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form10) x := by
  rw [rowCheck11086, Integer.Sparse.eval_collectBalanced, rawRowCheck11086]

def rawRow11087 : Integer.Sparse Key := [(key1652, -6), (key1452, -6), (key1652, -6), (key1334, -6), (key1565, 2), (key1614, 2), (key1538, 2), (key1416, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1383, 2), (key1565, 2), (key1288, 2), (key1538, 2), (key1308, 2)]

theorem rawRowCheck11087 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form10 = rawRow11087 := by decide +kernel

def row11087 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11087 : row11087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11087 := by decide +kernel

theorem rowEval11087 (x : Key → ℝ) : Integer.Sparse.eval row11087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11087, Integer.Sparse.eval_collectBalanced, rawRowCheck11087]

def rawRow11088 : Integer.Sparse Key := [(key1652, -6), (key1652, -6), (key1334, -6), (key1452, -6), (key1614, 2), (key1538, 2), (key1565, 2), (key1614, 2), (key1308, 2), (key1416, 2), (key1538, 2), (key1565, 2), (key1308, 2), (key1416, 2), (key1288, 2), (key1383, 2)]

theorem rawRowCheck11088 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form10 = rawRow11088 := by decide +kernel

def row11088 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11088 : row11088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11088 := by decide +kernel

theorem rowEval11088 (x : Key → ℝ) : Integer.Sparse.eval row11088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form10) x := by
  rw [rowCheck11088, Integer.Sparse.eval_collectBalanced, rawRowCheck11088]

def rawRow11089 : Integer.Sparse Key := [(key1652, -6), (key1652, -6), (key1452, -6), (key1334, -6), (key1614, 2), (key1565, 2), (key1538, 2), (key1614, 2), (key1416, 2), (key1308, 2), (key1565, 2), (key1538, 2), (key1416, 2), (key1308, 2), (key1383, 2), (key1288, 2)]

theorem rawRowCheck11089 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form10 = rawRow11089 := by decide +kernel

def row11089 : Integer.Sparse Key := [(key1288, 2), (key1308, 4), (key1334, -6), (key1383, 2), (key1416, 4), (key1452, -6), (key1538, 4), (key1565, 4), (key1614, 4), (key1652, -12)]

theorem rowCheck11089 : row11089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11089 := by decide +kernel

theorem rowEval11089 (x : Key → ℝ) : Integer.Sparse.eval row11089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form10) x := by
  rw [rowCheck11089, Integer.Sparse.eval_collectBalanced, rawRowCheck11089]

def rawRow11090 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rawRowCheck11090 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form11 = rawRow11090 := by decide +kernel

def row11090 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11090 : row11090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11090 := by decide +kernel

theorem rowEval11090 (x : Key → ℝ) : Integer.Sparse.eval row11090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11090, Integer.Sparse.eval_collectBalanced, rawRowCheck11090]

def rawRow11091 : Integer.Sparse Key := [(key2467, 6), (key2464, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2874, -6), (key2842, -6)]

theorem rawRowCheck11091 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form11 = rawRow11091 := by decide +kernel

def row11091 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11091 : row11091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11091 := by decide +kernel

theorem rowEval11091 (x : Key → ℝ) : Integer.Sparse.eval row11091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11091, Integer.Sparse.eval_collectBalanced, rawRowCheck11091]

def rawRow11092 : Integer.Sparse Key := [(key2464, 6), (key2476, 6), (key2467, 6), (key2499, 6), (key2586, -6), (key2842, -6), (key2765, -6), (key2874, -6)]

theorem rawRowCheck11092 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form11 = rawRow11092 := by decide +kernel

def row11092 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11092 : row11092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11092 := by decide +kernel

theorem rowEval11092 (x : Key → ℝ) : Integer.Sparse.eval row11092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11092, Integer.Sparse.eval_collectBalanced, rawRowCheck11092]

def rawRow11093 : Integer.Sparse Key := [(key2476, 6), (key2464, 6), (key2467, 6), (key2499, 6), (key2586, -6), (key2842, -6), (key2874, -6), (key2765, -6)]

theorem rawRowCheck11093 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form11 = rawRow11093 := by decide +kernel

def row11093 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11093 : row11093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11093 := by decide +kernel

theorem rowEval11093 (x : Key → ℝ) : Integer.Sparse.eval row11093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11093, Integer.Sparse.eval_collectBalanced, rawRowCheck11093]

def rawRow11094 : Integer.Sparse Key := [(key2467, 6), (key2476, 6), (key2464, 6), (key2499, 6), (key2586, -6), (key2874, -6), (key2765, -6), (key2842, -6)]

theorem rawRowCheck11094 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form11 = rawRow11094 := by decide +kernel

def row11094 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11094 : row11094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11094 := by decide +kernel

theorem rowEval11094 (x : Key → ℝ) : Integer.Sparse.eval row11094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11094, Integer.Sparse.eval_collectBalanced, rawRowCheck11094]

def rawRow11095 : Integer.Sparse Key := [(key2476, 6), (key2467, 6), (key2464, 6), (key2499, 6), (key2586, -6), (key2874, -6), (key2842, -6), (key2765, -6)]

theorem rawRowCheck11095 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form11 = rawRow11095 := by decide +kernel

def row11095 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11095 : row11095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11095 := by decide +kernel

theorem rowEval11095 (x : Key → ℝ) : Integer.Sparse.eval row11095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11095, Integer.Sparse.eval_collectBalanced, rawRowCheck11095]

def rawRow11096 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2499, 6), (key2476, 6), (key2765, -6), (key2586, -6), (key2842, -6), (key2874, -6)]

theorem rawRowCheck11096 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form11 = rawRow11096 := by decide +kernel

def row11096 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11096 : row11096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11096 := by decide +kernel

theorem rowEval11096 (x : Key → ℝ) : Integer.Sparse.eval row11096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11096, Integer.Sparse.eval_collectBalanced, rawRowCheck11096]

def rawRow11097 : Integer.Sparse Key := [(key2467, 6), (key2464, 6), (key2499, 6), (key2476, 6), (key2765, -6), (key2586, -6), (key2874, -6), (key2842, -6)]

theorem rawRowCheck11097 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form11 = rawRow11097 := by decide +kernel

def row11097 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11097 : row11097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11097 := by decide +kernel

theorem rowEval11097 (x : Key → ℝ) : Integer.Sparse.eval row11097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11097, Integer.Sparse.eval_collectBalanced, rawRowCheck11097]

def rawRow11098 : Integer.Sparse Key := [(key2464, 6), (key2499, 6), (key2467, 6), (key2476, 6), (key2765, -6), (key2842, -6), (key2586, -6), (key2874, -6)]

theorem rawRowCheck11098 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form11 = rawRow11098 := by decide +kernel

def row11098 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11098 : row11098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11098 := by decide +kernel

theorem rowEval11098 (x : Key → ℝ) : Integer.Sparse.eval row11098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11098, Integer.Sparse.eval_collectBalanced, rawRowCheck11098]

def rawRow11099 : Integer.Sparse Key := [(key2499, 6), (key2464, 6), (key2467, 6), (key2476, 6), (key2765, -6), (key2842, -6), (key2874, -6), (key2586, -6)]

theorem rawRowCheck11099 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form11 = rawRow11099 := by decide +kernel

def row11099 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11099 : row11099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11099 := by decide +kernel

theorem rowEval11099 (x : Key → ℝ) : Integer.Sparse.eval row11099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11099, Integer.Sparse.eval_collectBalanced, rawRowCheck11099]

def rawRow11100 : Integer.Sparse Key := [(key2467, 6), (key2499, 6), (key2464, 6), (key2476, 6), (key2765, -6), (key2874, -6), (key2586, -6), (key2842, -6)]

theorem rawRowCheck11100 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form11 = rawRow11100 := by decide +kernel

def row11100 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11100 : row11100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11100 := by decide +kernel

theorem rowEval11100 (x : Key → ℝ) : Integer.Sparse.eval row11100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11100, Integer.Sparse.eval_collectBalanced, rawRowCheck11100]

def rawRow11101 : Integer.Sparse Key := [(key2499, 6), (key2467, 6), (key2464, 6), (key2476, 6), (key2765, -6), (key2874, -6), (key2842, -6), (key2586, -6)]

theorem rawRowCheck11101 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form11 = rawRow11101 := by decide +kernel

def row11101 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11101 : row11101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11101 := by decide +kernel

theorem rowEval11101 (x : Key → ℝ) : Integer.Sparse.eval row11101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11101, Integer.Sparse.eval_collectBalanced, rawRowCheck11101]

def rawRow11102 : Integer.Sparse Key := [(key2464, 6), (key2476, 6), (key2499, 6), (key2467, 6), (key2842, -6), (key2586, -6), (key2765, -6), (key2874, -6)]

theorem rawRowCheck11102 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form11 = rawRow11102 := by decide +kernel

def row11102 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11102 : row11102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11102 := by decide +kernel

theorem rowEval11102 (x : Key → ℝ) : Integer.Sparse.eval row11102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, -1, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11102, Integer.Sparse.eval_collectBalanced, rawRowCheck11102]

def rawRow11103 : Integer.Sparse Key := [(key2476, 6), (key2464, 6), (key2499, 6), (key2467, 6), (key2842, -6), (key2586, -6), (key2874, -6), (key2765, -6)]

theorem rawRowCheck11103 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form11 = rawRow11103 := by decide +kernel

def row11103 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11103 : row11103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11103 := by decide +kernel

theorem rowEval11103 (x : Key → ℝ) : Integer.Sparse.eval row11103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -2, 1, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11103, Integer.Sparse.eval_collectBalanced, rawRowCheck11103]

def rawRow11104 : Integer.Sparse Key := [(key2464, 6), (key2499, 6), (key2476, 6), (key2467, 6), (key2842, -6), (key2765, -6), (key2586, -6), (key2874, -6)]

theorem rawRowCheck11104 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form11 = rawRow11104 := by decide +kernel

def row11104 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11104 : row11104 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11104 := by decide +kernel

theorem rowEval11104 (x : Key → ℝ) : Integer.Sparse.eval row11104 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, -2, 1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11104, Integer.Sparse.eval_collectBalanced, rawRowCheck11104]

def rawRow11105 : Integer.Sparse Key := [(key2499, 6), (key2464, 6), (key2476, 6), (key2467, 6), (key2842, -6), (key2765, -6), (key2874, -6), (key2586, -6)]

theorem rawRowCheck11105 : GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form11 = rawRow11105 := by decide +kernel

def row11105 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11105 : row11105 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11105 := by decide +kernel

theorem rowEval11105 (x : Key → ℝ) : Integer.Sparse.eval row11105 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, -1, 1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11105, Integer.Sparse.eval_collectBalanced, rawRowCheck11105]

def rawRow11106 : Integer.Sparse Key := [(key2476, 6), (key2499, 6), (key2464, 6), (key2467, 6), (key2842, -6), (key2874, -6), (key2586, -6), (key2765, -6)]

theorem rawRowCheck11106 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form11 = rawRow11106 := by decide +kernel

def row11106 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11106 : row11106 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11106 := by decide +kernel

theorem rowEval11106 (x : Key → ℝ) : Integer.Sparse.eval row11106 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11106, Integer.Sparse.eval_collectBalanced, rawRowCheck11106]

def rawRow11107 : Integer.Sparse Key := [(key2499, 6), (key2476, 6), (key2464, 6), (key2467, 6), (key2842, -6), (key2874, -6), (key2765, -6), (key2586, -6)]

theorem rawRowCheck11107 : GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form11 = rawRow11107 := by decide +kernel

def row11107 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11107 : row11107 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11107 := by decide +kernel

theorem rowEval11107 (x : Key → ℝ) : Integer.Sparse.eval row11107 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 0, 1, -1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11107, Integer.Sparse.eval_collectBalanced, rawRowCheck11107]

def rawRow11108 : Integer.Sparse Key := [(key2467, 6), (key2476, 6), (key2499, 6), (key2464, 6), (key2874, -6), (key2586, -6), (key2765, -6), (key2842, -6)]

theorem rawRowCheck11108 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form11 = rawRow11108 := by decide +kernel

def row11108 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11108 : row11108 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11108 := by decide +kernel

theorem rowEval11108 (x : Key → ℝ) : Integer.Sparse.eval row11108 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11108, Integer.Sparse.eval_collectBalanced, rawRowCheck11108]

def rawRow11109 : Integer.Sparse Key := [(key2476, 6), (key2467, 6), (key2499, 6), (key2464, 6), (key2874, -6), (key2586, -6), (key2842, -6), (key2765, -6)]

theorem rawRowCheck11109 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form11 = rawRow11109 := by decide +kernel

def row11109 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11109 : row11109 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11109 := by decide +kernel

theorem rowEval11109 (x : Key → ℝ) : Integer.Sparse.eval row11109 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -2, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11109, Integer.Sparse.eval_collectBalanced, rawRowCheck11109]

def rawRow11110 : Integer.Sparse Key := [(key2467, 6), (key2499, 6), (key2476, 6), (key2464, 6), (key2874, -6), (key2765, -6), (key2586, -6), (key2842, -6)]

theorem rawRowCheck11110 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form11 = rawRow11110 := by decide +kernel

def row11110 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11110 : row11110 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11110 := by decide +kernel

theorem rowEval11110 (x : Key → ℝ) : Integer.Sparse.eval row11110 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11110, Integer.Sparse.eval_collectBalanced, rawRowCheck11110]

def rawRow11111 : Integer.Sparse Key := [(key2499, 6), (key2467, 6), (key2476, 6), (key2464, 6), (key2874, -6), (key2765, -6), (key2842, -6), (key2586, -6)]

theorem rawRowCheck11111 : GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form11 = rawRow11111 := by decide +kernel

def row11111 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11111 : row11111 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11111 := by decide +kernel

theorem rowEval11111 (x : Key → ℝ) : Integer.Sparse.eval row11111 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, -1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11111, Integer.Sparse.eval_collectBalanced, rawRowCheck11111]

def rawRow11112 : Integer.Sparse Key := [(key2476, 6), (key2499, 6), (key2467, 6), (key2464, 6), (key2874, -6), (key2842, -6), (key2586, -6), (key2765, -6)]

theorem rawRowCheck11112 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form11 = rawRow11112 := by decide +kernel

def row11112 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11112 : row11112 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11112 := by decide +kernel

theorem rowEval11112 (x : Key → ℝ) : Integer.Sparse.eval row11112 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11112, Integer.Sparse.eval_collectBalanced, rawRowCheck11112]

def rawRow11113 : Integer.Sparse Key := [(key2499, 6), (key2476, 6), (key2467, 6), (key2464, 6), (key2874, -6), (key2842, -6), (key2765, -6), (key2586, -6)]

theorem rawRowCheck11113 : GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form11 = rawRow11113 := by decide +kernel

def row11113 : Integer.Sparse Key := [(key2464, 6), (key2467, 6), (key2476, 6), (key2499, 6), (key2586, -6), (key2765, -6), (key2842, -6), (key2874, -6)]

theorem rowCheck11113 : row11113 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11113 := by decide +kernel

theorem rowEval11113 (x : Key → ℝ) : Integer.Sparse.eval row11113 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, 1, 0, -1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11113, Integer.Sparse.eval_collectBalanced, rawRowCheck11113]

def rawRow11114 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2540, 6), (key2551, 6), (key2370, -6), (key2762, -6), (key2839, -6), (key2839, -6)]

theorem rawRowCheck11114 : GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form11 = rawRow11114 := by decide +kernel

def row11114 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

theorem rowCheck11114 : row11114 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11114 := by decide +kernel

theorem rowEval11114 (x : Key → ℝ) : Integer.Sparse.eval row11114 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, -1, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11114, Integer.Sparse.eval_collectBalanced, rawRowCheck11114]

def rawRow11115 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2762, -6), (key2839, -6)]

theorem rawRowCheck11115 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form11 = rawRow11115 := by decide +kernel

def row11115 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

theorem rowCheck11115 : row11115 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11115 := by decide +kernel

theorem rowEval11115 (x : Key → ℝ) : Integer.Sparse.eval row11115 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11115, Integer.Sparse.eval_collectBalanced, rawRowCheck11115]

def rawRow11116 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2534, 6), (key2551, 6), (key2370, -6), (key2839, -6), (key2839, -6), (key2762, -6)]

theorem rawRowCheck11116 : GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form11 = rawRow11116 := by decide +kernel

def row11116 : Integer.Sparse Key := [(key2370, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -12)]

theorem rowCheck11116 : row11116 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11116 := by decide +kernel

theorem rowEval11116 (x : Key → ℝ) : Integer.Sparse.eval row11116 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -2, 0, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11116, Integer.Sparse.eval_collectBalanced, rawRowCheck11116]

def rawRow11117 : Integer.Sparse Key := [(key2534, 6), (key2534, 6), (key2551, 6), (key2540, 6), (key2398, -6), (key2583, -6), (key2839, -6), (key2839, -6)]

theorem rawRowCheck11117 : GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form11 = rawRow11117 := by decide +kernel

def row11117 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

theorem rowCheck11117 : row11117 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11117 := by decide +kernel

theorem rowEval11117 (x : Key → ℝ) : Integer.Sparse.eval row11117 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, -2, 0, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11117, Integer.Sparse.eval_collectBalanced, rawRowCheck11117]

def rawRow11118 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2583, -6), (key2839, -6)]

theorem rawRowCheck11118 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form11 = rawRow11118 := by decide +kernel

def row11118 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

theorem rowCheck11118 : row11118 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11118 := by decide +kernel

theorem rowEval11118 (x : Key → ℝ) : Integer.Sparse.eval row11118 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11118, Integer.Sparse.eval_collectBalanced, rawRowCheck11118]

def rawRow11119 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2534, 6), (key2540, 6), (key2398, -6), (key2839, -6), (key2839, -6), (key2583, -6)]

theorem rawRowCheck11119 : GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form11 = rawRow11119 := by decide +kernel

def row11119 : Integer.Sparse Key := [(key2398, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -12)]

theorem rowCheck11119 : row11119 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11119 := by decide +kernel

theorem rowEval11119 (x : Key → ℝ) : Integer.Sparse.eval row11119 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, -1, 0, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11119, Integer.Sparse.eval_collectBalanced, rawRowCheck11119]

def rawRow11120 : Integer.Sparse Key := [(key2534, 6), (key2540, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2762, -6), (key2839, -6)]

theorem rawRowCheck11120 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form11 = rawRow11120 := by decide +kernel

def row11120 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

theorem rowCheck11120 : row11120 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11120 := by decide +kernel

theorem rowEval11120 (x : Key → ℝ) : Integer.Sparse.eval row11120 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, -1, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11120, Integer.Sparse.eval_collectBalanced, rawRowCheck11120]

def rawRow11121 : Integer.Sparse Key := [(key2540, 6), (key2534, 6), (key2551, 6), (key2534, 6), (key2464, -6), (key2370, -6), (key2839, -6), (key2762, -6)]

theorem rawRowCheck11121 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form11 = rawRow11121 := by decide +kernel

def row11121 : Integer.Sparse Key := [(key2370, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6), (key2839, -6)]

theorem rowCheck11121 : row11121 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11121 := by decide +kernel

theorem rowEval11121 (x : Key → ℝ) : Integer.Sparse.eval row11121 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -2, 0, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11121, Integer.Sparse.eval_collectBalanced, rawRowCheck11121]

def rawRow11122 : Integer.Sparse Key := [(key2534, 6), (key2551, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2583, -6), (key2839, -6)]

theorem rawRowCheck11122 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form11 = rawRow11122 := by decide +kernel

def row11122 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

theorem rowCheck11122 : row11122 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11122 := by decide +kernel

theorem rowEval11122 (x : Key → ℝ) : Integer.Sparse.eval row11122 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, -2, 0] GramFunctions.Block3.form11) x := by
  rw [rowCheck11122, Integer.Sparse.eval_collectBalanced, rawRowCheck11122]

def rawRow11123 : Integer.Sparse Key := [(key2551, 6), (key2534, 6), (key2540, 6), (key2534, 6), (key2464, -6), (key2398, -6), (key2839, -6), (key2583, -6)]

theorem rawRowCheck11123 : GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form11 = rawRow11123 := by decide +kernel

def row11123 : Integer.Sparse Key := [(key2398, -6), (key2464, -6), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6), (key2839, -6)]

theorem rowCheck11123 : row11123 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11123 := by decide +kernel

theorem rowEval11123 (x : Key → ℝ) : Integer.Sparse.eval row11123 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, -1, 0, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11123, Integer.Sparse.eval_collectBalanced, rawRowCheck11123]

def rawRow11124 : Integer.Sparse Key := [(key2540, 6), (key2551, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2370, -6), (key2762, -6)]

theorem rawRowCheck11124 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form11 = rawRow11124 := by decide +kernel

def row11124 : Integer.Sparse Key := [(key2370, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2762, -6)]

theorem rowCheck11124 : row11124 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11124 := by decide +kernel

theorem rowEval11124 (x : Key → ℝ) : Integer.Sparse.eval row11124 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -2, -1] GramFunctions.Block3.form11) x := by
  rw [rowCheck11124, Integer.Sparse.eval_collectBalanced, rawRowCheck11124]

def rawRow11125 : Integer.Sparse Key := [(key2551, 6), (key2540, 6), (key2534, 6), (key2534, 6), (key2464, -6), (key2464, -6), (key2398, -6), (key2583, -6)]

theorem rawRowCheck11125 : GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form11 = rawRow11125 := by decide +kernel

def row11125 : Integer.Sparse Key := [(key2398, -6), (key2464, -12), (key2534, 12), (key2540, 6), (key2551, 6), (key2583, -6)]

theorem rowCheck11125 : row11125 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11125 := by decide +kernel

theorem rowEval11125 (x : Key → ℝ) : Integer.Sparse.eval row11125 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 1, 0, 0, -1, -2] GramFunctions.Block3.form11) x := by
  rw [rowCheck11125, Integer.Sparse.eval_collectBalanced, rawRowCheck11125]

def rawRow11126 : Integer.Sparse Key := [(key2465, 6), (key2469, 6), (key2477, 6), (key2500, 6), (key2375, -6), (key2403, -6), (key2469, -6), (key2536, -6)]

theorem rawRowCheck11126 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12 = rawRow11126 := by decide +kernel

def row11126 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11126 : row11126 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11126 := by decide +kernel

theorem rowEval11126 (x : Key → ℝ) : Integer.Sparse.eval row11126 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11126, Integer.Sparse.eval_collectBalanced, rawRowCheck11126]

def rawRow11127 : Integer.Sparse Key := [(key2469, 6), (key2465, 6), (key2477, 6), (key2500, 6), (key2375, -6), (key2403, -6), (key2536, -6), (key2469, -6)]

theorem rawRowCheck11127 : GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12 = rawRow11127 := by decide +kernel

def row11127 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11127 : row11127 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11127 := by decide +kernel

theorem rowEval11127 (x : Key → ℝ) : Integer.Sparse.eval row11127 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, -1, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11127, Integer.Sparse.eval_collectBalanced, rawRowCheck11127]

def rawRow11128 : Integer.Sparse Key := [(key2465, 6), (key2477, 6), (key2469, 6), (key2500, 6), (key2375, -6), (key2469, -6), (key2403, -6), (key2536, -6)]

theorem rawRowCheck11128 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12 = rawRow11128 := by decide +kernel

def row11128 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11128 : row11128 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11128 := by decide +kernel

theorem rowEval11128 (x : Key → ℝ) : Integer.Sparse.eval row11128 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, -1, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11128, Integer.Sparse.eval_collectBalanced, rawRowCheck11128]

def rawRow11129 : Integer.Sparse Key := [(key2477, 6), (key2465, 6), (key2469, 6), (key2500, 6), (key2375, -6), (key2469, -6), (key2536, -6), (key2403, -6)]

theorem rawRowCheck11129 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12 = rawRow11129 := by decide +kernel

def row11129 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11129 : row11129 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11129 := by decide +kernel

theorem rowEval11129 (x : Key → ℝ) : Integer.Sparse.eval row11129 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 0, 1, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11129, Integer.Sparse.eval_collectBalanced, rawRowCheck11129]

def rawRow11130 : Integer.Sparse Key := [(key2469, 6), (key2477, 6), (key2465, 6), (key2500, 6), (key2375, -6), (key2536, -6), (key2403, -6), (key2469, -6)]

theorem rawRowCheck11130 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12 = rawRow11130 := by decide +kernel

def row11130 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11130 : row11130 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11130 := by decide +kernel

theorem rowEval11130 (x : Key → ℝ) : Integer.Sparse.eval row11130 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, -1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11130, Integer.Sparse.eval_collectBalanced, rawRowCheck11130]

def rawRow11131 : Integer.Sparse Key := [(key2477, 6), (key2469, 6), (key2465, 6), (key2500, 6), (key2375, -6), (key2536, -6), (key2469, -6), (key2403, -6)]

theorem rawRowCheck11131 : GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12 = rawRow11131 := by decide +kernel

def row11131 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11131 : row11131 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11131 := by decide +kernel

theorem rowEval11131 (x : Key → ℝ) : Integer.Sparse.eval row11131 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -2, 1, 0, -1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11131, Integer.Sparse.eval_collectBalanced, rawRowCheck11131]

def rawRow11132 : Integer.Sparse Key := [(key2465, 6), (key2469, 6), (key2500, 6), (key2477, 6), (key2403, -6), (key2375, -6), (key2469, -6), (key2536, -6)]

theorem rawRowCheck11132 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12 = rawRow11132 := by decide +kernel

def row11132 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11132 : row11132 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11132 := by decide +kernel

theorem rowEval11132 (x : Key → ℝ) : Integer.Sparse.eval row11132 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 0, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11132, Integer.Sparse.eval_collectBalanced, rawRowCheck11132]

def rawRow11133 : Integer.Sparse Key := [(key2469, 6), (key2465, 6), (key2500, 6), (key2477, 6), (key2403, -6), (key2375, -6), (key2536, -6), (key2469, -6)]

theorem rawRowCheck11133 : GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12 = rawRow11133 := by decide +kernel

def row11133 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11133 : row11133 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11133 := by decide +kernel

theorem rowEval11133 (x : Key → ℝ) : Integer.Sparse.eval row11133 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, -2, 1, 0] GramFunctions.Block3.form12) x := by
  rw [rowCheck11133, Integer.Sparse.eval_collectBalanced, rawRowCheck11133]

def rawRow11134 : Integer.Sparse Key := [(key2465, 6), (key2500, 6), (key2469, 6), (key2477, 6), (key2403, -6), (key2469, -6), (key2375, -6), (key2536, -6)]

theorem rawRowCheck11134 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12 = rawRow11134 := by decide +kernel

def row11134 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11134 : row11134 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11134 := by decide +kernel

theorem rowEval11134 (x : Key → ℝ) : Integer.Sparse.eval row11134 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, -2, 1] GramFunctions.Block3.form12) x := by
  rw [rowCheck11134, Integer.Sparse.eval_collectBalanced, rawRowCheck11134]

def rawRow11135 : Integer.Sparse Key := [(key2500, 6), (key2465, 6), (key2469, 6), (key2477, 6), (key2403, -6), (key2469, -6), (key2536, -6), (key2375, -6)]

theorem rawRowCheck11135 : GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12 = rawRow11135 := by decide +kernel

def row11135 : Integer.Sparse Key := [(key2375, -6), (key2403, -6), (key2465, 6), (key2477, 6), (key2500, 6), (key2536, -6)]

theorem rowCheck11135 : row11135 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow11135 := by decide +kernel

theorem rowEval11135 (x : Key → ℝ) : Integer.Sparse.eval row11135 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![2, 0, -1, 0, 1, -2] GramFunctions.Block3.form12) x := by
  rw [rowCheck11135, Integer.Sparse.eval_collectBalanced, rawRowCheck11135]

end MUB6.Certificate.GramRows

end OAI
