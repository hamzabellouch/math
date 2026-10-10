import OAI.Analysis.MutuallyUnbiased.Certificate.GramPolynomial
import OAI.Analysis.MutuallyUnbiased.GramFunctions.Block4
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block7
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block8
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block9
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block15
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block17
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block18
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block19
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block20
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block21
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block22
import OAI.Analysis.MutuallyUnbiased.GramKeys.Block23

namespace OAI

namespace MUB6.Certificate.GramRows

open GramNormalization

def rawRow14976 : Integer.Sparse Key := [(key1100, 4), (key1100, 4), (key1186, 4), (key1171, -2), (key1175, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1224, -2), (key1096, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1185, -2), (key1171, 4), (key1171, 4), (key1222, 4)]

theorem rawRowCheck14976 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5 = rawRow14976 := by decide +kernel

def row14976 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14976 : row14976 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14976 := by decide +kernel

theorem rowEval14976 (x : Key → ℝ) : Integer.Sparse.eval row14976 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14976, Integer.Sparse.eval_collectBalanced, rawRowCheck14976]

def rawRow14977 : Integer.Sparse Key := [(key1100, 4), (key1186, 4), (key1100, 4), (key1175, -2), (key1171, -2), (key1224, -2), (key1171, -2), (key1224, -2), (key1175, -2), (key1100, -2), (key1096, -2), (key1185, -2), (key1096, -2), (key1185, -2), (key1100, -2), (key1171, 4), (key1222, 4), (key1171, 4)]

theorem rawRowCheck14977 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5 = rawRow14977 := by decide +kernel

def row14977 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14977 : row14977 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14977 := by decide +kernel

theorem rowEval14977 (x : Key → ℝ) : Integer.Sparse.eval row14977 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14977, Integer.Sparse.eval_collectBalanced, rawRowCheck14977]

def rawRow14978 : Integer.Sparse Key := [(key1186, 4), (key1100, 4), (key1100, 4), (key1224, -2), (key1224, -2), (key1175, -2), (key1175, -2), (key1171, -2), (key1171, -2), (key1185, -2), (key1185, -2), (key1100, -2), (key1100, -2), (key1096, -2), (key1096, -2), (key1222, 4), (key1171, 4), (key1171, 4)]

theorem rawRowCheck14978 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5 = rawRow14978 := by decide +kernel

def row14978 : Integer.Sparse Key := [(key1096, -4), (key1100, 4), (key1171, 4), (key1175, -4), (key1185, -4), (key1186, 4), (key1222, 4), (key1224, -4)]

theorem rowCheck14978 : row14978 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14978 := by decide +kernel

theorem rowEval14978 (x : Key → ℝ) : Integer.Sparse.eval row14978 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14978, Integer.Sparse.eval_collectBalanced, rawRowCheck14978]

def rawRow14979 : Integer.Sparse Key := [(key986, 4), (key1171, 4), (key1224, 4), (key986, -2), (key988, -2), (key1100, -2), (key1186, -2), (key1175, -2), (key1224, -2), (key982, -2), (key986, -2), (key1096, -2), (key1185, -2), (key1171, -2), (key1222, -2), (key986, 4), (key1100, 4), (key1185, 4)]

theorem rawRowCheck14979 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5 = rawRow14979 := by decide +kernel

def row14979 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14979 : row14979 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14979 := by decide +kernel

theorem rowEval14979 (x : Key → ℝ) : Integer.Sparse.eval row14979 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14979, Integer.Sparse.eval_collectBalanced, rawRowCheck14979]

def rawRow14980 : Integer.Sparse Key := [(key986, 4), (key1224, 4), (key1171, 4), (key988, -2), (key986, -2), (key1186, -2), (key1100, -2), (key1224, -2), (key1175, -2), (key986, -2), (key982, -2), (key1185, -2), (key1096, -2), (key1222, -2), (key1171, -2), (key986, 4), (key1185, 4), (key1100, 4)]

theorem rawRowCheck14980 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5 = rawRow14980 := by decide +kernel

def row14980 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14980 : row14980 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14980 := by decide +kernel

theorem rowEval14980 (x : Key → ℝ) : Integer.Sparse.eval row14980 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14980, Integer.Sparse.eval_collectBalanced, rawRowCheck14980]

def rawRow14981 : Integer.Sparse Key := [(key1171, 4), (key986, 4), (key1224, 4), (key1100, -2), (key1175, -2), (key986, -2), (key1224, -2), (key988, -2), (key1186, -2), (key1096, -2), (key1171, -2), (key982, -2), (key1222, -2), (key986, -2), (key1185, -2), (key1100, 4), (key986, 4), (key1185, 4)]

theorem rawRowCheck14981 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5 = rawRow14981 := by decide +kernel

def row14981 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14981 : row14981 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14981 := by decide +kernel

theorem rowEval14981 (x : Key → ℝ) : Integer.Sparse.eval row14981 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form5) x := by
  rw [rowCheck14981, Integer.Sparse.eval_collectBalanced, rawRowCheck14981]

def rawRow14982 : Integer.Sparse Key := [(key1171, 4), (key1224, 4), (key986, 4), (key1175, -2), (key1100, -2), (key1224, -2), (key986, -2), (key1186, -2), (key988, -2), (key1171, -2), (key1096, -2), (key1222, -2), (key982, -2), (key1185, -2), (key986, -2), (key1100, 4), (key1185, 4), (key986, 4)]

theorem rawRowCheck14982 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5 = rawRow14982 := by decide +kernel

def row14982 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14982 : row14982 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14982 := by decide +kernel

theorem rowEval14982 (x : Key → ℝ) : Integer.Sparse.eval row14982 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14982, Integer.Sparse.eval_collectBalanced, rawRowCheck14982]

def rawRow14983 : Integer.Sparse Key := [(key1224, 4), (key986, 4), (key1171, 4), (key1186, -2), (key1224, -2), (key988, -2), (key1175, -2), (key986, -2), (key1100, -2), (key1185, -2), (key1222, -2), (key986, -2), (key1171, -2), (key982, -2), (key1096, -2), (key1185, 4), (key986, 4), (key1100, 4)]

theorem rawRowCheck14983 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5 = rawRow14983 := by decide +kernel

def row14983 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14983 : row14983 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14983 := by decide +kernel

theorem rowEval14983 (x : Key → ℝ) : Integer.Sparse.eval row14983 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14983, Integer.Sparse.eval_collectBalanced, rawRowCheck14983]

def rawRow14984 : Integer.Sparse Key := [(key1224, 4), (key1171, 4), (key986, 4), (key1224, -2), (key1186, -2), (key1175, -2), (key988, -2), (key1100, -2), (key986, -2), (key1222, -2), (key1185, -2), (key1171, -2), (key986, -2), (key1096, -2), (key982, -2), (key1185, 4), (key1100, 4), (key986, 4)]

theorem rawRowCheck14984 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5 = rawRow14984 := by decide +kernel

def row14984 : Integer.Sparse Key := [(key982, -2), (key986, 4), (key988, -2), (key1096, -2), (key1100, 2), (key1171, 2), (key1175, -2), (key1185, 2), (key1186, -2), (key1222, -2), (key1224, 2)]

theorem rowCheck14984 : row14984 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14984 := by decide +kernel

theorem rowEval14984 (x : Key → ℝ) : Integer.Sparse.eval row14984 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14984, Integer.Sparse.eval_collectBalanced, rawRowCheck14984]

def rawRow14985 : Integer.Sparse Key := [(key988, 4), (key1175, 4), (key1175, 4), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key986, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key1171, -2), (key982, 4), (key1096, 4), (key1096, 4)]

theorem rawRowCheck14985 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5 = rawRow14985 := by decide +kernel

def row14985 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

theorem rowCheck14985 : row14985 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14985 := by decide +kernel

theorem rowEval14985 (x : Key → ℝ) : Integer.Sparse.eval row14985 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14985, Integer.Sparse.eval_collectBalanced, rawRowCheck14985]

def rawRow14986 : Integer.Sparse Key := [(key1175, 4), (key988, 4), (key1175, 4), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1171, -2), (key986, -2), (key1100, -2), (key1096, 4), (key982, 4), (key1096, 4)]

theorem rawRowCheck14986 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5 = rawRow14986 := by decide +kernel

def row14986 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

theorem rowCheck14986 : row14986 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14986 := by decide +kernel

theorem rowEval14986 (x : Key → ℝ) : Integer.Sparse.eval row14986 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form5) x := by
  rw [rowCheck14986, Integer.Sparse.eval_collectBalanced, rawRowCheck14986]

def rawRow14987 : Integer.Sparse Key := [(key1175, 4), (key1175, 4), (key988, 4), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1171, -2), (key1100, -2), (key1171, -2), (key986, -2), (key1100, -2), (key986, -2), (key1096, 4), (key1096, 4), (key982, 4)]

theorem rawRowCheck14987 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5 = rawRow14987 := by decide +kernel

def row14987 : Integer.Sparse Key := [(key982, 4), (key986, -8), (key988, 4), (key1096, 8), (key1100, -8), (key1171, -8), (key1175, 8)]

theorem rowCheck14987 : row14987 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14987 := by decide +kernel

theorem rowEval14987 (x : Key → ℝ) : Integer.Sparse.eval row14987 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form5) x := by
  rw [rowCheck14987, Integer.Sparse.eval_collectBalanced, rawRowCheck14987]

def rawRow14988 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2509, -1), (key2509, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1), (key2569, 2), (key2576, 2), (key2576, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1)]

theorem rawRowCheck14988 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form6 = rawRow14988 := by decide +kernel

def row14988 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

theorem rowCheck14988 : row14988 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14988 := by decide +kernel

theorem rowEval14988 (x : Key → ℝ) : Integer.Sparse.eval row14988 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14988, Integer.Sparse.eval_collectBalanced, rawRowCheck14988]

def rawRow14989 : Integer.Sparse Key := [(key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2503, -1), (key2509, -1), (key2472, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2576, 2), (key2569, 2), (key2576, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1)]

theorem rawRowCheck14989 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form6 = rawRow14989 := by decide +kernel

def row14989 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

theorem rowCheck14989 : row14989 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14989 := by decide +kernel

theorem rowEval14989 (x : Key → ℝ) : Integer.Sparse.eval row14989 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14989, Integer.Sparse.eval_collectBalanced, rawRowCheck14989]

def rawRow14990 : Integer.Sparse Key := [(key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2509, -1), (key2503, -1), (key2509, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1), (key2576, 2), (key2576, 2), (key2569, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1)]

theorem rawRowCheck14990 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form6 = rawRow14990 := by decide +kernel

def row14990 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2472, -2), (key2480, 4), (key2484, -2), (key2503, 2), (key2509, -4), (key2524, 2), (key2569, 2), (key2571, -2), (key2576, 2), (key2580, -2)]

theorem rowCheck14990 : row14990 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14990 := by decide +kernel

theorem rowEval14990 (x : Key → ℝ) : Integer.Sparse.eval row14990 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14990, Integer.Sparse.eval_collectBalanced, rawRowCheck14990]

def rawRow14991 : Integer.Sparse Key := [(key2406, -1), (key2411, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2443, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2484, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2472, 2), (key2484, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2509, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2571, 2), (key2571, 2), (key2580, 2), (key2569, -1), (key2571, -1), (key2569, -1), (key2576, -1), (key2571, -1), (key2576, -1)]

theorem rawRowCheck14991 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form6 = rawRow14991 := by decide +kernel

def row14991 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

theorem rowCheck14991 : row14991 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14991 := by decide +kernel

theorem rowEval14991 (x : Key → ℝ) : Integer.Sparse.eval row14991 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14991, Integer.Sparse.eval_collectBalanced, rawRowCheck14991]

def rawRow14992 : Integer.Sparse Key := [(key2411, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2411, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2484, -1), (key2480, -1), (key2524, -1), (key2480, -1), (key2524, -1), (key2484, -1), (key2484, 2), (key2472, 2), (key2509, 2), (key2472, 2), (key2509, 2), (key2484, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2571, 2), (key2580, 2), (key2571, 2), (key2571, -1), (key2569, -1), (key2576, -1), (key2569, -1), (key2576, -1), (key2571, -1)]

theorem rawRowCheck14992 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form6 = rawRow14992 := by decide +kernel

def row14992 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

theorem rowCheck14992 : row14992 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14992 := by decide +kernel

theorem rowEval14992 (x : Key → ℝ) : Integer.Sparse.eval row14992 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14992, Integer.Sparse.eval_collectBalanced, rawRowCheck14992]

def rawRow14993 : Integer.Sparse Key := [(key2443, -1), (key2443, -1), (key2411, -1), (key2411, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2524, -1), (key2524, -1), (key2484, -1), (key2484, -1), (key2480, -1), (key2480, -1), (key2509, 2), (key2509, 2), (key2484, 2), (key2484, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2580, 2), (key2571, 2), (key2571, 2), (key2576, -1), (key2576, -1), (key2571, -1), (key2571, -1), (key2569, -1), (key2569, -1)]

theorem rawRowCheck14993 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form6 = rawRow14993 := by decide +kernel

def row14993 : Integer.Sparse Key := [(key2406, 2), (key2411, -2), (key2437, 2), (key2443, -2), (key2472, 2), (key2480, -4), (key2484, 2), (key2503, -2), (key2509, 4), (key2524, -2), (key2569, -2), (key2571, 2), (key2576, -2), (key2580, 2)]

theorem rowCheck14993 : row14993 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14993 := by decide +kernel

theorem rowEval14993 (x : Key → ℝ) : Integer.Sparse.eval row14993 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14993, Integer.Sparse.eval_collectBalanced, rawRowCheck14993]

def rawRow14994 : Integer.Sparse Key := [(key2843, -1), (key2843, -1), (key2966, -1), (key2966, -1), (key2968, -1), (key2968, -1), (key2880, 2), (key2989, 2), (key2989, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2443, -1), (key2443, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2524, 2), (key2524, 2), (key2571, -1), (key2571, -1), (key2576, -1), (key2576, -1), (key2580, -1), (key2580, -1), (key2411, 2), (key2443, 2), (key2443, 2), (key2484, -1), (key2484, -1), (key2509, -1), (key2509, -1), (key2524, -1), (key2524, -1)]

theorem rawRowCheck14994 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form6 = rawRow14994 := by decide +kernel

def row14994 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

theorem rowCheck14994 : row14994 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14994 := by decide +kernel

theorem rowEval14994 (x : Key → ℝ) : Integer.Sparse.eval row14994 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14994, Integer.Sparse.eval_collectBalanced, rawRowCheck14994]

def rawRow14995 : Integer.Sparse Key := [(key2966, -1), (key2968, -1), (key2843, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2989, 2), (key2880, 2), (key2989, 2), (key2437, -1), (key2443, -1), (key2406, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2524, 2), (key2480, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2576, -1), (key2580, -1), (key2571, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2443, 2), (key2411, 2), (key2443, 2), (key2509, -1), (key2524, -1), (key2484, -1), (key2524, -1), (key2484, -1), (key2509, -1)]

theorem rawRowCheck14995 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form6 = rawRow14995 := by decide +kernel

def row14995 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

theorem rowCheck14995 : row14995 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14995 := by decide +kernel

theorem rowEval14995 (x : Key → ℝ) : Integer.Sparse.eval row14995 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14995, Integer.Sparse.eval_collectBalanced, rawRowCheck14995]

def rawRow14996 : Integer.Sparse Key := [(key2968, -1), (key2966, -1), (key2968, -1), (key2843, -1), (key2966, -1), (key2843, -1), (key2989, 2), (key2989, 2), (key2880, 2), (key2443, -1), (key2437, -1), (key2443, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2524, 2), (key2503, 2), (key2524, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2580, -1), (key2576, -1), (key2580, -1), (key2571, -1), (key2576, -1), (key2571, -1), (key2443, 2), (key2443, 2), (key2411, 2), (key2524, -1), (key2509, -1), (key2524, -1), (key2484, -1), (key2509, -1), (key2484, -1)]

theorem rawRowCheck14996 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form6 = rawRow14996 := by decide +kernel

def row14996 : Integer.Sparse Key := [(key2406, -2), (key2411, 2), (key2437, -2), (key2443, 2), (key2480, 4), (key2484, -2), (key2503, 4), (key2509, -2), (key2524, 2), (key2571, -2), (key2576, -2), (key2580, -2), (key2843, -2), (key2880, 2), (key2966, -2), (key2968, -2), (key2989, 4)]

theorem rowCheck14996 : row14996 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14996 := by decide +kernel

theorem rowEval14996 (x : Key → ℝ) : Integer.Sparse.eval row14996 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14996, Integer.Sparse.eval_collectBalanced, rawRowCheck14996]

def rawRow14997 : Integer.Sparse Key := [(key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2843, 2), (key2966, 2), (key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1), (key2394, 2), (key2484, 2), (key2524, 2), (key2383, -1), (key2394, -1), (key2411, -1), (key2443, -1), (key2484, -1), (key2509, -1)]

theorem rawRowCheck14997 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form6 = rawRow14997 := by decide +kernel

def row14997 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck14997 : row14997 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14997 := by decide +kernel

theorem rowEval14997 (x : Key → ℝ) : Integer.Sparse.eval row14997 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14997, Integer.Sparse.eval_collectBalanced, rawRowCheck14997]

def rawRow14998 : Integer.Sparse Key := [(key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2587, 2), (key2966, 2), (key2843, 2), (key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1), (key2394, 2), (key2524, 2), (key2484, 2), (key2394, -1), (key2383, -1), (key2443, -1), (key2411, -1), (key2509, -1), (key2484, -1)]

theorem rawRowCheck14998 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form6 = rawRow14998 := by decide +kernel

def row14998 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck14998 : row14998 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14998 := by decide +kernel

theorem rowEval14998 (x : Key → ℝ) : Integer.Sparse.eval row14998 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck14998, Integer.Sparse.eval_collectBalanced, rawRowCheck14998]

def rawRow14999 : Integer.Sparse Key := [(key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2843, 2), (key2587, 2), (key2966, 2), (key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1), (key2484, 2), (key2394, 2), (key2524, 2), (key2411, -1), (key2484, -1), (key2383, -1), (key2509, -1), (key2394, -1), (key2443, -1)]

theorem rawRowCheck14999 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form6 = rawRow14999 := by decide +kernel

def row14999 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck14999 : row14999 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow14999 := by decide +kernel

theorem rowEval14999 (x : Key → ℝ) : Integer.Sparse.eval row14999 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck14999, Integer.Sparse.eval_collectBalanced, rawRowCheck14999]

def rawRow15000 : Integer.Sparse Key := [(key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2843, 2), (key2966, 2), (key2587, 2), (key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1), (key2484, 2), (key2524, 2), (key2394, 2), (key2484, -1), (key2411, -1), (key2509, -1), (key2383, -1), (key2443, -1), (key2394, -1)]

theorem rawRowCheck15000 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form6 = rawRow15000 := by decide +kernel

def row15000 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck15000 : row15000 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15000 := by decide +kernel

theorem rowEval15000 (x : Key → ℝ) : Integer.Sparse.eval row15000 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck15000, Integer.Sparse.eval_collectBalanced, rawRowCheck15000]

def rawRow15001 : Integer.Sparse Key := [(key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2966, 2), (key2587, 2), (key2843, 2), (key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1), (key2524, 2), (key2394, 2), (key2484, 2), (key2443, -1), (key2509, -1), (key2394, -1), (key2484, -1), (key2383, -1), (key2411, -1)]

theorem rawRowCheck15001 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form6 = rawRow15001 := by decide +kernel

def row15001 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck15001 : row15001 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15001 := by decide +kernel

theorem rowEval15001 (x : Key → ℝ) : Integer.Sparse.eval row15001 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15001, Integer.Sparse.eval_collectBalanced, rawRowCheck15001]

def rawRow15002 : Integer.Sparse Key := [(key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2966, 2), (key2843, 2), (key2587, 2), (key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1), (key2524, 2), (key2484, 2), (key2394, 2), (key2509, -1), (key2443, -1), (key2484, -1), (key2394, -1), (key2411, -1), (key2383, -1)]

theorem rawRowCheck15002 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form6 = rawRow15002 := by decide +kernel

def row15002 : Integer.Sparse Key := [(key2378, -1), (key2383, -1), (key2390, -1), (key2394, 1), (key2406, -1), (key2411, -1), (key2437, -1), (key2443, -1), (key2480, -1), (key2484, 1), (key2503, -1), (key2509, -1), (key2524, 2), (key2587, 3), (key2593, -1), (key2598, -1), (key2600, 1), (key2766, 2), (key2843, 1), (key2880, -1), (key2887, -1), (key2910, 1), (key2931, 2), (key2966, 2), (key2968, -1), (key2989, 1), (key2995, -1), (key3002, -1)]

theorem rowCheck15002 : row15002 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15002 := by decide +kernel

theorem rowEval15002 (x : Key → ℝ) : Integer.Sparse.eval row15002 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck15002, Integer.Sparse.eval_collectBalanced, rawRowCheck15002]

def rawRow15003 : Integer.Sparse Key := [(key2887, -1), (key2889, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2995, -1), (key2910, 2), (key2910, 2), (key3002, 2), (key2766, -1), (key2772, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2931, -1), (key2843, 2), (key2889, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2968, 2), (key2880, -1), (key2910, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2989, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1)]

theorem rawRowCheck15003 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form6 = rawRow15003 := by decide +kernel

def row15003 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck15003 : row15003 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15003 := by decide +kernel

theorem rowEval15003 (x : Key → ℝ) : Integer.Sparse.eval row15003 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15003, Integer.Sparse.eval_collectBalanced, rawRowCheck15003]

def rawRow15004 : Integer.Sparse Key := [(key2889, -1), (key2887, -1), (key2995, -1), (key2887, -1), (key2995, -1), (key2889, -1), (key2910, 2), (key3002, 2), (key2910, 2), (key2772, -1), (key2766, -1), (key2931, -1), (key2766, -1), (key2931, -1), (key2772, -1), (key2889, 2), (key2843, 2), (key2968, 2), (key2843, 2), (key2968, 2), (key2889, 2), (key2910, -1), (key2880, -1), (key2989, -1), (key2880, -1), (key2989, -1), (key2910, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1)]

theorem rawRowCheck15004 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form6 = rawRow15004 := by decide +kernel

def row15004 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck15004 : row15004 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15004 := by decide +kernel

theorem rowEval15004 (x : Key → ℝ) : Integer.Sparse.eval row15004 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15004, Integer.Sparse.eval_collectBalanced, rawRowCheck15004]

def rawRow15005 : Integer.Sparse Key := [(key2995, -1), (key2995, -1), (key2889, -1), (key2889, -1), (key2887, -1), (key2887, -1), (key3002, 2), (key2910, 2), (key2910, 2), (key2931, -1), (key2931, -1), (key2772, -1), (key2772, -1), (key2766, -1), (key2766, -1), (key2968, 2), (key2968, 2), (key2889, 2), (key2889, 2), (key2843, 2), (key2843, 2), (key2989, -1), (key2989, -1), (key2910, -1), (key2910, -1), (key2880, -1), (key2880, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1)]

theorem rawRowCheck15005 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form6 = rawRow15005 := by decide +kernel

def row15005 : Integer.Sparse Key := [(key2406, 4), (key2437, 2), (key2472, -2), (key2480, -2), (key2503, -2), (key2766, -2), (key2772, -2), (key2843, 4), (key2880, -2), (key2887, -2), (key2889, 2), (key2910, 2), (key2931, -2), (key2968, 4), (key2989, -2), (key2995, -2), (key3002, 2)]

theorem rowCheck15005 : row15005 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15005 := by decide +kernel

theorem rowEval15005 (x : Key → ℝ) : Integer.Sparse.eval row15005 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15005, Integer.Sparse.eval_collectBalanced, rawRowCheck15005]

def rawRow15006 : Integer.Sparse Key := [(key2598, -1), (key2600, -1), (key2887, -1), (key2995, -1), (key2910, -1), (key3002, -1), (key2600, 2), (key2889, 2), (key2995, 2), (key2587, -1), (key2593, -1), (key2843, -1), (key2968, -1), (key2880, -1), (key2989, -1), (key2587, 2), (key2600, 2), (key2766, 2), (key2931, 2), (key2910, 2), (key2989, 2), (key2593, -1), (key2600, -1), (key2772, -1), (key2931, -1), (key2889, -1), (key2968, -1), (key2378, 2), (key2472, 2), (key2503, 2), (key2378, -1), (key2390, -1), (key2406, -1), (key2437, -1), (key2480, -1), (key2503, -1)]

theorem rawRowCheck15006 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form6 = rawRow15006 := by decide +kernel

def row15006 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15006 : row15006 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15006 := by decide +kernel

theorem rowEval15006 (x : Key → ℝ) : Integer.Sparse.eval row15006 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15006, Integer.Sparse.eval_collectBalanced, rawRowCheck15006]

def rawRow15007 : Integer.Sparse Key := [(key2600, -1), (key2598, -1), (key2995, -1), (key2887, -1), (key3002, -1), (key2910, -1), (key2600, 2), (key2995, 2), (key2889, 2), (key2593, -1), (key2587, -1), (key2968, -1), (key2843, -1), (key2989, -1), (key2880, -1), (key2600, 2), (key2587, 2), (key2931, 2), (key2766, 2), (key2989, 2), (key2910, 2), (key2600, -1), (key2593, -1), (key2931, -1), (key2772, -1), (key2968, -1), (key2889, -1), (key2378, 2), (key2503, 2), (key2472, 2), (key2390, -1), (key2378, -1), (key2437, -1), (key2406, -1), (key2503, -1), (key2480, -1)]

theorem rawRowCheck15007 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form6 = rawRow15007 := by decide +kernel

def row15007 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15007 : row15007 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15007 := by decide +kernel

theorem rowEval15007 (x : Key → ℝ) : Integer.Sparse.eval row15007 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15007, Integer.Sparse.eval_collectBalanced, rawRowCheck15007]

def rawRow15008 : Integer.Sparse Key := [(key2887, -1), (key2910, -1), (key2598, -1), (key3002, -1), (key2600, -1), (key2995, -1), (key2889, 2), (key2600, 2), (key2995, 2), (key2843, -1), (key2880, -1), (key2587, -1), (key2989, -1), (key2593, -1), (key2968, -1), (key2766, 2), (key2910, 2), (key2587, 2), (key2989, 2), (key2600, 2), (key2931, 2), (key2772, -1), (key2889, -1), (key2593, -1), (key2968, -1), (key2600, -1), (key2931, -1), (key2472, 2), (key2378, 2), (key2503, 2), (key2406, -1), (key2480, -1), (key2378, -1), (key2503, -1), (key2390, -1), (key2437, -1)]

theorem rawRowCheck15008 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form6 = rawRow15008 := by decide +kernel

def row15008 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15008 : row15008 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15008 := by decide +kernel

theorem rowEval15008 (x : Key → ℝ) : Integer.Sparse.eval row15008 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form6) x := by
  rw [rowCheck15008, Integer.Sparse.eval_collectBalanced, rawRowCheck15008]

def rawRow15009 : Integer.Sparse Key := [(key2910, -1), (key2887, -1), (key3002, -1), (key2598, -1), (key2995, -1), (key2600, -1), (key2889, 2), (key2995, 2), (key2600, 2), (key2880, -1), (key2843, -1), (key2989, -1), (key2587, -1), (key2968, -1), (key2593, -1), (key2910, 2), (key2766, 2), (key2989, 2), (key2587, 2), (key2931, 2), (key2600, 2), (key2889, -1), (key2772, -1), (key2968, -1), (key2593, -1), (key2931, -1), (key2600, -1), (key2472, 2), (key2503, 2), (key2378, 2), (key2480, -1), (key2406, -1), (key2503, -1), (key2378, -1), (key2437, -1), (key2390, -1)]

theorem rawRowCheck15009 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form6 = rawRow15009 := by decide +kernel

def row15009 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15009 : row15009 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15009 := by decide +kernel

theorem rowEval15009 (x : Key → ℝ) : Integer.Sparse.eval row15009 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck15009, Integer.Sparse.eval_collectBalanced, rawRowCheck15009]

def rawRow15010 : Integer.Sparse Key := [(key2995, -1), (key3002, -1), (key2600, -1), (key2910, -1), (key2598, -1), (key2887, -1), (key2995, 2), (key2600, 2), (key2889, 2), (key2968, -1), (key2989, -1), (key2593, -1), (key2880, -1), (key2587, -1), (key2843, -1), (key2931, 2), (key2989, 2), (key2600, 2), (key2910, 2), (key2587, 2), (key2766, 2), (key2931, -1), (key2968, -1), (key2600, -1), (key2889, -1), (key2593, -1), (key2772, -1), (key2503, 2), (key2378, 2), (key2472, 2), (key2437, -1), (key2503, -1), (key2390, -1), (key2480, -1), (key2378, -1), (key2406, -1)]

theorem rawRowCheck15010 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form6 = rawRow15010 := by decide +kernel

def row15010 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15010 : row15010 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15010 := by decide +kernel

theorem rowEval15010 (x : Key → ℝ) : Integer.Sparse.eval row15010 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15010, Integer.Sparse.eval_collectBalanced, rawRowCheck15010]

def rawRow15011 : Integer.Sparse Key := [(key3002, -1), (key2995, -1), (key2910, -1), (key2600, -1), (key2887, -1), (key2598, -1), (key2995, 2), (key2889, 2), (key2600, 2), (key2989, -1), (key2968, -1), (key2880, -1), (key2593, -1), (key2843, -1), (key2587, -1), (key2989, 2), (key2931, 2), (key2910, 2), (key2600, 2), (key2766, 2), (key2587, 2), (key2968, -1), (key2931, -1), (key2889, -1), (key2600, -1), (key2772, -1), (key2593, -1), (key2503, 2), (key2472, 2), (key2378, 2), (key2503, -1), (key2437, -1), (key2480, -1), (key2390, -1), (key2406, -1), (key2378, -1)]

theorem rawRowCheck15011 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form6 = rawRow15011 := by decide +kernel

def row15011 : Integer.Sparse Key := [(key2378, 1), (key2390, -1), (key2406, -1), (key2437, -1), (key2472, 2), (key2480, -1), (key2503, 1), (key2587, 1), (key2593, -2), (key2598, -1), (key2600, 2), (key2766, 2), (key2772, -1), (key2843, -1), (key2880, -1), (key2887, -1), (key2889, 1), (key2910, 1), (key2931, 1), (key2968, -2), (key2989, 1), (key2995, 1), (key3002, -1)]

theorem rowCheck15011 : row15011 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15011 := by decide +kernel

theorem rowEval15011 (x : Key → ℝ) : Integer.Sparse.eval row15011 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck15011, Integer.Sparse.eval_collectBalanced, rawRowCheck15011]

def rawRow15012 : Integer.Sparse Key := [(key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2598, 2), (key2887, 2), (key2887, 2), (key2600, -1), (key2600, -1), (key2889, -1), (key2889, -1), (key2910, -1), (key2910, -1), (key2593, 2), (key2593, 2), (key2772, 2), (key2772, 2), (key2880, 2), (key2880, 2), (key2587, -1), (key2587, -1), (key2766, -1), (key2766, -1), (key2843, -1), (key2843, -1), (key2390, 2), (key2480, 2), (key2480, 2), (key2378, -1), (key2378, -1), (key2406, -1), (key2406, -1), (key2472, -1), (key2472, -1)]

theorem rawRowCheck15012 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form6 = rawRow15012 := by decide +kernel

def row15012 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

theorem rowCheck15012 : row15012 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15012 := by decide +kernel

theorem rowEval15012 (x : Key → ℝ) : Integer.Sparse.eval row15012 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15012, Integer.Sparse.eval_collectBalanced, rawRowCheck15012]

def rawRow15013 : Integer.Sparse Key := [(key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2887, 2), (key2598, 2), (key2887, 2), (key2889, -1), (key2910, -1), (key2600, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2772, 2), (key2880, 2), (key2593, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2766, -1), (key2843, -1), (key2587, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2480, 2), (key2390, 2), (key2480, 2), (key2406, -1), (key2472, -1), (key2378, -1), (key2472, -1), (key2378, -1), (key2406, -1)]

theorem rawRowCheck15013 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form6 = rawRow15013 := by decide +kernel

def row15013 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

theorem rowCheck15013 : row15013 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15013 := by decide +kernel

theorem rowEval15013 (x : Key → ℝ) : Integer.Sparse.eval row15013 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form6) x := by
  rw [rowCheck15013, Integer.Sparse.eval_collectBalanced, rawRowCheck15013]

def rawRow15014 : Integer.Sparse Key := [(key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2887, 2), (key2887, 2), (key2598, 2), (key2910, -1), (key2889, -1), (key2910, -1), (key2600, -1), (key2889, -1), (key2600, -1), (key2880, 2), (key2772, 2), (key2880, 2), (key2593, 2), (key2772, 2), (key2593, 2), (key2843, -1), (key2766, -1), (key2843, -1), (key2587, -1), (key2766, -1), (key2587, -1), (key2480, 2), (key2480, 2), (key2390, 2), (key2472, -1), (key2406, -1), (key2472, -1), (key2378, -1), (key2406, -1), (key2378, -1)]

theorem rawRowCheck15014 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form6 = rawRow15014 := by decide +kernel

def row15014 : Integer.Sparse Key := [(key2378, -2), (key2390, 2), (key2406, -2), (key2472, -2), (key2480, 4), (key2587, -2), (key2593, 4), (key2598, 2), (key2600, -4), (key2766, -2), (key2772, 4), (key2843, -2), (key2880, 4), (key2887, 4), (key2889, -4), (key2910, -4)]

theorem rowCheck15014 : row15014 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15014 := by decide +kernel

theorem rowEval15014 (x : Key → ℝ) : Integer.Sparse.eval row15014 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form6) x := by
  rw [rowCheck15014, Integer.Sparse.eval_collectBalanced, rawRowCheck15014]

def rawRow15015 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2495, -4), (key2504, -4), (key2504, 12)]

theorem rawRowCheck15015 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form7 = rawRow15015 := by decide +kernel

def row15015 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15015 : row15015 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15015 := by decide +kernel

theorem rowEval15015 (x : Key → ℝ) : Integer.Sparse.eval row15015 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15015, Integer.Sparse.eval_collectBalanced, rawRowCheck15015]

def rawRow15016 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2427, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2495, -4), (key2504, 12)]

theorem rawRowCheck15016 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form7 = rawRow15016 := by decide +kernel

def row15016 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15016 : row15016 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15016 := by decide +kernel

theorem rowEval15016 (x : Key → ℝ) : Integer.Sparse.eval row15016 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15016, Integer.Sparse.eval_collectBalanced, rawRowCheck15016]

def rawRow15017 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2495, -4), (key2504, 12)]

theorem rawRowCheck15017 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form7 = rawRow15017 := by decide +kernel

def row15017 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15017 : row15017 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15017 := by decide +kernel

theorem rowEval15017 (x : Key → ℝ) : Integer.Sparse.eval row15017 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15017, Integer.Sparse.eval_collectBalanced, rawRowCheck15017]

def rawRow15018 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2504, -4), (key2504, -4), (key2495, 12)]

theorem rawRowCheck15018 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form7 = rawRow15018 := by decide +kernel

def row15018 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15018 : row15018 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15018 := by decide +kernel

theorem rowEval15018 (x : Key → ℝ) : Integer.Sparse.eval row15018 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15018, Integer.Sparse.eval_collectBalanced, rawRowCheck15018]

def rawRow15019 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2427, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2495, -4), (key2504, -4), (key2495, 12)]

theorem rawRowCheck15019 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form7 = rawRow15019 := by decide +kernel

def row15019 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15019 : row15019 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15019 := by decide +kernel

theorem rowEval15019 (x : Key → ℝ) : Integer.Sparse.eval row15019 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15019, Integer.Sparse.eval_collectBalanced, rawRowCheck15019]

def rawRow15020 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2427, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2504, -4), (key2495, -4), (key2495, 12)]

theorem rawRowCheck15020 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form7 = rawRow15020 := by decide +kernel

def row15020 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15020 : row15020 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15020 := by decide +kernel

theorem rowEval15020 (x : Key → ℝ) : Integer.Sparse.eval row15020 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15020, Integer.Sparse.eval_collectBalanced, rawRowCheck15020]

def rawRow15021 : Integer.Sparse Key := [(key2420, 4), (key2427, 4), (key2427, 4), (key2495, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2438, -4), (key2504, 12)]

theorem rawRowCheck15021 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form7 = rawRow15021 := by decide +kernel

def row15021 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15021 : row15021 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15021 := by decide +kernel

theorem rowEval15021 (x : Key → ℝ) : Integer.Sparse.eval row15021 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15021, Integer.Sparse.eval_collectBalanced, rawRowCheck15021]

def rawRow15022 : Integer.Sparse Key := [(key2427, 4), (key2420, 4), (key2427, 4), (key2495, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2427, -4), (key2504, 12)]

theorem rawRowCheck15022 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form7 = rawRow15022 := by decide +kernel

def row15022 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15022 : row15022 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15022 := by decide +kernel

theorem rowEval15022 (x : Key → ℝ) : Integer.Sparse.eval row15022 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15022, Integer.Sparse.eval_collectBalanced, rawRowCheck15022]

def rawRow15023 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2420, 4), (key2504, -4), (key2495, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2427, -4), (key2504, 12)]

theorem rawRowCheck15023 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form7 = rawRow15023 := by decide +kernel

def row15023 : Integer.Sparse Key := [(key2420, 4), (key2438, -4), (key2495, -8), (key2504, 8)]

theorem rowCheck15023 : row15023 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15023 := by decide +kernel

theorem rowEval15023 (x : Key → ℝ) : Integer.Sparse.eval row15023 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15023, Integer.Sparse.eval_collectBalanced, rawRowCheck15023]

def rawRow15024 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2438, -4), (key2504, -4), (key2427, 12)]

theorem rawRowCheck15024 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form7 = rawRow15024 := by decide +kernel

def row15024 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15024 : row15024 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15024 := by decide +kernel

theorem rowEval15024 (x : Key → ℝ) : Integer.Sparse.eval row15024 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15024, Integer.Sparse.eval_collectBalanced, rawRowCheck15024]

def rawRow15025 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2427, -4), (key2420, -4), (key2495, -4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, 12)]

theorem rawRowCheck15025 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form7 = rawRow15025 := by decide +kernel

def row15025 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15025 : row15025 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15025 := by decide +kernel

theorem rowEval15025 (x : Key → ℝ) : Integer.Sparse.eval row15025 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15025, Integer.Sparse.eval_collectBalanced, rawRowCheck15025]

def rawRow15026 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2504, -4), (key2438, -4), (key2427, 12)]

theorem rawRowCheck15026 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form7 = rawRow15026 := by decide +kernel

def row15026 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15026 : row15026 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15026 := by decide +kernel

theorem rowEval15026 (x : Key → ℝ) : Integer.Sparse.eval row15026 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15026, Integer.Sparse.eval_collectBalanced, rawRowCheck15026]

def rawRow15027 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2495, -4), (key2420, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2438, -4), (key2427, 12)]

theorem rawRowCheck15027 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form7 = rawRow15027 := by decide +kernel

def row15027 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15027 : row15027 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15027 := by decide +kernel

theorem rowEval15027 (x : Key → ℝ) : Integer.Sparse.eval row15027 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15027, Integer.Sparse.eval_collectBalanced, rawRowCheck15027]

def rawRow15028 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2427, -4), (key2495, -4), (key2420, -4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, 12)]

theorem rawRowCheck15028 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form7 = rawRow15028 := by decide +kernel

def row15028 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15028 : row15028 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15028 := by decide +kernel

theorem rowEval15028 (x : Key → ℝ) : Integer.Sparse.eval row15028 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15028, Integer.Sparse.eval_collectBalanced, rawRowCheck15028]

def rawRow15029 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2495, -4), (key2427, -4), (key2420, -4), (key2504, -4), (key2438, -4), (key2427, -4), (key2427, 12)]

theorem rawRowCheck15029 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form7 = rawRow15029 := by decide +kernel

def row15029 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15029 : row15029 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15029 := by decide +kernel

theorem rowEval15029 (x : Key → ℝ) : Integer.Sparse.eval row15029 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15029, Integer.Sparse.eval_collectBalanced, rawRowCheck15029]

def rawRow15030 : Integer.Sparse Key := [(key2427, 4), (key2427, 4), (key2438, 4), (key2495, -4), (key2504, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2427, -4), (key2495, 12)]

theorem rawRowCheck15030 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form7 = rawRow15030 := by decide +kernel

def row15030 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15030 : row15030 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15030 := by decide +kernel

theorem rowEval15030 (x : Key → ℝ) : Integer.Sparse.eval row15030 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15030, Integer.Sparse.eval_collectBalanced, rawRowCheck15030]

def rawRow15031 : Integer.Sparse Key := [(key2427, 4), (key2438, 4), (key2427, 4), (key2504, -4), (key2495, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2427, -4), (key2495, 12)]

theorem rawRowCheck15031 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form7 = rawRow15031 := by decide +kernel

def row15031 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15031 : row15031 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15031 := by decide +kernel

theorem rowEval15031 (x : Key → ℝ) : Integer.Sparse.eval row15031 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15031, Integer.Sparse.eval_collectBalanced, rawRowCheck15031]

def rawRow15032 : Integer.Sparse Key := [(key2438, 4), (key2427, 4), (key2427, 4), (key2504, -4), (key2504, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, -4), (key2495, 12)]

theorem rawRowCheck15032 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form7 = rawRow15032 := by decide +kernel

def row15032 : Integer.Sparse Key := [(key2420, -4), (key2438, 4), (key2495, 8), (key2504, -8)]

theorem rowCheck15032 : row15032 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15032 := by decide +kernel

theorem rowEval15032 (x : Key → ℝ) : Integer.Sparse.eval row15032 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15032, Integer.Sparse.eval_collectBalanced, rawRowCheck15032]

def rawRow15033 : Integer.Sparse Key := [(key2427, 4), (key2495, 4), (key2504, 4), (key2427, -4), (key2438, -4), (key2504, -4), (key2420, -4), (key2427, -4), (key2495, -4), (key2427, 12)]

theorem rawRowCheck15033 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form7 = rawRow15033 := by decide +kernel

def row15033 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15033 : row15033 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15033 := by decide +kernel

theorem rowEval15033 (x : Key → ℝ) : Integer.Sparse.eval row15033 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15033, Integer.Sparse.eval_collectBalanced, rawRowCheck15033]

def rawRow15034 : Integer.Sparse Key := [(key2427, 4), (key2504, 4), (key2495, 4), (key2438, -4), (key2427, -4), (key2504, -4), (key2427, -4), (key2420, -4), (key2495, -4), (key2427, 12)]

theorem rawRowCheck15034 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form7 = rawRow15034 := by decide +kernel

def row15034 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15034 : row15034 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15034 := by decide +kernel

theorem rowEval15034 (x : Key → ℝ) : Integer.Sparse.eval row15034 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15034, Integer.Sparse.eval_collectBalanced, rawRowCheck15034]

def rawRow15035 : Integer.Sparse Key := [(key2495, 4), (key2427, 4), (key2504, 4), (key2427, -4), (key2504, -4), (key2438, -4), (key2420, -4), (key2495, -4), (key2427, -4), (key2427, 12)]

theorem rawRowCheck15035 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form7 = rawRow15035 := by decide +kernel

def row15035 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15035 : row15035 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15035 := by decide +kernel

theorem rowEval15035 (x : Key → ℝ) : Integer.Sparse.eval row15035 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form7) x := by
  rw [rowCheck15035, Integer.Sparse.eval_collectBalanced, rawRowCheck15035]

def rawRow15036 : Integer.Sparse Key := [(key2495, 4), (key2504, 4), (key2427, 4), (key2504, -4), (key2427, -4), (key2438, -4), (key2495, -4), (key2420, -4), (key2427, -4), (key2427, 12)]

theorem rawRowCheck15036 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form7 = rawRow15036 := by decide +kernel

def row15036 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15036 : row15036 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15036 := by decide +kernel

theorem rowEval15036 (x : Key → ℝ) : Integer.Sparse.eval row15036 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15036, Integer.Sparse.eval_collectBalanced, rawRowCheck15036]

def rawRow15037 : Integer.Sparse Key := [(key2504, 4), (key2427, 4), (key2495, 4), (key2438, -4), (key2504, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, -4), (key2427, 12)]

theorem rawRowCheck15037 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form7 = rawRow15037 := by decide +kernel

def row15037 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15037 : row15037 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15037 := by decide +kernel

theorem rowEval15037 (x : Key → ℝ) : Integer.Sparse.eval row15037 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15037, Integer.Sparse.eval_collectBalanced, rawRowCheck15037]

def rawRow15038 : Integer.Sparse Key := [(key2504, 4), (key2495, 4), (key2427, 4), (key2504, -4), (key2438, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, -4), (key2427, 12)]

theorem rawRowCheck15038 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form7 = rawRow15038 := by decide +kernel

def row15038 : Integer.Sparse Key := [(key2420, -4), (key2427, 8), (key2438, -4)]

theorem rowCheck15038 : row15038 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15038 := by decide +kernel

theorem rowEval15038 (x : Key → ℝ) : Integer.Sparse.eval row15038 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15038, Integer.Sparse.eval_collectBalanced, rawRowCheck15038]

def rawRow15039 : Integer.Sparse Key := [(key2438, 4), (key2504, 4), (key2504, 4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2420, 12)]

theorem rawRowCheck15039 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form7 = rawRow15039 := by decide +kernel

def row15039 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

theorem rowCheck15039 : row15039 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15039 := by decide +kernel

theorem rowEval15039 (x : Key → ℝ) : Integer.Sparse.eval row15039 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15039, Integer.Sparse.eval_collectBalanced, rawRowCheck15039]

def rawRow15040 : Integer.Sparse Key := [(key2504, 4), (key2438, 4), (key2504, 4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2420, 12)]

theorem rawRowCheck15040 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form7 = rawRow15040 := by decide +kernel

def row15040 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

theorem rowCheck15040 : row15040 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15040 := by decide +kernel

theorem rowEval15040 (x : Key → ℝ) : Integer.Sparse.eval row15040 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form7) x := by
  rw [rowCheck15040, Integer.Sparse.eval_collectBalanced, rawRowCheck15040]

def rawRow15041 : Integer.Sparse Key := [(key2504, 4), (key2504, 4), (key2438, 4), (key2495, -4), (key2427, -4), (key2427, -4), (key2495, -4), (key2427, -4), (key2427, -4), (key2420, 12)]

theorem rawRowCheck15041 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form7 = rawRow15041 := by decide +kernel

def row15041 : Integer.Sparse Key := [(key2420, 12), (key2427, -16), (key2438, 4), (key2495, -8), (key2504, 8)]

theorem rowCheck15041 : row15041 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15041 := by decide +kernel

theorem rowEval15041 (x : Key → ℝ) : Integer.Sparse.eval row15041 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form7) x := by
  rw [rowCheck15041, Integer.Sparse.eval_collectBalanced, rawRowCheck15041]

def rawRow15042 : Integer.Sparse Key := [(key2361, -2), (key2361, -2), (key2364, -2), (key2364, 6), (key2456, -2), (key2456, -2), (key2459, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2459, -2), (key2520, -2), (key2520, -2), (key2531, 6), (key2531, -2), (key2561, -2), (key2561, -2)]

theorem rawRowCheck15042 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form8 = rawRow15042 := by decide +kernel

def row15042 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15042 : row15042 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15042 := by decide +kernel

theorem rowEval15042 (x : Key → ℝ) : Integer.Sparse.eval row15042 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15042, Integer.Sparse.eval_collectBalanced, rawRowCheck15042]

def rawRow15043 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2361, -2), (key2364, 6), (key2456, -2), (key2459, -2), (key2456, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2520, -2), (key2459, -2), (key2520, -2), (key2531, 6), (key2561, -2), (key2531, -2), (key2561, -2)]

theorem rawRowCheck15043 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form8 = rawRow15043 := by decide +kernel

def row15043 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15043 : row15043 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15043 := by decide +kernel

theorem rowEval15043 (x : Key → ℝ) : Integer.Sparse.eval row15043 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15043, Integer.Sparse.eval_collectBalanced, rawRowCheck15043]

def rawRow15044 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2361, -2), (key2364, 6), (key2459, -2), (key2456, -2), (key2456, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2520, -2), (key2520, -2), (key2459, -2), (key2531, 6), (key2561, -2), (key2561, -2), (key2531, -2)]

theorem rawRowCheck15044 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form8 = rawRow15044 := by decide +kernel

def row15044 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15044 : row15044 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15044 := by decide +kernel

theorem rowEval15044 (x : Key → ℝ) : Integer.Sparse.eval row15044 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15044, Integer.Sparse.eval_collectBalanced, rawRowCheck15044]

def rawRow15045 : Integer.Sparse Key := [(key2361, -2), (key2364, -2), (key2364, -2), (key2361, 6), (key2517, -2), (key2520, -2), (key2520, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2456, -2), (key2456, -2), (key2517, -2), (key2561, 6), (key2531, -2), (key2531, -2), (key2561, -2)]

theorem rawRowCheck15045 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form8 = rawRow15045 := by decide +kernel

def row15045 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15045 : row15045 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15045 := by decide +kernel

theorem rowEval15045 (x : Key → ℝ) : Integer.Sparse.eval row15045 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15045, Integer.Sparse.eval_collectBalanced, rawRowCheck15045]

def rawRow15046 : Integer.Sparse Key := [(key2364, -2), (key2361, -2), (key2364, -2), (key2361, 6), (key2520, -2), (key2517, -2), (key2520, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2456, -2), (key2517, -2), (key2456, -2), (key2561, 6), (key2531, -2), (key2561, -2), (key2531, -2)]

theorem rawRowCheck15046 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form8 = rawRow15046 := by decide +kernel

def row15046 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15046 : row15046 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15046 := by decide +kernel

theorem rowEval15046 (x : Key → ℝ) : Integer.Sparse.eval row15046 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15046, Integer.Sparse.eval_collectBalanced, rawRowCheck15046]

def rawRow15047 : Integer.Sparse Key := [(key2364, -2), (key2364, -2), (key2361, -2), (key2361, 6), (key2520, -2), (key2520, -2), (key2517, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2517, -2), (key2456, -2), (key2456, -2), (key2561, 6), (key2561, -2), (key2531, -2), (key2531, -2)]

theorem rawRowCheck15047 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form8 = rawRow15047 := by decide +kernel

def row15047 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15047 : row15047 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15047 := by decide +kernel

theorem rowEval15047 (x : Key → ℝ) : Integer.Sparse.eval row15047 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15047, Integer.Sparse.eval_collectBalanced, rawRowCheck15047]

def rawRow15048 : Integer.Sparse Key := [(key2456, -2), (key2456, -2), (key2459, -2), (key2531, 6), (key2361, -2), (key2361, -2), (key2364, -2), (key2456, 2), (key2456, 2), (key2517, 2), (key2517, 2), (key2520, 2), (key2520, 2), (key2531, -2), (key2561, -2), (key2561, -2), (key2364, 6), (key2459, -2), (key2520, -2), (key2520, -2)]

theorem rawRowCheck15048 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form8 = rawRow15048 := by decide +kernel

def row15048 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15048 : row15048 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15048 := by decide +kernel

theorem rowEval15048 (x : Key → ℝ) : Integer.Sparse.eval row15048 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15048, Integer.Sparse.eval_collectBalanced, rawRowCheck15048]

def rawRow15049 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2456, -2), (key2531, 6), (key2361, -2), (key2364, -2), (key2361, -2), (key2517, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2561, -2), (key2531, -2), (key2561, -2), (key2364, 6), (key2520, -2), (key2459, -2), (key2520, -2)]

theorem rawRowCheck15049 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form8 = rawRow15049 := by decide +kernel

def row15049 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15049 : row15049 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15049 := by decide +kernel

theorem rowEval15049 (x : Key → ℝ) : Integer.Sparse.eval row15049 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15049, Integer.Sparse.eval_collectBalanced, rawRowCheck15049]

def rawRow15050 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2456, -2), (key2531, 6), (key2364, -2), (key2361, -2), (key2361, -2), (key2520, 2), (key2517, 2), (key2520, 2), (key2456, 2), (key2517, 2), (key2456, 2), (key2561, -2), (key2561, -2), (key2531, -2), (key2364, 6), (key2520, -2), (key2520, -2), (key2459, -2)]

theorem rawRowCheck15050 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form8 = rawRow15050 := by decide +kernel

def row15050 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2459, -4), (key2517, 4), (key2531, 4), (key2561, -4)]

theorem rowCheck15050 : row15050 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15050 := by decide +kernel

theorem rowEval15050 (x : Key → ℝ) : Integer.Sparse.eval row15050 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15050, Integer.Sparse.eval_collectBalanced, rawRowCheck15050]

def rawRow15051 : Integer.Sparse Key := [(key2456, -2), (key2459, -2), (key2531, -2), (key2456, 6), (key2517, -2), (key2520, -2), (key2561, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2361, -2), (key2456, -2), (key2517, -2), (key2520, 6), (key2364, -2), (key2459, -2), (key2520, -2)]

theorem rawRowCheck15051 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form8 = rawRow15051 := by decide +kernel

def row15051 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15051 : row15051 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15051 := by decide +kernel

theorem rowEval15051 (x : Key → ℝ) : Integer.Sparse.eval row15051 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15051, Integer.Sparse.eval_collectBalanced, rawRowCheck15051]

def rawRow15052 : Integer.Sparse Key := [(key2459, -2), (key2456, -2), (key2531, -2), (key2456, 6), (key2520, -2), (key2517, -2), (key2561, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2361, -2), (key2517, -2), (key2456, -2), (key2520, 6), (key2364, -2), (key2520, -2), (key2459, -2)]

theorem rawRowCheck15052 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form8 = rawRow15052 := by decide +kernel

def row15052 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15052 : row15052 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15052 := by decide +kernel

theorem rowEval15052 (x : Key → ℝ) : Integer.Sparse.eval row15052 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15052, Integer.Sparse.eval_collectBalanced, rawRowCheck15052]

def rawRow15053 : Integer.Sparse Key := [(key2456, -2), (key2531, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2561, -2), (key2520, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2456, -2), (key2361, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2364, -2), (key2520, -2)]

theorem rawRowCheck15053 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form8 = rawRow15053 := by decide +kernel

def row15053 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15053 : row15053 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15053 := by decide +kernel

theorem rowEval15053 (x : Key → ℝ) : Integer.Sparse.eval row15053 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15053, Integer.Sparse.eval_collectBalanced, rawRowCheck15053]

def rawRow15054 : Integer.Sparse Key := [(key2531, -2), (key2456, -2), (key2459, -2), (key2456, 6), (key2561, -2), (key2517, -2), (key2520, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2456, -2), (key2517, -2), (key2361, -2), (key2520, 6), (key2459, -2), (key2520, -2), (key2364, -2)]

theorem rawRowCheck15054 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form8 = rawRow15054 := by decide +kernel

def row15054 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15054 : row15054 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15054 := by decide +kernel

theorem rowEval15054 (x : Key → ℝ) : Integer.Sparse.eval row15054 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck15054, Integer.Sparse.eval_collectBalanced, rawRowCheck15054]

def rawRow15055 : Integer.Sparse Key := [(key2459, -2), (key2531, -2), (key2456, -2), (key2456, 6), (key2520, -2), (key2561, -2), (key2517, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2517, -2), (key2361, -2), (key2456, -2), (key2520, 6), (key2520, -2), (key2364, -2), (key2459, -2)]

theorem rawRowCheck15055 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form8 = rawRow15055 := by decide +kernel

def row15055 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15055 : row15055 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15055 := by decide +kernel

theorem rowEval15055 (x : Key → ℝ) : Integer.Sparse.eval row15055 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15055, Integer.Sparse.eval_collectBalanced, rawRowCheck15055]

def rawRow15056 : Integer.Sparse Key := [(key2531, -2), (key2459, -2), (key2456, -2), (key2456, 6), (key2561, -2), (key2520, -2), (key2517, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2517, -2), (key2456, -2), (key2361, -2), (key2520, 6), (key2520, -2), (key2459, -2), (key2364, -2)]

theorem rawRowCheck15056 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form8 = rawRow15056 := by decide +kernel

def row15056 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15056 : row15056 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15056 := by decide +kernel

theorem rowEval15056 (x : Key → ℝ) : Integer.Sparse.eval row15056 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck15056, Integer.Sparse.eval_collectBalanced, rawRowCheck15056]

def rawRow15057 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2520, -2), (key2561, 6), (key2361, -2), (key2364, -2), (key2364, -2), (key2456, 2), (key2459, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2520, 2), (key2531, -2), (key2531, -2), (key2561, -2), (key2361, 6), (key2456, -2), (key2456, -2), (key2517, -2)]

theorem rawRowCheck15057 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form8 = rawRow15057 := by decide +kernel

def row15057 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15057 : row15057 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15057 := by decide +kernel

theorem rowEval15057 (x : Key → ℝ) : Integer.Sparse.eval row15057 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15057, Integer.Sparse.eval_collectBalanced, rawRowCheck15057]

def rawRow15058 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2520, -2), (key2561, 6), (key2364, -2), (key2361, -2), (key2364, -2), (key2459, 2), (key2456, 2), (key2520, 2), (key2456, 2), (key2520, 2), (key2459, 2), (key2531, -2), (key2561, -2), (key2531, -2), (key2361, 6), (key2456, -2), (key2517, -2), (key2456, -2)]

theorem rawRowCheck15058 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form8 = rawRow15058 := by decide +kernel

def row15058 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15058 : row15058 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15058 := by decide +kernel

theorem rowEval15058 (x : Key → ℝ) : Integer.Sparse.eval row15058 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15058, Integer.Sparse.eval_collectBalanced, rawRowCheck15058]

def rawRow15059 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2517, -2), (key2561, 6), (key2364, -2), (key2364, -2), (key2361, -2), (key2520, 2), (key2520, 2), (key2459, 2), (key2459, 2), (key2456, 2), (key2456, 2), (key2561, -2), (key2531, -2), (key2531, -2), (key2361, 6), (key2517, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck15059 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form8 = rawRow15059 := by decide +kernel

def row15059 : Integer.Sparse Key := [(key2361, 4), (key2364, -4), (key2459, 4), (key2517, -4), (key2531, -4), (key2561, 4)]

theorem rowCheck15059 : row15059 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15059 := by decide +kernel

theorem rowEval15059 (x : Key → ℝ) : Integer.Sparse.eval row15059 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15059, Integer.Sparse.eval_collectBalanced, rawRowCheck15059]

def rawRow15060 : Integer.Sparse Key := [(key2517, -2), (key2520, -2), (key2561, -2), (key2520, 6), (key2456, -2), (key2459, -2), (key2531, -2), (key2361, 2), (key2364, 2), (key2456, 2), (key2520, 2), (key2531, 2), (key2561, 2), (key2364, -2), (key2459, -2), (key2520, -2), (key2456, 6), (key2361, -2), (key2456, -2), (key2517, -2)]

theorem rawRowCheck15060 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form8 = rawRow15060 := by decide +kernel

def row15060 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15060 : row15060 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15060 := by decide +kernel

theorem rowEval15060 (x : Key → ℝ) : Integer.Sparse.eval row15060 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15060, Integer.Sparse.eval_collectBalanced, rawRowCheck15060]

def rawRow15061 : Integer.Sparse Key := [(key2520, -2), (key2517, -2), (key2561, -2), (key2520, 6), (key2459, -2), (key2456, -2), (key2531, -2), (key2364, 2), (key2361, 2), (key2520, 2), (key2456, 2), (key2561, 2), (key2531, 2), (key2364, -2), (key2520, -2), (key2459, -2), (key2456, 6), (key2361, -2), (key2517, -2), (key2456, -2)]

theorem rawRowCheck15061 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form8 = rawRow15061 := by decide +kernel

def row15061 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15061 : row15061 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15061 := by decide +kernel

theorem rowEval15061 (x : Key → ℝ) : Integer.Sparse.eval row15061 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15061, Integer.Sparse.eval_collectBalanced, rawRowCheck15061]

def rawRow15062 : Integer.Sparse Key := [(key2517, -2), (key2561, -2), (key2520, -2), (key2520, 6), (key2456, -2), (key2531, -2), (key2459, -2), (key2456, 2), (key2531, 2), (key2361, 2), (key2561, 2), (key2364, 2), (key2520, 2), (key2459, -2), (key2364, -2), (key2520, -2), (key2456, 6), (key2456, -2), (key2361, -2), (key2517, -2)]

theorem rawRowCheck15062 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form8 = rawRow15062 := by decide +kernel

def row15062 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15062 : row15062 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15062 := by decide +kernel

theorem rowEval15062 (x : Key → ℝ) : Integer.Sparse.eval row15062 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form8) x := by
  rw [rowCheck15062, Integer.Sparse.eval_collectBalanced, rawRowCheck15062]

def rawRow15063 : Integer.Sparse Key := [(key2561, -2), (key2517, -2), (key2520, -2), (key2520, 6), (key2531, -2), (key2456, -2), (key2459, -2), (key2531, 2), (key2456, 2), (key2561, 2), (key2361, 2), (key2520, 2), (key2364, 2), (key2459, -2), (key2520, -2), (key2364, -2), (key2456, 6), (key2456, -2), (key2517, -2), (key2361, -2)]

theorem rawRowCheck15063 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form8 = rawRow15063 := by decide +kernel

def row15063 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15063 : row15063 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15063 := by decide +kernel

theorem rowEval15063 (x : Key → ℝ) : Integer.Sparse.eval row15063 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck15063, Integer.Sparse.eval_collectBalanced, rawRowCheck15063]

def rawRow15064 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2517, -2), (key2520, 6), (key2459, -2), (key2531, -2), (key2456, -2), (key2520, 2), (key2561, 2), (key2364, 2), (key2531, 2), (key2361, 2), (key2456, 2), (key2520, -2), (key2364, -2), (key2459, -2), (key2456, 6), (key2517, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck15064 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form8 = rawRow15064 := by decide +kernel

def row15064 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15064 : row15064 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15064 := by decide +kernel

theorem rowEval15064 (x : Key → ℝ) : Integer.Sparse.eval row15064 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15064, Integer.Sparse.eval_collectBalanced, rawRowCheck15064]

def rawRow15065 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2517, -2), (key2520, 6), (key2531, -2), (key2459, -2), (key2456, -2), (key2561, 2), (key2520, 2), (key2531, 2), (key2364, 2), (key2456, 2), (key2361, 2), (key2520, -2), (key2459, -2), (key2364, -2), (key2456, 6), (key2517, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck15065 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form8 = rawRow15065 := by decide +kernel

def row15065 : Integer.Sparse Key := [(key2456, 4), (key2459, -4), (key2517, -4), (key2520, 4)]

theorem rowCheck15065 : row15065 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15065 := by decide +kernel

theorem rowEval15065 (x : Key → ℝ) : Integer.Sparse.eval row15065 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck15065, Integer.Sparse.eval_collectBalanced, rawRowCheck15065]

def rawRow15066 : Integer.Sparse Key := [(key2520, -2), (key2520, -2), (key2561, -2), (key2517, 6), (key2520, -2), (key2520, -2), (key2561, -2), (key2364, 2), (key2364, 2), (key2459, 2), (key2459, 2), (key2531, 2), (key2531, 2), (key2361, -2), (key2456, -2), (key2456, -2), (key2517, 6), (key2361, -2), (key2456, -2), (key2456, -2)]

theorem rawRowCheck15066 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form8 = rawRow15066 := by decide +kernel

def row15066 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

theorem rowCheck15066 : row15066 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15066 := by decide +kernel

theorem rowEval15066 (x : Key → ℝ) : Integer.Sparse.eval row15066 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15066, Integer.Sparse.eval_collectBalanced, rawRowCheck15066]

def rawRow15067 : Integer.Sparse Key := [(key2520, -2), (key2561, -2), (key2520, -2), (key2517, 6), (key2520, -2), (key2561, -2), (key2520, -2), (key2459, 2), (key2531, 2), (key2364, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2456, -2), (key2361, -2), (key2456, -2), (key2517, 6), (key2456, -2), (key2361, -2), (key2456, -2)]

theorem rawRowCheck15067 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form8 = rawRow15067 := by decide +kernel

def row15067 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

theorem rowCheck15067 : row15067 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15067 := by decide +kernel

theorem rowEval15067 (x : Key → ℝ) : Integer.Sparse.eval row15067 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form8) x := by
  rw [rowCheck15067, Integer.Sparse.eval_collectBalanced, rawRowCheck15067]

def rawRow15068 : Integer.Sparse Key := [(key2561, -2), (key2520, -2), (key2520, -2), (key2517, 6), (key2561, -2), (key2520, -2), (key2520, -2), (key2531, 2), (key2459, 2), (key2531, 2), (key2364, 2), (key2459, 2), (key2364, 2), (key2456, -2), (key2456, -2), (key2361, -2), (key2517, 6), (key2456, -2), (key2456, -2), (key2361, -2)]

theorem rawRowCheck15068 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form8 = rawRow15068 := by decide +kernel

def row15068 : Integer.Sparse Key := [(key2361, -4), (key2364, 4), (key2456, -8), (key2459, 4), (key2517, 12), (key2520, -8), (key2531, 4), (key2561, -4)]

theorem rowCheck15068 : row15068 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15068 := by decide +kernel

theorem rowEval15068 (x : Key → ℝ) : Integer.Sparse.eval row15068 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form8) x := by
  rw [rowCheck15068, Integer.Sparse.eval_collectBalanced, rawRowCheck15068]

def rawRow15069 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key2217, -4), (key2261, -4), (key2261, 12)]

theorem rawRowCheck15069 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form9 = rawRow15069 := by decide +kernel

def row15069 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15069 : row15069 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15069 := by decide +kernel

theorem rowEval15069 (x : Key → ℝ) : Integer.Sparse.eval row15069 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15069, Integer.Sparse.eval_collectBalanced, rawRowCheck15069]

def rawRow15070 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key1980, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2217, -4), (key2261, 12)]

theorem rawRowCheck15070 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form9 = rawRow15070 := by decide +kernel

def row15070 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15070 : row15070 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15070 := by decide +kernel

theorem rowEval15070 (x : Key → ℝ) : Integer.Sparse.eval row15070 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15070, Integer.Sparse.eval_collectBalanced, rawRowCheck15070]

def rawRow15071 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2217, -4), (key2261, 12)]

theorem rawRowCheck15071 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form9 = rawRow15071 := by decide +kernel

def row15071 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15071 : row15071 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15071 := by decide +kernel

theorem rowEval15071 (x : Key → ℝ) : Integer.Sparse.eval row15071 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15071, Integer.Sparse.eval_collectBalanced, rawRowCheck15071]

def rawRow15072 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key2261, -4), (key2261, -4), (key2217, 12)]

theorem rawRowCheck15072 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form9 = rawRow15072 := by decide +kernel

def row15072 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15072 : row15072 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15072 := by decide +kernel

theorem rowEval15072 (x : Key → ℝ) : Integer.Sparse.eval row15072 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15072, Integer.Sparse.eval_collectBalanced, rawRowCheck15072]

def rawRow15073 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key1980, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key2217, -4), (key2261, -4), (key2217, 12)]

theorem rawRowCheck15073 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form9 = rawRow15073 := by decide +kernel

def row15073 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15073 : row15073 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15073 := by decide +kernel

theorem rowEval15073 (x : Key → ℝ) : Integer.Sparse.eval row15073 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15073, Integer.Sparse.eval_collectBalanced, rawRowCheck15073]

def rawRow15074 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key1980, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key2261, -4), (key2217, -4), (key2217, 12)]

theorem rawRowCheck15074 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form9 = rawRow15074 := by decide +kernel

def row15074 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15074 : row15074 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15074 := by decide +kernel

theorem rowEval15074 (x : Key → ℝ) : Integer.Sparse.eval row15074 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15074, Integer.Sparse.eval_collectBalanced, rawRowCheck15074]

def rawRow15075 : Integer.Sparse Key := [(key1975, 4), (key1980, 4), (key1980, 4), (key2217, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key1996, -4), (key2261, 12)]

theorem rawRowCheck15075 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form9 = rawRow15075 := by decide +kernel

def row15075 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15075 : row15075 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15075 := by decide +kernel

theorem rowEval15075 (x : Key → ℝ) : Integer.Sparse.eval row15075 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15075, Integer.Sparse.eval_collectBalanced, rawRowCheck15075]

def rawRow15076 : Integer.Sparse Key := [(key1980, 4), (key1975, 4), (key1980, 4), (key2217, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key1980, -4), (key2261, 12)]

theorem rawRowCheck15076 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form9 = rawRow15076 := by decide +kernel

def row15076 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15076 : row15076 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15076 := by decide +kernel

theorem rowEval15076 (x : Key → ℝ) : Integer.Sparse.eval row15076 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15076, Integer.Sparse.eval_collectBalanced, rawRowCheck15076]

def rawRow15077 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1975, 4), (key2261, -4), (key2217, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key1980, -4), (key2261, 12)]

theorem rawRowCheck15077 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form9 = rawRow15077 := by decide +kernel

def row15077 : Integer.Sparse Key := [(key1975, 4), (key1996, -4), (key2217, -8), (key2261, 8)]

theorem rowCheck15077 : row15077 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15077 := by decide +kernel

theorem rowEval15077 (x : Key → ℝ) : Integer.Sparse.eval row15077 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15077, Integer.Sparse.eval_collectBalanced, rawRowCheck15077]

def rawRow15078 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1996, -4), (key2261, -4), (key1980, 12)]

theorem rawRowCheck15078 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form9 = rawRow15078 := by decide +kernel

def row15078 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15078 : row15078 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15078 := by decide +kernel

theorem rowEval15078 (x : Key → ℝ) : Integer.Sparse.eval row15078 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15078, Integer.Sparse.eval_collectBalanced, rawRowCheck15078]

def rawRow15079 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1980, -4), (key1975, -4), (key2217, -4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, 12)]

theorem rawRowCheck15079 : GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form9 = rawRow15079 := by decide +kernel

def row15079 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15079 : row15079 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15079 := by decide +kernel

theorem rowEval15079 (x : Key → ℝ) : Integer.Sparse.eval row15079 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, -3, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15079, Integer.Sparse.eval_collectBalanced, rawRowCheck15079]

def rawRow15080 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2261, -4), (key1996, -4), (key1980, 12)]

theorem rawRowCheck15080 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form9 = rawRow15080 := by decide +kernel

def row15080 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15080 : row15080 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15080 := by decide +kernel

theorem rowEval15080 (x : Key → ℝ) : Integer.Sparse.eval row15080 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, -3, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15080, Integer.Sparse.eval_collectBalanced, rawRowCheck15080]

def rawRow15081 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2217, -4), (key1975, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1996, -4), (key1980, 12)]

theorem rawRowCheck15081 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form9 = rawRow15081 := by decide +kernel

def row15081 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15081 : row15081 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15081 := by decide +kernel

theorem rowEval15081 (x : Key → ℝ) : Integer.Sparse.eval row15081 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 0, 1, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15081, Integer.Sparse.eval_collectBalanced, rawRowCheck15081]

def rawRow15082 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1980, -4), (key2217, -4), (key1975, -4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, 12)]

theorem rawRowCheck15082 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form9 = rawRow15082 := by decide +kernel

def row15082 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15082 : row15082 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15082 := by decide +kernel

theorem rowEval15082 (x : Key → ℝ) : Integer.Sparse.eval row15082 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15082, Integer.Sparse.eval_collectBalanced, rawRowCheck15082]

def rawRow15083 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2217, -4), (key1980, -4), (key1975, -4), (key2261, -4), (key1996, -4), (key1980, -4), (key1980, 12)]

theorem rawRowCheck15083 : GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form9 = rawRow15083 := by decide +kernel

def row15083 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15083 : row15083 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15083 := by decide +kernel

theorem rowEval15083 (x : Key → ℝ) : Integer.Sparse.eval row15083 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, 1, 1, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15083, Integer.Sparse.eval_collectBalanced, rawRowCheck15083]

def rawRow15084 : Integer.Sparse Key := [(key1980, 4), (key1980, 4), (key1996, 4), (key2217, -4), (key2261, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key1980, -4), (key2217, 12)]

theorem rawRowCheck15084 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form9 = rawRow15084 := by decide +kernel

def row15084 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15084 : row15084 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15084 := by decide +kernel

theorem rowEval15084 (x : Key → ℝ) : Integer.Sparse.eval row15084 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15084, Integer.Sparse.eval_collectBalanced, rawRowCheck15084]

def rawRow15085 : Integer.Sparse Key := [(key1980, 4), (key1996, 4), (key1980, 4), (key2261, -4), (key2217, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key1980, -4), (key2217, 12)]

theorem rawRowCheck15085 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form9 = rawRow15085 := by decide +kernel

def row15085 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15085 : row15085 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15085 := by decide +kernel

theorem rowEval15085 (x : Key → ℝ) : Integer.Sparse.eval row15085 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 0, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15085, Integer.Sparse.eval_collectBalanced, rawRowCheck15085]

def rawRow15086 : Integer.Sparse Key := [(key1996, 4), (key1980, 4), (key1980, 4), (key2261, -4), (key2261, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, -4), (key2217, 12)]

theorem rawRowCheck15086 : GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form9 = rawRow15086 := by decide +kernel

def row15086 : Integer.Sparse Key := [(key1975, -4), (key1996, 4), (key2217, 8), (key2261, -8)]

theorem rowCheck15086 : row15086 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15086 := by decide +kernel

theorem rowEval15086 (x : Key → ℝ) : Integer.Sparse.eval row15086 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, -3, 1, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15086, Integer.Sparse.eval_collectBalanced, rawRowCheck15086]

def rawRow15087 : Integer.Sparse Key := [(key1980, 4), (key2217, 4), (key2261, 4), (key1980, -4), (key1996, -4), (key2261, -4), (key1975, -4), (key1980, -4), (key2217, -4), (key1980, 12)]

theorem rawRowCheck15087 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form9 = rawRow15087 := by decide +kernel

def row15087 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15087 : row15087 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15087 := by decide +kernel

theorem rowEval15087 (x : Key → ℝ) : Integer.Sparse.eval row15087 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 0, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15087, Integer.Sparse.eval_collectBalanced, rawRowCheck15087]

def rawRow15088 : Integer.Sparse Key := [(key1980, 4), (key2261, 4), (key2217, 4), (key1996, -4), (key1980, -4), (key2261, -4), (key1980, -4), (key1975, -4), (key2217, -4), (key1980, 12)]

theorem rawRowCheck15088 : GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form9 = rawRow15088 := by decide +kernel

def row15088 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15088 : row15088 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15088 := by decide +kernel

theorem rowEval15088 (x : Key → ℝ) : Integer.Sparse.eval row15088 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, -3, 1, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15088, Integer.Sparse.eval_collectBalanced, rawRowCheck15088]

def rawRow15089 : Integer.Sparse Key := [(key2217, 4), (key1980, 4), (key2261, 4), (key1980, -4), (key2261, -4), (key1996, -4), (key1975, -4), (key2217, -4), (key1980, -4), (key1980, 12)]

theorem rawRowCheck15089 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form9 = rawRow15089 := by decide +kernel

def row15089 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15089 : row15089 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15089 := by decide +kernel

theorem rowEval15089 (x : Key → ℝ) : Integer.Sparse.eval row15089 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, -3, 1] GramFunctions.Block4.form9) x := by
  rw [rowCheck15089, Integer.Sparse.eval_collectBalanced, rawRowCheck15089]

def rawRow15090 : Integer.Sparse Key := [(key2217, 4), (key2261, 4), (key1980, 4), (key2261, -4), (key1980, -4), (key1996, -4), (key2217, -4), (key1975, -4), (key1980, -4), (key1980, 12)]

theorem rawRowCheck15090 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form9 = rawRow15090 := by decide +kernel

def row15090 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15090 : row15090 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15090 := by decide +kernel

theorem rowEval15090 (x : Key → ℝ) : Integer.Sparse.eval row15090 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 0, 1, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15090, Integer.Sparse.eval_collectBalanced, rawRowCheck15090]

def rawRow15091 : Integer.Sparse Key := [(key2261, 4), (key1980, 4), (key2217, 4), (key1996, -4), (key2261, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, -4), (key1980, 12)]

theorem rawRowCheck15091 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form9 = rawRow15091 := by decide +kernel

def row15091 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15091 : row15091 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15091 := by decide +kernel

theorem rowEval15091 (x : Key → ℝ) : Integer.Sparse.eval row15091 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15091, Integer.Sparse.eval_collectBalanced, rawRowCheck15091]

def rawRow15092 : Integer.Sparse Key := [(key2261, 4), (key2217, 4), (key1980, 4), (key2261, -4), (key1996, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, -4), (key1980, 12)]

theorem rawRowCheck15092 : GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form9 = rawRow15092 := by decide +kernel

def row15092 : Integer.Sparse Key := [(key1975, -4), (key1980, 8), (key1996, -4)]

theorem rowCheck15092 : row15092 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15092 := by decide +kernel

theorem rowEval15092 (x : Key → ℝ) : Integer.Sparse.eval row15092 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 0, 1, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15092, Integer.Sparse.eval_collectBalanced, rawRowCheck15092]

def rawRow15093 : Integer.Sparse Key := [(key1996, 4), (key2261, 4), (key2261, 4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1975, 12)]

theorem rawRowCheck15093 : GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form9 = rawRow15093 := by decide +kernel

def row15093 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

theorem rowCheck15093 : row15093 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15093 := by decide +kernel

theorem rowEval15093 (x : Key → ℝ) : Integer.Sparse.eval row15093 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, -3, 0, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15093, Integer.Sparse.eval_collectBalanced, rawRowCheck15093]

def rawRow15094 : Integer.Sparse Key := [(key2261, 4), (key1996, 4), (key2261, 4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1975, 12)]

theorem rawRowCheck15094 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form9 = rawRow15094 := by decide +kernel

def row15094 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

theorem rowCheck15094 : row15094 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15094 := by decide +kernel

theorem rowEval15094 (x : Key → ℝ) : Integer.Sparse.eval row15094 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, -3, 0] GramFunctions.Block4.form9) x := by
  rw [rowCheck15094, Integer.Sparse.eval_collectBalanced, rawRowCheck15094]

def rawRow15095 : Integer.Sparse Key := [(key2261, 4), (key2261, 4), (key1996, 4), (key2217, -4), (key1980, -4), (key1980, -4), (key2217, -4), (key1980, -4), (key1980, -4), (key1975, 12)]

theorem rawRowCheck15095 : GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form9 = rawRow15095 := by decide +kernel

def row15095 : Integer.Sparse Key := [(key1975, 12), (key1980, -16), (key1996, 4), (key2217, -8), (key2261, 8)]

theorem rowCheck15095 : row15095 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15095 := by decide +kernel

theorem rowEval15095 (x : Key → ℝ) : Integer.Sparse.eval row15095 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 1, 1, 0, 0, -3] GramFunctions.Block4.form9) x := by
  rw [rowCheck15095, Integer.Sparse.eval_collectBalanced, rawRowCheck15095]

def rawRow15096 : Integer.Sparse Key := [(key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1)]

theorem rawRowCheck15096 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form10 = rawRow15096 := by decide +kernel

def row15096 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15096 : row15096 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15096 := by decide +kernel

theorem rowEval15096 (x : Key → ℝ) : Integer.Sparse.eval row15096 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 0, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15096, Integer.Sparse.eval_collectBalanced, rawRowCheck15096]

def rawRow15097 : Integer.Sparse Key := [(key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1)]

theorem rawRowCheck15097 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form10 = rawRow15097 := by decide +kernel

def row15097 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15097 : row15097 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15097 := by decide +kernel

theorem rowEval15097 (x : Key → ℝ) : Integer.Sparse.eval row15097 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15097, Integer.Sparse.eval_collectBalanced, rawRowCheck15097]

def rawRow15098 : Integer.Sparse Key := [(key2440, -1), (key2437, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2406, -1), (key2440, 2), (key2440, 2), (key2409, 2), (key2506, -1), (key2503, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2522, 2), (key2503, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2480, 2), (key2522, -1), (key2506, -1), (key2522, -1), (key2482, -1), (key2506, -1), (key2482, -1), (key2554, 2), (key2554, 2), (key2538, 2), (key2563, -1), (key2554, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2543, -1)]

theorem rawRowCheck15098 : GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form10 = rawRow15098 := by decide +kernel

def row15098 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15098 : row15098 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15098 := by decide +kernel

theorem rowEval15098 (x : Key → ℝ) : Integer.Sparse.eval row15098 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 0, 1, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15098, Integer.Sparse.eval_collectBalanced, rawRowCheck15098]

def rawRow15099 : Integer.Sparse Key := [(key2406, -1), (key2409, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2440, -1), (key2406, 2), (key2406, 2), (key2437, 2), (key2480, -1), (key2482, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2472, 2), (key2482, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2506, 2), (key2472, -1), (key2480, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2503, -1), (key2543, 2), (key2543, 2), (key2563, 2), (key2538, -1), (key2543, -1), (key2538, -1), (key2554, -1), (key2543, -1), (key2554, -1)]

theorem rawRowCheck15099 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form10 = rawRow15099 := by decide +kernel

def row15099 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15099 : row15099 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15099 := by decide +kernel

theorem rowEval15099 (x : Key → ℝ) : Integer.Sparse.eval row15099 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15099, Integer.Sparse.eval_collectBalanced, rawRowCheck15099]

def rawRow15100 : Integer.Sparse Key := [(key2409, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2409, -1), (key2406, 2), (key2437, 2), (key2406, 2), (key2482, -1), (key2480, -1), (key2522, -1), (key2480, -1), (key2522, -1), (key2482, -1), (key2482, 2), (key2472, 2), (key2506, 2), (key2472, 2), (key2506, 2), (key2482, 2), (key2480, -1), (key2472, -1), (key2503, -1), (key2472, -1), (key2503, -1), (key2480, -1), (key2543, 2), (key2563, 2), (key2543, 2), (key2543, -1), (key2538, -1), (key2554, -1), (key2538, -1), (key2554, -1), (key2543, -1)]

theorem rawRowCheck15100 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form10 = rawRow15100 := by decide +kernel

def row15100 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15100 : row15100 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15100 := by decide +kernel

theorem rowEval15100 (x : Key → ℝ) : Integer.Sparse.eval row15100 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 0, 1, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15100, Integer.Sparse.eval_collectBalanced, rawRowCheck15100]

def rawRow15101 : Integer.Sparse Key := [(key2440, -1), (key2440, -1), (key2409, -1), (key2409, -1), (key2406, -1), (key2406, -1), (key2437, 2), (key2406, 2), (key2406, 2), (key2522, -1), (key2522, -1), (key2482, -1), (key2482, -1), (key2480, -1), (key2480, -1), (key2506, 2), (key2506, 2), (key2482, 2), (key2482, 2), (key2472, 2), (key2472, 2), (key2503, -1), (key2503, -1), (key2480, -1), (key2480, -1), (key2472, -1), (key2472, -1), (key2563, 2), (key2543, 2), (key2543, 2), (key2554, -1), (key2554, -1), (key2543, -1), (key2543, -1), (key2538, -1), (key2538, -1)]

theorem rawRowCheck15101 : GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form10 = rawRow15101 := by decide +kernel

def row15101 : Integer.Sparse Key := [(key2406, 2), (key2409, -2), (key2437, 2), (key2440, -2), (key2472, 2), (key2480, -4), (key2482, 2), (key2503, -2), (key2506, 4), (key2522, -2), (key2538, -2), (key2543, 2), (key2554, -2), (key2563, 2)]

theorem rowCheck15101 : row15101 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15101 := by decide +kernel

theorem rowEval15101 (x : Key → ℝ) : Integer.Sparse.eval row15101 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, -3, 1, 1, 0, 0] GramFunctions.Block4.form10) x := by
  rw [rowCheck15101, Integer.Sparse.eval_collectBalanced, rawRowCheck15101]

def rawRow15102 : Integer.Sparse Key := [(key2472, -1), (key2472, -1), (key2503, -1), (key2503, -1), (key2506, -1), (key2506, -1), (key2538, 2), (key2554, 2), (key2554, 2), (key2406, -1), (key2406, -1), (key2437, -1), (key2437, -1), (key2440, -1), (key2440, -1), (key2480, 2), (key2480, 2), (key2503, 2), (key2503, 2), (key2522, 2), (key2522, 2), (key2543, -1), (key2543, -1), (key2554, -1), (key2554, -1), (key2563, -1), (key2563, -1), (key2409, 2), (key2440, 2), (key2440, 2), (key2482, -1), (key2482, -1), (key2506, -1), (key2506, -1), (key2522, -1), (key2522, -1)]

theorem rawRowCheck15102 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form10 = rawRow15102 := by decide +kernel

def row15102 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15102 : row15102 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15102 := by decide +kernel

theorem rowEval15102 (x : Key → ℝ) : Integer.Sparse.eval row15102 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 0, 1, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15102, Integer.Sparse.eval_collectBalanced, rawRowCheck15102]

def rawRow15103 : Integer.Sparse Key := [(key2503, -1), (key2506, -1), (key2472, -1), (key2506, -1), (key2472, -1), (key2503, -1), (key2554, 2), (key2538, 2), (key2554, 2), (key2437, -1), (key2440, -1), (key2406, -1), (key2440, -1), (key2406, -1), (key2437, -1), (key2503, 2), (key2522, 2), (key2480, 2), (key2522, 2), (key2480, 2), (key2503, 2), (key2554, -1), (key2563, -1), (key2543, -1), (key2563, -1), (key2543, -1), (key2554, -1), (key2440, 2), (key2409, 2), (key2440, 2), (key2506, -1), (key2522, -1), (key2482, -1), (key2522, -1), (key2482, -1), (key2506, -1)]

theorem rawRowCheck15103 : GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form10 = rawRow15103 := by decide +kernel

def row15103 : Integer.Sparse Key := [(key2406, -2), (key2409, 2), (key2437, -2), (key2440, 2), (key2472, -2), (key2480, 4), (key2482, -2), (key2503, 2), (key2506, -4), (key2522, 2), (key2538, 2), (key2543, -2), (key2554, 2), (key2563, -2)]

theorem rowCheck15103 : row15103 =
    Integer.Sparse.collectBalanced GramPolynomial.keyLess rawRow15103 := by decide +kernel

theorem rowEval15103 (x : Key → ℝ) : Integer.Sparse.eval row15103 x =
    Integer.Sparse.eval (GramPolynomial.normalizedRow 1 ![1, 0, -3, 1, 0, 1] GramFunctions.Block4.form10) x := by
  rw [rowCheck15103, Integer.Sparse.eval_collectBalanced, rawRowCheck15103]

end MUB6.Certificate.GramRows

end OAI
