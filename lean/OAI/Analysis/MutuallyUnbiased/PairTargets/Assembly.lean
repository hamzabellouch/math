import OAI.Analysis.MutuallyUnbiased.PairTargets.IntegerTerms
import OAI.Analysis.MutuallyUnbiased.PairSources.Data

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

def integerMerge0 : Integer.Sparse (Fin 909) := [(0, -12410496), (1, -17962560), (2, 4898880), (5, -9797760), (8, -39191040), (24, 39191040), (27, 29393280), (30, 78382080), (68, 58786560), (126, 78382080), (236, 156764160)]

theorem integerMergeCheck0 : integerMerge0 =
    Integer.Sparse.merge integerTerm1 integerTerm2 := by decide +kernel

theorem integerMergeEval0 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge0 x =
      Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck0, Integer.Sparse.eval_merge]

def integerMerge1 : Integer.Sparse (Fin 909) := [(0, 11104128), (1, -27760320), (2, -4898880), (5, 9797760), (8, -39191040), (24, 39191040), (27, -29393280), (30, 78382080), (68, -58786560), (126, 78382080), (236, 156764160)]

theorem integerMergeCheck1 : integerMerge1 =
    Integer.Sparse.merge integerTerm0 integerMerge0 := by decide +kernel

theorem integerMergeEval1 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge1 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck1, Integer.Sparse.eval_merge]
  rw [integerMergeEval0]
  all_goals ring

def integerMerge2 : Integer.Sparse (Fin 909) := [(0, -14696640), (1, -11430720), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 58786560), (126, 39191040), (236, 195955200)]

theorem integerMergeCheck2 : integerMerge2 =
    Integer.Sparse.merge integerTerm4 integerTerm5 := by decide +kernel

theorem integerMergeEval2 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge2 x =
      Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck2, Integer.Sparse.eval_merge]

def integerMerge3 : Integer.Sparse (Fin 909) := [(0, -20248704), (1, -6531840), (2, -3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 78382080), (126, 78382080), (236, 235146240)]

theorem integerMergeCheck3 : integerMerge3 =
    Integer.Sparse.merge integerTerm3 integerMerge2 := by decide +kernel

theorem integerMergeEval3 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge3 x =
      Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck3, Integer.Sparse.eval_merge]
  rw [integerMergeEval2]
  all_goals ring

def integerMerge4 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -34292160), (2, -8164800), (5, 3265920), (8, -65318400), (24, 39191040), (27, -9797760), (30, 156764160), (68, 19595520), (126, 156764160), (236, 391910400)]

theorem integerMergeCheck4 : integerMerge4 =
    Integer.Sparse.merge integerMerge1 integerMerge3 := by decide +kernel

theorem integerMergeEval4 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge4 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck4, Integer.Sparse.eval_merge]
  rw [integerMergeEval1, integerMergeEval3]
  all_goals ring

def integerMerge5 : Integer.Sparse (Fin 909) := [(0, -5878656), (1, -544320), (2, 544320), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -13063680), (126, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

theorem integerMergeCheck5 : integerMerge5 =
    Integer.Sparse.merge integerTerm7 integerTerm8 := by decide +kernel

theorem integerMergeEval5 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge5 x =
      Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck5, Integer.Sparse.eval_merge]

def integerMerge6 : Integer.Sparse (Fin 909) := [(0, 8055936), (1, 21228480), (2, -3810240), (5, 3265920), (8, 26127360), (20, -39191040), (24, -13063680), (27, -9797760), (28, -78382080), (30, -26127360), (68, -26127360), (126, -39191040), (208, -117573120), (236, -169827840), (253, -195955200)]

theorem integerMergeCheck6 : integerMerge6 =
    Integer.Sparse.merge integerTerm6 integerMerge5 := by decide +kernel

theorem integerMergeEval6 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge6 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck6, Integer.Sparse.eval_merge]
  rw [integerMergeEval5]
  all_goals ring

def integerMerge7 : Integer.Sparse (Fin 909) := [(0, -6749568), (1, -2177280), (2, 1088640), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 13063680), (126, 65318400), (208, -39191040), (236, -39191040), (253, -39191040)]

theorem integerMergeCheck7 : integerMerge7 =
    Integer.Sparse.merge integerTerm9 integerTerm10 := by decide +kernel

theorem integerMergeEval7 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge7 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x := by
  rw [integerMergeCheck7, Integer.Sparse.eval_merge]

def integerMerge8 : Integer.Sparse (Fin 909) := [(0, 1251936), (1, -3538080), (2, -544320), (3, 8709120), (4, 8709120), (5, 1632960), (8, 13063680), (12, 4354560), (17, -19595520), (20, -39191040), (24, -26127360), (27, -4898880), (30, 6531840), (68, -9797760), (126, -52254720), (203, -39191040), (208, -78382080), (236, -26127360)]

theorem integerMergeCheck8 : integerMerge8 =
    Integer.Sparse.merge integerTerm11 integerTerm12 := by decide +kernel

theorem integerMergeEval8 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge8 x =
      Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck8, Integer.Sparse.eval_merge]

def integerMerge9 : Integer.Sparse (Fin 909) := [(0, -5497632), (1, -5715360), (2, 544320), (3, 8709120), (4, 8709120), (5, -1632960), (12, 4354560), (17, -19595520), (20, -39191040), (24, 13063680), (27, 4898880), (30, 6531840), (68, 3265920), (126, 13063680), (203, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

theorem integerMergeCheck9 : integerMerge9 =
    Integer.Sparse.merge integerMerge7 integerMerge8 := by decide +kernel

theorem integerMergeEval9 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge9 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck9, Integer.Sparse.eval_merge]
  rw [integerMergeEval7, integerMergeEval8]
  all_goals ring

def integerMerge10 : Integer.Sparse (Fin 909) := [(0, 2558304), (1, 15513120), (2, -3265920), (3, 8709120), (4, 8709120), (5, 1632960), (8, 26127360), (12, 4354560), (17, -19595520), (20, -78382080), (27, -4898880), (28, -78382080), (30, -19595520), (68, -22861440), (126, -26127360), (203, -39191040), (208, -235146240), (236, -235146240), (253, -235146240)]

theorem integerMergeCheck10 : integerMerge10 =
    Integer.Sparse.merge integerMerge6 integerMerge9 := by decide +kernel

theorem integerMergeEval10 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge10 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck10, Integer.Sparse.eval_merge]
  rw [integerMergeEval6, integerMergeEval9]
  all_goals ring

def integerMerge11 : Integer.Sparse (Fin 909) := [(0, -6586272), (1, -18779040), (2, -11430720), (3, 8709120), (4, 8709120), (5, 4898880), (8, -39191040), (12, 4354560), (17, -19595520), (20, -78382080), (24, 39191040), (27, -14696640), (28, -78382080), (30, 137168640), (68, -3265920), (126, 130636800), (203, -39191040), (208, -235146240), (236, 156764160), (253, -235146240)]

theorem integerMergeCheck11 : integerMerge11 =
    Integer.Sparse.merge integerMerge4 integerMerge10 := by decide +kernel

theorem integerMergeEval11 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge11 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck11, Integer.Sparse.eval_merge]
  rw [integerMergeEval4, integerMergeEval10]
  all_goals ring

def integerMerge12 : Integer.Sparse (Fin 909) := [(0, -5143824), (1, 3674160), (2, -2993760), (4, 2177280), (31, -6531840), (68, 16329600), (126, 19595520), (207, -19595520), (208, -19595520), (236, 32659200)]

theorem integerMergeCheck12 : integerMerge12 =
    Integer.Sparse.merge integerTerm14 integerTerm15 := by decide +kernel

theorem integerMergeEval12 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge12 x =
      Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck12, Integer.Sparse.eval_merge]

def integerMerge13 : Integer.Sparse (Fin 909) := [(0, -4735584), (1, 2449440), (2, -2721600), (4, 4354560), (31, -13063680), (68, 13063680), (207, -39191040), (208, -39191040), (236, 26127360)]

theorem integerMergeCheck13 : integerMerge13 =
    Integer.Sparse.merge integerTerm13 integerMerge12 := by decide +kernel

theorem integerMergeEval13 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge13 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck13, Integer.Sparse.eval_merge]
  rw [integerMergeEval12]
  all_goals ring

def integerMerge14 : Integer.Sparse (Fin 909) := [(0, 6477408), (1, -6804000), (2, 3810240), (3, 4354560), (4, 6531840), (31, -6531840), (68, -6531840), (126, -32659200), (203, -19595520), (207, -19595520), (208, -19595520), (236, -19595520), (253, -19595520)]

theorem integerMergeCheck14 : integerMerge14 =
    Integer.Sparse.merge integerTerm17 integerTerm18 := by decide +kernel

theorem integerMergeEval14 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge14 x =
      Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck14, Integer.Sparse.eval_merge]

def integerMerge15 : Integer.Sparse (Fin 909) := [(0, 2993760), (1, -7348320), (2, 3265920), (3, 4354560), (4, 6531840), (31, -6531840), (68, -13063680), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -58786560), (253, -58786560)]

theorem integerMergeCheck15 : integerMerge15 =
    Integer.Sparse.merge integerTerm16 integerMerge14 := by decide +kernel

theorem integerMergeEval15 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge15 x =
      Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck15, Integer.Sparse.eval_merge]
  rw [integerMergeEval14]
  all_goals ring

def integerMerge16 : Integer.Sparse (Fin 909) := [(0, -1741824), (1, -4898880), (2, 544320), (3, 4354560), (4, 10886400), (31, -19595520), (126, -45722880), (203, -19595520), (207, -58786560), (208, -97977600), (236, -32659200), (253, -58786560)]

theorem integerMergeCheck16 : integerMerge16 =
    Integer.Sparse.merge integerMerge13 integerMerge15 := by decide +kernel

theorem integerMergeEval16 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge16 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck16, Integer.Sparse.eval_merge]
  rw [integerMergeEval13, integerMergeEval15]
  all_goals ring

def integerMerge17 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, 4354560), (2, -3810240), (68, 13063680), (126, 26127360), (208, -39191040), (253, -39191040)]

theorem integerMergeCheck17 : integerMerge17 =
    Integer.Sparse.merge integerTerm20 integerTerm21 := by decide +kernel

theorem integerMergeEval17 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge17 x =
      Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck17, Integer.Sparse.eval_merge]

def integerMerge18 : Integer.Sparse (Fin 909) := [(0, -7947072), (1, 2721600), (2, -3265920), (68, 9797760), (126, 13063680), (208, -78382080), (236, -13063680), (253, -39191040)]

theorem integerMergeCheck18 : integerMerge18 =
    Integer.Sparse.merge integerTerm19 integerMerge17 := by decide +kernel

theorem integerMergeEval18 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge18 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck18, Integer.Sparse.eval_merge]
  rw [integerMergeEval17]
  all_goals ring

def integerMerge19 : Integer.Sparse (Fin 909) := [(0, 1496880), (1, -2857680), (2, 816480), (4, 2177280), (31, -6531840), (68, -6531840), (126, -32659200), (207, -19595520), (208, -58786560), (236, -19595520)]

theorem integerMergeCheck19 : integerMerge19 =
    Integer.Sparse.merge integerTerm22 integerTerm23 := by decide +kernel

theorem integerMergeEval19 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge19 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x := by
  rw [integerMergeCheck19, Integer.Sparse.eval_merge]

def integerMerge20 : Integer.Sparse (Fin 909) := [(0, 5742576), (1, -12292560), (2, 4762800), (3, -4354560), (4, 4354560), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (58, 45360), (68, -2177280), (69, -2903040), (126, -13063680), (203, -19595520), (230, 6531840), (236, -13063680), (253, -19595520)]

theorem integerMergeCheck20 : integerMerge20 =
    Integer.Sparse.merge integerTerm24 integerTerm25 := by decide +kernel

theorem integerMergeEval20 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge20 x =
      Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck20, Integer.Sparse.eval_merge]

def integerMerge21 : Integer.Sparse (Fin 909) := [(0, 7239456), (1, -15150240), (2, 5579280), (3, -4354560), (4, 6531840), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -6531840), (58, 45360), (68, -8709120), (69, -2903040), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (230, 6531840), (236, -32659200), (253, -19595520)]

theorem integerMergeCheck21 : integerMerge21 =
    Integer.Sparse.merge integerMerge19 integerMerge20 := by decide +kernel

theorem integerMergeEval21 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge21 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck21, Integer.Sparse.eval_merge]
  rw [integerMergeEval19, integerMergeEval20]
  all_goals ring

def integerMerge22 : Integer.Sparse (Fin 909) := [(0, -707616), (1, -12428640), (2, 2313360), (3, -4354560), (4, 6531840), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -6531840), (58, 45360), (68, 1088640), (69, -2903040), (126, -32659200), (203, -19595520), (207, -19595520), (208, -137168640), (230, 6531840), (236, -45722880), (253, -58786560)]

theorem integerMergeCheck22 : integerMerge22 =
    Integer.Sparse.merge integerMerge18 integerMerge21 := by decide +kernel

theorem integerMergeEval22 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge22 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck22, Integer.Sparse.eval_merge]
  rw [integerMergeEval18, integerMergeEval21]
  all_goals ring

def integerMerge23 : Integer.Sparse (Fin 909) := [(0, -2449440), (1, -17327520), (2, 2857680), (4, 17418240), (5, -2177280), (6, -181440), (7, -5806080), (12, -5806080), (23, -8709120), (27, -2177280), (31, -26127360), (58, 45360), (68, 1088640), (69, -2903040), (126, -78382080), (203, -39191040), (207, -78382080), (208, -235146240), (230, 6531840), (236, -78382080), (253, -117573120)]

theorem integerMergeCheck23 : integerMerge23 =
    Integer.Sparse.merge integerMerge16 integerMerge22 := by decide +kernel

theorem integerMergeEval23 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge23 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck23, Integer.Sparse.eval_merge]
  rw [integerMergeEval16, integerMergeEval22]
  all_goals ring

def integerMerge24 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, -36106560), (2, -8573040), (3, 8709120), (4, 26127360), (5, 2721600), (6, -181440), (7, -5806080), (8, -39191040), (12, -1451520), (17, -19595520), (20, -78382080), (23, -8709120), (24, 39191040), (27, -16873920), (28, -78382080), (30, 137168640), (31, -26127360), (58, 45360), (68, -2177280), (69, -2903040), (126, 52254720), (203, -78382080), (207, -78382080), (208, -470292480), (230, 6531840), (236, 78382080), (253, -352719360)]

theorem integerMergeCheck24 : integerMerge24 =
    Integer.Sparse.merge integerMerge11 integerMerge23 := by decide +kernel

theorem integerMergeEval24 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge24 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x + Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm25 x := by
  rw [integerMergeCheck24, Integer.Sparse.eval_merge]
  rw [integerMergeEval11, integerMergeEval23]
  all_goals ring

def integerMerge25 : Integer.Sparse (Fin 909) := [(0, -12410496), (1, -17962560), (2, 4898880), (5, -9797760), (8, -39191040), (24, 39191040), (27, 29393280), (30, 78382080), (68, 58786560), (126, 78382080), (236, 156764160)]

theorem integerMergeCheck25 : integerMerge25 =
    Integer.Sparse.merge integerTerm1 integerTerm2 := by decide +kernel

theorem integerMergeEval25 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge25 x =
      Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck25, Integer.Sparse.eval_merge]

def integerMerge26 : Integer.Sparse (Fin 909) := [(0, 11104128), (1, -27760320), (2, -4898880), (5, 9797760), (8, -39191040), (24, 39191040), (27, -29393280), (30, 78382080), (68, -58786560), (126, 78382080), (236, 156764160)]

theorem integerMergeCheck26 : integerMerge26 =
    Integer.Sparse.merge integerTerm0 integerMerge25 := by decide +kernel

theorem integerMergeEval26 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge26 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x := by
  rw [integerMergeCheck26, Integer.Sparse.eval_merge]
  rw [integerMergeEval25]
  all_goals ring

def integerMerge27 : Integer.Sparse (Fin 909) := [(0, -14696640), (1, -11430720), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 58786560), (126, 39191040), (236, 195955200)]

theorem integerMergeCheck27 : integerMerge27 =
    Integer.Sparse.merge integerTerm4 integerTerm5 := by decide +kernel

theorem integerMergeEval27 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge27 x =
      Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck27, Integer.Sparse.eval_merge]

def integerMerge28 : Integer.Sparse (Fin 909) := [(0, -20248704), (1, -6531840), (2, -3265920), (5, -6531840), (8, -26127360), (27, 19595520), (30, 78382080), (68, 78382080), (126, 78382080), (236, 235146240)]

theorem integerMergeCheck28 : integerMerge28 =
    Integer.Sparse.merge integerTerm3 integerMerge27 := by decide +kernel

theorem integerMergeEval28 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge28 x =
      Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck28, Integer.Sparse.eval_merge]
  rw [integerMergeEval27]
  all_goals ring

def integerMerge29 : Integer.Sparse (Fin 909) := [(0, -9144576), (1, -34292160), (2, -8164800), (5, 3265920), (8, -65318400), (24, 39191040), (27, -9797760), (30, 156764160), (68, 19595520), (126, 156764160), (236, 391910400)]

theorem integerMergeCheck29 : integerMerge29 =
    Integer.Sparse.merge integerMerge26 integerMerge28 := by decide +kernel

theorem integerMergeEval29 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge29 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x := by
  rw [integerMergeCheck29, Integer.Sparse.eval_merge]
  rw [integerMergeEval26, integerMergeEval28]
  all_goals ring

def integerMerge30 : Integer.Sparse (Fin 909) := [(0, -5878656), (1, -544320), (2, 544320), (5, 1088640), (8, 8709120), (20, -39191040), (24, -13063680), (27, -3265920), (68, -13063680), (126, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

theorem integerMergeCheck30 : integerMerge30 =
    Integer.Sparse.merge integerTerm7 integerTerm8 := by decide +kernel

theorem integerMergeEval30 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge30 x =
      Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck30, Integer.Sparse.eval_merge]

def integerMerge31 : Integer.Sparse (Fin 909) := [(0, 8055936), (1, 21228480), (2, -3810240), (5, 3265920), (8, 26127360), (20, -39191040), (24, -13063680), (27, -9797760), (28, -78382080), (30, -26127360), (68, -26127360), (126, -39191040), (208, -117573120), (236, -169827840), (253, -195955200)]

theorem integerMergeCheck31 : integerMerge31 =
    Integer.Sparse.merge integerTerm6 integerMerge30 := by decide +kernel

theorem integerMergeEval31 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge31 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x := by
  rw [integerMergeCheck31, Integer.Sparse.eval_merge]
  rw [integerMergeEval30]
  all_goals ring

def integerMerge32 : Integer.Sparse (Fin 909) := [(0, -6749568), (1, -2177280), (2, 1088640), (5, -3265920), (8, -13063680), (24, 39191040), (27, 9797760), (68, 13063680), (126, 65318400), (208, -39191040), (236, -39191040), (253, -39191040)]

theorem integerMergeCheck32 : integerMerge32 =
    Integer.Sparse.merge integerTerm9 integerTerm10 := by decide +kernel

theorem integerMergeEval32 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge32 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x := by
  rw [integerMergeCheck32, Integer.Sparse.eval_merge]

def integerMerge33 : Integer.Sparse (Fin 909) := [(0, 1251936), (1, -3538080), (2, -544320), (3, 8709120), (4, 8709120), (5, 1632960), (8, 13063680), (12, 4354560), (17, -19595520), (20, -39191040), (24, -26127360), (27, -4898880), (30, 6531840), (68, -9797760), (126, -52254720), (203, -39191040), (208, -78382080), (236, -26127360)]

theorem integerMergeCheck33 : integerMerge33 =
    Integer.Sparse.merge integerTerm11 integerTerm12 := by decide +kernel

theorem integerMergeEval33 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge33 x =
      Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck33, Integer.Sparse.eval_merge]

def integerMerge34 : Integer.Sparse (Fin 909) := [(0, -5497632), (1, -5715360), (2, 544320), (3, 8709120), (4, 8709120), (5, -1632960), (12, 4354560), (17, -19595520), (20, -39191040), (24, 13063680), (27, 4898880), (30, 6531840), (68, 3265920), (126, 13063680), (203, -39191040), (208, -117573120), (236, -65318400), (253, -39191040)]

theorem integerMergeCheck34 : integerMerge34 =
    Integer.Sparse.merge integerMerge32 integerMerge33 := by decide +kernel

theorem integerMergeEval34 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge34 x =
      Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck34, Integer.Sparse.eval_merge]
  rw [integerMergeEval32, integerMergeEval33]
  all_goals ring

def integerMerge35 : Integer.Sparse (Fin 909) := [(0, 2558304), (1, 15513120), (2, -3265920), (3, 8709120), (4, 8709120), (5, 1632960), (8, 26127360), (12, 4354560), (17, -19595520), (20, -78382080), (27, -4898880), (28, -78382080), (30, -19595520), (68, -22861440), (126, -26127360), (203, -39191040), (208, -235146240), (236, -235146240), (253, -235146240)]

theorem integerMergeCheck35 : integerMerge35 =
    Integer.Sparse.merge integerMerge31 integerMerge34 := by decide +kernel

theorem integerMergeEval35 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge35 x =
      Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck35, Integer.Sparse.eval_merge]
  rw [integerMergeEval31, integerMergeEval34]
  all_goals ring

def integerMerge36 : Integer.Sparse (Fin 909) := [(0, -6586272), (1, -18779040), (2, -11430720), (3, 8709120), (4, 8709120), (5, 4898880), (8, -39191040), (12, 4354560), (17, -19595520), (20, -78382080), (24, 39191040), (27, -14696640), (28, -78382080), (30, 137168640), (68, -3265920), (126, 130636800), (203, -39191040), (208, -235146240), (236, 156764160), (253, -235146240)]

theorem integerMergeCheck36 : integerMerge36 =
    Integer.Sparse.merge integerMerge29 integerMerge35 := by decide +kernel

theorem integerMergeEval36 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge36 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x := by
  rw [integerMergeCheck36, Integer.Sparse.eval_merge]
  rw [integerMergeEval29, integerMergeEval35]
  all_goals ring

def integerMerge37 : Integer.Sparse (Fin 909) := [(0, -5143824), (1, 3674160), (2, -2993760), (4, 2177280), (31, -6531840), (68, 16329600), (126, 19595520), (207, -19595520), (208, -19595520), (236, 32659200)]

theorem integerMergeCheck37 : integerMerge37 =
    Integer.Sparse.merge integerTerm14 integerTerm15 := by decide +kernel

theorem integerMergeEval37 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge37 x =
      Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck37, Integer.Sparse.eval_merge]

def integerMerge38 : Integer.Sparse (Fin 909) := [(0, -4735584), (1, 2449440), (2, -2721600), (4, 4354560), (31, -13063680), (68, 13063680), (207, -39191040), (208, -39191040), (236, 26127360)]

theorem integerMergeCheck38 : integerMerge38 =
    Integer.Sparse.merge integerTerm13 integerMerge37 := by decide +kernel

theorem integerMergeEval38 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge38 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x := by
  rw [integerMergeCheck38, Integer.Sparse.eval_merge]
  rw [integerMergeEval37]
  all_goals ring

def integerMerge39 : Integer.Sparse (Fin 909) := [(0, 6477408), (1, -6804000), (2, 3810240), (3, 4354560), (4, 6531840), (31, -6531840), (68, -6531840), (126, -32659200), (203, -19595520), (207, -19595520), (208, -19595520), (236, -19595520), (253, -19595520)]

theorem integerMergeCheck39 : integerMerge39 =
    Integer.Sparse.merge integerTerm17 integerTerm18 := by decide +kernel

theorem integerMergeEval39 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge39 x =
      Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck39, Integer.Sparse.eval_merge]

def integerMerge40 : Integer.Sparse (Fin 909) := [(0, 2993760), (1, -7348320), (2, 3265920), (3, 4354560), (4, 6531840), (31, -6531840), (68, -13063680), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -58786560), (253, -58786560)]

theorem integerMergeCheck40 : integerMerge40 =
    Integer.Sparse.merge integerTerm16 integerMerge39 := by decide +kernel

theorem integerMergeEval40 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge40 x =
      Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck40, Integer.Sparse.eval_merge]
  rw [integerMergeEval39]
  all_goals ring

def integerMerge41 : Integer.Sparse (Fin 909) := [(0, -1741824), (1, -4898880), (2, 544320), (3, 4354560), (4, 10886400), (31, -19595520), (126, -45722880), (203, -19595520), (207, -58786560), (208, -97977600), (236, -32659200), (253, -58786560)]

theorem integerMergeCheck41 : integerMerge41 =
    Integer.Sparse.merge integerMerge38 integerMerge40 := by decide +kernel

theorem integerMergeEval41 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge41 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x := by
  rw [integerMergeCheck41, Integer.Sparse.eval_merge]
  rw [integerMergeEval38, integerMergeEval40]
  all_goals ring

def integerMerge42 : Integer.Sparse (Fin 909) := [(0, -9035712), (1, 4354560), (2, -3810240), (68, 13063680), (126, 26127360), (208, -39191040), (253, -39191040)]

theorem integerMergeCheck42 : integerMerge42 =
    Integer.Sparse.merge integerTerm20 integerTerm21 := by decide +kernel

theorem integerMergeEval42 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge42 x =
      Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck42, Integer.Sparse.eval_merge]

def integerMerge43 : Integer.Sparse (Fin 909) := [(0, -7947072), (1, 2721600), (2, -3265920), (68, 9797760), (126, 13063680), (208, -78382080), (236, -13063680), (253, -39191040)]

theorem integerMergeCheck43 : integerMerge43 =
    Integer.Sparse.merge integerTerm19 integerMerge42 := by decide +kernel

theorem integerMergeEval43 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge43 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x := by
  rw [integerMergeCheck43, Integer.Sparse.eval_merge]
  rw [integerMergeEval42]
  all_goals ring

def integerMerge44 : Integer.Sparse (Fin 909) := [(0, 1496880), (1, -2857680), (2, 816480), (4, 2177280), (31, -6531840), (68, -6531840), (126, -32659200), (207, -19595520), (208, -58786560), (236, -19595520)]

theorem integerMergeCheck44 : integerMerge44 =
    Integer.Sparse.merge integerTerm22 integerTerm23 := by decide +kernel

theorem integerMergeEval44 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge44 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x := by
  rw [integerMergeCheck44, Integer.Sparse.eval_merge]

def integerMerge45 : Integer.Sparse (Fin 909) := [(0, 6051024), (1, -11385360), (2, 4082400), (3, 4354560), (4, 4354560), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (35, -5806080), (63, -8709120), (68, -3265920), (126, -13063680), (203, -19595520), (236, -13063680), (253, -19595520)]

theorem integerMergeCheck45 : integerMerge45 =
    Integer.Sparse.merge integerTerm24 integerTerm26 := by decide +kernel

theorem integerMergeEval45 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge45 x =
      Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck45, Integer.Sparse.eval_merge]

def integerMerge46 : Integer.Sparse (Fin 909) := [(0, 7547904), (1, -14243040), (2, 4898880), (3, 4354560), (4, 6531840), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -6531840), (35, -5806080), (63, -8709120), (68, -9797760), (126, -45722880), (203, -19595520), (207, -19595520), (208, -58786560), (236, -32659200), (253, -19595520)]

theorem integerMergeCheck46 : integerMerge46 =
    Integer.Sparse.merge integerMerge44 integerMerge45 := by decide +kernel

theorem integerMergeEval46 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge46 x =
      Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck46, Integer.Sparse.eval_merge]
  rw [integerMergeEval44, integerMergeEval45]
  all_goals ring

def integerMerge47 : Integer.Sparse (Fin 909) := [(0, -399168), (1, -11521440), (2, 1632960), (3, 4354560), (4, 6531840), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -6531840), (35, -5806080), (63, -8709120), (126, -32659200), (203, -19595520), (207, -19595520), (208, -137168640), (236, -45722880), (253, -58786560)]

theorem integerMergeCheck47 : integerMerge47 =
    Integer.Sparse.merge integerMerge43 integerMerge46 := by decide +kernel

theorem integerMergeEval47 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge47 x =
      Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck47, Integer.Sparse.eval_merge]
  rw [integerMergeEval43, integerMergeEval46]
  all_goals ring

def integerMerge48 : Integer.Sparse (Fin 909) := [(0, -2140992), (1, -16420320), (2, 2177280), (3, 8709120), (4, 17418240), (5, -362880), (6, 272160), (7, -8709120), (12, -8709120), (13, -5806080), (23, -13063680), (27, 1088640), (31, -26127360), (35, -5806080), (63, -8709120), (126, -78382080), (203, -39191040), (207, -78382080), (208, -235146240), (236, -78382080), (253, -117573120)]

theorem integerMergeCheck48 : integerMerge48 =
    Integer.Sparse.merge integerMerge41 integerMerge47 := by decide +kernel

theorem integerMergeEval48 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge48 x =
      Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck48, Integer.Sparse.eval_merge]
  rw [integerMergeEval41, integerMergeEval47]
  all_goals ring

def integerMerge49 : Integer.Sparse (Fin 909) := [(0, -8727264), (1, -35199360), (2, -9253440), (3, 17418240), (4, 26127360), (5, 4536000), (6, 272160), (7, -8709120), (8, -39191040), (12, -4354560), (13, -5806080), (17, -19595520), (20, -78382080), (23, -13063680), (24, 39191040), (27, -13608000), (28, -78382080), (30, 137168640), (31, -26127360), (35, -5806080), (63, -8709120), (68, -3265920), (126, 52254720), (203, -78382080), (207, -78382080), (208, -470292480), (236, 78382080), (253, -352719360)]

theorem integerMergeCheck49 : integerMerge49 =
    Integer.Sparse.merge integerMerge36 integerMerge48 := by decide +kernel

theorem integerMergeEval49 (x : Fin 909 → ℝ) :
    Integer.Sparse.eval integerMerge49 x =
      Integer.Sparse.eval integerTerm0 x + Integer.Sparse.eval integerTerm1 x + Integer.Sparse.eval integerTerm2 x + Integer.Sparse.eval integerTerm3 x + Integer.Sparse.eval integerTerm4 x + Integer.Sparse.eval integerTerm5 x + Integer.Sparse.eval integerTerm6 x + Integer.Sparse.eval integerTerm7 x + Integer.Sparse.eval integerTerm8 x + Integer.Sparse.eval integerTerm9 x + Integer.Sparse.eval integerTerm10 x + Integer.Sparse.eval integerTerm11 x + Integer.Sparse.eval integerTerm12 x + Integer.Sparse.eval integerTerm13 x + Integer.Sparse.eval integerTerm14 x + Integer.Sparse.eval integerTerm15 x + Integer.Sparse.eval integerTerm16 x + Integer.Sparse.eval integerTerm17 x + Integer.Sparse.eval integerTerm18 x + Integer.Sparse.eval integerTerm19 x + Integer.Sparse.eval integerTerm20 x + Integer.Sparse.eval integerTerm21 x + Integer.Sparse.eval integerTerm22 x + Integer.Sparse.eval integerTerm23 x + Integer.Sparse.eval integerTerm24 x + Integer.Sparse.eval integerTerm26 x := by
  rw [integerMergeCheck49, Integer.Sparse.eval_merge]
  rw [integerMergeEval36, integerMergeEval48]
  all_goals ring

theorem finalReindex0 : List.Perm
    (Integer.Sparse.reindex PairSourceBridge.coordinateMap PairData.target0) integerMerge24 := by decide +kernel

theorem finalReindex1 : List.Perm
    (Integer.Sparse.reindex PairSourceBridge.coordinateMap PairData.target1) integerMerge49 := by decide +kernel

end MUB6.Certificate.PairTargetSemantics

end OAI
