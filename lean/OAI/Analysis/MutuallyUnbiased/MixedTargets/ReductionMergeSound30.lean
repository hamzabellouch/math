import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData30
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound29
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound30
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound31

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval960 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge960 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge960 (originalVector B) := by
  rw [reducedMerge960Check, Integer.Sparse.eval_mergeBy, reducedTermEval962 B hB hF, reducedTermEval963 B hB hF]
  rw [originalMerge960, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval961 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge961 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge961 (originalVector B) := by
  rw [reducedMerge961Check, Integer.Sparse.eval_mergeBy, reducedTermEval964 B hB hF, reducedTermEval965 B hB hF]
  rw [originalMerge961, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval962 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge962 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge962 (originalVector B) := by
  rw [reducedMerge962Check, Integer.Sparse.eval_mergeBy, reducedMergeEval960 B hB hF, reducedMergeEval961 B hB hF]
  rw [originalMerge962, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval963 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge963 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge963 (originalVector B) := by
  rw [reducedMerge963Check, Integer.Sparse.eval_mergeBy, reducedMergeEval959 B hB hF, reducedMergeEval962 B hB hF]
  rw [originalMerge963, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval964 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge964 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge964 (originalVector B) := by
  rw [reducedMerge964Check, Integer.Sparse.eval_mergeBy, reducedTermEval966 B hB hF, reducedTermEval967 B hB hF]
  rw [originalMerge964, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval965 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge965 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge965 (originalVector B) := by
  rw [reducedMerge965Check, Integer.Sparse.eval_mergeBy, reducedTermEval968 B hB hF, reducedTermEval969 B hB hF]
  rw [originalMerge965, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval966 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge966 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge966 (originalVector B) := by
  rw [reducedMerge966Check, Integer.Sparse.eval_mergeBy, reducedMergeEval964 B hB hF, reducedMergeEval965 B hB hF]
  rw [originalMerge966, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval967 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge967 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge967 (originalVector B) := by
  rw [reducedMerge967Check, Integer.Sparse.eval_mergeBy, reducedTermEval970 B hB hF, reducedTermEval971 B hB hF]
  rw [originalMerge967, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval968 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge968 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge968 (originalVector B) := by
  rw [reducedMerge968Check, Integer.Sparse.eval_mergeBy, reducedTermEval972 B hB hF, reducedTermEval973 B hB hF]
  rw [originalMerge968, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval969 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge969 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge969 (originalVector B) := by
  rw [reducedMerge969Check, Integer.Sparse.eval_mergeBy, reducedMergeEval967 B hB hF, reducedMergeEval968 B hB hF]
  rw [originalMerge969, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval970 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge970 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge970 (originalVector B) := by
  rw [reducedMerge970Check, Integer.Sparse.eval_mergeBy, reducedMergeEval966 B hB hF, reducedMergeEval969 B hB hF]
  rw [originalMerge970, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval971 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge971 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge971 (originalVector B) := by
  rw [reducedMerge971Check, Integer.Sparse.eval_mergeBy, reducedMergeEval963 B hB hF, reducedMergeEval970 B hB hF]
  rw [originalMerge971, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval972 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge972 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge972 (originalVector B) := by
  rw [reducedMerge972Check, Integer.Sparse.eval_mergeBy, reducedTermEval975 B hB hF, reducedTermEval976 B hB hF]
  rw [originalMerge972, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval973 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge973 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge973 (originalVector B) := by
  rw [reducedMerge973Check, Integer.Sparse.eval_mergeBy, reducedTermEval974 B hB hF, reducedMergeEval972 B hB hF]
  rw [originalMerge973, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval974 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge974 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge974 (originalVector B) := by
  rw [reducedMerge974Check, Integer.Sparse.eval_mergeBy, reducedTermEval977 B hB hF, reducedTermEval978 B hB hF]
  rw [originalMerge974, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval975 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge975 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge975 (originalVector B) := by
  rw [reducedMerge975Check, Integer.Sparse.eval_mergeBy, reducedTermEval979 B hB hF, reducedTermEval980 B hB hF]
  rw [originalMerge975, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval976 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge976 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge976 (originalVector B) := by
  rw [reducedMerge976Check, Integer.Sparse.eval_mergeBy, reducedMergeEval974 B hB hF, reducedMergeEval975 B hB hF]
  rw [originalMerge976, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval977 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge977 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge977 (originalVector B) := by
  rw [reducedMerge977Check, Integer.Sparse.eval_mergeBy, reducedMergeEval973 B hB hF, reducedMergeEval976 B hB hF]
  rw [originalMerge977, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval978 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge978 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge978 (originalVector B) := by
  rw [reducedMerge978Check, Integer.Sparse.eval_mergeBy, reducedTermEval981 B hB hF, reducedTermEval982 B hB hF]
  rw [originalMerge978, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval979 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge979 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge979 (originalVector B) := by
  rw [reducedMerge979Check, Integer.Sparse.eval_mergeBy, reducedTermEval983 B hB hF, reducedTermEval984 B hB hF]
  rw [originalMerge979, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval980 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge980 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge980 (originalVector B) := by
  rw [reducedMerge980Check, Integer.Sparse.eval_mergeBy, reducedMergeEval978 B hB hF, reducedMergeEval979 B hB hF]
  rw [originalMerge980, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval981 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge981 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge981 (originalVector B) := by
  rw [reducedMerge981Check, Integer.Sparse.eval_mergeBy, reducedTermEval985 B hB hF, reducedTermEval986 B hB hF]
  rw [originalMerge981, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval982 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge982 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge982 (originalVector B) := by
  rw [reducedMerge982Check, Integer.Sparse.eval_mergeBy, reducedTermEval987 B hB hF, reducedTermEval988 B hB hF]
  rw [originalMerge982, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval983 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge983 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge983 (originalVector B) := by
  rw [reducedMerge983Check, Integer.Sparse.eval_mergeBy, reducedMergeEval981 B hB hF, reducedMergeEval982 B hB hF]
  rw [originalMerge983, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval984 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge984 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge984 (originalVector B) := by
  rw [reducedMerge984Check, Integer.Sparse.eval_mergeBy, reducedMergeEval980 B hB hF, reducedMergeEval983 B hB hF]
  rw [originalMerge984, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval985 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge985 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge985 (originalVector B) := by
  rw [reducedMerge985Check, Integer.Sparse.eval_mergeBy, reducedMergeEval977 B hB hF, reducedMergeEval984 B hB hF]
  rw [originalMerge985, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval986 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge986 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge986 (originalVector B) := by
  rw [reducedMerge986Check, Integer.Sparse.eval_mergeBy, reducedMergeEval971 B hB hF, reducedMergeEval985 B hB hF]
  rw [originalMerge986, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval987 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge987 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge987 (originalVector B) := by
  rw [reducedMerge987Check, Integer.Sparse.eval_mergeBy, reducedTermEval990 B hB hF, reducedTermEval991 B hB hF]
  rw [originalMerge987, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval988 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge988 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge988 (originalVector B) := by
  rw [reducedMerge988Check, Integer.Sparse.eval_mergeBy, reducedTermEval989 B hB hF, reducedMergeEval987 B hB hF]
  rw [originalMerge988, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval989 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge989 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge989 (originalVector B) := by
  rw [reducedMerge989Check, Integer.Sparse.eval_mergeBy, reducedTermEval992 B hB hF, reducedTermEval993 B hB hF]
  rw [originalMerge989, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval990 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge990 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge990 (originalVector B) := by
  rw [reducedMerge990Check, Integer.Sparse.eval_mergeBy, reducedTermEval994 B hB hF, reducedTermEval995 B hB hF]
  rw [originalMerge990, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval991 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge991 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge991 (originalVector B) := by
  rw [reducedMerge991Check, Integer.Sparse.eval_mergeBy, reducedMergeEval989 B hB hF, reducedMergeEval990 B hB hF]
  rw [originalMerge991, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
