import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted0
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted1
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted2
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted3
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted4
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted5
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted6
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted7
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted8
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted9
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted10
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted11
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted12
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted13
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted14
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted15
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted16
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted17
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted18
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted19
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted20
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted21
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted22
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted23
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted24
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted25
import OAI.Analysis.MutuallyUnbiased.PairTargets.Weighted26
import OAI.Analysis.MutuallyUnbiased.PairMoments.PairTermSums
import OAI.Analysis.MutuallyUnbiased.PairSources.Main
import OAI.Analysis.MutuallyUnbiased.PairTargets.Assembly

namespace OAI

namespace MUB6.Certificate.PairTargetSemantics

open scoped BigOperators

theorem expandedIdentity0 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * expanded0 H =
      Integer.Sparse.eval integerMerge24 (PairSemantics.momentVector H) := by
  rw [integerMergeEval24]
  unfold expanded0
  rw [sum_terms0_expand]
  simp only [mul_add]
  rw [weightedTerm0 hH, weightedTerm1 hH, weightedTerm2 hH, weightedTerm3 hH, weightedTerm4 hH, weightedTerm5 hH, weightedTerm6 hH, weightedTerm7 hH, weightedTerm8 hH, weightedTerm9 hH, weightedTerm10 hH, weightedTerm11 hH, weightedTerm12 hH, weightedTerm13 hH, weightedTerm14 hH, weightedTerm15 hH, weightedTerm16 hH, weightedTerm17 hH, weightedTerm18 hH, weightedTerm19 hH, weightedTerm20 hH, weightedTerm21 hH, weightedTerm22 hH, weightedTerm23 hH, weightedTerm24 hH, weightedTerm25 hH]

theorem certificate_zero0 {H : CMatrix} (hH : IsHadamard H) : expanded0 H = 0 := by
  have hz := PairSourceBridge.targetZero0 hH
  unfold PairSourceBridge.momentVector at hz
  rw [← Integer.Sparse.eval_reindex] at hz
  rw [Integer.Sparse.eval_perm finalReindex0] at hz
  have he := expandedIdentity0 hH
  rw [hz] at he
  linarith

theorem expandedIdentity1 {H : CMatrix} (hH : IsHadamard H) :
    (47029248 : ℝ) * expanded1 H =
      Integer.Sparse.eval integerMerge49 (PairSemantics.momentVector H) := by
  rw [integerMergeEval49]
  unfold expanded1
  rw [sum_terms1_expand]
  simp only [mul_add]
  rw [weightedTerm0 hH, weightedTerm1 hH, weightedTerm2 hH, weightedTerm3 hH, weightedTerm4 hH, weightedTerm5 hH, weightedTerm6 hH, weightedTerm7 hH, weightedTerm8 hH, weightedTerm9 hH, weightedTerm10 hH, weightedTerm11 hH, weightedTerm12 hH, weightedTerm13 hH, weightedTerm14 hH, weightedTerm15 hH, weightedTerm16 hH, weightedTerm17 hH, weightedTerm18 hH, weightedTerm19 hH, weightedTerm20 hH, weightedTerm21 hH, weightedTerm22 hH, weightedTerm23 hH, weightedTerm24 hH, weightedTerm26 hH]

theorem certificate_zero1 {H : CMatrix} (hH : IsHadamard H) : expanded1 H = 0 := by
  have hz := PairSourceBridge.targetZero1 hH
  unfold PairSourceBridge.momentVector at hz
  rw [← Integer.Sparse.eval_reindex] at hz
  rw [Integer.Sparse.eval_perm finalReindex1] at hz
  have he := expandedIdentity1 hH
  rw [hz] at he
  linarith

end MUB6.Certificate.PairTargetSemantics

end OAI
