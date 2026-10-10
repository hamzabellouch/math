import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound3
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound4

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval96 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge96 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge96 (originalVector B) := by
  rw [reducedMerge96Check, Integer.Sparse.eval_mergeBy, reducedTermEval100 B hB hF, reducedTermEval101 B hB hF]
  rw [originalMerge96, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval97 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge97 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge97 (originalVector B) := by
  rw [reducedMerge97Check, Integer.Sparse.eval_mergeBy, reducedTermEval102 B hB hF, reducedTermEval103 B hB hF]
  rw [originalMerge97, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval98 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge98 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge98 (originalVector B) := by
  rw [reducedMerge98Check, Integer.Sparse.eval_mergeBy, reducedMergeEval96 B hB hF, reducedMergeEval97 B hB hF]
  rw [originalMerge98, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval99 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge99 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge99 (originalVector B) := by
  rw [reducedMerge99Check, Integer.Sparse.eval_mergeBy, reducedMergeEval95 B hB hF, reducedMergeEval98 B hB hF]
  rw [originalMerge99, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval100 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge100 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge100 (originalVector B) := by
  rw [reducedMerge100Check, Integer.Sparse.eval_mergeBy, reducedMergeEval92 B hB hF, reducedMergeEval99 B hB hF]
  rw [originalMerge100, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval101 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge101 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge101 (originalVector B) := by
  rw [reducedMerge101Check, Integer.Sparse.eval_mergeBy, reducedTermEval105 B hB hF, reducedTermEval106 B hB hF]
  rw [originalMerge101, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval102 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge102 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge102 (originalVector B) := by
  rw [reducedMerge102Check, Integer.Sparse.eval_mergeBy, reducedTermEval104 B hB hF, reducedMergeEval101 B hB hF]
  rw [originalMerge102, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval103 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge103 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge103 (originalVector B) := by
  rw [reducedMerge103Check, Integer.Sparse.eval_mergeBy, reducedTermEval107 B hB hF, reducedTermEval108 B hB hF]
  rw [originalMerge103, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval104 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge104 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge104 (originalVector B) := by
  rw [reducedMerge104Check, Integer.Sparse.eval_mergeBy, reducedTermEval109 B hB hF, reducedTermEval110 B hB hF]
  rw [originalMerge104, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval105 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge105 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge105 (originalVector B) := by
  rw [reducedMerge105Check, Integer.Sparse.eval_mergeBy, reducedMergeEval103 B hB hF, reducedMergeEval104 B hB hF]
  rw [originalMerge105, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval106 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge106 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge106 (originalVector B) := by
  rw [reducedMerge106Check, Integer.Sparse.eval_mergeBy, reducedMergeEval102 B hB hF, reducedMergeEval105 B hB hF]
  rw [originalMerge106, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval107 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge107 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge107 (originalVector B) := by
  rw [reducedMerge107Check, Integer.Sparse.eval_mergeBy, reducedTermEval111 B hB hF, reducedTermEval112 B hB hF]
  rw [originalMerge107, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval108 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge108 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge108 (originalVector B) := by
  rw [reducedMerge108Check, Integer.Sparse.eval_mergeBy, reducedTermEval113 B hB hF, reducedTermEval114 B hB hF]
  rw [originalMerge108, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval109 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge109 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge109 (originalVector B) := by
  rw [reducedMerge109Check, Integer.Sparse.eval_mergeBy, reducedMergeEval107 B hB hF, reducedMergeEval108 B hB hF]
  rw [originalMerge109, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval110 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge110 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge110 (originalVector B) := by
  rw [reducedMerge110Check, Integer.Sparse.eval_mergeBy, reducedTermEval115 B hB hF, reducedTermEval116 B hB hF]
  rw [originalMerge110, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval111 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge111 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge111 (originalVector B) := by
  rw [reducedMerge111Check, Integer.Sparse.eval_mergeBy, reducedTermEval117 B hB hF, reducedTermEval118 B hB hF]
  rw [originalMerge111, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval112 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge112 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge112 (originalVector B) := by
  rw [reducedMerge112Check, Integer.Sparse.eval_mergeBy, reducedMergeEval110 B hB hF, reducedMergeEval111 B hB hF]
  rw [originalMerge112, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval113 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge113 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge113 (originalVector B) := by
  rw [reducedMerge113Check, Integer.Sparse.eval_mergeBy, reducedMergeEval109 B hB hF, reducedMergeEval112 B hB hF]
  rw [originalMerge113, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval114 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge114 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge114 (originalVector B) := by
  rw [reducedMerge114Check, Integer.Sparse.eval_mergeBy, reducedMergeEval106 B hB hF, reducedMergeEval113 B hB hF]
  rw [originalMerge114, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval115 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge115 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge115 (originalVector B) := by
  rw [reducedMerge115Check, Integer.Sparse.eval_mergeBy, reducedMergeEval100 B hB hF, reducedMergeEval114 B hB hF]
  rw [originalMerge115, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval116 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge116 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge116 (originalVector B) := by
  rw [reducedMerge116Check, Integer.Sparse.eval_mergeBy, reducedMergeEval86 B hB hF, reducedMergeEval115 B hB hF]
  rw [originalMerge116, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval117 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge117 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge117 (originalVector B) := by
  rw [reducedMerge117Check, Integer.Sparse.eval_mergeBy, reducedMergeEval57 B hB hF, reducedMergeEval116 B hB hF]
  rw [originalMerge117, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval118 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge118 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge118 (originalVector B) := by
  rw [reducedMerge118Check, Integer.Sparse.eval_mergeBy, reducedTermEval120 B hB hF, reducedTermEval121 B hB hF]
  rw [originalMerge118, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval119 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge119 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge119 (originalVector B) := by
  rw [reducedMerge119Check, Integer.Sparse.eval_mergeBy, reducedTermEval119 B hB hF, reducedMergeEval118 B hB hF]
  rw [originalMerge119, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval120 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge120 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge120 (originalVector B) := by
  rw [reducedMerge120Check, Integer.Sparse.eval_mergeBy, reducedTermEval122 B hB hF, reducedTermEval123 B hB hF]
  rw [originalMerge120, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval121 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge121 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge121 (originalVector B) := by
  rw [reducedMerge121Check, Integer.Sparse.eval_mergeBy, reducedTermEval124 B hB hF, reducedTermEval125 B hB hF]
  rw [originalMerge121, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval122 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge122 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge122 (originalVector B) := by
  rw [reducedMerge122Check, Integer.Sparse.eval_mergeBy, reducedMergeEval120 B hB hF, reducedMergeEval121 B hB hF]
  rw [originalMerge122, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval123 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge123 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge123 (originalVector B) := by
  rw [reducedMerge123Check, Integer.Sparse.eval_mergeBy, reducedMergeEval119 B hB hF, reducedMergeEval122 B hB hF]
  rw [originalMerge123, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval124 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge124 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge124 (originalVector B) := by
  rw [reducedMerge124Check, Integer.Sparse.eval_mergeBy, reducedTermEval126 B hB hF, reducedTermEval127 B hB hF]
  rw [originalMerge124, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval125 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge125 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge125 (originalVector B) := by
  rw [reducedMerge125Check, Integer.Sparse.eval_mergeBy, reducedTermEval128 B hB hF, reducedTermEval129 B hB hF]
  rw [originalMerge125, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval126 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge126 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge126 (originalVector B) := by
  rw [reducedMerge126Check, Integer.Sparse.eval_mergeBy, reducedMergeEval124 B hB hF, reducedMergeEval125 B hB hF]
  rw [originalMerge126, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval127 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge127 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge127 (originalVector B) := by
  rw [reducedMerge127Check, Integer.Sparse.eval_mergeBy, reducedTermEval130 B hB hF, reducedTermEval131 B hB hF]
  rw [originalMerge127, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
