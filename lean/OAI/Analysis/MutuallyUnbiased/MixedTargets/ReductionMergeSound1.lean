import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound0
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound2

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval32 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge32 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge32 (originalVector B) := by
  rw [reducedMerge32Check, Integer.Sparse.eval_mergeBy, reducedMergeEval30 B hB hF, reducedMergeEval31 B hB hF]
  rw [originalMerge32, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval33 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge33 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge33 (originalVector B) := by
  rw [reducedMerge33Check, Integer.Sparse.eval_mergeBy, reducedMergeEval29 B hB hF, reducedMergeEval32 B hB hF]
  rw [originalMerge33, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval34 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge34 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge34 (originalVector B) := by
  rw [reducedMerge34Check, Integer.Sparse.eval_mergeBy, reducedTermEval36 B hB hF, reducedTermEval37 B hB hF]
  rw [originalMerge34, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval35 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge35 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge35 (originalVector B) := by
  rw [reducedMerge35Check, Integer.Sparse.eval_mergeBy, reducedTermEval38 B hB hF, reducedTermEval39 B hB hF]
  rw [originalMerge35, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval36 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge36 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge36 (originalVector B) := by
  rw [reducedMerge36Check, Integer.Sparse.eval_mergeBy, reducedMergeEval34 B hB hF, reducedMergeEval35 B hB hF]
  rw [originalMerge36, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval37 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge37 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge37 (originalVector B) := by
  rw [reducedMerge37Check, Integer.Sparse.eval_mergeBy, reducedTermEval40 B hB hF, reducedTermEval41 B hB hF]
  rw [originalMerge37, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval38 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge38 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge38 (originalVector B) := by
  rw [reducedMerge38Check, Integer.Sparse.eval_mergeBy, reducedTermEval42 B hB hF, reducedTermEval43 B hB hF]
  rw [originalMerge38, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval39 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge39 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge39 (originalVector B) := by
  rw [reducedMerge39Check, Integer.Sparse.eval_mergeBy, reducedMergeEval37 B hB hF, reducedMergeEval38 B hB hF]
  rw [originalMerge39, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval40 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge40 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge40 (originalVector B) := by
  rw [reducedMerge40Check, Integer.Sparse.eval_mergeBy, reducedMergeEval36 B hB hF, reducedMergeEval39 B hB hF]
  rw [originalMerge40, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval41 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge41 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge41 (originalVector B) := by
  rw [reducedMerge41Check, Integer.Sparse.eval_mergeBy, reducedMergeEval33 B hB hF, reducedMergeEval40 B hB hF]
  rw [originalMerge41, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval42 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge42 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge42 (originalVector B) := by
  rw [reducedMerge42Check, Integer.Sparse.eval_mergeBy, reducedTermEval45 B hB hF, reducedTermEval46 B hB hF]
  rw [originalMerge42, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval43 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge43 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge43 (originalVector B) := by
  rw [reducedMerge43Check, Integer.Sparse.eval_mergeBy, reducedTermEval44 B hB hF, reducedMergeEval42 B hB hF]
  rw [originalMerge43, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval44 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge44 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge44 (originalVector B) := by
  rw [reducedMerge44Check, Integer.Sparse.eval_mergeBy, reducedTermEval47 B hB hF, reducedTermEval48 B hB hF]
  rw [originalMerge44, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval45 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge45 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge45 (originalVector B) := by
  rw [reducedMerge45Check, Integer.Sparse.eval_mergeBy, reducedTermEval49 B hB hF, reducedTermEval50 B hB hF]
  rw [originalMerge45, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval46 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge46 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge46 (originalVector B) := by
  rw [reducedMerge46Check, Integer.Sparse.eval_mergeBy, reducedMergeEval44 B hB hF, reducedMergeEval45 B hB hF]
  rw [originalMerge46, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval47 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge47 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge47 (originalVector B) := by
  rw [reducedMerge47Check, Integer.Sparse.eval_mergeBy, reducedMergeEval43 B hB hF, reducedMergeEval46 B hB hF]
  rw [originalMerge47, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval48 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge48 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge48 (originalVector B) := by
  rw [reducedMerge48Check, Integer.Sparse.eval_mergeBy, reducedTermEval51 B hB hF, reducedTermEval52 B hB hF]
  rw [originalMerge48, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval49 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge49 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge49 (originalVector B) := by
  rw [reducedMerge49Check, Integer.Sparse.eval_mergeBy, reducedTermEval53 B hB hF, reducedTermEval54 B hB hF]
  rw [originalMerge49, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval50 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge50 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge50 (originalVector B) := by
  rw [reducedMerge50Check, Integer.Sparse.eval_mergeBy, reducedMergeEval48 B hB hF, reducedMergeEval49 B hB hF]
  rw [originalMerge50, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval51 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge51 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge51 (originalVector B) := by
  rw [reducedMerge51Check, Integer.Sparse.eval_mergeBy, reducedTermEval55 B hB hF, reducedTermEval56 B hB hF]
  rw [originalMerge51, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval52 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge52 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge52 (originalVector B) := by
  rw [reducedMerge52Check, Integer.Sparse.eval_mergeBy, reducedTermEval57 B hB hF, reducedTermEval58 B hB hF]
  rw [originalMerge52, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval53 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge53 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge53 (originalVector B) := by
  rw [reducedMerge53Check, Integer.Sparse.eval_mergeBy, reducedMergeEval51 B hB hF, reducedMergeEval52 B hB hF]
  rw [originalMerge53, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval54 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge54 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge54 (originalVector B) := by
  rw [reducedMerge54Check, Integer.Sparse.eval_mergeBy, reducedMergeEval50 B hB hF, reducedMergeEval53 B hB hF]
  rw [originalMerge54, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval55 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge55 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge55 (originalVector B) := by
  rw [reducedMerge55Check, Integer.Sparse.eval_mergeBy, reducedMergeEval47 B hB hF, reducedMergeEval54 B hB hF]
  rw [originalMerge55, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval56 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge56 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge56 (originalVector B) := by
  rw [reducedMerge56Check, Integer.Sparse.eval_mergeBy, reducedMergeEval41 B hB hF, reducedMergeEval55 B hB hF]
  rw [originalMerge56, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval57 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge57 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge57 (originalVector B) := by
  rw [reducedMerge57Check, Integer.Sparse.eval_mergeBy, reducedMergeEval27 B hB hF, reducedMergeEval56 B hB hF]
  rw [originalMerge57, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval58 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge58 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge58 (originalVector B) := by
  rw [reducedMerge58Check, Integer.Sparse.eval_mergeBy, reducedTermEval60 B hB hF, reducedTermEval61 B hB hF]
  rw [originalMerge58, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval59 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge59 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge59 (originalVector B) := by
  rw [reducedMerge59Check, Integer.Sparse.eval_mergeBy, reducedTermEval59 B hB hF, reducedMergeEval58 B hB hF]
  rw [originalMerge59, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval60 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge60 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge60 (originalVector B) := by
  rw [reducedMerge60Check, Integer.Sparse.eval_mergeBy, reducedTermEval62 B hB hF, reducedTermEval63 B hB hF]
  rw [originalMerge60, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval61 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge61 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge61 (originalVector B) := by
  rw [reducedMerge61Check, Integer.Sparse.eval_mergeBy, reducedTermEval64 B hB hF, reducedTermEval65 B hB hF]
  rw [originalMerge61, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval62 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge62 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge62 (originalVector B) := by
  rw [reducedMerge62Check, Integer.Sparse.eval_mergeBy, reducedMergeEval60 B hB hF, reducedMergeEval61 B hB hF]
  rw [originalMerge62, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval63 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge63 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge63 (originalVector B) := by
  rw [reducedMerge63Check, Integer.Sparse.eval_mergeBy, reducedMergeEval59 B hB hF, reducedMergeEval62 B hB hF]
  rw [originalMerge63, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
