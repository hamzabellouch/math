import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound1
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound2
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound3

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval64 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge64 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge64 (originalVector B) := by
  rw [reducedMerge64Check, Integer.Sparse.eval_mergeBy, reducedTermEval66 B hB hF, reducedTermEval67 B hB hF]
  rw [originalMerge64, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval65 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge65 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge65 (originalVector B) := by
  rw [reducedMerge65Check, Integer.Sparse.eval_mergeBy, reducedTermEval68 B hB hF, reducedTermEval69 B hB hF]
  rw [originalMerge65, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval66 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge66 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge66 (originalVector B) := by
  rw [reducedMerge66Check, Integer.Sparse.eval_mergeBy, reducedMergeEval64 B hB hF, reducedMergeEval65 B hB hF]
  rw [originalMerge66, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval67 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge67 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge67 (originalVector B) := by
  rw [reducedMerge67Check, Integer.Sparse.eval_mergeBy, reducedTermEval70 B hB hF, reducedTermEval71 B hB hF]
  rw [originalMerge67, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval68 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge68 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge68 (originalVector B) := by
  rw [reducedMerge68Check, Integer.Sparse.eval_mergeBy, reducedTermEval72 B hB hF, reducedTermEval73 B hB hF]
  rw [originalMerge68, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval69 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge69 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge69 (originalVector B) := by
  rw [reducedMerge69Check, Integer.Sparse.eval_mergeBy, reducedMergeEval67 B hB hF, reducedMergeEval68 B hB hF]
  rw [originalMerge69, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval70 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge70 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge70 (originalVector B) := by
  rw [reducedMerge70Check, Integer.Sparse.eval_mergeBy, reducedMergeEval66 B hB hF, reducedMergeEval69 B hB hF]
  rw [originalMerge70, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval71 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge71 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge71 (originalVector B) := by
  rw [reducedMerge71Check, Integer.Sparse.eval_mergeBy, reducedMergeEval63 B hB hF, reducedMergeEval70 B hB hF]
  rw [originalMerge71, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval72 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge72 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge72 (originalVector B) := by
  rw [reducedMerge72Check, Integer.Sparse.eval_mergeBy, reducedTermEval75 B hB hF, reducedTermEval76 B hB hF]
  rw [originalMerge72, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval73 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge73 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge73 (originalVector B) := by
  rw [reducedMerge73Check, Integer.Sparse.eval_mergeBy, reducedTermEval74 B hB hF, reducedMergeEval72 B hB hF]
  rw [originalMerge73, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval74 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge74 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge74 (originalVector B) := by
  rw [reducedMerge74Check, Integer.Sparse.eval_mergeBy, reducedTermEval77 B hB hF, reducedTermEval78 B hB hF]
  rw [originalMerge74, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval75 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge75 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge75 (originalVector B) := by
  rw [reducedMerge75Check, Integer.Sparse.eval_mergeBy, reducedTermEval79 B hB hF, reducedTermEval80 B hB hF]
  rw [originalMerge75, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval76 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge76 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge76 (originalVector B) := by
  rw [reducedMerge76Check, Integer.Sparse.eval_mergeBy, reducedMergeEval74 B hB hF, reducedMergeEval75 B hB hF]
  rw [originalMerge76, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval77 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge77 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge77 (originalVector B) := by
  rw [reducedMerge77Check, Integer.Sparse.eval_mergeBy, reducedMergeEval73 B hB hF, reducedMergeEval76 B hB hF]
  rw [originalMerge77, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval78 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge78 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge78 (originalVector B) := by
  rw [reducedMerge78Check, Integer.Sparse.eval_mergeBy, reducedTermEval81 B hB hF, reducedTermEval82 B hB hF]
  rw [originalMerge78, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval79 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge79 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge79 (originalVector B) := by
  rw [reducedMerge79Check, Integer.Sparse.eval_mergeBy, reducedTermEval83 B hB hF, reducedTermEval84 B hB hF]
  rw [originalMerge79, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval80 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge80 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge80 (originalVector B) := by
  rw [reducedMerge80Check, Integer.Sparse.eval_mergeBy, reducedMergeEval78 B hB hF, reducedMergeEval79 B hB hF]
  rw [originalMerge80, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval81 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge81 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge81 (originalVector B) := by
  rw [reducedMerge81Check, Integer.Sparse.eval_mergeBy, reducedTermEval85 B hB hF, reducedTermEval86 B hB hF]
  rw [originalMerge81, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval82 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge82 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge82 (originalVector B) := by
  rw [reducedMerge82Check, Integer.Sparse.eval_mergeBy, reducedTermEval87 B hB hF, reducedTermEval88 B hB hF]
  rw [originalMerge82, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval83 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge83 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge83 (originalVector B) := by
  rw [reducedMerge83Check, Integer.Sparse.eval_mergeBy, reducedMergeEval81 B hB hF, reducedMergeEval82 B hB hF]
  rw [originalMerge83, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval84 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge84 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge84 (originalVector B) := by
  rw [reducedMerge84Check, Integer.Sparse.eval_mergeBy, reducedMergeEval80 B hB hF, reducedMergeEval83 B hB hF]
  rw [originalMerge84, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval85 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge85 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge85 (originalVector B) := by
  rw [reducedMerge85Check, Integer.Sparse.eval_mergeBy, reducedMergeEval77 B hB hF, reducedMergeEval84 B hB hF]
  rw [originalMerge85, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval86 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge86 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge86 (originalVector B) := by
  rw [reducedMerge86Check, Integer.Sparse.eval_mergeBy, reducedMergeEval71 B hB hF, reducedMergeEval85 B hB hF]
  rw [originalMerge86, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval87 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge87 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge87 (originalVector B) := by
  rw [reducedMerge87Check, Integer.Sparse.eval_mergeBy, reducedTermEval90 B hB hF, reducedTermEval91 B hB hF]
  rw [originalMerge87, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval88 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge88 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge88 (originalVector B) := by
  rw [reducedMerge88Check, Integer.Sparse.eval_mergeBy, reducedTermEval89 B hB hF, reducedMergeEval87 B hB hF]
  rw [originalMerge88, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval89 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge89 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge89 (originalVector B) := by
  rw [reducedMerge89Check, Integer.Sparse.eval_mergeBy, reducedTermEval92 B hB hF, reducedTermEval93 B hB hF]
  rw [originalMerge89, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval90 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge90 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge90 (originalVector B) := by
  rw [reducedMerge90Check, Integer.Sparse.eval_mergeBy, reducedTermEval94 B hB hF, reducedTermEval95 B hB hF]
  rw [originalMerge90, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval91 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge91 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge91 (originalVector B) := by
  rw [reducedMerge91Check, Integer.Sparse.eval_mergeBy, reducedMergeEval89 B hB hF, reducedMergeEval90 B hB hF]
  rw [originalMerge91, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval92 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge92 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge92 (originalVector B) := by
  rw [reducedMerge92Check, Integer.Sparse.eval_mergeBy, reducedMergeEval88 B hB hF, reducedMergeEval91 B hB hF]
  rw [originalMerge92, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval93 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge93 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge93 (originalVector B) := by
  rw [reducedMerge93Check, Integer.Sparse.eval_mergeBy, reducedTermEval96 B hB hF, reducedTermEval97 B hB hF]
  rw [originalMerge93, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval94 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge94 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge94 (originalVector B) := by
  rw [reducedMerge94Check, Integer.Sparse.eval_mergeBy, reducedTermEval98 B hB hF, reducedTermEval99 B hB hF]
  rw [originalMerge94, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval95 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge95 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge95 (originalVector B) := by
  rw [reducedMerge95Check, Integer.Sparse.eval_mergeBy, reducedMergeEval93 B hB hF, reducedMergeEval94 B hB hF]
  rw [originalMerge95, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
