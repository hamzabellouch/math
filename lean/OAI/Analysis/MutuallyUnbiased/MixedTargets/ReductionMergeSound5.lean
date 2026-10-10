import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound4
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound5
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound6

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval160 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge160 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge160 (originalVector B) := by
  rw [reducedMerge160Check, Integer.Sparse.eval_mergeBy, reducedMergeEval152 B hB hF, reducedMergeEval159 B hB hF]
  rw [originalMerge160, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval161 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge161 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge161 (originalVector B) := by
  rw [reducedMerge161Check, Integer.Sparse.eval_mergeBy, reducedTermEval165 B hB hF, reducedTermEval166 B hB hF]
  rw [originalMerge161, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval162 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge162 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge162 (originalVector B) := by
  rw [reducedMerge162Check, Integer.Sparse.eval_mergeBy, reducedTermEval164 B hB hF, reducedMergeEval161 B hB hF]
  rw [originalMerge162, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval163 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge163 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge163 (originalVector B) := by
  rw [reducedMerge163Check, Integer.Sparse.eval_mergeBy, reducedTermEval167 B hB hF, reducedTermEval168 B hB hF]
  rw [originalMerge163, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval164 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge164 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge164 (originalVector B) := by
  rw [reducedMerge164Check, Integer.Sparse.eval_mergeBy, reducedTermEval169 B hB hF, reducedTermEval170 B hB hF]
  rw [originalMerge164, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval165 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge165 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge165 (originalVector B) := by
  rw [reducedMerge165Check, Integer.Sparse.eval_mergeBy, reducedMergeEval163 B hB hF, reducedMergeEval164 B hB hF]
  rw [originalMerge165, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval166 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge166 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge166 (originalVector B) := by
  rw [reducedMerge166Check, Integer.Sparse.eval_mergeBy, reducedMergeEval162 B hB hF, reducedMergeEval165 B hB hF]
  rw [originalMerge166, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval167 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge167 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge167 (originalVector B) := by
  rw [reducedMerge167Check, Integer.Sparse.eval_mergeBy, reducedTermEval171 B hB hF, reducedTermEval172 B hB hF]
  rw [originalMerge167, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval168 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge168 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge168 (originalVector B) := by
  rw [reducedMerge168Check, Integer.Sparse.eval_mergeBy, reducedTermEval173 B hB hF, reducedTermEval174 B hB hF]
  rw [originalMerge168, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval169 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge169 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge169 (originalVector B) := by
  rw [reducedMerge169Check, Integer.Sparse.eval_mergeBy, reducedMergeEval167 B hB hF, reducedMergeEval168 B hB hF]
  rw [originalMerge169, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval170 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge170 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge170 (originalVector B) := by
  rw [reducedMerge170Check, Integer.Sparse.eval_mergeBy, reducedTermEval175 B hB hF, reducedTermEval176 B hB hF]
  rw [originalMerge170, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval171 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge171 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge171 (originalVector B) := by
  rw [reducedMerge171Check, Integer.Sparse.eval_mergeBy, reducedTermEval177 B hB hF, reducedTermEval178 B hB hF]
  rw [originalMerge171, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval172 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge172 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge172 (originalVector B) := by
  rw [reducedMerge172Check, Integer.Sparse.eval_mergeBy, reducedMergeEval170 B hB hF, reducedMergeEval171 B hB hF]
  rw [originalMerge172, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval173 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge173 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge173 (originalVector B) := by
  rw [reducedMerge173Check, Integer.Sparse.eval_mergeBy, reducedMergeEval169 B hB hF, reducedMergeEval172 B hB hF]
  rw [originalMerge173, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval174 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge174 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge174 (originalVector B) := by
  rw [reducedMerge174Check, Integer.Sparse.eval_mergeBy, reducedMergeEval166 B hB hF, reducedMergeEval173 B hB hF]
  rw [originalMerge174, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval175 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge175 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge175 (originalVector B) := by
  rw [reducedMerge175Check, Integer.Sparse.eval_mergeBy, reducedMergeEval160 B hB hF, reducedMergeEval174 B hB hF]
  rw [originalMerge175, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval176 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge176 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge176 (originalVector B) := by
  rw [reducedMerge176Check, Integer.Sparse.eval_mergeBy, reducedMergeEval146 B hB hF, reducedMergeEval175 B hB hF]
  rw [originalMerge176, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval177 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge177 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge177 (originalVector B) := by
  rw [reducedMerge177Check, Integer.Sparse.eval_mergeBy, reducedTermEval180 B hB hF, reducedTermEval181 B hB hF]
  rw [originalMerge177, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval178 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge178 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge178 (originalVector B) := by
  rw [reducedMerge178Check, Integer.Sparse.eval_mergeBy, reducedTermEval179 B hB hF, reducedMergeEval177 B hB hF]
  rw [originalMerge178, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval179 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge179 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge179 (originalVector B) := by
  rw [reducedMerge179Check, Integer.Sparse.eval_mergeBy, reducedTermEval182 B hB hF, reducedTermEval183 B hB hF]
  rw [originalMerge179, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval180 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge180 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge180 (originalVector B) := by
  rw [reducedMerge180Check, Integer.Sparse.eval_mergeBy, reducedTermEval184 B hB hF, reducedTermEval185 B hB hF]
  rw [originalMerge180, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval181 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge181 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge181 (originalVector B) := by
  rw [reducedMerge181Check, Integer.Sparse.eval_mergeBy, reducedMergeEval179 B hB hF, reducedMergeEval180 B hB hF]
  rw [originalMerge181, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval182 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge182 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge182 (originalVector B) := by
  rw [reducedMerge182Check, Integer.Sparse.eval_mergeBy, reducedMergeEval178 B hB hF, reducedMergeEval181 B hB hF]
  rw [originalMerge182, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval183 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge183 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge183 (originalVector B) := by
  rw [reducedMerge183Check, Integer.Sparse.eval_mergeBy, reducedTermEval186 B hB hF, reducedTermEval187 B hB hF]
  rw [originalMerge183, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval184 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge184 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge184 (originalVector B) := by
  rw [reducedMerge184Check, Integer.Sparse.eval_mergeBy, reducedTermEval188 B hB hF, reducedTermEval189 B hB hF]
  rw [originalMerge184, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval185 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge185 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge185 (originalVector B) := by
  rw [reducedMerge185Check, Integer.Sparse.eval_mergeBy, reducedMergeEval183 B hB hF, reducedMergeEval184 B hB hF]
  rw [originalMerge185, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval186 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge186 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge186 (originalVector B) := by
  rw [reducedMerge186Check, Integer.Sparse.eval_mergeBy, reducedTermEval190 B hB hF, reducedTermEval191 B hB hF]
  rw [originalMerge186, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval187 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge187 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge187 (originalVector B) := by
  rw [reducedMerge187Check, Integer.Sparse.eval_mergeBy, reducedTermEval192 B hB hF, reducedTermEval193 B hB hF]
  rw [originalMerge187, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval188 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge188 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge188 (originalVector B) := by
  rw [reducedMerge188Check, Integer.Sparse.eval_mergeBy, reducedMergeEval186 B hB hF, reducedMergeEval187 B hB hF]
  rw [originalMerge188, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval189 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge189 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge189 (originalVector B) := by
  rw [reducedMerge189Check, Integer.Sparse.eval_mergeBy, reducedMergeEval185 B hB hF, reducedMergeEval188 B hB hF]
  rw [originalMerge189, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval190 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge190 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge190 (originalVector B) := by
  rw [reducedMerge190Check, Integer.Sparse.eval_mergeBy, reducedMergeEval182 B hB hF, reducedMergeEval189 B hB hF]
  rw [originalMerge190, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval191 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge191 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge191 (originalVector B) := by
  rw [reducedMerge191Check, Integer.Sparse.eval_mergeBy, reducedTermEval195 B hB hF, reducedTermEval196 B hB hF]
  rw [originalMerge191, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
