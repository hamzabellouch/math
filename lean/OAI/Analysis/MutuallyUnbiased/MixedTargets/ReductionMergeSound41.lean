import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData41
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound40
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound41
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound42

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1312 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1312 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1312 (originalVector B) := by
  rw [reducedMerge1312Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1304 B hB hF, reducedMergeEval1311 B hB hF]
  rw [originalMerge1312, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1313 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1313 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1313 (originalVector B) := by
  rw [reducedMerge1313Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1298 B hB hF, reducedMergeEval1312 B hB hF]
  rw [originalMerge1313, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1314 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1314 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1314 (originalVector B) := by
  rw [reducedMerge1314Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1284 B hB hF, reducedMergeEval1313 B hB hF]
  rw [originalMerge1314, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1315 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1315 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1315 (originalVector B) := by
  rw [reducedMerge1315Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1255 B hB hF, reducedMergeEval1314 B hB hF]
  rw [originalMerge1315, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1316 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1316 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1316 (originalVector B) := by
  rw [reducedMerge1316Check, Integer.Sparse.eval_mergeBy, reducedTermEval1320 B hB hF, reducedTermEval1321 B hB hF]
  rw [originalMerge1316, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1317 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1317 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1317 (originalVector B) := by
  rw [reducedMerge1317Check, Integer.Sparse.eval_mergeBy, reducedTermEval1319 B hB hF, reducedMergeEval1316 B hB hF]
  rw [originalMerge1317, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1318 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1318 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1318 (originalVector B) := by
  rw [reducedMerge1318Check, Integer.Sparse.eval_mergeBy, reducedTermEval1322 B hB hF, reducedTermEval1323 B hB hF]
  rw [originalMerge1318, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1319 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1319 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1319 (originalVector B) := by
  rw [reducedMerge1319Check, Integer.Sparse.eval_mergeBy, reducedTermEval1324 B hB hF, reducedTermEval1325 B hB hF]
  rw [originalMerge1319, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1320 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1320 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1320 (originalVector B) := by
  rw [reducedMerge1320Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1318 B hB hF, reducedMergeEval1319 B hB hF]
  rw [originalMerge1320, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1321 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1321 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1321 (originalVector B) := by
  rw [reducedMerge1321Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1317 B hB hF, reducedMergeEval1320 B hB hF]
  rw [originalMerge1321, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1322 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1322 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1322 (originalVector B) := by
  rw [reducedMerge1322Check, Integer.Sparse.eval_mergeBy, reducedTermEval1326 B hB hF, reducedTermEval1327 B hB hF]
  rw [originalMerge1322, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1323 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1323 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1323 (originalVector B) := by
  rw [reducedMerge1323Check, Integer.Sparse.eval_mergeBy, reducedTermEval1328 B hB hF, reducedTermEval1329 B hB hF]
  rw [originalMerge1323, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1324 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1324 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1324 (originalVector B) := by
  rw [reducedMerge1324Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1322 B hB hF, reducedMergeEval1323 B hB hF]
  rw [originalMerge1324, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1325 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1325 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1325 (originalVector B) := by
  rw [reducedMerge1325Check, Integer.Sparse.eval_mergeBy, reducedTermEval1330 B hB hF, reducedTermEval1331 B hB hF]
  rw [originalMerge1325, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1326 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1326 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1326 (originalVector B) := by
  rw [reducedMerge1326Check, Integer.Sparse.eval_mergeBy, reducedTermEval1332 B hB hF, reducedTermEval1333 B hB hF]
  rw [originalMerge1326, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1327 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1327 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1327 (originalVector B) := by
  rw [reducedMerge1327Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1325 B hB hF, reducedMergeEval1326 B hB hF]
  rw [originalMerge1327, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1328 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1328 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1328 (originalVector B) := by
  rw [reducedMerge1328Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1324 B hB hF, reducedMergeEval1327 B hB hF]
  rw [originalMerge1328, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1329 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1329 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1329 (originalVector B) := by
  rw [reducedMerge1329Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1321 B hB hF, reducedMergeEval1328 B hB hF]
  rw [originalMerge1329, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1330 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1330 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1330 (originalVector B) := by
  rw [reducedMerge1330Check, Integer.Sparse.eval_mergeBy, reducedTermEval1335 B hB hF, reducedTermEval1336 B hB hF]
  rw [originalMerge1330, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1331 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1331 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1331 (originalVector B) := by
  rw [reducedMerge1331Check, Integer.Sparse.eval_mergeBy, reducedTermEval1334 B hB hF, reducedMergeEval1330 B hB hF]
  rw [originalMerge1331, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1332 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1332 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1332 (originalVector B) := by
  rw [reducedMerge1332Check, Integer.Sparse.eval_mergeBy, reducedTermEval1337 B hB hF, reducedTermEval1338 B hB hF]
  rw [originalMerge1332, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1333 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1333 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1333 (originalVector B) := by
  rw [reducedMerge1333Check, Integer.Sparse.eval_mergeBy, reducedTermEval1339 B hB hF, reducedTermEval1340 B hB hF]
  rw [originalMerge1333, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1334 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1334 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1334 (originalVector B) := by
  rw [reducedMerge1334Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1332 B hB hF, reducedMergeEval1333 B hB hF]
  rw [originalMerge1334, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1335 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1335 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1335 (originalVector B) := by
  rw [reducedMerge1335Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1331 B hB hF, reducedMergeEval1334 B hB hF]
  rw [originalMerge1335, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1336 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1336 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1336 (originalVector B) := by
  rw [reducedMerge1336Check, Integer.Sparse.eval_mergeBy, reducedTermEval1341 B hB hF, reducedTermEval1342 B hB hF]
  rw [originalMerge1336, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1337 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1337 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1337 (originalVector B) := by
  rw [reducedMerge1337Check, Integer.Sparse.eval_mergeBy, reducedTermEval1343 B hB hF, reducedTermEval1344 B hB hF]
  rw [originalMerge1337, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1338 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1338 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1338 (originalVector B) := by
  rw [reducedMerge1338Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1336 B hB hF, reducedMergeEval1337 B hB hF]
  rw [originalMerge1338, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1339 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1339 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1339 (originalVector B) := by
  rw [reducedMerge1339Check, Integer.Sparse.eval_mergeBy, reducedTermEval1345 B hB hF, reducedTermEval1346 B hB hF]
  rw [originalMerge1339, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1340 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1340 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1340 (originalVector B) := by
  rw [reducedMerge1340Check, Integer.Sparse.eval_mergeBy, reducedTermEval1347 B hB hF, reducedTermEval1348 B hB hF]
  rw [originalMerge1340, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1341 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1341 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1341 (originalVector B) := by
  rw [reducedMerge1341Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1339 B hB hF, reducedMergeEval1340 B hB hF]
  rw [originalMerge1341, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1342 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1342 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1342 (originalVector B) := by
  rw [reducedMerge1342Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1338 B hB hF, reducedMergeEval1341 B hB hF]
  rw [originalMerge1342, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1343 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1343 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1343 (originalVector B) := by
  rw [reducedMerge1343Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1335 B hB hF, reducedMergeEval1342 B hB hF]
  rw [originalMerge1343, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
