import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeData40
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionMergeSound39
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound40
import OAI.Analysis.MutuallyUnbiased.MixedTargets.ReductionSound41

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

open MixedSemantics

theorem reducedMergeEval1280 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1280 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1280 (originalVector B) := by
  rw [reducedMerge1280Check, Integer.Sparse.eval_mergeBy, reducedTermEval1287 B hB hF, reducedTermEval1288 B hB hF]
  rw [originalMerge1280, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1281 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1281 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1281 (originalVector B) := by
  rw [reducedMerge1281Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1279 B hB hF, reducedMergeEval1280 B hB hF]
  rw [originalMerge1281, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1282 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1282 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1282 (originalVector B) := by
  rw [reducedMerge1282Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1278 B hB hF, reducedMergeEval1281 B hB hF]
  rw [originalMerge1282, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1283 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1283 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1283 (originalVector B) := by
  rw [reducedMerge1283Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1275 B hB hF, reducedMergeEval1282 B hB hF]
  rw [originalMerge1283, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1284 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1284 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1284 (originalVector B) := by
  rw [reducedMerge1284Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1269 B hB hF, reducedMergeEval1283 B hB hF]
  rw [originalMerge1284, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1285 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1285 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1285 (originalVector B) := by
  rw [reducedMerge1285Check, Integer.Sparse.eval_mergeBy, reducedTermEval1290 B hB hF, reducedTermEval1291 B hB hF]
  rw [originalMerge1285, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1286 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1286 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1286 (originalVector B) := by
  rw [reducedMerge1286Check, Integer.Sparse.eval_mergeBy, reducedTermEval1289 B hB hF, reducedMergeEval1285 B hB hF]
  rw [originalMerge1286, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1287 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1287 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1287 (originalVector B) := by
  rw [reducedMerge1287Check, Integer.Sparse.eval_mergeBy, reducedTermEval1292 B hB hF, reducedTermEval1293 B hB hF]
  rw [originalMerge1287, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1288 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1288 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1288 (originalVector B) := by
  rw [reducedMerge1288Check, Integer.Sparse.eval_mergeBy, reducedTermEval1294 B hB hF, reducedTermEval1295 B hB hF]
  rw [originalMerge1288, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1289 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1289 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1289 (originalVector B) := by
  rw [reducedMerge1289Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1287 B hB hF, reducedMergeEval1288 B hB hF]
  rw [originalMerge1289, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1290 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1290 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1290 (originalVector B) := by
  rw [reducedMerge1290Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1286 B hB hF, reducedMergeEval1289 B hB hF]
  rw [originalMerge1290, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1291 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1291 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1291 (originalVector B) := by
  rw [reducedMerge1291Check, Integer.Sparse.eval_mergeBy, reducedTermEval1296 B hB hF, reducedTermEval1297 B hB hF]
  rw [originalMerge1291, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1292 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1292 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1292 (originalVector B) := by
  rw [reducedMerge1292Check, Integer.Sparse.eval_mergeBy, reducedTermEval1298 B hB hF, reducedTermEval1299 B hB hF]
  rw [originalMerge1292, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1293 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1293 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1293 (originalVector B) := by
  rw [reducedMerge1293Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1291 B hB hF, reducedMergeEval1292 B hB hF]
  rw [originalMerge1293, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1294 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1294 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1294 (originalVector B) := by
  rw [reducedMerge1294Check, Integer.Sparse.eval_mergeBy, reducedTermEval1300 B hB hF, reducedTermEval1301 B hB hF]
  rw [originalMerge1294, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1295 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1295 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1295 (originalVector B) := by
  rw [reducedMerge1295Check, Integer.Sparse.eval_mergeBy, reducedTermEval1302 B hB hF, reducedTermEval1303 B hB hF]
  rw [originalMerge1295, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1296 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1296 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1296 (originalVector B) := by
  rw [reducedMerge1296Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1294 B hB hF, reducedMergeEval1295 B hB hF]
  rw [originalMerge1296, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1297 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1297 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1297 (originalVector B) := by
  rw [reducedMerge1297Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1293 B hB hF, reducedMergeEval1296 B hB hF]
  rw [originalMerge1297, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1298 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1298 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1298 (originalVector B) := by
  rw [reducedMerge1298Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1290 B hB hF, reducedMergeEval1297 B hB hF]
  rw [originalMerge1298, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1299 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1299 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1299 (originalVector B) := by
  rw [reducedMerge1299Check, Integer.Sparse.eval_mergeBy, reducedTermEval1305 B hB hF, reducedTermEval1306 B hB hF]
  rw [originalMerge1299, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1300 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1300 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1300 (originalVector B) := by
  rw [reducedMerge1300Check, Integer.Sparse.eval_mergeBy, reducedTermEval1304 B hB hF, reducedMergeEval1299 B hB hF]
  rw [originalMerge1300, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1301 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1301 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1301 (originalVector B) := by
  rw [reducedMerge1301Check, Integer.Sparse.eval_mergeBy, reducedTermEval1307 B hB hF, reducedTermEval1308 B hB hF]
  rw [originalMerge1301, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1302 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1302 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1302 (originalVector B) := by
  rw [reducedMerge1302Check, Integer.Sparse.eval_mergeBy, reducedTermEval1309 B hB hF, reducedTermEval1310 B hB hF]
  rw [originalMerge1302, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1303 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1303 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1303 (originalVector B) := by
  rw [reducedMerge1303Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1301 B hB hF, reducedMergeEval1302 B hB hF]
  rw [originalMerge1303, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1304 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1304 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1304 (originalVector B) := by
  rw [reducedMerge1304Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1300 B hB hF, reducedMergeEval1303 B hB hF]
  rw [originalMerge1304, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1305 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1305 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1305 (originalVector B) := by
  rw [reducedMerge1305Check, Integer.Sparse.eval_mergeBy, reducedTermEval1311 B hB hF, reducedTermEval1312 B hB hF]
  rw [originalMerge1305, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1306 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1306 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1306 (originalVector B) := by
  rw [reducedMerge1306Check, Integer.Sparse.eval_mergeBy, reducedTermEval1313 B hB hF, reducedTermEval1314 B hB hF]
  rw [originalMerge1306, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1307 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1307 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1307 (originalVector B) := by
  rw [reducedMerge1307Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1305 B hB hF, reducedMergeEval1306 B hB hF]
  rw [originalMerge1307, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1308 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1308 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1308 (originalVector B) := by
  rw [reducedMerge1308Check, Integer.Sparse.eval_mergeBy, reducedTermEval1315 B hB hF, reducedTermEval1316 B hB hF]
  rw [originalMerge1308, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1309 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1309 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1309 (originalVector B) := by
  rw [reducedMerge1309Check, Integer.Sparse.eval_mergeBy, reducedTermEval1317 B hB hF, reducedTermEval1318 B hB hF]
  rw [originalMerge1309, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1310 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1310 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1310 (originalVector B) := by
  rw [reducedMerge1310Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1308 B hB hF, reducedMergeEval1309 B hB hF]
  rw [originalMerge1310, Integer.Sparse.eval_append]
  ring

theorem reducedMergeEval1311 (B : Fin 7 → Basis) (hB : IsMUBFamily B)
    (hF : AllTransitionsFourierZero B) :
    Integer.Sparse.eval reducedMerge1311 (mixedVector B) =
      (37623398400 : ℝ) * Integer.Sparse.eval originalMerge1311 (originalVector B) := by
  rw [reducedMerge1311Check, Integer.Sparse.eval_mergeBy, reducedMergeEval1307 B hB hF, reducedMergeEval1310 B hB hF]
  rw [originalMerge1311, Integer.Sparse.eval_append]
  ring

end MUB6.Certificate.MixedTargetSemantics

end OAI
