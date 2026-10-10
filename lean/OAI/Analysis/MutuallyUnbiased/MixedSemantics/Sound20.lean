import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Coordinates
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Values20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.SoundPriority
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound0
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound1
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Sound2
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Zeros20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Singletons20

namespace OAI

namespace MUB6.Certificate.MixedSemantics

theorem sound1280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1280 node1280Labels = Sparse.eval nodeValue1280 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1280) = mixedMoment B node1280 node1280Labels := rfl
  simpa [nodeValue1280, Sparse.eval] using hc.symm

theorem sound1281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1281 node1281Labels = Sparse.eval nodeValue1281 (mixedVector B) := by
  have h := singleton1281 B _hB
  rw [sound135 B _hB _hF] at h
  norm_num [nodeValue1281, nodeValue135, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1282 node1282Labels = Sparse.eval nodeValue1282 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1282) = mixedMoment B node1282 node1282Labels := rfl
  simpa [nodeValue1282, Sparse.eval] using hc.symm

theorem sound1283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1283 node1283Labels = Sparse.eval nodeValue1283 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1283) = mixedMoment B node1283 node1283Labels := rfl
  simpa [nodeValue1283, Sparse.eval] using hc.symm

theorem sound1284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1284 node1284Labels = Sparse.eval nodeValue1284 (mixedVector B) := by
  have h := singleton1284 B _hB
  rw [sound136 B _hB _hF] at h
  norm_num [nodeValue1284, nodeValue136, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1285 node1285Labels = Sparse.eval nodeValue1285 (mixedVector B) := by
  have h := singleton1285 B _hB
  rw [sound57 B _hB _hF] at h
  norm_num [nodeValue1285, nodeValue57, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1286 node1286Labels = Sparse.eval nodeValue1286 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1286) = mixedMoment B node1286 node1286Labels := rfl
  simpa [nodeValue1286, Sparse.eval] using hc.symm

theorem sound1287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1287 node1287Labels = Sparse.eval nodeValue1287 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1287) = mixedMoment B node1287 node1287Labels := rfl
  simpa [nodeValue1287, Sparse.eval] using hc.symm

theorem sound1288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1288 node1288Labels = Sparse.eval nodeValue1288 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1288) = mixedMoment B node1288 node1288Labels := rfl
  simpa [nodeValue1288, Sparse.eval] using hc.symm

theorem sound1289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1289 node1289Labels = Sparse.eval nodeValue1289 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1289) = mixedMoment B node1289 node1289Labels := rfl
  simpa [nodeValue1289, Sparse.eval] using hc.symm

theorem sound1290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1290 node1290Labels = Sparse.eval nodeValue1290 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1290) = mixedMoment B node1290 node1290Labels := rfl
  simpa [nodeValue1290, Sparse.eval] using hc.symm

theorem sound1291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1291 node1291Labels = Sparse.eval nodeValue1291 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1291) = mixedMoment B node1291 node1291Labels := rfl
  simpa [nodeValue1291, Sparse.eval] using hc.symm

theorem sound1292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1292 node1292Labels = Sparse.eval nodeValue1292 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1292) = mixedMoment B node1292 node1292Labels := rfl
  simpa [nodeValue1292, Sparse.eval] using hc.symm

theorem sound1293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1293 node1293Labels = Sparse.eval nodeValue1293 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1293) = mixedMoment B node1293 node1293Labels := rfl
  simpa [nodeValue1293, Sparse.eval] using hc.symm

theorem sound1294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1294 node1294Labels = Sparse.eval nodeValue1294 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1294) = mixedMoment B node1294 node1294Labels := rfl
  simpa [nodeValue1294, Sparse.eval] using hc.symm

theorem sound1295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1295 node1295Labels = Sparse.eval nodeValue1295 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1295) = mixedMoment B node1295 node1295Labels := rfl
  simpa [nodeValue1295, Sparse.eval] using hc.symm

theorem sound1296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1296 node1296Labels = Sparse.eval nodeValue1296 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1296) = mixedMoment B node1296 node1296Labels := rfl
  simpa [nodeValue1296, Sparse.eval] using hc.symm

theorem sound1297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1297 node1297Labels = Sparse.eval nodeValue1297 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1297) = mixedMoment B node1297 node1297Labels := rfl
  simpa [nodeValue1297, Sparse.eval] using hc.symm

theorem sound1298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1298 node1298Labels = Sparse.eval nodeValue1298 (mixedVector B) := by
  have h := singleton1298 B _hB
  rw [sound151 B _hB _hF] at h
  norm_num [nodeValue1298, nodeValue151, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1299 node1299Labels = Sparse.eval nodeValue1299 (mixedVector B) := by
  have h := singleton1299 B _hB
  rw [sound155 B _hB _hF] at h
  norm_num [nodeValue1299, nodeValue155, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1300 node1300Labels = Sparse.eval nodeValue1300 (mixedVector B) := by
  have h := singleton1300 B _hB
  rw [sound156 B _hB _hF] at h
  norm_num [nodeValue1300, nodeValue156, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1301 node1301Labels = Sparse.eval nodeValue1301 (mixedVector B) := by
  have h := singleton1301 B _hB
  rw [sound157 B _hB _hF] at h
  norm_num [nodeValue1301, nodeValue157, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1302 node1302Labels = Sparse.eval nodeValue1302 (mixedVector B) := by
  have h := singleton1302 B _hB
  rw [sound152 B _hB _hF] at h
  norm_num [nodeValue1302, nodeValue152, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1303 node1303Labels = Sparse.eval nodeValue1303 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1303) = mixedMoment B node1303 node1303Labels := rfl
  simpa [nodeValue1303, Sparse.eval] using hc.symm

theorem sound1304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1304 node1304Labels = Sparse.eval nodeValue1304 (mixedVector B) := by
  have h := singleton1304 B _hB
  rw [sound158 B _hB _hF] at h
  norm_num [nodeValue1304, nodeValue158, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1305 node1305Labels = Sparse.eval nodeValue1305 (mixedVector B) := by
  have h := singleton1305 B _hB
  rw [sound156 B _hB _hF] at h
  norm_num [nodeValue1305, nodeValue156, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1306 node1306Labels = Sparse.eval nodeValue1306 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1306) = mixedMoment B node1306 node1306Labels := rfl
  simpa [nodeValue1306, Sparse.eval] using hc.symm

theorem sound1307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1307 node1307Labels = Sparse.eval nodeValue1307 (mixedVector B) := by
  have h := singleton1307 B _hB
  rw [sound158 B _hB _hF] at h
  norm_num [nodeValue1307, nodeValue158, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1308 node1308Labels = Sparse.eval nodeValue1308 (mixedVector B) := by
  have h := singleton1308 B _hB
  rw [sound154 B _hB _hF] at h
  norm_num [nodeValue1308, nodeValue154, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1309 node1309Labels = Sparse.eval nodeValue1309 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1309) = mixedMoment B node1309 node1309Labels := rfl
  simpa [nodeValue1309, Sparse.eval] using hc.symm

theorem sound1310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1310 node1310Labels = Sparse.eval nodeValue1310 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1310) = mixedMoment B node1310 node1310Labels := rfl
  simpa [nodeValue1310, Sparse.eval] using hc.symm

theorem sound1311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1311 node1311Labels = Sparse.eval nodeValue1311 (mixedVector B) := by
  have h := singleton1311 B _hB
  rw [sound160 B _hB _hF] at h
  norm_num [nodeValue1311, nodeValue160, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1312 node1312Labels = Sparse.eval nodeValue1312 (mixedVector B) := by
  have h := singleton1312 B _hB
  rw [sound161 B _hB _hF] at h
  norm_num [nodeValue1312, nodeValue161, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1313 node1313Labels = Sparse.eval nodeValue1313 (mixedVector B) := by
  have h := singleton1313 B _hB
  rw [sound162 B _hB _hF] at h
  norm_num [nodeValue1313, nodeValue162, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1314 node1314Labels = Sparse.eval nodeValue1314 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1314) = mixedMoment B node1314 node1314Labels := rfl
  simpa [nodeValue1314, Sparse.eval] using hc.symm

theorem sound1315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1315 node1315Labels = Sparse.eval nodeValue1315 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1315) = mixedMoment B node1315 node1315Labels := rfl
  simpa [nodeValue1315, Sparse.eval] using hc.symm

theorem sound1316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1316 node1316Labels = Sparse.eval nodeValue1316 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1316) = mixedMoment B node1316 node1316Labels := rfl
  simpa [nodeValue1316, Sparse.eval] using hc.symm

theorem sound1317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1317 node1317Labels = Sparse.eval nodeValue1317 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1317) = mixedMoment B node1317 node1317Labels := rfl
  simpa [nodeValue1317, Sparse.eval] using hc.symm

theorem sound1318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1318 node1318Labels = Sparse.eval nodeValue1318 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1318) = mixedMoment B node1318 node1318Labels := rfl
  simpa [nodeValue1318, Sparse.eval] using hc.symm

theorem sound1319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1319 node1319Labels = Sparse.eval nodeValue1319 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1319) = mixedMoment B node1319 node1319Labels := rfl
  simpa [nodeValue1319, Sparse.eval] using hc.symm

theorem sound1320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1320 node1320Labels = Sparse.eval nodeValue1320 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1320) = mixedMoment B node1320 node1320Labels := rfl
  simpa [nodeValue1320, Sparse.eval] using hc.symm

theorem sound1321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1321 node1321Labels = Sparse.eval nodeValue1321 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1321) = mixedMoment B node1321 node1321Labels := rfl
  simpa [nodeValue1321, Sparse.eval] using hc.symm

theorem sound1322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1322 node1322Labels = Sparse.eval nodeValue1322 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1322) = mixedMoment B node1322 node1322Labels := rfl
  simpa [nodeValue1322, Sparse.eval] using hc.symm

theorem sound1323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1323 node1323Labels = Sparse.eval nodeValue1323 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1323) = mixedMoment B node1323 node1323Labels := rfl
  simpa [nodeValue1323, Sparse.eval] using hc.symm

theorem sound1324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1324 node1324Labels = Sparse.eval nodeValue1324 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1324) = mixedMoment B node1324 node1324Labels := rfl
  simpa [nodeValue1324, Sparse.eval] using hc.symm

theorem sound1325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1325 node1325Labels = Sparse.eval nodeValue1325 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1325) = mixedMoment B node1325 node1325Labels := rfl
  simpa [nodeValue1325, Sparse.eval] using hc.symm

theorem sound1326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1326 node1326Labels = Sparse.eval nodeValue1326 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1326) = mixedMoment B node1326 node1326Labels := rfl
  simpa [nodeValue1326, Sparse.eval] using hc.symm

theorem sound1327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1327 node1327Labels = Sparse.eval nodeValue1327 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1327) = mixedMoment B node1327 node1327Labels := rfl
  simpa [nodeValue1327, Sparse.eval] using hc.symm

theorem sound1328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1328 node1328Labels = Sparse.eval nodeValue1328 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1328) = mixedMoment B node1328 node1328Labels := rfl
  simpa [nodeValue1328, Sparse.eval] using hc.symm

theorem sound1329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1329 node1329Labels = Sparse.eval nodeValue1329 (mixedVector B) := by
  simpa only [nodeValue1329, Sparse.eval_nil] using zero1329 B _hB _hF

theorem sound1330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1330 node1330Labels = Sparse.eval nodeValue1330 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1330) = mixedMoment B node1330 node1330Labels := rfl
  simpa [nodeValue1330, Sparse.eval] using hc.symm

theorem sound1331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1331 node1331Labels = Sparse.eval nodeValue1331 (mixedVector B) := by
  simpa only [nodeValue1331, Sparse.eval_nil] using zero1331 B _hB _hF

theorem sound1332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1332 node1332Labels = Sparse.eval nodeValue1332 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1332) = mixedMoment B node1332 node1332Labels := rfl
  simpa [nodeValue1332, Sparse.eval] using hc.symm

theorem sound1333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1333 node1333Labels = Sparse.eval nodeValue1333 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1333) = mixedMoment B node1333 node1333Labels := rfl
  simpa [nodeValue1333, Sparse.eval] using hc.symm

theorem sound1334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1334 node1334Labels = Sparse.eval nodeValue1334 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1334) = mixedMoment B node1334 node1334Labels := rfl
  simpa [nodeValue1334, Sparse.eval] using hc.symm

theorem sound1335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1335 node1335Labels = Sparse.eval nodeValue1335 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1335) = mixedMoment B node1335 node1335Labels := rfl
  simpa [nodeValue1335, Sparse.eval] using hc.symm

theorem sound1336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1336 node1336Labels = Sparse.eval nodeValue1336 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1336) = mixedMoment B node1336 node1336Labels := rfl
  simpa [nodeValue1336, Sparse.eval] using hc.symm

theorem sound1337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1337 node1337Labels = Sparse.eval nodeValue1337 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1337) = mixedMoment B node1337 node1337Labels := rfl
  simpa [nodeValue1337, Sparse.eval] using hc.symm

theorem sound1338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1338 node1338Labels = Sparse.eval nodeValue1338 (mixedVector B) := by
  have hc : mixedVector B (Sum.inr 1338) = mixedMoment B node1338 node1338Labels := rfl
  simpa [nodeValue1338, Sparse.eval] using hc.symm

theorem sound1339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1339 node1339Labels = Sparse.eval nodeValue1339 (mixedVector B) := by
  have h := singleton1339 B _hB
  rw [sound63 B _hB _hF] at h
  norm_num [nodeValue1339, nodeValue63, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1340 node1340Labels = Sparse.eval nodeValue1340 (mixedVector B) := by
  have h := singleton1340 B _hB
  rw [sound66 B _hB _hF] at h
  norm_num [nodeValue1340, nodeValue66, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1341 node1341Labels = Sparse.eval nodeValue1341 (mixedVector B) := by
  have h := singleton1341 B _hB
  rw [sound61 B _hB _hF] at h
  norm_num [nodeValue1341, nodeValue61, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1342 node1342Labels = Sparse.eval nodeValue1342 (mixedVector B) := by
  have h := singleton1342 B _hB
  rw [sound64 B _hB _hF] at h
  norm_num [nodeValue1342, nodeValue64, Sparse.eval] at h ⊢
  linarith only [h]

theorem sound1343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B)
    (_hF : AllTransitionsFourierZero B) :
    mixedMoment B node1343 node1343Labels = Sparse.eval nodeValue1343 (mixedVector B) := by
  have h := singleton1343 B _hB
  rw [sound68 B _hB _hF] at h
  norm_num [nodeValue1343, nodeValue68, Sparse.eval] at h ⊢
  linarith only [h]

end MUB6.Certificate.MixedSemantics

end OAI
