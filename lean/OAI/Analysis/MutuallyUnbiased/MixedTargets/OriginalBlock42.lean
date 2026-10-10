import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock42 : Integer.Sparse (Fin 2886) := [(1344, -2970057600), (1345, -26715732480), (1346, -4533575040), (1347, 52311168000), (1348, -52311168000), (1349, -7891734240), (1350, -22104192000), (1351, 15341940000), (1352, -74367161280), (1353, -37363283520), (1354, -1506232320), (1355, 2970057600), (1356, -25064469120), (1357, 25436791680), (1358, 966442560), (1359, -28143720000), (1360, -105367920000), (1361, -25225598400), (1362, 71961876000), (1363, 120667120320), (1364, 55501712640), (1365, -40269264000), (1366, -33493728000), (1367, 16369293120), (1368, 50334995520), (1369, -26364576000), (1370, -11764436160), (1371, 6565147200), (1372, -3582112320), (1373, -36428678400), (1374, 61334378880), (1375, -7770451200)]

def originalBlock42 : Integer.Sparse OriginalKey := [(Sum.inl 1294, 76709700000), (Sum.inl 1297, -39458671200), (Sum.inl 2105, -14850288000), (Sum.inl 2109, -7531161600), (Sum.inl 2112, -133578662400), (Sum.inl 2116, 14850288000), (Sum.inl 2266, -182143392000), (Sum.inl 2294, -140718600000), (Sum.inl 2589, 4832212800), (Sum.inl 2590, 127183958400), (Sum.inl 2724, 306671894400), (Sum.inl 2744, -526839600000), (Sum.inl 2764, -125322345600), (Sum.inl 2765, -186816417600), (Sum.inl 2782, -371835806400), (Sum.inl 2783, -110520960000), (Sum.inl 2954, -22667875200), (Sum.inl 3040, -38852256000), (Sum.inl 3056, -126127992000), (Sum.inl 3079, -201346320000), (Sum.inl 3378, -17910561600), (Sum.inl 3379, -58822180800), (Sum.inl 3395, 251674977600), (Sum.inl 3396, 277508563200), (Sum.inl 3505, 32825736000), (Sum.inl 3506, -131822880000), (Sum.inl 3541, -167468640000), (Sum.inl 3573, 81846465600), (Sum.inl 3584, 603335601600), (Sum.inl 3626, 359809380000), (Sum.inl 3787, -261555840000), (Sum.inl 3876, 261555840000)]

theorem originalBlockCheck42 : originalBlock42 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock42 keyMomentRows) := by decide +kernel

theorem originalBlockEval42 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock42 x =
      Integer.Sparse.eval keyPolynomialBlock42 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck42, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
