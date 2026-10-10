import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock43 : Integer.Sparse (Fin 2886) := [(1376, 24607056000), (1377, -91344896000), (1378, 40644088560), (1379, 37128933120), (1380, -8551584000), (1381, 116316597600), (1382, 13325332000), (1383, 65205118080), (1384, -39856968000), (1385, -54907276800), (1386, -11396067600), (1387, -3560809200), (1388, -24607056000), (1389, -5177069760), (1390, -36703621600), (1391, -36738299360), (1392, -20382734800), (1393, -47565599040), (1394, -11371866400), (1395, 7127592000), (1396, 11104874400), (1397, 3560809200), (1398, 291193200), (1399, 72370704000), (1400, 81295103040), (1401, 48699081600), (1402, -24607056000), (1403, 71909843360), (1404, -55199090640), (1405, 9746162880), (1406, 16078464000), (1407, -140203089600)]

def originalBlock43 : Integer.Sparse OriginalKey := [(Sum.inl 2279, 361853520000), (Sum.inl 2732, 406475515200), (Sum.inl 2864, 35637960000), (Sum.inl 2867, -237827995200), (Sum.inl 2885, -183691496800), (Sum.inl 2888, -25885348800), (Sum.inl 3045, 243495408000), (Sum.inl 3066, -42757920000), (Sum.inl 3069, 80392320000), (Sum.inl 3379, 48730814400), (Sum.inl 3395, 185644665600), (Sum.inl 3535, 123035280000), (Sum.inl 3541, -123035280000), (Sum.inl 3584, -123035280000), (Sum.inl 3720, 1455966000), (Sum.inl 3722, -274536384000), (Sum.inl 3730, -199284840000), (Sum.inl 3733, -101913674000), (Sum.inl 3809, -456724480000), (Sum.inl 3814, 359549216800), (Sum.inl 3839, 581582988000), (Sum.inl 3841, -701015448000), (Sum.inl 3877, -459513561200), (Sum.inl 3946, 55524372000), (Sum.inl 3949, -56859332000), (Sum.inl 3954, 17804046000), (Sum.inl 3959, 203220442800), (Sum.inl 3972, 66626660000), (Sum.inl 4022, 326025590400), (Sum.inl 4024, -56980338000), (Sum.inl 4025, -17804046000)]

theorem originalBlockCheck43 : originalBlock43 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock43 keyMomentRows) := by decide +kernel

theorem originalBlockEval43 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock43 x =
      Integer.Sparse.eval keyPolynomialBlock43 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck43, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
