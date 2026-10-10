import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock41 : Integer.Sparse (Fin 2886) := [(1312, -17018832400), (1313, 14328529440), (1314, 291193200), (1315, 23566032000), (1316, -58035288000), (1317, -49478184000), (1318, 58035288000), (1319, 52661520000), (1320, 17018832400), (1321, 37409533440), (1322, -291193200), (1323, 61018948800), (1324, 86787635040), (1325, 46598368320), (1326, -24973506720), (1327, 22104192000), (1328, 109088208000), (1329, 37691688960), (1330, -8201856960), (1331, 32595648000), (1332, 25460485440), (1333, -78060799680), (1334, 1506232320), (1335, -21544810560), (1336, -1362458880), (1337, 22670596800), (1338, 25670966400), (1339, 2266787520), (1340, -45977080320), (1341, 41107896000), (1342, 2266787520), (1343, -41107896000)]

def originalBlock41 : Integer.Sparse OriginalKey := [(Sum.inl 1264, 187047667200), (Sum.inl 2106, 7531161600), (Sum.inl 2110, -229885401600), (Sum.inl 2115, -124867533600), (Sum.inl 2569, -1455966000), (Sum.inl 2614, 1455966000), (Sum.inl 2617, -247390920000), (Sum.inl 2618, 263307600000), (Sum.inl 2620, 71642647200), (Sum.inl 2631, -290176440000), (Sum.inl 2632, -85094162000), (Sum.inl 2633, 290176440000), (Sum.inl 2635, 85094162000), (Sum.inl 2641, 117830160000), (Sum.inl 3582, 110520960000), (Sum.inl 3623, 128354832000), (Sum.inl 3633, 305094744000), (Sum.inl 3731, -107724052800), (Sum.inl 3732, -41009284800), (Sum.inl 3786, 113352984000), (Sum.inl 3789, 11333937600), (Sum.inl 3849, -6812294400), (Sum.inl 3850, -390303998400), (Sum.inl 3857, 162978240000), (Sum.inl 3875, -205539480000), (Sum.inl 3885, 199792382400), (Sum.inl 3886, 232991841600), (Sum.inl 3907, 433938175200), (Sum.inl 3910, 127302427200), (Sum.inl 3913, 545441040000), (Sum.inl 4010, 205539480000)]

theorem originalBlockCheck41 : originalBlock41 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock41 keyMomentRows) := by decide +kernel

theorem originalBlockEval41 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock41 x =
      Integer.Sparse.eval keyPolynomialBlock41 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck41, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
