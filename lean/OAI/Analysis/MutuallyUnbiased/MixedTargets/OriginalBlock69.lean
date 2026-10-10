import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock69 : Integer.Sparse (Fin 2886) := [(2208, 2325747648), (2209, 10174585920), (2210, 14458983120), (2211, 6983544192), (2212, 41118433920), (2213, 105727698240), (2214, 127482366800), (2215, 94717871040), (2216, -59917721280), (2217, 90265586880), (2218, 15186376800), (2219, 13468067520), (2220, 13111545984), (2221, -75491113920), (2222, 141650632560), (2223, 17611916400), (2224, 127434411360), (2225, 40687487520), (2226, 37452674880), (2227, 90834899520), (2228, -30881651760), (2229, 16489344000), (2230, 248886167040), (2231, -34073200800), (2232, 82874491680), (2233, -20093569560), (2234, -22251735600), (2235, 71848187280), (2236, 140375734080), (2237, 31275884160), (2238, -15890849280), (2239, 13876855680)]

def originalBlock69 : Integer.Sparse OriginalKey := [(Sum.inl 2144, 13111545984), (Sum.inl 2154, -22251735600), (Sum.inl 2155, -30881651760), (Sum.inl 2160, 9309291840), (Sum.inl 2176, -34073200800), (Sum.inl 2179, 10174585920), (Sum.inl 2194, 13468067520), (Sum.inl 2195, 15186376800), (Sum.inl 2196, 90265586880), (Sum.inl 2211, 82874491680), (Sum.inl 2212, 90834899520), (Sum.inl 2213, -20093569560), (Sum.inl 2217, 37452674880), (Sum.inl 2219, 14458983120), (Sum.inl 2231, 13876855680), (Sum.inl 2232, -15890849280), (Sum.inl 2233, 31275884160), (Sum.inl 2234, 140375734080), (Sum.inl 2235, 71848187280), (Sum.inl 2248, -75491113920), (Sum.inl 2249, -59917721280), (Sum.inl 2250, 141650632560), (Sum.inl 2251, 94717871040), (Sum.inl 2252, 17611916400), (Sum.inl 2253, 127482366800), (Sum.inl 2254, 105727698240), (Sum.inl 2255, 41118433920), (Sum.inl 2272, 16489344000), (Sum.inl 2273, 40687487520), (Sum.inl 2274, 248886167040), (Sum.inl 2280, 127434411360), (Sum.inl 4665, 52446183936), (Sum.inl 4667, 37237167360), (Sum.inl 4668, -89006942400), (Sum.inl 4669, -123526607040), (Sum.inl 4695, 55507422720), (Sum.inl 4698, -301964455680), (Sum.inl 4700, -239670885120), (Sum.inl 4703, 65957376000), (Sum.inl 4704, 162749950080), (Sum.inl 4756, -136292803200), (Sum.inl 4765, 40698343680), (Sum.inl 4773, 53872270080), (Sum.inl 4775, 331497966720), (Sum.inl 4776, 363339598080), (Sum.inl 4793, 57835932480), (Sum.inl 4795, -80374278240), (Sum.inl 4803, 60745507200), (Sum.inl 4816, 361062347520), (Sum.inl 4821, 149810699520), (Sum.inl 4852, 566602530240), (Sum.inl 4856, 995544668160), (Sum.inl 4863, -63563397120), (Sum.inl 4867, 378871484160), (Sum.inl 4878, 561502936320), (Sum.inl 4880, 422910792960), (Sum.inl 4884, 509737645440), (Sum.inl 4885, 195551202240), (Sum.inl 4886, 287392749120), (Sum.inl 4891, 509929467200), (Sum.inl 4892, 164473735680)]

theorem originalBlockCheck69 : originalBlock69 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock69 keyMomentRows) := by decide +kernel

theorem originalBlockEval69 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock69 x =
      Integer.Sparse.eval keyPolynomialBlock69 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck69, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
