import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock89 : Integer.Sparse (Fin 2886) := [(2848, 198699576000), (2849, 146133607680), (2850, -35628653280), (2851, -198699576000), (2852, 27259584000), (2853, 11397799200), (2854, -11136233600), (2855, 15069535200), (2856, -18178405600), (2857, 46994318640), (2858, 28414555200), (2859, 6419160960), (2860, 37829664000), (2861, -26084940672), (2862, -49229709120), (2863, -56475672000), (2864, 6893352000), (2865, 56475672000), (2866, -28414555200), (2867, -6106736640), (2868, -37829664000), (2869, -16844256000), (2870, 2393825280), (2871, 10373020800), (2872, -37829664000), (2873, -157695480000), (2874, 157695480000), (2875, -7631160000), (2876, 37829664000), (2877, -31119062400), (2878, -5614752000), (2879, -7075401600)]

def originalBlock89 : Integer.Sparse OriginalKey := [(Sum.inl 1501, -16844256000), (Sum.inl 1502, -37829664000), (Sum.inl 1504, -31119062400), (Sum.inl 1508, 37829664000), (Sum.inl 1699, -6106736640), (Sum.inl 1700, -28414555200), (Sum.inl 1709, -7631160000), (Sum.inl 2140, -5614752000), (Sum.inl 2142, -37829664000), (Sum.inl 2187, 28414555200), (Sum.inl 2192, 2393825280), (Sum.inl 2232, 37829664000), (Sum.inl 2233, 6419160960), (Sum.inl 2235, 46994318640), (Sum.inl 2240, 10373020800), (Sum.inl 2688, 56475672000), (Sum.inl 2690, -56475672000), (Sum.inl 3058, 6893352000), (Sum.inl 3059, -49229709120), (Sum.inl 3221, -26084940672), (Sum.inl 3257, 157695480000), (Sum.inl 3290, 27259584000), (Sum.inl 3291, -11136233600), (Sum.inl 3294, -198699576000), (Sum.inl 3297, -18178405600), (Sum.inl 3510, -7075401600), (Sum.inl 3516, 11397799200), (Sum.inl 3535, -35628653280), (Sum.inl 3554, -157695480000), (Sum.inl 3832, 198699576000), (Sum.inl 3835, 15069535200), (Sum.inl 4024, 146133607680), (Sum.inl 4149, -67377024000), (Sum.inl 4150, -124476249600), (Sum.inl 4169, -151318656000), (Sum.inl 4173, 151318656000), (Sum.inl 4473, -24426946560), (Sum.inl 4474, -30524640000), (Sum.inl 4494, -113658220800), (Sum.inl 4540, 225902688000), (Sum.inl 4542, 630781920000), (Sum.inl 4590, 109038336000), (Sum.inl 4591, -44544934400), (Sum.inl 4593, -72713622400), (Sum.inl 4603, -794798304000), (Sum.inl 4663, -22459008000), (Sum.inl 4677, -151318656000), (Sum.inl 4815, 9575301120), (Sum.inl 4830, 113658220800), (Sum.inl 4851, 41492083200), (Sum.inl 4863, 151318656000), (Sum.inl 4885, -78663118848), (Sum.inl 4886, 187977274560), (Sum.inl 4956, -28301606400), (Sum.inl 4964, -630781920000), (Sum.inl 4975, -225902688000), (Sum.inl 5097, 27573408000), (Sum.inl 5129, 45591196800), (Sum.inl 5266, -142514613120), (Sum.inl 5277, -196918836480), (Sum.inl 5377, 60278140800), (Sum.inl 5379, 794798304000), (Sum.inl 5445, 584534430720)]

theorem originalBlockCheck89 : originalBlock89 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock89 keyMomentRows) := by decide +kernel

theorem originalBlockEval89 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock89 x =
      Integer.Sparse.eval keyPolynomialBlock89 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck89, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
