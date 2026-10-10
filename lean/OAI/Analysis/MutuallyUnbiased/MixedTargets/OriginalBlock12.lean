import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock12 : Integer.Sparse (Fin 2886) := [(384, -4367116800), (385, -7681584000), (386, 13595421600), (387, -41996073600), (388, -3382263360), (389, 49787942400), (390, 62829660000), (391, 22394548800), (392, 7681584000), (393, -984853440), (394, 8297990400), (395, -8088133200), (396, -4263292800), (397, -3591436800), (398, -31722650400), (399, -3021984000), (400, -10020873120), (401, 17944001280), (402, -1539187200), (403, -24958425600), (404, -7805568000), (405, -6949261440), (406, 33191961600), (407, 72531276000), (408, -55627355000), (409, -19406008800), (410, -84224625600), (411, 4891350000), (412, 4593000600), (413, 5899104000), (414, 5839412600), (415, -5899104000)]

def originalBlock12 : Integer.Sparse OriginalKey := [(Sum.inl 10, 89720006400), (Sum.inl 12, -50104365600), (Sum.inl 27, -15109920000), (Sum.inl 29, -21316464000), (Sum.inl 101, -17957184000), (Sum.inl 114, -40440666000), (Sum.inl 123, -4924267200), (Sum.inl 142, -158613252000), (Sum.inl 167, -34746307200), (Sum.inl 184, -39027840000), (Sum.inl 229, -7695936000), (Sum.inl 240, -124792128000), (Sum.inl 278, 111972744000), (Sum.inl 280, 314148300000), (Sum.inl 282, -421123128000), (Sum.inl 288, -16911316800), (Sum.inl 309, 29197063000), (Sum.inl 313, 38407920000), (Sum.inl 325, -29495520000), (Sum.inl 356, -21835584000), (Sum.inl 398, -38407920000), (Sum.inl 426, 24456750000), (Sum.inl 427, 362656380000), (Sum.inl 428, 22965003000), (Sum.inl 429, 29495520000), (Sum.inl 432, -97030044000), (Sum.inl 434, 414899520000), (Sum.inl 435, -278136775000), (Sum.inl 446, -209980368000), (Sum.inl 467, 67977108000), (Sum.inr 6, 41489952000)]

theorem originalBlockCheck12 : originalBlock12 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock12 keyMomentRows) := by decide +kernel

theorem originalBlockEval12 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock12 x =
      Integer.Sparse.eval keyPolynomialBlock12 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck12, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
