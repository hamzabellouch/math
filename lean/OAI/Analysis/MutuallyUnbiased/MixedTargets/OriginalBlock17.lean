import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock17 : Integer.Sparse (Fin 2886) := [(544, 5297333760), (545, -84562560), (546, -8701539840), (547, -1872743040), (548, -2536649280), (549, -50415792000), (550, -3081579840), (551, 50415792000), (552, 13244495680), (553, -5277668160), (554, -1684920960), (555, 1684920960), (556, 372539520), (557, 1684920960), (558, -1872743040), (559, -745079040), (560, -1684920960), (561, 6383759040), (562, -10337482560), (563, -7602509760), (564, 9079309440), (565, -5277668160), (566, 372539520), (567, 84562560), (568, -6052872960), (569, -4900762080), (570, 5465156040), (571, 4836802720), (572, 25540245600), (573, 30498751440), (574, 824652960), (575, -22643952240)]

def originalBlock17 : Integer.Sparse OriginalKey := [(Sum.inl 40, 31918795200), (Sum.inl 66, -30264364800), (Sum.inl 72, 422812800), (Sum.inl 96, 45396547200), (Sum.inl 112, -51687412800), (Sum.inl 114, -113219761200), (Sum.inl 117, 4123264800), (Sum.inl 133, -9363715200), (Sum.inl 139, 127701228000), (Sum.inl 140, 152493757200), (Sum.inl 145, 27325780200), (Sum.inl 147, 24184013600), (Sum.inl 148, -24503810400), (Sum.inl 207, -43507699200), (Sum.inl 211, -422812800), (Sum.inl 224, 26486668800), (Sum.inl 283, 8424604800), (Sum.inl 286, -12683246400), (Sum.inl 287, -8424604800), (Sum.inl 290, -15407899200), (Sum.inl 334, 1862697600), (Sum.inl 336, -3725395200), (Sum.inl 339, -26388340800), (Sum.inl 341, -26388340800), (Sum.inl 344, 1862697600), (Sum.inl 351, -8424604800), (Sum.inl 352, 8424604800), (Sum.inl 353, -252078960000), (Sum.inl 355, 252078960000), (Sum.inl 405, 66222478400), (Sum.inl 407, -38012548800), (Sum.inl 412, -9363715200)]

theorem originalBlockCheck17 : originalBlock17 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock17 keyMomentRows) := by decide +kernel

theorem originalBlockEval17 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock17 x =
      Integer.Sparse.eval keyPolynomialBlock17 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck17, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
