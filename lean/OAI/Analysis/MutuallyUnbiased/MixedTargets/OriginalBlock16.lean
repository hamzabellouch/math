import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock16 : Integer.Sparse (Fin 2886) := [(512, -5899104000), (513, 31096581600), (514, -4891350000), (515, -4593000600), (516, 513062400), (517, 15986424960), (518, 4783584000), (519, 24893262720), (520, -8297990400), (521, -9701616000), (522, 22435393400), (523, 10342394400), (524, 21394965600), (525, -4891350000), (526, -4593000600), (527, -5899104000), (528, -14137403000), (529, 5899104000), (530, -31096581600), (531, 4891350000), (532, 4593000600), (533, -513062400), (534, -4531807200), (535, 19934159040), (536, -22430001600), (537, -14953334400), (538, 1099785600), (539, -1350411840), (540, -30273848640), (541, 10337482560), (542, 377769600), (543, 1350411840)]

def originalBlock16 : Integer.Sparse OriginalKey := [(Sum.inl 11, 99670795200), (Sum.inl 18, -74766672000), (Sum.inl 122, -155482908000), (Sum.inl 146, -22659036000), (Sum.inl 147, 155482908000), (Sum.inl 164, 124466313600), (Sum.inl 169, -112150008000), (Sum.inl 176, 23917920000), (Sum.inl 180, 6752059200), (Sum.inl 187, -151369243200), (Sum.inl 236, 51687412800), (Sum.inl 239, 79932124800), (Sum.inl 249, -6752059200), (Sum.inl 262, 1888848000), (Sum.inl 270, 5498928000), (Sum.inl 281, 106974828000), (Sum.inl 292, 24456750000), (Sum.inl 297, -48508080000), (Sum.inl 298, -24456750000), (Sum.inl 299, 22965003000), (Sum.inl 300, -22965003000), (Sum.inl 301, -29495520000), (Sum.inl 303, 29495520000), (Sum.inl 306, 51711972000), (Sum.inl 308, -70687015000), (Sum.inl 309, 112176967000), (Sum.inl 323, -24456750000), (Sum.inl 374, -22965003000), (Sum.inl 379, -29495520000), (Sum.inr 1, 2565312000), (Sum.inr 2, -2565312000), (Sum.inr 6, -41489952000)]

theorem originalBlockCheck16 : originalBlock16 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock16 keyMomentRows) := by decide +kernel

theorem originalBlockEval16 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock16 x =
      Integer.Sparse.eval keyPolynomialBlock16 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck16, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
