import OAI.Analysis.MutuallyUnbiased.MixedTargets.OriginalMerge5
import OAI.Analysis.MutuallyUnbiased.GramAssembly.Combined

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

abbrev originalPolynomial := originalNode89

theorem keyPolynomialCheck : keyPolynomialNode89 = GramAssembly.polynomial := by decide +kernel

theorem originalPolynomialEval (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalPolynomial x =
      Integer.Sparse.eval GramAssembly.polynomial (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalNodeEval89, keyPolynomialCheck]

end MUB6.Certificate.MixedTargetSemantics

end OAI
