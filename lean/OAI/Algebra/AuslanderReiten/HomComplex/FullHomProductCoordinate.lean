import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductReindex

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory CochainComplex CochainComplex.HomComplex
universe u w
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {a b c d : ℤ}

theorem fullHomProduct_coordinate
    (h : a=b) (h₁ : b+c=d) (h₂ : a+c=d)
    {x : CohomologyClass K L a} {y : CohomologyClass K L b}
    {p : CohomologyClass L M c} {z : CohomologyClass K M d}
    (hy : y = TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) h x)
    (hz : z = TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₁ (fullHomProduct y p)) :
    z = TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₂ (fullHomProduct x p) := by
  rw [hz, hy, fullHomProduct_reindex_left]

end ArExplicit.CompleteComparison

end

end OAI
