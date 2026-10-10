import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProductLinear
import OAI.Algebra.AuslanderReiten.Complete.TateKoszul

namespace OAI

noncomputable section
namespace ArExplicit.CompleteComparison
open CategoryTheory
open CochainComplex CochainComplex.HomComplex
universe u w
variable {k : Type u} [Field k]
variable {C : Type w} [Category.{u} C] [Preadditive C] [Linear k C]
variable {K L M : CochainComplex C ℤ} {a b c d : ℤ}

theorem fullHomProduct_reindex_left (h : a=b) (h₁ : b+c=d) (h₂ : a+c=d)
    (x : CohomologyClass K L a) (y : CohomologyClass L M c) :
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₁
      (fullHomProduct (TateKoszul.degreeEquiv (k := k) (CohomologyClass K L) h x) y) =
    TateKoszul.degreeEquiv (k := k) (CohomologyClass K M) h₂ (fullHomProduct x y) := by
  subst b
  rfl

theorem degreeEquiv_trans_apply {H : ℤ → Type u} [∀ i, AddCommGroup (H i)] [∀ i, Module k (H i)]
    (h₁ : a=b) (h₂ : b=c) (x : H a) :
    TateKoszul.degreeEquiv (k := k) H h₂ (TateKoszul.degreeEquiv (k := k) H h₁ x) =
      TateKoszul.degreeEquiv (k := k) H (h₁.trans h₂) x := by
  subst b
  subst c
  rfl

end ArExplicit.CompleteComparison

end

end OAI
