import OAI.NumberTheory.Ostmann.Characters.ProductPriorSplit

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template.OneSidedPhase
open Construction
attribute [local instance] Classical.propDecidable

theorem productPrior_sum_cmean {I J Ω : Type*}
    [Fintype I] [Fintype J] [Fintype Ω] [DecidableEq I] [DecidableEq J]
    (μ : I → FinitePrior Ω) (ν : J → FinitePrior Ω)
    (F : ((I ⊕ J) → Ω) → ℂ) :
    (productPrior (Sum.elim μ ν)).cmean F =
      (productPrior ν).cmean (fun y => (productPrior μ).cmean (fun h => F (Sum.elim h y))) := by
  classical
  unfold FinitePrior.cmean
  rw [← (splitPriorSampleEquiv (Ω:=Ω) (Equiv.refl (I ⊕ J))).sum_comp
    (fun p => ((productPrior (Sum.elim μ ν)).mass p:ℂ)*F p)]
  simp only [Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro h hh
  change ((productPrior (Sum.elim μ ν)).mass
    (splitPriorSample (Equiv.refl (I ⊕ J)) y h):ℂ)*
    F (splitPriorSample (Equiv.refl (I ⊕ J)) y h) = _
  rw [productPrior_split_mass]
  simp only [Equiv.refl_apply,Sum.elim_inl,Sum.elim_inr,Complex.ofReal_mul,mul_assoc]
  rfl

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI
