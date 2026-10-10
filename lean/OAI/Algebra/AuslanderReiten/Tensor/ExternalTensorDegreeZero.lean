import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorBottom

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct ModuleCat.Algebra
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

theorem bottomProjection_zero_injective : Function.Injective (bottomProjection k A B P Q 0) := by
  intro x y h
  apply (termDirectSumEquiv k A B P Q 0).injective
  apply DFinsupp.ext
  intro ij
  obtain ⟨⟨i,j⟩,hij⟩ := ij
  have hi : i = 0 := by omega
  have hj : j = 0 := by omega
  subst i; subst j
  exact h

theorem bottomInsert_projection_zero (x : (complex k A B P Q).X 0) :
    cubicInsert k A B P Q 0 ⟨(0,0),rfl⟩ (bottomProjection k A B P Q 0 x) = x := by
  apply bottomProjection_zero_injective k A B P Q
  exact bottomProjection_bottom k A B P Q 0 _

end ArExplicit.ExternalTensor

end

end OAI
