import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubic

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor

open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

theorem cubic_hom_ext {V : Type u} [AddCommGroup V] [Module E V] (n : ℕ)
    (f g : (complex k A B P Q).X n →ₗ[E] V)
    (h : ∀ (ij : Diagonal n) (x : summands k A B P Q n ij),
      f (cubicInsert k A B P Q n ij x) = g (cubicInsert k A B P Q n ij x)) : f = g := by
  have hh : f.comp (termDirectSumEquiv k A B P Q n).symm.toLinearMap =
      g.comp (termDirectSumEquiv k A B P Q n).symm.toLinearMap := by
    apply DFinsupp.lhom_ext
    intro ij x
    exact h ij x
  apply LinearMap.ext
  intro x
  have hx := DFunLike.congr_fun hh (termDirectSumEquiv k A B P Q n x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hx

theorem map_interchange {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (g : N ⟶ N') (x : moduleObject k A B M N) :
    map k A B f.hom (LinearMap.id : N' →ₗ[B] N')
      (map k A B (LinearMap.id : M →ₗ[A] M) g.hom x) =
    map k A B (LinearMap.id : M' →ₗ[A] M') g.hom
      (map k A B f.hom (LinearMap.id : N →ₗ[B] N) x) := by
  have h : mapHom k A B (𝟙 M) g ≫ mapHom k A B f (𝟙 N') =
      mapHom k A B f (𝟙 N) ≫ mapHom k A B (𝟙 M') g := by
    rw [← mapHom_comp, ← mapHom_comp]
    simp only [Category.id_comp, Category.comp_id]
  exact congrArg (fun t => t.hom x) h

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)

theorem cubic_commute (n : ℕ) :
    (firstCubic k A B P Q p n).comp (secondCubic k A B P Q r (n+3)) =
      (secondCubic k A B P Q r n).comp (firstCubic k A B P Q p (n+3)) := by
  apply cubic_hom_ext k A B P Q (n+3+3)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert, secondCubic_insert]
  rcases i with _ | (_ | (_ | i)) <;> rcases j with _ | (_ | (_ | j))
  all_goals simp only [firstCubicEntry, secondCubicEntry, LinearMap.zero_apply,
    LinearMap.comp_apply, firstCubic_insert, secondCubic_insert, map_zero]
  exact congrArg (cubicInsert k A B P Q n ⟨(i,j), by omega⟩)
    (map_interchange k A B (p i) (r j) x)

end ArExplicit.ExternalTensor

end

end OAI
