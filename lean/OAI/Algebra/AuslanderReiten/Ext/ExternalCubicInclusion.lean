import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorCubicDifferential

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (p : ∀ n, P.X (n+3) ⟶ P.X n) (r : ∀ n, Q.X (n+3) ⟶ Q.X n)

theorem inclusion_firstCubic (i j n : ℕ) (h : i+j=n+3) :
    inclusion k A B P Q i j (n+3) h ≫ ModuleCat.ofHom (firstCubic k A B P Q p n) =
      ModuleCat.ofHom (firstCubicEntry k A B P Q p n ⟨(i,j),h⟩) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change firstCubic k A B P Q p n ((inclusion k A B P Q i j (n+3) h).hom x) = _
  rw [inclusion_eq_cubicInsert, firstCubic_insert]
  rfl

theorem inclusion_secondCubic (i j n : ℕ) (h : i+j=n+3) :
    inclusion k A B P Q i j (n+3) h ≫ ModuleCat.ofHom (secondCubic k A B P Q r n) =
      ModuleCat.ofHom (secondCubicEntry k A B P Q r n ⟨(i,j),h⟩) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change secondCubic k A B P Q r n ((inclusion k A B P Q i j (n+3) h).hom x) = _
  rw [inclusion_eq_cubicInsert, secondCubic_insert]
  rfl

@[simp] theorem firstCubicEntry_high (i j n : ℕ) (h : i+3+j=n+3) :
    ModuleCat.ofHom (firstCubicEntry k A B P Q p n ⟨(i+3,j),h⟩) =
      mapHom k A B (p i) (𝟙 (Q.X j)) ≫
        inclusion k A B P Q i j n (by omega) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cubicInsert k A B P Q n ⟨(i,j),_⟩ (map k A B (p i).hom LinearMap.id x) = _
  rw [← inclusion_eq_cubicInsert]
  rfl

@[simp] theorem secondCubicEntry_high (i j n : ℕ) (h : i+(j+3)=n+3) :
    ModuleCat.ofHom (secondCubicEntry k A B P Q r n ⟨(i,j+3),h⟩) =
      mapHom k A B (𝟙 (P.X i)) (r j) ≫
        inclusion k A B P Q i j n (by omega) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change cubicInsert k A B P Q n ⟨(i,j),_⟩ (map k A B LinearMap.id (r j).hom x) = _
  rw [← inclusion_eq_cubicInsert]
  rfl

end ArExplicit.ExternalTensor

end

end OAI
