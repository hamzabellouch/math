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
local notation "E" => A ⊗[k] B

private theorem hom_zero_apply {M N : ModuleCat.{u} E} (x : M) : (0 : M ⟶ N) x = 0 := rfl

variable (p : (n : ℕ) → P.X (n+3) ⟶ P.X n)
variable (r : (n : ℕ) → Q.X (n+3) ⟶ Q.X n)
variable (hp : ∀ n, p (n+1) ≫ P.d (n+1) n = P.d (n+4) (n+3) ≫ p n)
variable (hr : ∀ n, r (n+1) ≫ Q.d (n+1) n = Q.d (n+4) (n+3) ≫ r n)

include hp in
private theorem first_map_chain (i j : ℕ)
    (x : moduleObject k A B (P.X (i+4)) (Q.X j)) :
    map k A B (P.d (i+1) i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j)
      (map k A B (p (i+1)).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) =
    map k A B (p i).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j)
      (map k A B (P.d (i+4) (i+3)).hom (LinearMap.id : Q.X j →ₗ[B] Q.X j) x) := by
  have hh := congrArg (fun f => mapHom k A B f (𝟙 (Q.X j))) (hp i)
  rw [show 𝟙 (Q.X j) = 𝟙 (Q.X j) ≫ 𝟙 (Q.X j) from (Category.id_comp _).symm,
    mapHom_comp, mapHom_comp] at hh
  exact congrArg (fun f => f.hom x) hh

variable [CharP k 2]

include hp in

theorem firstCubic_chain (n : ℕ) :
    ((complex k A B P Q).d (n+1) n).hom.comp (firstCubic k A B P Q p (n+1)) =
      (firstCubic k A B P Q p n).comp ((complex k A B P Q).d (n+4) (n+3)).hom := by
  apply cubic_hom_ext k A B P Q (n+4)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, firstCubic_insert, cubicInsert_d]
  rcases i with _ | (_ | (_ | (_ | i))) <;> rcases j with _ | j
  all_goals simp (disch := omega) only [firstCubicEntry, LinearMap.comp_apply, map_zero,
    cubicInsert_d, horizontal_zero, vertical_zero, hom_zero_apply,
    horizontal_succ_apply, vertical_succ_apply, map_add, add_zero, zero_add,
    firstCubic_insert, LinearMap.zero_apply]
  all_goals simp only [first_map_chain k A B P Q p hp, map_interchange k A B]

omit [CharP k 2] in
include hr in
private theorem second_map_chain (i j : ℕ)
    (x : moduleObject k A B (P.X i) (Q.X (j+4))) :
    map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+1) j).hom
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r (j+1)).hom x) =
    map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (r j).hom
      (map k A B (LinearMap.id : P.X i →ₗ[A] P.X i) (Q.d (j+4) (j+3)).hom x) := by
  have hh := congrArg (fun f => mapHom k A B (𝟙 (P.X i)) f) (hr j)
  rw [show 𝟙 (P.X i) = 𝟙 (P.X i) ≫ 𝟙 (P.X i) from (Category.id_comp _).symm,
    mapHom_comp, mapHom_comp] at hh
  exact congrArg (fun f => f.hom x) hh

include hr in

theorem secondCubic_chain (n : ℕ) :
    ((complex k A B P Q).d (n+1) n).hom.comp (secondCubic k A B P Q r (n+1)) =
      (secondCubic k A B P Q r n).comp ((complex k A B P Q).d (n+4) (n+3)).hom := by
  apply cubic_hom_ext k A B P Q (n+4)
  rintro ⟨⟨i,j⟩,h⟩ x
  simp only [LinearMap.comp_apply, secondCubic_insert, cubicInsert_d]
  rcases j with _ | (_ | (_ | (_ | j))) <;> rcases i with _ | i
  all_goals simp (disch := omega) only [secondCubicEntry, LinearMap.comp_apply, map_zero,
    cubicInsert_d, horizontal_zero, vertical_zero, hom_zero_apply,
    horizontal_succ_apply, vertical_succ_apply, map_add, add_zero, zero_add,
    secondCubic_insert, LinearMap.zero_apply]
  all_goals simp only [second_map_chain k A B P Q r hr, map_interchange k A B]

end ArExplicit.ExternalTensor

end

end OAI
