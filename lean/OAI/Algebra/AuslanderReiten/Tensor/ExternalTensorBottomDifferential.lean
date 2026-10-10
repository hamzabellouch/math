import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorBottom

namespace OAI

noncomputable section
namespace ArExplicit.ExternalTensor
open CategoryTheory
open scoped TensorProduct
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P U : ChainComplex (ModuleCat.{u} A) ℕ) (Q V : ChainComplex (ModuleCat.{u} B) ℕ)
local notation "E" => A ⊗[k] B

private theorem hom_zero_apply {M N : ModuleCat.{u} E} (x : M) : (0 : M ⟶ N) x = 0 := rfl

theorem map_comp_apply {M₀ M₁ M₂ : ModuleCat.{u} A} {N₀ N₁ N₂ : ModuleCat.{u} B}
    (f : M₀ ⟶ M₁) (f' : M₁ ⟶ M₂) (g : N₀ ⟶ N₁) (g' : N₁ ⟶ N₂)
    (x : moduleObject k A B M₀ N₀) :
    map k A B f'.hom g'.hom (map k A B f.hom g.hom x) =
      map k A B (f ≫ f').hom (g ≫ g').hom x :=
  (congrArg (fun h => h.hom x) (mapHom_comp k A B f f' g g')).symm

@[simp] theorem map_zero_right_apply {M M' : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ M') (x : moduleObject k A B M N) :
    map k A B f.hom (0 : N →ₗ[B] N') x = 0 := by
  let y : M ⊗[k] N := x
  change TensorProduct.map (f.hom.restrictScalars k) (0 : N →ₗ[k] N') y = 0
  rw [TensorProduct.map_zero_right, LinearMap.zero_apply]

theorem bottomMap_d_target (s t : ℕ) (f : U.X s ⟶ P.X (t+1)) (g : V.X 0 ⟶ Q.X 0) :
    ((complex k A B P Q).d (t+1) t).hom.comp (bottomMap k A B P Q U V s (t+1) f g) =
      bottomMap k A B P Q U V s t (f ≫ P.d (t+1) t) g := by
  apply cubic_hom_ext k A B U V s
  rintro ⟨⟨i,j⟩,h⟩ x
  cases j with
  | zero =>
    have hi : i=s := by simpa using h
    subst i
    simp only [LinearMap.comp_apply, bottomMap_bottom, cubicInsert_d,
      horizontal_succ_apply k A B P Q t 0 t (Nat.add_zero t), vertical_zero,
      hom_zero_apply, add_zero]
    congr 1
    have hh := map_comp_apply k A B f (P.d (t+1) t) g (𝟙 (Q.X 0)) x
    simp only [Category.comp_id] at hh
    convert! hh using 1
  | succ j => simp only [LinearMap.comp_apply, bottomMap_positive, map_zero]

variable [CharP k 2]

theorem bottomMap_d_source (s t : ℕ) (f : U.X s ⟶ P.X t) (g : V.X 0 ⟶ Q.X 0)
    (hg : V.d 1 0 ≫ g = 0) :
    (bottomMap k A B P Q U V s t f g).comp ((complex k A B U V).d (s+1) s).hom =
      bottomMap k A B P Q U V (s+1) t (U.d (s+1) s ≫ f) g := by
  apply cubic_hom_ext k A B U V (s+1)
  rintro ⟨⟨i,j⟩,h⟩ x
  cases j with
  | zero =>
    have hi : i=s+1 := by simpa using h
    subst i
    simp only [LinearMap.comp_apply, cubicInsert_d,
      horizontal_succ_apply k A B U V s 0 s (Nat.add_zero s), vertical_zero,
      hom_zero_apply, add_zero, bottomMap_bottom]
    congr 1
    have hh := map_comp_apply k A B (U.d (s+1) s) f (𝟙 (V.X 0)) g x
    simp only [Category.id_comp] at hh
    convert! hh using 1
  | succ j =>
    cases j with
    | zero =>
      have hi : i=s := by omega
      subst i
      cases s with
      | zero =>
        simp only [LinearMap.comp_apply, cubicInsert_d, horizontal_zero, hom_zero_apply,
          vertical_succ_apply k A B U V 0 0 0 rfl, zero_add, bottomMap_bottom,
          bottomMap_positive]
        have hh := map_comp_apply k A B (𝟙 (U.X 0)) f (V.d 1 0) g x
        simp only [Category.id_comp, hg, ModuleCat.hom_zero, map_zero_right_apply] at hh
        have he : map k A B f.hom g.hom (map k A B LinearMap.id (V.d 1 0).hom x) = 0 := by
          convert! hh using 1
        rw [he, map_zero]
      | succ s =>
        simp only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_succ_apply k A B U V s 1 (s+1) rfl,
          vertical_succ_apply k A B U V (s+1) 0 (s+1) (Nat.add_zero _), map_add,
          bottomMap_positive, bottomMap_bottom, zero_add]
        have hh := map_comp_apply k A B (𝟙 (U.X (s+1))) f (V.d 1 0) g x
        simp only [Category.id_comp, hg, ModuleCat.hom_zero, map_zero_right_apply] at hh
        have he : map k A B f.hom g.hom (map k A B LinearMap.id (V.d 1 0).hom x) = 0 := by
          convert! hh using 1
        rw [he, map_zero]
    | succ j =>
      cases i with
      | zero =>
        simp (disch := omega) only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_zero, hom_zero_apply, vertical_succ_apply, zero_add,
          bottomMap_positive]
      | succ i =>
        simp (disch := omega) only [LinearMap.comp_apply, cubicInsert_d,
          horizontal_succ_apply, vertical_succ_apply, map_add, bottomMap_positive,
          zero_add]

end ArExplicit.ExternalTensor

end

end OAI
