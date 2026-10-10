import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorHomComplex

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower
variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)
variable (U : ModuleCat.{u} A) (V : ModuleCat.{u} B)

theorem homCochainInclusion_d_tmul (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (homCochainTotal k A B P Q U V).d n (n+1)
      (homCochainInclusion k A B P Q U V i j n h (f ⊗ₜ[k] g)) =
      homCochainInclusion k A B P Q U V (i+1) j (n+1) (show i+1+j=n+1 by omega)
        ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) +
      (-1 : ℤˣ)^i • homCochainInclusion k A B P Q U V i (j+1) (n+1) (by omega)
        (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) := by
  have hd : homCochainInclusion k A B P Q U V i j n h ≫
      (homCochainTotal k A B P Q U V).d n (n+1) =
      mapBifunctor.d₁ (homCochain k A P U) (homCochain k B Q V)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j (n+1) +
      mapBifunctor.d₂ (homCochain k A P U) (homCochain k B Q V)
        (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j (n+1) := by
    change ιMapBifunctor (homCochain k A P U) (homCochain k B Q V)
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.up ℕ) i j n h ≫ _ = _
    rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]
  rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℕ).Rel i (i+1) from rfl) j (n+1) (show i+1+j=n+1 by omega),
    mapBifunctor.d₂_eq _ _ _ _ i (show (ComplexShape.up ℕ).Rel j (j+1) from rfl) (n+1) (show i+(j+1)=n+1 by omega)] at hd
  rw [show ComplexShape.ε₁ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (i,j) = (1 : ℤˣ) from rfl,
    show ComplexShape.ε₂ (ComplexShape.up ℕ) (ComplexShape.up ℕ) (ComplexShape.up ℕ) (i,j) = (-1 : ℤˣ)^i from rfl,
    one_smul] at hd
  have hh := congrArg (fun l => l.hom (f ⊗ₜ[k] g)) hd
  simp only [homCochain_d, ModuleCat.hom_comp, LinearMap.comp_apply] at hh
  exact hh

variable [∀ n, Module.Finite A (P.X n)] [∀ n, Module.Projective A (P.X n)]
variable [∀ n, Module.Finite B (Q.X n)] [∀ n, Module.Projective B (Q.X n)]

abbrev elementaryHom (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (complex k A B P Q).X n →ₗ[A ⊗[k] B] moduleObject k A B U V :=
  homCochainTermEquiv k A B P Q U V n
    (homCochainInclusion k A B P Q U V i j n h (f ⊗ₜ[k] g))

theorem elementary_horizontal_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (horizontal k A B P Q (i+1) j n).hom =
      map k A B (f.comp (P.d (i+1) i).hom) g := by
  rw [horizontal_succ k A B P Q i j n h, ModuleCat.hom_comp, ← LinearMap.comp_assoc]
  rw [homCochainTermEquiv_inclusion_same, homMap_tmul]
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem elementary_horizontal_zero (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n+1) (hne : (a,b) ≠ (i+1,j)) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (horizontal k A B P Q a b n).hom = 0 := by
  cases a with
  | zero => rw [horizontal_zero, ModuleCat.hom_zero, LinearMap.comp_zero]
  | succ a =>
    have hh : a+b=n := by omega
    have hn : (a,b) ≠ (i,j) := by intro he; rcases Prod.mk.inj he with ⟨rfl,rfl⟩; exact hne rfl
    rw [horizontal_succ k A B P Q a b n hh, ModuleCat.hom_comp, ← LinearMap.comp_assoc,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hh hn,
      LinearMap.zero_comp]

theorem elementary_vertical_same (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (vertical k A B P Q i (j+1) n).hom =
      (-1 : ℤˣ)^i • map k A B f (g.comp (Q.d (j+1) j).hom) := by
  rw [vertical_succ k A B P Q i j n h, ModuleCat.hom_smul, ModuleCat.hom_comp,
    LinearMap.comp_smul, ← LinearMap.comp_assoc, homCochainTermEquiv_inclusion_same, homMap_tmul]
  congr 1
  apply LinearMap.restrictScalars_injective k
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  rfl

theorem elementary_vertical_zero (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V)
    (a b : ℕ) (hab : a+b=n+1) (hne : (a,b) ≠ (i,j+1)) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      (vertical k A B P Q a b n).hom = 0 := by
  cases b with
  | zero => rw [vertical_zero, ModuleCat.hom_zero, LinearMap.comp_zero]
  | succ b =>
    have hh : a+b=n := by omega
    have hn : (a,b) ≠ (i,j) := by intro he; rcases Prod.mk.inj he with ⟨rfl,rfl⟩; exact hne rfl
    rw [vertical_succ k A B P Q a b n hh, ModuleCat.hom_smul, ModuleCat.hom_comp,
      LinearMap.comp_smul, ← LinearMap.comp_assoc,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i j n h (f ⊗ₜ[k] g) a b hh hn,
      LinearMap.zero_comp, smul_zero]

theorem elementary_d (i j n : ℕ) (h : i+j=n)
    (f : P.X i →ₗ[A] U) (g : Q.X j →ₗ[B] V) :
    (elementaryHom k A B P Q U V i j n h f g).comp
      ((complex k A B P Q).d (n+1) n).hom =
      elementaryHom k A B P Q U V (i+1) j (n+1) (by omega)
        (f.comp (P.d (i+1) i).hom) g +
      (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega)
        f (g.comp (Q.d (j+1) j).hom) := by
  suffices hh : ModuleCat.ofHom (X := (complex k A B P Q).X (n+1)) (Y := moduleObject k A B U V)
      ((elementaryHom k A B P Q U V i j n h f g).comp ((complex k A B P Q).d (n+1) n).hom) =
      ModuleCat.ofHom (X := (complex k A B P Q).X (n+1)) (Y := moduleObject k A B U V)
      (elementaryHom k A B P Q U V (i+1) j (n+1) (by omega) (f.comp (P.d (i+1) i).hom) g +
        (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega) f (g.comp (Q.d (j+1) j).hom)) by
    exact congrArg (fun z => z.hom) hh
  apply hom_ext k A B P Q
  intro a b hab
  apply ModuleCat.hom_ext
  change ((elementaryHom k A B P Q U V i j n h f g).comp
    ((complex k A B P Q).d (n+1) n).hom).comp (inclusion k A B P Q a b (n+1) hab).hom =
    (elementaryHom k A B P Q U V (i+1) j (n+1) (by omega) (f.comp (P.d (i+1) i).hom) g +
      (-1 : ℤˣ)^i • elementaryHom k A B P Q U V i (j+1) (n+1) (by omega) f (g.comp (Q.d (j+1) j).hom)).comp
        (inclusion k A B P Q a b (n+1) hab).hom
  rw [LinearMap.comp_assoc,
    show ((complex k A B P Q).d (n+1) n).hom.comp (inclusion k A B P Q a b (n+1) hab).hom =
      (horizontal k A B P Q a b n).hom + (vertical k A B P Q a b n).hom from
      congrArg (fun z => z.hom) (inclusion_d k A B P Q a b (n+1) n hab),
    LinearMap.comp_add, LinearMap.add_comp, LinearMap.smul_comp]
  by_cases ha : a=i+1
  · have hb : b=j := by omega
    subst a
    subst b
    have hn : (i+1,j) ≠ (i,j+1) := by intro hh; have := congrArg Prod.fst hh; omega
    rw [elementary_horizontal_same, elementary_vertical_zero k A B P Q U V i j n h f g _ _ hab hn,
      homCochainTermEquiv_inclusion_same, homMap_tmul,
      homCochainTermEquiv_inclusion_ne k A B P Q U V i (j+1) (n+1) (by omega)
        (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) _ _ hab hn, smul_zero]
  · by_cases hb : b=j+1
    · have hai : a=i := by omega
      subst a
      subst b
      have hn : (i,j+1) ≠ (i+1,j) := by intro hh; have := congrArg Prod.fst hh; omega
      rw [elementary_horizontal_zero k A B P Q U V i j n h f g _ _ hab hn, elementary_vertical_same,
        homCochainTermEquiv_inclusion_ne k A B P Q U V (i+1) j (n+1) (by omega)
          ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) _ _ hab hn,
        homCochainTermEquiv_inclusion_same, homMap_tmul]
    · have hna : (a,b) ≠ (i+1,j) := by intro hh; exact ha (congrArg Prod.fst hh)
      have hnb : (a,b) ≠ (i,j+1) := by intro hh; exact hb (congrArg Prod.snd hh)
      rw [elementary_horizontal_zero k A B P Q U V i j n h f g _ _ hab hna,
        elementary_vertical_zero k A B P Q U V i j n h f g _ _ hab hnb,
        homCochainTermEquiv_inclusion_ne k A B P Q U V (i+1) j (n+1) (by omega)
          ((f.comp (P.d (i+1) i).hom) ⊗ₜ[k] g) _ _ hab hna,
        homCochainTermEquiv_inclusion_ne k A B P Q U V i (j+1) (n+1) (by omega)
          (f ⊗ₜ[k] (g.comp (Q.d (j+1) j).hom)) _ _ hab hnb, smul_zero]

def homCochainTotalIso : homCochainTotal k A B P Q U V ≅
    homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homCochainTermEquiv k A B P Q U V n).toModuleIso)
    (fun n m h => by
      have hnm : n+1=m := h
      subst m
      apply mapBifunctor.hom_ext
      intro i j hij
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      apply LinearMap.ext
      intro f
      apply LinearMap.ext
      intro g
      change (P.X i →ₗ[A] U) at f
      change (Q.X j →ₗ[B] V) at g
      change i+j=n at hij
      change (homCochain k (A ⊗[k] B) (complex k A B P Q) (moduleObject k A B U V)).d n (n+1)
        (elementaryHom k A B P Q U V i j n hij f g) =
        homCochainTermEquiv k A B P Q U V (n+1)
          ((homCochainTotal k A B P Q U V).d n (n+1)
            (homCochainInclusion k A B P Q U V i j n hij (f ⊗ₜ[k] g)))
      rw [homCochainInclusion_d_tmul, homCochain_d]
      simp only [map_add, Units.smul_def, map_zsmul]
      exact elementary_d k A B P Q U V i j n hij f g)

end ArExplicit.ExternalTensor

end

end OAI
