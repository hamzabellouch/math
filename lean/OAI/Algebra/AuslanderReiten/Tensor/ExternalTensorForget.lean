import OAI.Algebra.AuslanderReiten.Tensor.ExternalTensorDifferential
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import OAI.Algebra.AuslanderReiten.Modules.ModuleRestriction

namespace OAI

noncomputable section
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped TensorProduct
namespace ArExplicit.ExternalTensor
universe u
variable (k A B : Type u) [Field k] [Ring A] [Ring B] [Algebra k A] [Algebra k B]
attribute [local instance] moduleCatBaseModule moduleCatBaseTower

abbrev forgetField : ModuleCat.{u} A ⥤ ModuleCat.{u} k :=
  ModuleCat.restrictScalars (algebraMap k A)

abbrev forgetComplex (P : ChainComplex (ModuleCat.{u} A) ℕ) : ChainComplex (ModuleCat.{u} k) ℕ :=
  ((forgetField k A).mapHomologicalComplex _).obj P

variable (P : ChainComplex (ModuleCat.{u} A) ℕ) (Q : ChainComplex (ModuleCat.{u} B) ℕ)

instance hasScalarTotal : HomologicalComplex.HasMapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) := fun _ => inferInstance

abbrev scalarTotal : ChainComplex (ModuleCat.{u} k) ℕ :=
  HomologicalComplex.mapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ)

abbrev scalarSummands (n : ℕ) (p : Diagonal n) : ModuleCat.{u} k :=
  ModuleCat.of k ((forgetComplex k A P).X p.val.1 ⊗[k] (forgetComplex k B Q).X p.val.2)

def scalarTermDirectSumEquiv (n : ℕ) :
    (scalarTotal k A B P Q).X n ≃ₗ[k] (Π₀ p : Diagonal n, scalarSummands k A B P Q n p) :=
  CategoryTheory.Iso.toLinearEquiv (ModuleCat.coprodIsoDirectSum (scalarSummands k A B P Q n))

def forgetTermEquiv (n : ℕ) :
    (forgetComplex k (A ⊗[k] B) (complex k A B P Q)).X n ≃ₗ[k] (scalarTotal k A B P Q).X n :=
  ((termDirectSumEquiv k A B P Q n).restrictScalars k).trans
    (scalarTermDirectSumEquiv k A B P Q n).symm

abbrev scalarInclusion (i j n : ℕ) (h : i+j=n) :
    scalarSummands k A B P Q n ⟨(i,j),h⟩ ⟶ (scalarTotal k A B P Q).X n :=
  ιMapBifunctor (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n h

def forgetTermIso (n : ℕ) :
    (forgetComplex k (A ⊗[k] B) (complex k A B P Q)).X n ≅ (scalarTotal k A B P Q).X n :=
  (forgetTermEquiv k A B P Q n).toModuleIso

theorem scalarTermDirectSumEquiv_inclusion (i j n : ℕ) (h : i+j=n) :
    (scalarTermDirectSumEquiv k A B P Q n).toLinearMap.comp
      (scalarInclusion k A B P Q i j n h).hom =
      DFinsupp.lsingle (R := k) (M := fun p : Diagonal n => scalarSummands k A B P Q n p)
        ⟨(i,j),h⟩ := by
  exact congrArg (fun f => f.hom)
    (ModuleCat.ι_coprodIsoDirectSum_hom (scalarSummands k A B P Q n) ⟨(i,j),h⟩)

@[reassoc] theorem scalarInclusion_forgetTermIso_inv (i j n : ℕ) (h : i+j=n) :
    scalarInclusion k A B P Q i j n h ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((inclusion k A B P Q i j n h).hom.restrictScalars k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (termDirectSumEquiv k A B P Q n).injective
  change (termDirectSumEquiv k A B P Q n)
    ((termDirectSumEquiv k A B P Q n).symm
      ((scalarTermDirectSumEquiv k A B P Q n)
        ((scalarInclusion k A B P Q i j n h).hom x))) = _
  exact (LinearEquiv.apply_symm_apply (termDirectSumEquiv k A B P Q n) _).trans
    ((LinearMap.congr_fun (scalarTermDirectSumEquiv_inclusion k A B P Q i j n h) x).trans
      (LinearMap.congr_fun (termDirectSumEquiv_inclusion k A B P Q i j n h) x).symm)

abbrev scalarHorizontal (i j n : ℕ) :=
  mapBifunctor.d₁ (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n

abbrev scalarVertical (i j n : ℕ) :=
  mapBifunctor.d₂ (forgetComplex k A P) (forgetComplex k B Q)
    (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) i j n

theorem scalarHorizontal_comp (i j n : ℕ) (h : i+j=n+1) :
    scalarHorizontal k A B P Q i j n ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((horizontal k A B P Q i j n).hom.restrictScalars k) := by
  cases i with
  | zero =>
    rw [show scalarHorizontal k A B P Q 0 j n = 0 from
      mapBifunctor.d₁_eq_zero _ _ _ _ 0 j n (by change ¬ ((ComplexShape.down ℕ).next 0 + 1 = 0); omega),
      zero_comp, horizontal_zero]
    rfl
  | succ i =>
    have hij : i+j=n := by omega
    dsimp only [scalarHorizontal]
    rw [mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl) j n hij]
    change ((1 : ℤˣ) • _) ≫ _ = _
    rw [one_smul, Category.assoc, scalarInclusion_forgetTermIso_inv,
      horizontal_succ k A B P Q i j n hij]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

theorem scalarVertical_comp (i j n : ℕ) (h : i+j=n+1) :
    scalarVertical k A B P Q i j n ≫ (forgetTermIso k A B P Q n).inv =
      ModuleCat.ofHom ((vertical k A B P Q i j n).hom.restrictScalars k) := by
  cases j with
  | zero =>
    rw [show scalarVertical k A B P Q i 0 n = 0 from
      mapBifunctor.d₂_eq_zero _ _ _ _ i 0 n (by change ¬ ((ComplexShape.down ℕ).next 0 + 1 = 0); omega),
      zero_comp, vertical_zero]
    rfl
  | succ j =>
    have hij : i+j=n := by omega
    dsimp only [scalarVertical]
    rw [mapBifunctor.d₂_eq _ _ _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl) n hij]
    change ((-1 : ℤˣ)^i • _) ≫ _ = _
    rw [Linear.units_smul_comp, Category.assoc, scalarInclusion_forgetTermIso_inv,
      vertical_succ k A B P Q i j n hij]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rfl

theorem scalarInclusion_d (i j n n' : ℕ) (h : i+j=n) :
    scalarInclusion k A B P Q i j n h ≫ (scalarTotal k A B P Q).d n n' =
      scalarHorizontal k A B P Q i j n' + scalarVertical k A B P Q i j n' := by
  change ιMapBifunctor _ _ _ _ i j n h ≫ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁, mapBifunctor.ι_D₂]

def scalarForgetTotalIso : scalarTotal k A B P Q ≅
    forgetComplex k (A ⊗[k] B) (complex k A B P Q) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (forgetTermIso k A B P Q n).symm)
    (fun n m h => by
      have hnm : m+1=n := h
      subst n
      apply mapBifunctor.hom_ext
      intro i j hij
      change scalarInclusion k A B P Q i j (m+1) hij ≫
        ((forgetTermIso k A B P Q (m+1)).inv ≫ _) =
        scalarInclusion k A B P Q i j (m+1) hij ≫
        ((scalarTotal k A B P Q).d (m+1) m ≫ (forgetTermIso k A B P Q m).inv)
      rw [← Category.assoc, scalarInclusion_forgetTermIso_inv, ← Category.assoc,
        scalarInclusion_d, Preadditive.add_comp,
        scalarHorizontal_comp k A B P Q i j m hij,
        scalarVertical_comp k A B P Q i j m hij]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun f => f.hom x) (inclusion_d k A B P Q i j (m+1) m hij))

def forgetTotalIso : forgetComplex k (A ⊗[k] B) (complex k A B P Q) ≅
    scalarTotal k A B P Q := (scalarForgetTotalIso k A B P Q).symm

variable {P Q}
variable {P' : ChainComplex (ModuleCat.{u} A) ℕ} {Q' : ChainComplex (ModuleCat.{u} B) ℕ}

theorem scalarForgetTotalIso_naturality (f : P ⟶ P') (g : Q ⟶ Q') :
    mapBifunctorMap (((forgetField k A).mapHomologicalComplex _).map f)
      (((forgetField k B).mapHomologicalComplex _).map g)
      (MonoidalCategory.curriedTensor (ModuleCat.{u} k)) (ComplexShape.down ℕ) ≫
        (scalarForgetTotalIso k A B P' Q').hom =
      (scalarForgetTotalIso k A B P Q).hom ≫
        (((forgetField k (A ⊗[k] B)).mapHomologicalComplex _).map
          (mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ))) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply mapBifunctor.hom_ext
  intro i j hij
  change scalarInclusion k A B P Q i j n hij ≫
    ((mapBifunctorMap _ _ _ _).f n ≫ (forgetTermIso k A B P' Q' n).inv) =
      scalarInclusion k A B P Q i j n hij ≫
        ((forgetTermIso k A B P Q n).inv ≫ _)
  rw [← Category.assoc, ι_mapBifunctorMap, Category.assoc, Category.assoc,
    scalarInclusion_forgetTermIso_inv, ← Category.assoc, scalarInclusion_forgetTermIso_inv]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  exact (congrArg (fun u => u.hom (x ⊗ₜ[k] y))
    (ι_mapBifunctorMap f g (bifunctor k A B) (ComplexShape.down ℕ) i j n hij)).symm

end ArExplicit.ExternalTensor

end

end OAI
