import Mathlib
import OAI.GroupTheory.FiniteType.ProductCoefficientAffineShift

namespace OAI

noncomputable section
open CategoryTheory
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
open CategoryTheory CategoryTheory.Limits
open CategoryTheory
namespace CategoryTheory.ShortComplex
open scoped _root_.CategoryTheory _root_.CategoryTheory.ShortComplex
variable {R : Type*} [Ring R] {S T : _root_.CategoryTheory.ShortComplex (ModuleCat R)}

def concreteCyclesMap (φ : S ⟶ T) : LinearMap.ker S.g.hom →ₗ[R] LinearMap.ker T.g.hom :=
  (φ.τ₂.hom.comp (LinearMap.ker S.g.hom).subtype).codRestrict _ (by
    intro z
    change T.g (φ.τ₂ z.val) = 0
    have h := congrArg (fun q => q z.val) φ.comm₂₃
    change T.g (φ.τ₂ z.val) = φ.τ₃ (S.g z.val) at h
    rw [h,show S.g z.val=0 from z.property,map_zero])

lemma concreteCyclesMap_range (φ : S ⟶ T) :
    LinearMap.range S.moduleCatToCycles ≤
      (LinearMap.range T.moduleCatToCycles).comap (concreteCyclesMap φ) := by
  rintro z ⟨a,rfl⟩
  refine ⟨φ.τ₁ a,?_⟩
  apply Subtype.ext
  have h := congrArg (fun q => q a) φ.comm₁₂
  exact h

def concreteHomologyMap (φ : S ⟶ T) :
    S.moduleCatLeftHomologyData.H →ₗ[R] T.moduleCatLeftHomologyData.H :=
  (LinearMap.range S.moduleCatToCycles).mapQ (LinearMap.range T.moduleCatToCycles)
    (concreteCyclesMap φ) (concreteCyclesMap_range φ)

def concreteHomologyMapData (φ : S ⟶ T) :
    _root_.CategoryTheory.ShortComplex.LeftHomologyMapData φ S.moduleCatLeftHomologyData T.moduleCatLeftHomologyData where
  φK := ModuleCat.ofHom (concreteCyclesMap φ)
  φH := ModuleCat.ofHom (concreteHomologyMap φ)
  commi := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl
  commf' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact (congrArg (fun q => q z) φ.comm₁₂).symm
  commπ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    rfl

lemma concreteHomologyMap_naturality (φ : S ⟶ T) :
    _root_.CategoryTheory.ShortComplex.homologyMap φ ≫ T.moduleCatHomologyIso.hom =
      S.moduleCatHomologyIso.hom ≫ ModuleCat.ofHom (concreteHomologyMap φ) :=
  (concreteHomologyMapData φ).homologyMap_comm

end CategoryTheory.ShortComplex

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

def productShiftSc (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    productShortComplex G I C n ⟶ productShortComplex G I C n where
  τ₁ := ModuleCat.ofHom (shiftChains G I C f σ δ (n+2))
  τ₂ := ModuleCat.ofHom (shiftChains G I C f σ δ (n+1))
  τ₃ := ModuleCat.ofHom (shiftChains G I C f σ δ n)
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ (n+1) z
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ n z

lemma productHomologyQuotientEquiv_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (x : BoundedProductHomology G I C (n+1)) :
    productHomologyQuotientEquiv G I C n (shiftHomology G I C f σ δ (n+1) x) =
      ShortComplex.concreteHomologyMap (productShiftSc G I C f σ δ n)
        (productHomologyQuotientEquiv G I C n x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ z => rfl

def productScHomologyQuotientIso (n : ℕ) :
    (productShortComplex G I C n).homology ≅
      ModuleCat.of ℤ (BoundedProductHomology G I C (n+1)) :=
  (productShortComplex G I C n).moduleCatHomologyIso ≪≫
    (productHomologyQuotientEquiv G I C n).symm.toModuleIso

lemma productScHomologyQuotientIso_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (x : (productShortComplex G I C n).homology) :
    (productScHomologyQuotientIso G I C n).hom
      (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) x) =
      shiftHomology G I C f σ δ (n+1) ((productScHomologyQuotientIso G I C n).hom x) := by
  change (productHomologyQuotientEquiv G I C n).symm
      ((productShortComplex G I C n).moduleCatHomologyIso.hom
        (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) x)) = _
  apply (productHomologyQuotientEquiv G I C n).injective
  rw [LinearEquiv.apply_symm_apply,productHomologyQuotientEquiv_shift]
  have h := congrArg (fun q => q x)
    (ShortComplex.concreteHomologyMap_naturality (productShiftSc G I C f σ δ n))
  change _ = ShortComplex.concreteHomologyMap _
    (productHomologyQuotientEquiv G I C n
      ((productHomologyQuotientEquiv G I C n).symm
        ((productShortComplex G I C n).moduleCatHomologyIso.hom x)))
  rw [LinearEquiv.apply_symm_apply]
  exact h

lemma productScHomologyQuotientIso_shift_iterate (f : G →* G) (σ : C → C) (δ : C → G)
    (n k : ℕ) (x : (productShortComplex G I C n).homology) :
    (productScHomologyQuotientIso G I C n).hom
      ((ShortComplex.homologyMap (productShiftSc G I C f σ δ n) :
        (productShortComplex G I C n).homology → _)^[k] x) =
      (shiftHomology G I C f σ δ (n+1) : BoundedProductHomology G I C (n+1) → _)^[k]
        ((productScHomologyQuotientIso G I C n).hom x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',
      productScHomologyQuotientIso_shift,ih]

theorem UniformFillings.productSc_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (productShortComplex G I C n).homology, ∃ k : ℕ,
      (ShortComplex.homologyMap (productShiftSc G I C f σ δ n) :
        (productShortComplex G I C n).homology → _)^[k] x = 0 := by
  intro x
  obtain ⟨k,hk⟩ := hf.product_local_nilpotence G I C (Nat.succ_pos n) σ δ
    ((productScHomologyQuotientIso G I C n).hom x)
  refine ⟨k,?_⟩
  apply (ModuleCat.mono_iff_injective (productScHomologyQuotientIso G I C n).hom).mp inferInstance
  rw [productScHomologyQuotientIso_shift_iterate,hk,map_zero]

end ListChains

open CategoryTheory
namespace HomologyTransport
section
variable {R : Type} [CommRing R] {M N : ModuleCat R}

lemma iterate_commute (u : M ⟶ M) (v : N ⟶ N) (e : M ⟶ N)
    (h : u ≫ e = e ≫ v) (k : ℕ) (x : M) :
    e ((u : M → M)^[k] x) = (v : N → N)^[k] (e x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply']
    change (u ≫ e) ((u : M → M)^[k] x) = _
    rw [h]
    change v (e ((u : M → M)^[k] x)) = _
    rw [ih]

lemma localNilpotence_transfer (u : M ⟶ M) (v : N ⟶ N) (e : M ≅ N)
    (h : u ≫ e.hom = e.hom ≫ v)
    (hv : ∀ y : N, ∃ k : ℕ, (v : N → N)^[k] y = 0) :
    ∀ x : M, ∃ k : ℕ, (u : M → M)^[k] x = 0 := by
  intro x
  obtain ⟨k,hk⟩ := hv (e.hom x)
  refine ⟨k,?_⟩
  apply (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  rw [iterate_commute u v e.hom h,hk,map_zero]

lemma localNilpotence_transfer_reverse (u : M ⟶ M) (v : N ⟶ N) (e : M ≅ N)
    (h : u ≫ e.hom = e.hom ≫ v)
    (hu : ∀ x : M, ∃ k : ℕ, (u : M → M)^[k] x = 0) :
    ∀ y : N, ∃ k : ℕ, (v : N → N)^[k] y = 0 := by
  intro y
  obtain ⟨k,hk⟩ := hu (e.inv y)
  refine ⟨k,?_⟩
  have he : e.hom (e.inv y) = y := by
    change (e.inv ≫ e.hom) y = y
    rw [e.inv_hom_id]
    rfl
  calc
    (v : N → N)^[k] y = (v : N → N)^[k] (e.hom (e.inv y)) := congrArg _ he.symm
    _ = e.hom ((u : M → M)^[k] (e.inv y)) := (iterate_commute u v e.hom h k _).symm
    _ = 0 := by rw [hk,map_zero]
end

open CategoryTheory
lemma intertwine_trans {D : Type*} [Category D] {X Y Z : D}
    (u : X ⟶ X) (v : Y ⟶ Y) (w : Z ⟶ Z) (e : X ≅ Y) (d : Y ≅ Z)
    (h₁ : u ≫ e.hom = e.hom ≫ v) (h₂ : v ≫ d.hom = d.hom ≫ w) :
    u ≫ (e ≪≫ d).hom = (e ≪≫ d).hom ≫ w := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
end HomologyTransport

namespace ListChains
open CategoryTheory
variable (G I C : Type) [Group G]

def boundedHomologyScIso (n : ℕ) :
    (boundedProductComplex G I C).homology (n+1) ≅
      (productShortComplex G I C n).homology :=
  (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
    (n+2) (n+1) n (by simp) (by simp)).app (boundedProductComplex G I C) ≪≫
      ShortComplex.homologyMapIso (boundedProductScIso G I C n)

lemma boundedHomologyScIso_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1) ≫
      (boundedHomologyScIso G I C n).hom =
    (boundedHomologyScIso G I C n).hom ≫
      ShortComplex.homologyMap (productShiftSc G I C f σ δ n) := by
  apply HomologyTransport.intertwine_trans _ _ _
    ((HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
      (n+2) (n+1) n (by simp) (by simp)).app (boundedProductComplex G I C))
    (ShortComplex.homologyMapIso (boundedProductScIso G I C n))
  · exact (HomologicalComplex.homologyFunctorIso' (ModuleCat ℤ) (ComplexShape.down ℕ)
      (n+2) (n+1) n (by simp) (by simp)).hom.naturality
        (boundedShiftChainMap G I C f σ δ)
  · have hsc :
        (HomologicalComplex.shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ)
          (n+2) (n+1) n).map (boundedShiftChainMap G I C f σ δ) ≫
          (boundedProductScIso G I C n).hom =
        (boundedProductScIso G I C n).hom ≫ productShiftSc G I C f σ δ n := by
      ext <;> rfl
    change (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
        (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ =
      (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _ ≫
        (ShortComplex.homologyFunctor (ModuleCat ℤ)).map _
    simpa only [CategoryTheory.Functor.map_comp] using
      congrArg (ShortComplex.homologyFunctor (ModuleCat ℤ)).map hsc

lemma UniformFillings.bounded_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (boundedProductComplex G I C).homology (n+1), ∃ k : ℕ,
      (HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1) :
        (boundedProductComplex G I C).homology (n+1) → _)^[k] x = 0 := by
  exact HomologyTransport.localNilpotence_transfer _ _ (boundedHomologyScIso G I C n)
    (boundedHomologyScIso_shift G I C f σ δ n) (hf.productSc_local_nilpotence G I C σ δ)

lemma standardShiftChainMap_naturality (f : G →* G) (σ : C → C) (δ : C → G) :
    standardShiftChainMap G I C f σ δ ≫ (standardProductComplexIso G I C).hom =
      (standardProductComplexIso G I C).hom ≫ boundedShiftChainMap G I C f σ δ := by
  simp [standardShiftChainMap,Category.assoc]

lemma UniformFillings.standard_local_nilpotence {f : G →* G} {n : ℕ}
    (hf : UniformFillings G f (n+1)) (σ : C → C) (δ : C → G) :
    ∀ x : (standardProductComplex G I C).homology (n+1), ∃ k : ℕ,
      (HomologicalComplex.homologyMap (standardShiftChainMap G I C f σ δ) (n+1) :
        (standardProductComplex G I C).homology (n+1) → _)^[k] x = 0 := by
  apply HomologyTransport.localNilpotence_transfer _
    (HomologicalComplex.homologyMap (boundedShiftChainMap G I C f σ δ) (n+1))
    ((HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1)).mapIso
      (standardProductComplexIso G I C))
  · change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp,← HomologicalComplex.homologyMap_comp,
      standardShiftChainMap_naturality]
  · exact hf.bounded_local_nilpotence G I C σ δ

end ListChains

end

end OAI
