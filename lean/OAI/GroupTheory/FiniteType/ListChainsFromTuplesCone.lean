import Mathlib
import OAI.GroupTheory.FiniteType.Representation

namespace OAI

noncomputable section
open CategoryTheory
namespace ListChains
section
variable (G : Type)

lemma fromTuples_cone (a : G) (n : ℕ) (c : ControlledChains.Chain G n) :
    fromTuples G (n+1) (ControlledChains.cone G a n c) = cone G a (fromTuples G n c) := by
  have h : (fromTuples G (n+1)).comp (ControlledChains.cone G a n) =
      (cone G a).comp (fromTuples G n) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, ControlledChains.cone_single,fromTuples_single,
      Fin.cons_zero,Fin.cons_succ,cone_single,simplexCone,List.ofFn_succ]
  exact LinearMap.congr_fun h c

lemma fromTuples_augmentation (c : ControlledChains.Chain G 0) :
    augmentation G (fromTuples G 0 c) = ControlledChains.augmentation G c := by
  have h : (augmentation G).comp (fromTuples G 0) = ControlledChains.augmentation G := by
    apply Finsupp.lhom_ext
    intro s r
    simp [fromTuples_single]
  exact LinearMap.congr_fun h c

lemma fromTuples_augmentation_succ (n : ℕ) (c : ControlledChains.Chain G (n+1)) :
    augmentation G (fromTuples G (n+1) c) = 0 := by
  have h : (augmentation G).comp (fromTuples G (n+1)) = 0 := by
    apply Finsupp.lhom_ext
    intro s r
    simp [fromTuples_single,List.ofFn_succ]
  exact LinearMap.congr_fun h c

lemma tuple_single_as_cone (n : ℕ) (c : Fin (n+2) → G) (r : ℤ) :
    Finsupp.single c r = ControlledChains.cone G (c 0) n
      (Finsupp.single (fun i => c i.succ) r) := by
  rw [ControlledChains.cone_single]
  congr 1
  exact (Fin.cons_self_tail c).symm

lemma fromTuples_boundary (n : ℕ) (c : ControlledChains.Chain G (n+1)) :
    fromTuples G n (ControlledChains.boundary G n c) = boundary G (fromTuples G (n+1) c) := by
  induction n with
  | zero =>
    have h : (fromTuples G 0).comp (ControlledChains.boundary G 0) =
        (boundary G).comp (fromTuples G 1) := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply]
      rw [tuple_single_as_cone,ControlledChains.boundary_cone_zero,fromTuples_cone,map_sub,
        fromTuples_single,fromTuples_single]
      simp only [List.ofFn_zero,ControlledChains.augmentation_single]
      rw [boundary_cone]
      have hz : boundary G (Finsupp.single (s (Fin.succ 0),[]) r) = 0 := by
        have he : Finsupp.single (s (Fin.succ 0),[]) r = r • vertex G (s (Fin.succ 0)) := by simp [vertex,simplexVertex]
        rw [he,map_smul,boundary_vertex,smul_zero]
      rw [hz,map_zero,sub_zero]
      simp [vertex,simplexVertex,K_apply]
    exact LinearMap.congr_fun h c
  | succ n ih =>
    have h : (fromTuples G (n+1)).comp (ControlledChains.boundary G (n+1)) =
        (boundary G).comp (fromTuples G (n+2)) := by
      apply Finsupp.lhom_ext
      intro s r
      simp only [LinearMap.comp_apply]
      rw [tuple_single_as_cone,fromTuples_cone]
      rw [eq_sub_of_add_eq (ControlledChains.boundary_cone G (s 0) n
        (Finsupp.single (fun i => s i.succ) r))]
      rw [map_sub,fromTuples_cone,ih,boundary_cone,K_apply,fromTuples_augmentation_succ,
        zero_smul,sub_zero]
    exact LinearMap.congr_fun h c

end

section
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

def productChainD (n : ℕ) : productChains G I C (n+1) →ₗ[ℤ] productChains G I C n where
  toFun z := ⟨productBoundary G I C z.val,
    productBoundary_mem_bounded G I C z.property.1,
    productBoundary_mem_degree G I C z.property.2⟩
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

@[simp] lemma productChainD_val (n : ℕ) (z : productChains G I C (n+1)) :
    (productChainD G I C n z).val = productBoundary G I C z.val := rfl

@[simp] lemma productChainD_squared (n : ℕ) (z : productChains G I C (n+2)) :
    productChainD G I C n (productChainD G I C (n+1) z) = 0 := by
  apply Subtype.ext
  exact productBoundary_squared G I C z.val

def boundedProductComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of ℤ (productChains G I C n))
    (fun n => ModuleCat.ofHom (productChainD G I C n)) (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      exact productChainD_squared G I C n)

@[simp] lemma boundedProductComplex_d (n : ℕ) :
    (boundedProductComplex G I C).d (n+1) n = ModuleCat.ofHom (productChainD G I C n) := by
  simp [boundedProductComplex]

abbrev standardProductComplex : ChainComplex (ModuleCat ℤ) ℕ :=
  (Rep.standardComplex ℤ G).coinvariantsTensorObj (ProductCoefficient.rep G I C)

lemma standardProductComplex_d_mk_tmul (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+2) → G)) :
    (standardProductComplex G I C).d (n+1) n
      (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
        Coinvariants.mk _ (a ⊗ₜ[ℤ] (Rep.standardComplex.d ℤ G (n+1) z)) := by
  change Coinvariants.mk _
    (Representation.IntertwiningMap.tensor (Representation.IntertwiningMap.id _)
      ((Rep.standardComplex ℤ G).d (n+1) n).hom (a ⊗ₜ[ℤ] z)) = _
  rw [Representation.IntertwiningMap.tensor_apply]
  simp only [Representation.IntertwiningMap.id_apply, Rep.standardComplex.d_apply]
  rfl

lemma standardProductEquiv_boundary (n : ℕ)
    (z : (standardProductComplex G I C).X (n+1)) :
    standardProductEquiv G I C n ((standardProductComplex G I C).d (n+1) n z) =
      productChainD G I C n (standardProductEquiv G I C (n+1) z) := by
  have h : (standardProductEquiv G I C n).toLinearMap.comp
      ((standardProductComplex G I C).d (n+1) n).hom =
      (productChainD G I C n).comp (standardProductEquiv G I C (n+1)).toLinearMap := by
    apply Coinvariants.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    funext i
    change (standardProductEquiv G I C n
      ((standardProductComplex G I C).d (n+1) n (Coinvariants.mk _ (a ⊗ₜ[ℤ] b)))).val i = _
    rw [standardProductComplex_d_mk_tmul]
    change (standardProductEquiv G I C n
      (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ
        (a ⊗ₜ[ℤ] (Rep.standardComplex.d ℤ G (n+1) b)))).val i =
      cosetBoundary G ((standardProductEquiv G I C (n+1)
        (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+2)).ρ
          (a ⊗ₜ[ℤ] b))).val i)
    rw [standardProductEquiv_mk_tmul]
    change place G C (a i) (fromTuples G n
        (ControlledChains.boundary G n (MonoidAlgebra.coeffLinearEquiv ℤ b))) =
      cosetBoundary G ((standardProductEquiv G I C (n+1)
        (Coinvariants.mk _ (a ⊗ₜ[ℤ] b))).val i)
    rw [standardProductEquiv_mk_tmul,fromTuples_boundary,boundary_place]
  exact LinearMap.congr_fun h z

def standardProductComplexIso :
    standardProductComplex G I C ≅ boundedProductComplex G I C :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => LinearEquiv.toModuleIso (standardProductEquiv G I C n)) (fun i j => by
      rintro (rfl : j+1=i)
      rw [boundedProductComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro z
      change productChainD G I C j (standardProductEquiv G I C (j+1) z) =
        standardProductEquiv G I C j ((standardProductComplex G I C).d (j+1) j z)
      exact (standardProductEquiv_boundary G I C j z).symm)

def groupHomologyBoundedIso (n : ℕ) :
    groupHomology (ProductCoefficient.rep G I C) n ≅
      (boundedProductComplex G I C).homology n := by
  classical
  exact groupHomologyIso (ProductCoefficient.rep G I C) n
    (Rep.standardResolution ℤ G) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) n).mapIso
        (standardProductComplexIso G I C)

end

open CategoryTheory
variable (G I C : Type) [Group G]

def productShortComplex (n : ℕ) : ShortComplex (ModuleCat ℤ) :=
  ShortComplex.moduleCatMk (productChainD G I C (n+1)) (productChainD G I C n)
    (by apply LinearMap.ext; intro z; exact productChainD_squared G I C n z)

def productCycleKernelEquiv (n : ℕ) :
    productCycles G I C (n+1) ≃ₗ[ℤ] LinearMap.ker (productChainD G I C n) where
  toFun z := ⟨⟨z.val,z.property.1⟩,Subtype.ext z.property.2⟩
  invFun z := ⟨z.val.val,z.val.property,congrArg Subtype.val z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma productCycleKernelEquiv_boundaries (n : ℕ) :
    (productBoundaries G I C (n+1)).map (productCycleKernelEquiv G I C n).toLinearMap =
      LinearMap.range (productShortComplex G I C n).moduleCatToCycles := by
  rw [productBoundaries,← LinearMap.range_comp]
  rfl

def productHomologyQuotientEquiv (n : ℕ) :
    BoundedProductHomology G I C (n+1) ≃ₗ[ℤ]
      (productShortComplex G I C n).moduleCatLeftHomologyData.H :=
  Submodule.Quotient.equiv _ _ (productCycleKernelEquiv G I C n)
    (productCycleKernelEquiv_boundaries G I C n)

def boundedProductScIso (n : ℕ) :
    (boundedProductComplex G I C).sc' (n+2) (n+1) n ≅ productShortComplex G I C n :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by
      change _ ≫ ModuleCat.ofHom (productChainD G I C (n+1)) =
        (boundedProductComplex G I C).d (n+2) (n+1) ≫ _
      rw [boundedProductComplex_d]
      rfl)
    (by
      change _ ≫ ModuleCat.ofHom (productChainD G I C n) =
        (boundedProductComplex G I C).d (n+1) n ≫ _
      rw [boundedProductComplex_d]
      rfl)

def groupHomologyProductQuotientIso (n : ℕ) :
    groupHomology (ProductCoefficient.rep G I C) (n+1) ≅
      ModuleCat.of ℤ (BoundedProductHomology G I C (n+1)) :=
  groupHomologyBoundedIso G I C (n+1) ≪≫
    (boundedProductComplex G I C).homologyIsoSc' (n+2) (n+1) n (by simp) (by simp) ≪≫
    ShortComplex.homologyMapIso (boundedProductScIso G I C n) ≪≫
    (productShortComplex G I C n).moduleCatHomologyIso ≪≫
    (productHomologyQuotientEquiv G I C n).symm.toModuleIso

end ListChains

end

end OAI
