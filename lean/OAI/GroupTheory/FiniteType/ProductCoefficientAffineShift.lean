import Mathlib
import OAI.GroupTheory.FiniteType.ListChainsFromTuplesCone

namespace OAI

noncomputable section
open CategoryTheory
namespace ProductCoefficient
variable (G I C : Type*) [Group G]

def affineShift (f : G →* G) (σ : C → C) (δ : C → G) :
    (C × G →₀ ℤ) →ₗ[ℤ] (C × G →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ (fun p => (σ p.1,δ p.1*f p.2))

@[simp] lemma affineShift_single (f : G →* G) (σ : C → C) (δ : C → G)
    (c : C) (g : G) (r : ℤ) :
    affineShift G C f σ δ (Finsupp.single (c,g) r) = Finsupp.single (σ c,δ c*f g) r := by
  simp [affineShift]

def productAffineShift (f : G →* G) (σ : C → C) (δ : C → G) :
    Module G I C →ₗ[ℤ] Module G I C :=
  LinearMap.pi (fun i => (affineShift G C f σ δ).comp (LinearMap.proj i))

@[simp] lemma productAffineShift_apply (f : G →* G) (σ : C → C) (δ : C → G)
    (a : Module G I C) (i : I) :
    productAffineShift G I C f σ δ a i = affineShift G C f σ δ (a i) := rfl

end ProductCoefficient

namespace ListChains
open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
variable (G I C : Type) [Group G]

lemma cosetShift_place (f : G →* G) (σ : C → C) (δ : C → G)
    (a : C × G →₀ ℤ) (z : Chain G) :
    cosetShift G f σ δ (place G C a z) =
      place G C (ProductCoefficient.affineShift G C f σ δ a) (mapChain G f z) := by
  have h : (cosetShift G f σ δ).comp ((place G C).flip z) =
      ((place G C).flip (mapChain G f z)).comp (ProductCoefficient.affineShift G C f σ δ) := by
    apply Finsupp.lhom_ext
    rintro ⟨c,u⟩ r
    simp only [LinearMap.comp_apply,LinearMap.flip_apply,place_single,map_smul,
      ProductCoefficient.affineShift_single,cosetShift,cosetMap_single,mapChain_comp]
    congr 3
    apply congrArg (mapChain G)
    funext x
    simp [mul_assoc]
  exact LinearMap.congr_fun h a

omit [Group G] in
lemma fromTuples_mapChain (f : G → G) (n : ℕ) (z : ControlledChains.Chain G n) :
    fromTuples G n (ControlledChains.mapChain G f n z) =
      mapChain G f (fromTuples G n z) := by
  have h : (fromTuples G n).comp (ControlledChains.mapChain G f n) =
      (mapChain G f).comp (fromTuples G n) := by
    apply Finsupp.lhom_ext
    intro s r
    simp only [LinearMap.comp_apply, ControlledChains.mapChain, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      fromTuples_single, mapChain_single, List.map_ofFn]
    rfl
  exact LinearMap.congr_fun h z

def standardTupleMap (f : G →* G) (n : ℕ) :
    MonoidAlgebra ℤ (Fin (n+1) → G) →ₗ[ℤ] MonoidAlgebra ℤ (Fin (n+1) → G) :=
  (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp
    ((ControlledChains.mapChain G f n).comp (MonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap)

def standardShift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    Coinvariants ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ →ₗ[ℤ]
      Coinvariants ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ :=
  (standardProductEquiv G I C n).symm.toLinearMap.comp
    ((shiftChains G I C f σ δ n).comp (standardProductEquiv G I C n).toLinearMap)

lemma standardShift_mk_tmul (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (a : ProductCoefficient.Module G I C) (z : MonoidAlgebra ℤ (Fin (n+1) → G)) :
    standardShift G I C f σ δ n (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)) =
      Coinvariants.mk _ (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ]
        standardTupleMap G f n z) := by
  change (standardProductEquiv G I C n).symm
    (shiftChains G I C f σ δ n (standardProductEquiv G I C n
       (Coinvariants.mk _ (a ⊗ₜ[ℤ] z)))) = _
  rw [LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext i
  change cosetShift G f σ δ ((standardProductEquiv G I C n
    (Coinvariants.mk _ (a ⊗ₜ[ℤ] z))).val i) = _
  rw [standardProductEquiv_mk_tmul]
  change _ = (standardProductEquiv G I C n
    (Coinvariants.mk ((ProductCoefficient.rep G I C) ⊗ Rep.diagonal ℤ G (n+1)).ρ
      (ProductCoefficient.productAffineShift G I C f σ δ a ⊗ₜ[ℤ]
        standardTupleMap G f n z))).val i
  rw [standardProductEquiv_mk_tmul,ProductCoefficient.productAffineShift_apply]
  simp only [standardTupleMap,LinearMap.comp_apply,LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply,fromTuples_mapChain,cosetShift_place]

lemma productChainD_shift (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ)
    (z : productChains G I C (n+1)) :
    productChainD G I C n (shiftChains G I C f σ δ (n+1) z) =
      shiftChains G I C f σ δ n (productChainD G I C n z) := by
  apply Subtype.ext
  exact productBoundary_shift G I C f σ δ z.val

def boundedShiftChainMap (f : G →* G) (σ : C → C) (δ : C → G) :
    boundedProductComplex G I C ⟶ boundedProductComplex G I C :=
  HomologicalComplex.Hom.mk (fun n => ModuleCat.ofHom (shiftChains G I C f σ δ n)) (by
    intro i j h
    obtain rfl : j+1=i := h
    rw [boundedProductComplex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    exact productChainD_shift G I C f σ δ j z)

def standardShiftChainMap (f : G →* G) (σ : C → C) (δ : C → G) :
    standardProductComplex G I C ⟶ standardProductComplex G I C :=
  (standardProductComplexIso G I C).hom ≫ boundedShiftChainMap G I C f σ δ ≫
    (standardProductComplexIso G I C).inv

@[simp] lemma standardShiftChainMap_f (f : G →* G) (σ : C → C) (δ : C → G) (n : ℕ) :
    (standardShiftChainMap G I C f σ δ).f n = ModuleCat.ofHom (standardShift G I C f σ δ n) := by
  change (standardProductComplexIso G I C).hom.f n ≫
      (boundedShiftChainMap G I C f σ δ).f n ≫ (standardProductComplexIso G I C).inv.f n = _
  change ModuleCat.ofHom ((standardProductEquiv G I C n).toLinearMap) ≫
      ModuleCat.ofHom (shiftChains G I C f σ δ n) ≫
      ModuleCat.ofHom ((standardProductEquiv G I C n).symm.toLinearMap) = _
  simp only [standardShift, ModuleCat.ofHom_comp, Category.assoc]

end ListChains

open CategoryTheory MonoidalCategory _root_.Representation _root_.OAI.Representation TensorProduct
namespace SemilinearCoinvariants
variable {R G H : Type*} [CommRing R] [Group G] [Group H]
variable {V W : Type*} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
variable (ρ : Representation R G V) (τ : Representation R H W) (φ : G →* H)
variable (T : V →ₗ[R] W) (hT : ∀ g, T.comp (ρ g) = (τ (φ g)).comp T)

def map : Coinvariants ρ →ₗ[R] Coinvariants τ :=
  Coinvariants.lift ρ ((Coinvariants.mk τ).comp T) (by
    intro g
    rw [LinearMap.comp_assoc,hT,← LinearMap.comp_assoc]
    congr 1
    apply LinearMap.ext
    intro w
    exact Coinvariants.mk_self_apply τ (φ g) w)

@[simp] lemma map_mk (v : V) : map ρ τ φ T hT (Coinvariants.mk ρ v) = Coinvariants.mk τ (T v) := rfl

lemma map_add (T' : V →ₗ[R] W) (hT' : ∀ g, T'.comp (ρ g) = (τ (φ g)).comp T') :
    map ρ τ φ (T+T') (fun g => by simp [LinearMap.add_comp,LinearMap.comp_add,hT,hT']) =
      map ρ τ φ T hT + map ρ τ φ T' hT' := by
  apply Coinvariants.hom_ext
  ext v
  simp

variable {K : Type*} [Group K] {Z : Type*} [AddCommGroup Z] [Module R Z]

lemma map_comp (υ : Representation R K Z) (ψ : H →* K)
    (U : W →ₗ[R] Z) (hU : ∀ h, U.comp (τ h) = (υ (ψ h)).comp U) :
    (map τ υ ψ U hU).comp (map ρ τ φ T hT) =
      map ρ υ (ψ.comp φ) (U.comp T) (fun g => by
        rw [LinearMap.comp_assoc,hT,← LinearMap.comp_assoc,hU,LinearMap.comp_assoc]; rfl) := by
  apply Coinvariants.hom_ext
  ext v
  rfl

variable {A P : Rep R G} {B Q : Rep R H}

def tensorMap (α : A ⟶ Rep.res φ B) (β : P ⟶ Rep.res φ Q) :
    Coinvariants (A ⊗ P).ρ →ₗ[R] Coinvariants (B ⊗ Q).ρ :=
  map (A ⊗ P).ρ (B ⊗ Q).ρ φ (TensorProduct.map α.hom.toLinearMap β.hom.toLinearMap) (by
    intro g
    apply TensorProduct.ext'
    intro a p
    simp [Rep.tensor_ρ,Rep.hom_comm_apply α,Rep.hom_comm_apply β])

@[simp] lemma tensorMap_mk_tmul (α : A ⟶ Rep.res φ B) (β : P ⟶ Rep.res φ Q) (a : A) (p : P) :
    tensorMap φ α β (Coinvariants.mk _ (a ⊗ₜ[R] p)) =
      Coinvariants.mk _ (α a ⊗ₜ[R] β p) := by
  simp [tensorMap]

end SemilinearCoinvariants

namespace StandardVertex
open CategoryTheory _root_.Representation _root_.OAI.Representation MonoidalCategory TensorProduct
variable {R G H : Type} [CommRing R] [Group G] [Group H]
variable (φ : G →* H) (v : G → H) (hv : ∀ g x, v (g*x) = φ g * v x)

def map (n : ℕ) : Rep.diagonal R G (n+1) ⟶
    Rep.res φ (Rep.diagonal R H (n+1)) :=
  Rep.ofHom ⟨MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s),by
    intro g
    apply MonoidAlgebra.lhom_ext'
    intro s
    apply LinearMap.ext_ring
    change MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
        ((Representation.ofMulAction R G (Fin (n+1) → G)) g (MonoidAlgebra.single s 1)) =
      ((Representation.ofMulAction R H (Fin (n+1) → H)) (φ g))
        (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
          (MonoidAlgebra.single s 1))
    simp only [Representation.ofMulAction_single,MonoidAlgebra.mapDomainLinearMap_single]
    congr 1
    ext i
    exact hv g (s i)⟩

@[simp] lemma map_single (n : ℕ) (s : Fin (n+1) → G) (r : R) :
    map φ v hv n (MonoidAlgebra.single s r) = MonoidAlgebra.single (v ∘ s) r := by
  exact MonoidAlgebra.mapDomainLinearMap_single _ _ _

lemma comm (n : ℕ) : map φ v hv (n+1) ≫
    (Rep.resFunctor φ).map ((Rep.standardComplex R H).d (n+1) n) =
      (Rep.standardComplex R G).d (n+1) n ≫ map φ v hv n := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  change (((Rep.standardComplex R H).d (n+1) n).hom.toLinearMap).comp
      (map φ v hv (n+1)).hom.toLinearMap =
    (map φ v hv n).hom.toLinearMap.comp
      ((Rep.standardComplex R G).d (n+1) n).hom.toLinearMap
  rw [Rep.standardComplex.d_eq,Rep.standardComplex.d_eq]
  apply MonoidAlgebra.lhom_ext'
  intro s
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply,MonoidAlgebra.lsingle_apply]
  change Rep.standardComplex.d R H (n+1)
      (MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+2) → G => v ∘ s)
        (MonoidAlgebra.single s 1)) =
    MonoidAlgebra.mapDomainLinearMap R R (fun s : Fin (n+1) → G => v ∘ s)
      (Rep.standardComplex.d R G (n+1) (MonoidAlgebra.single s 1))
  simp only [MonoidAlgebra.mapDomainLinearMap_single,Rep.standardComplex.d_single,map_sum,
    Function.comp_assoc]

def chainMap : Rep.standardComplex R G ⟶
    ((Rep.resFunctor φ).mapHomologicalComplex (ComplexShape.down ℕ)).obj (Rep.standardComplex R H) :=
  HomologicalComplex.Hom.mk (map φ v hv) (by
    intro i j hij
    obtain rfl : j+1=i := hij
    exact comm φ v hv j)

end StandardVertex

end

end OAI
