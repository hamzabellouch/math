import Mathlib
import OAI.GroupTheory.FiniteType.SingularSigmaSingleMerge

namespace OAI

noncomputable section
namespace SingularChains
open CategoryTheory HomologicalComplex AlgebraicTopology
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def zeroAugmentation (X : Type) [TopologicalSpace X] :
    (chains X).homology 0 ⟶ ModuleCat.of ℤ ℤ :=
  (TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)

instance zeroAugmentation_isIso [PathConnectedSpace X] : IsIso (zeroAugmentation X) :=
  inferInstanceAs (IsIso ((TopCat.of X).singularHomology₀ε (ModuleCat.of ℤ ℤ)))

lemma zeroAugmentation_natural (f : C(X,Y)) :
    homologyMap (map f) 0 ≫ zeroAugmentation Y = zeroAugmentation X := by
  let K := chains X
  let e := K.iCyclesIso 0 0 (by simp) (by simp)
  apply (cancel_epi (K.homologyπ 0)).mp
  apply (cancel_epi e.inv).mp
  apply hom_ext
  intro s
  have he : generator s ≫ e.inv = K.liftCycles (generator s) 0 (by simp) (by simp) := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp [e,Category.assoc]
    exact Category.comp_id _
  simp only [← Category.assoc (generator s),he]
  rw [homologyπ_naturality_assoc,← Category.assoc _ (cyclesMap (map f) 0),
    liftCycles_comp_cyclesMap,generator_map]
  change (chains Y).liftCycles ((singular Y).ιChainComplex (simplex (f.comp s))) 0 _ _ ≫
      (chains Y).homologyπ 0 ≫ (singular Y).homology₀ε (ModuleCat.of ℤ ℤ) =
    (chains X).liftCycles ((singular X).ιChainComplex (simplex s)) 0 _ _ ≫
      (chains X).homologyπ 0 ≫ (singular X).homology₀ε (ModuleCat.of ℤ ℤ)
  simp only [SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε]
end SingularChains

namespace CWEquivariant
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CWCellular CategoryTheory HomologicalComplex
variable {G X : Type} [Group G] [TopologicalSpace X] [T2Space X]
  [MulAction G X] [ContinuousConstSMul G X] [CWComplex (univ : Set X)]
  [∀ n, MulAction G (RelCWComplex.cell (univ : Set X) n)]
variable (hc : ∀ (g : G) n (i : RelCWComplex.cell (univ : Set X) n) (v : Disk n),
  g • RelCWComplex.map n i v = RelCWComplex.map n (g • i) v)

abbrev object (n : ℕ) : Rep ℤ G := Rep.of (rep (G:=G) (X:=X) n)
def differential (n : ℕ) : object (G:=G) (X:=X) (n+1) ⟶ object (G:=G) (X:=X) n :=
  Rep.ofHom (boundaryIntertwiner hc n)
lemma differential_comp (n : ℕ) : differential hc (n+1) ≫ differential hc n = 0 := by
  apply Rep.Hom.ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  exact congrArg (fun f => f x) (boundary_comp hc n)

def complex : ChainComplex (Rep ℤ G) ℕ :=
  ChainComplex.of (object (G:=G) (X:=X)) (differential hc) (differential_comp hc)

lemma complex_exactAt (n : ℕ)
    (hz : CategoryTheory.Limits.IsZero ((SingularChains.chains (univ : Set X)).homology (n+1))) :
    (complex hc).ExactAt (n+1) := by
  rw [exactAt_iff' _ (n+2) (n+1) n
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl)]
  change (ShortComplex.mk ((complex hc).d (n+2) (n+1)) ((complex hc).d (n+1) n) _).Exact
  have hd₁ : (complex hc).d (n+2) (n+1) = differential hc (n+1) := ChainComplex.of_d _ _ _
  have hd₂ : (complex hc).d (n+1) n = differential hc n := ChainComplex.of_d _ _ _
  simp only [hd₁,hd₂]
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  exact (boundary_exact hc n hz x).mp hx

def onSpace (g : G) : C((univ : Set X),(univ : Set X)) :=
  ⟨fun x => ⟨g • x.1,mem_univ _⟩,
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩

lemma augmentation_natural (g : G) :
    (skeletal hc g).cellMap 0 ≫ augmentation (C:=(univ : Set X)) =
      augmentation ≫ homologyMap (SingularChains.map (onSpace (X:=X) g)) 0 := by
  have := q_zero_isIso (C:=(univ : Set X))
  apply (cancel_epi (q (C:=(univ : Set X)) 0 0)).mp
  change q 0 0 ≫ homologyMap ((skeletal hc g).relativeMap 0) 0 ≫ augmentation = _
  rw [← Category.assoc,(skeletal hc g).q_natural,Category.assoc,q_augmentation,
    ← Category.assoc,q_augmentation,← homologyMap_comp,← homologyMap_comp]
  congr 1
  unfold SkeletalMap.absoluteMap
  rw [← SingularChains.map_comp,← SingularChains.map_comp]
  rfl

def augLinear : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) 0) →ₗ[ℤ] ℤ :=
  ((orientedIso (X:=X) 0).hom ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)).hom

include hc in
lemma augLinear_smul (g : G) (x : MonoidAlgebra ℤ (RelCWComplex.cell (univ : Set X) 0)) :
    augLinear (X:=X) (rep (G:=G) 0 g x) = augLinear (X:=X) x := by
  change (((orientedIso 0).hom ≫ augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    (rep (G:=G) 0 g x)) = _
  change (augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    ((orientedIso 0).hom (rep (G:=G) 0 g x)) = _
  rw [← orientedIso_smul hc]
  change ((skeletal hc g).cellMap 0 ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)) ((orientedIso 0).hom x) = _
  rw [← Category.assoc,augmentation_natural hc,Category.assoc,
    SingularChains.zeroAugmentation_natural]
  rfl

def aug : object (G:=G) (X:=X) 0 ⟶ Rep.trivial ℤ G ℤ :=
  Rep.ofHom ((augLinear (X:=X)).intertwiningMap_of_isIntertwiningMap _ _ (by
    intro g x
    exact augLinear_smul hc g x))

lemma d_aug : (complex hc).d 1 0 ≫ aug hc = 0 := by
  ext x
  change (augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
      ((orientedIso 0).hom (boundary 0 x)) = 0
  erw [oriented_boundary]
  change (CWCellular.d 0 ≫ augmentation ≫ SingularChains.zeroAugmentation (univ : Set X))
    ((orientedIso 1).hom x) = 0
  rw [← Category.assoc,d_augmentation,CategoryTheory.Limits.zero_comp]
  rfl

lemma aug_epi [PathConnectedSpace (univ : Set X)] : Epi (aug hc) := by
  apply ConcreteCategory.epi_of_surjective
  change Function.Surjective (((orientedIso 0).hom ≫ augmentation ≫
    SingularChains.zeroAugmentation (univ : Set X)) : _ → _)
  have := augmentation_epi (C:=(univ : Set X))
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

lemma aug_exact [PathConnectedSpace (univ : Set X)] :
    (ShortComplex.mk ((complex hc).d 1 0) (aug hc) (d_aug hc)).Exact := by
  rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep ℤ G) (ModuleCat ℤ)),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hx' : augmentation ((orientedIso 0).hom x) = 0 := by
    apply (ModuleCat.mono_iff_injective (SingularChains.zeroAugmentation (univ : Set X))).mp inferInstance
    rw [map_zero]
    exact hx
  obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (augmentation_exact (C:=(univ : Set X))) _ hx'
  refine ⟨(orientedIso 1).inv y,?_⟩
  apply (orientedIso 0).toLinearEquiv.injective
  change (orientedIso 0).hom (boundary 0 ((orientedIso 1).inv y)) = _
  rw [oriented_boundary]
  change CWCellular.d 0 (((orientedIso 1).inv ≫ (orientedIso 1).hom) y) = _
  rw [Iso.inv_hom_id]
  exact hy

attribute [instance] AddCommGroup.toIntModule
end CWEquivariant

namespace RegularProductR
open CategoryTheory
variable (k G I : Type) [CommRing k] [Group G]

abbrev Module := I → (G →₀ k)

def rightShift (g : G) : (G →₀ k) →ₗ[k] (G →₀ k) :=
  Finsupp.lmapDomain k k (fun x => x*g⁻¹)

@[simp] lemma rightShift_single (g x : G) (r : k) :
    rightShift k G g (Finsupp.single x r) = Finsupp.single (x*g⁻¹) r := by
  simp [rightShift]

lemma rightShift_one : rightShift k G 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro x r
  simp

lemma rightShift_mul (g h : G) :
    rightShift k G (g*h) = (rightShift k G g).comp (rightShift k G h) := by
  apply Finsupp.lhom_ext
  intro x r
  simp [mul_assoc]

def representation : Representation k G (Module k G I) where
  toFun g := LinearMap.pi (fun i => (rightShift k G g).comp (LinearMap.proj i))
  map_one' := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_one k G) (a i)
  map_mul' g h := by
    apply LinearMap.ext
    intro a
    funext i
    exact LinearMap.congr_fun (rightShift_mul k G g h) (a i)

abbrev rep : Rep k G := Rep.of (representation k G I)

end RegularProductR

namespace ProductCriterion
open CategoryTheory Representation
open scoped TensorProduct MonoidAlgebra MonoidalCategory
variable {k G I : Type} [CommRing k] [Group G]

lemma rightShift_eq_mul (g : G) (a : G →₀ k) :
    MonoidAlgebra.ofCoeff (RegularProductR.rightShift k G g a) =
      MonoidAlgebra.ofCoeff a * MonoidAlgebra.of k G g⁻¹ := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add,MonoidAlgebra.ofCoeff_add,ha,hb,add_mul]
  | single x r => simp [MonoidAlgebra.of_apply,MonoidAlgebra.single_mul_single]

variable (C : Rep k G)

def evalPair (i : I) : RegularProductR.Module k G I →ₗ[k] C →ₗ[k] C :=
  C.ρ.asAlgebraHom.toLinearMap.comp
    ((MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.comp (LinearMap.proj i))

lemma evalPair_invariant (i : I) (g : G)
    (a : RegularProductR.Module k G I) (c : C) :
    evalPair C i (RegularProductR.representation k G I g a) (C.ρ g c) = evalPair C i a c := by
  change C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (RegularProductR.rightShift k G g (a i))) (C.ρ g c) = _
  rw [rightShift_eq_mul,map_mul,Representation.asAlgebraHom_of]
  change C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) ((C.ρ g⁻¹) (C.ρ g c)) = _
  have h : (C.ρ g⁻¹) (C.ρ g c) = c := by
    change (C.ρ g⁻¹ * C.ρ g) c = c
    rw [← map_mul,inv_mul_cancel,map_one]
    rfl
  rw [h]
  rfl

def coordinate (i : I) :
    (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k] C :=
  Coinvariants.lift _ (TensorProduct.lift (evalPair C i)) (fun g => by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro a
    apply LinearMap.ext
    intro c
    exact evalPair_invariant C i g a c)

@[simp] lemma coordinate_mk_tmul (i : I)
    (a : RegularProductR.Module k G I) (c : C) :
    coordinate C i (Coinvariants.mk _ (a ⊗ₜ[k] c)) = C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) c := rfl

lemma coordinates_finite_span (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
    ∃ s : Finset C.ρ.asModule, ∀ i : I,
      C.ρ.asModuleEquiv.symm (coordinate C i y) ∈ Submodule.span k[G] (s : Set C.ρ.asModule) := by
  classical
  induction y using Coinvariants.induction_on with
  | h y =>
    induction y using TensorProduct.inductionOn with
    | tmul a c =>
      refine ⟨{C.ρ.asModuleEquiv.symm c},fun i => ?_⟩
      simp only [Finset.coe_singleton]
      apply Submodule.mem_span_singleton.mpr
      refine ⟨MonoidAlgebra.ofCoeff (a i),?_⟩
      apply C.ρ.asModuleEquiv.injective
      rw [Representation.asModuleEquiv_map_smul,LinearEquiv.apply_symm_apply,
        LinearEquiv.apply_symm_apply]
      rfl
    | add x y hx hy =>
      obtain ⟨sx,hx⟩ := hx
      obtain ⟨sy,hy⟩ := hy
      refine ⟨sx∪sy,fun i => ?_⟩
      simp only [map_add]
      apply Submodule.add_mem
      · exact Submodule.span_mono (by simp only [Finset.coe_union]; exact Set.subset_union_left) (hx i)
      · exact Submodule.span_mono (by simp only [Finset.coe_union]; exact Set.subset_union_right) (hy i)

variable {C} (D : Rep k G)

lemma map_asAlgebraHom (f : C ⟶ D) (a : k[G]) (c : C) :
    f.hom (C.ρ.asAlgebraHom a c) = D.ρ.asAlgebraHom a (f.hom c) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb]
  | single g r => simp [Representation.asAlgebraHom_single,f.hom.isIntertwining]

def tensorMap (f : C ⟶ D) : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants →ₗ[k]
    (RegularProductR.rep k G I ⊗ D).ρ.Coinvariants :=
  Coinvariants.map _ _ ((IntertwiningMap.id _).tensor f.hom)

lemma coordinate_natural (f : C ⟶ D) (i : I)
    (y : (RegularProductR.rep k G I ⊗ C).ρ.Coinvariants) :
    coordinate D i (tensorMap D f y) = f.hom (coordinate C i y) := by
  induction y using Coinvariants.induction_on with
  | h y =>
    induction y using TensorProduct.inductionOn with
    | add x y hx hy =>
      simp only [map_add]
      exact congrArg₂ (·+·) hx hy
    | tmul a c =>
      change D.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) (f.hom c) =
        f.hom (C.ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i)) c)
      exact (map_asAlgebraHom D f _ c).symm

variable (α : Type) [DecidableEq α]

omit [DecidableEq α] in
lemma free_algebra_action (a : k[G]) (c : Rep.free k G α) :
    (Rep.free k G α).ρ.asAlgebraHom a c = a • (c : α →₀ k[G]) := by
  exact (congrArg (free k G α).asModuleEquiv
    ((finsuppLEquivFreeAsModule k G α).map_smul a c)).symm

lemma coordinate_free_inverse_single (i : I) (j : α) (a : RegularProductR.Module k G I) :
    coordinate (Rep.free k G α) i
      ((Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm
        (Finsupp.single j a)) = Finsupp.single j (MonoidAlgebra.ofCoeff (a i)) := by
  change coordinate (Rep.free k G α) i
    (Rep.finsuppToCoinvariantsTensorFree _ _ (Finsupp.single j a)) = _
  rw [Rep.finsuppToCoinvariantsTensorFree_single]
  change (Rep.free k G α).ρ.asAlgebraHom (MonoidAlgebra.ofCoeff (a i))
    (Finsupp.single j (MonoidAlgebra.single 1 1)) = _
  rw [free_algebra_action,Finsupp.smul_single]
  change Finsupp.single j (MonoidAlgebra.ofCoeff (a i) * 1) = _
  rw [mul_one]

lemma coordinate_free_inverse_apply (i : I) (j : α) (z : α →₀ RegularProductR.Module k G I) :
    coordinate (Rep.free k G α) i
      ((Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm z) j =
      MonoidAlgebra.ofCoeff (z j i) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,Pi.add_apply,MonoidAlgebra.ofCoeff_add,hx,hy]
  | single l a =>
    rw [coordinate_free_inverse_single]
    by_cases h : l=j
    · subst l; simp
    · simp [h]

lemma free_coordinates_injective : Function.Injective
    (fun y : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants =>
        fun i : I => coordinate (Rep.free k G α) i y) := by
  intro x y h
  let E := Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α
  apply E.injective
  apply Finsupp.ext
  intro j
  funext i
  apply MonoidAlgebra.ofCoeff_injective
  have hh := congrArg (fun f : I → Rep.free k G α => f i j) h
  have hx := coordinate_free_inverse_apply α i j (E x)
  have hy := coordinate_free_inverse_apply α i j (E y)
  rw [E.symm_apply_apply] at hx hy
  exact hx.symm.trans (hh.trans hy)

lemma free_coordinates_surjective [Finite α] : Function.Surjective
    (fun y : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants =>
        fun i : I => coordinate (Rep.free k G α) i y) := by
  intro f
  let z : α →₀ RegularProductR.Module k G I :=
    (Finsupp.linearEquivFunOnFinite k (RegularProductR.Module k G I) α).symm
      (fun j i => (f i j).coeff)
  refine ⟨(Rep.coinvariantsTensorFreeLEquiv (RegularProductR.rep k G I) α).symm z,?_⟩
  funext i
  ext j
  rw [coordinate_free_inverse_apply]
  rfl

variable {D α}

def moduleMap (f : C ⟶ D) : C.ρ.asModule →ₗ[k[G]] D.ρ.asModule :=
  IntertwiningMap.equivLinearMapAsModule _ _ f.hom

@[simp] lemma moduleMap_apply (f : C ⟶ D) (c : C) :
    moduleMap f (C.ρ.asModuleEquiv.symm c) = D.ρ.asModuleEquiv.symm (f.hom c) := rfl

lemma kernel_fg_of_product_exact {α β : Type} [Finite α] (B : Rep k G)
    (f : B ⟶ Rep.free k G α) (g : Rep.free k G α ⟶ Rep.free k G β)
    (hfg : f ≫ g = 0)
    (hexact : ∀ I : Type,
      ∀ x : (RegularProductR.rep k G I ⊗ Rep.free k G α).ρ.Coinvariants,
        tensorMap (Rep.free k G β) g x = 0 →
          ∃ y : (RegularProductR.rep k G I ⊗ B).ρ.Coinvariants,
            tensorMap (Rep.free k G α) f y = x) : (moduleMap g).ker.FG := by
  classical
  let K := (moduleMap g).ker
  let z : K → Rep.free k G α := fun t => (Rep.free k G α).ρ.asModuleEquiv t.val
  obtain ⟨x,hx⟩ := free_coordinates_surjective (k:=k) (G:=G) (I:=K) α z
  have hcycle : tensorMap (Rep.free k G β) g x = 0 := by
    apply free_coordinates_injective β
    funext t
    dsimp only
    rw [coordinate_natural,map_zero]
    have hxt : coordinate (Rep.free k G α) t x = z t := congrFun hx t
    rw [hxt]
    change g.hom (z t) = 0
    have ht := t.property
    change moduleMap g t.val = 0 at ht
    exact congrArg (Rep.free k G β).ρ.asModuleEquiv ht
  obtain ⟨y,hy⟩ := hexact K x hcycle
  obtain ⟨s,hs⟩ := coordinates_finite_span B y
  refine Submodule.fg_def.mpr ⟨moduleMap f '' (s : Set B.ρ.asModule),
    s.finite_toSet.image _,le_antisymm ?_ ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨c,hc,rfl⟩
    change moduleMap g (moduleMap f c) = 0
    have h := congrArg (fun l : B ⟶ Rep.free k G β => l.hom (B.ρ.asModuleEquiv c)) hfg
    exact congrArg (Rep.free k G β).ρ.asModuleEquiv.symm h
  · intro t ht
    let t' : K := ⟨t,ht⟩
    have hm := Submodule.mem_map_of_mem (f:=moduleMap f) (hs t')
    rw [Submodule.map_span] at hm
    have he : moduleMap f (B.ρ.asModuleEquiv.symm (coordinate B t' y)) = t := by
      rw [moduleMap_apply]
      apply (Rep.free k G α).ρ.asModuleEquiv.injective
      rw [LinearEquiv.apply_symm_apply,← coordinate_natural,hy]
      exact congrFun hx t'
    exact he ▸ hm

lemma kernel_fg_of_tensor_homology_zero {α β : Type} [Finite α] (B : Rep k G)
    (f : B ⟶ Rep.free k G α) (g : Rep.free k G α ⟶ Rep.free k G β)
    (hfg : f ≫ g = 0)
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (((ShortComplex.mk f g hfg).map
        ((Rep.coinvariantsTensor k G).obj (RegularProductR.rep k G I))).homology)) :
    (moduleMap g).ker.FG := by
  apply kernel_fg_of_product_exact B f g hfg
  intro I x hx
  have he := (ShortComplex.exact_iff_isZero_homology _).mpr (hzero I)
  exact (ShortComplex.moduleCat_exact_iff _).mp he x hx

lemma product_resolution_exact (P : ProjectiveResolution (Rep.trivial k G k)) (n : ℕ)
    (hzero : ∀ I : Type, CategoryTheory.Limits.IsZero
      (groupHomology (RegularProductR.rep k G I) n)) (I : Type) :
    (P.complex.coinvariantsTensorObj (RegularProductR.rep k G I)).ExactAt n := by
  classical
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr
  exact (hzero I).of_iso (groupHomologyIso (RegularProductR.rep k G I) n P).symm

end ProductCriterion

end

end OAI
