import Mathlib
import OAI.GroupTheory.FiniteType.HurewiczInverse

namespace OAI

noncomputable section
namespace RepresentationKilling
attribute [-instance] AddCommGroup.toIntModule
variable {G M N : Type} [Group G] [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N] (ρ : Representation ℤ G M)
  (φ : M →ₗ[ℤ] N)

def stableKernel : Submodule (MonoidAlgebra ℤ G) ρ.asModule where
  carrier := {x | ∀ g : G, φ (ρ g (ρ.asModuleEquiv x)) = 0}
  zero_mem' := by intro g; simp
  add_mem' := by intro x y hx hy g; simp only [map_add,hx g,hy g,add_zero]
  smul_mem' := by
    intro r x hx g
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add r s hr hs => simp only [add_smul,map_add,hr,hs,add_zero]
    | single h a =>
      rw [Representation.asModuleEquiv_map_smul,Representation.asAlgebraHom_single]
      simp only [LinearMap.smul_apply]
      rw [(ρ g).map_smul, φ.map_smul]
      have hh := hx (g*h)
      rw [map_mul] at hh
      change φ (ρ g (ρ h (ρ.asModuleEquiv x))) = 0 at hh
      rw [hh,smul_zero]

theorem eq_zero {ι : Type} (z : ι → ρ.asModule)
    (hz : Submodule.span (MonoidAlgebra ℤ G) (Set.range z) = ⊤)
    (hk : ∀ g i, φ (ρ g (ρ.asModuleEquiv (z i))) = 0) : φ = 0 := by
  have hle : Submodule.span (MonoidAlgebra ℤ G) (Set.range z) ≤ stableKernel ρ φ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact fun g => hk g i
  rw [hz] at hle
  ext x
  have h := hle (Submodule.mem_top (x:=ρ.asModuleEquiv.symm x)) (1 : G)
  simpa using h
attribute [instance] AddCommGroup.toIntModule
end RepresentationKilling

namespace PresentationGeometry.CellCoverExtension
open Set Topology Cells CWExtension CategoryTheory CategoryTheory.Limits HomologicalComplex SingularChains
open HurewiczConstruction
variable {X ι Q : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
  [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
  {k n : ℕ} (f : C(boundary k (n+3),X)) (b : X) (Z : FiberBundleCore ι X Q)
  (pot : ι → X → Q) (s : C(boundary k (n+3),Z.TotalSpace))
  (hs : ∀ c, Z.proj (s c) = f c)
  (hpot : ∀ i j x q, Z.coordChange i j x q = pot j x * (pot i x)⁻¹ * q)
  [Nonempty X] [CWComplex (univ : Set X)] [RelCWComplex.FiniteType (univ : Set X)]
  (hdim : ∀ m, RelCWComplex.cell (univ : Set X) m → m < n+3)

include hdim in

lemma critical_homology_zero
    (hgen : letI := CoreDeck.action Z
      letI := CoreDeck.continuousAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Qᵐᵒᵖ)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Qᵐᵒᵖ) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    IsZero ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
  let := CoreDeck.action Z
  let := CoreDeck.continuousAction Z (CoreDeck.of_potential Z pot hpot)
  have hzero : (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom = 0 := by
    apply RepresentationKilling.eq_zero (homologyRep (G:=Qᵐᵒᵖ) (X:=Z.TotalSpace) (n+2))
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom
      (fun i : Fin k => sphereModuleClass (G:=Qᵐᵒᵖ) (n+2) (s.comp (boundarySlice i))) hgen
    intro q i
    have hk := deck_attaching_homology_killed f b Z pot s hs hpot rfl i q.unop (n+2) (by omega)
    exact congrArg (fun a => a (SingularSphereCycle.fundamentalClass (n+2))) hk
  have hsur := oldLift_homology_surjective f b Z pot s hs hpot hdim (n+2) (by omega)
  let : Subsingleton ((chains (coveringCore f b Z pot s hs hpot).TotalSpace).homology (n+2)) := by
    constructor
    intro u v
    obtain ⟨u,rfl⟩ := hsur u
    obtain ⟨v,rfl⟩ := hsur v
    change (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom u =
      (homologyMap (map (oldLift f b Z pot s hs hpot)) (n+2)).hom v
    rw [hzero]
    rfl
  exact ModuleCat.isZero_of_subsingleton _

include hdim in

theorem coveringCore_connectivity [SimplyConnectedSpace Z.TotalSpace]
    (hπ : ∀ p ≤ n+1, ∀ z : Z.TotalSpace, Subsingleton (HomotopyGroup (Fin p) Z.TotalSpace z))
    (hgen : letI := CoreDeck.action Z
      letI := CoreDeck.continuousAction Z (CoreDeck.of_potential Z pot hpot)
      Submodule.span (MonoidAlgebra ℤ Qᵐᵒᵖ)
        (Set.range (fun i : Fin k => sphereModuleClass (G:=Qᵐᵒᵖ) (n+2) (s.comp (boundarySlice i)))) = ⊤) :
    ∀ p ≤ n+2, ∀ z : (coveringCore f b Z pot s hs hpot).TotalSpace,
      Subsingleton (HomotopyGroup (Fin p) (coveringCore f b Z pot s hs hpot).TotalSpace z) := by
  let := coveringCore_simplyConnected f b Z pot s hs hpot (by omega)
  apply homotopy_trivial_of_homology_zero (n+2)
  intro j hj hjn
  by_cases he : j = n+2
  · subst j
    exact critical_homology_zero f b Z pot s hs hpot hdim hgen
  · have hj1 : j ≤ n+1 := by omega
    have hOld : IsZero ((chains Z.TotalSpace).homology j) := by
      cases j with
      | zero => omega
      | succ j => exact homology_zero_of_homotopy (fun p hp z => hπ p (hp.trans hj1) z) ⟨b,(1:Q)⟩
    let := ModuleCat.isZero_iff_subsingleton.mp hOld
    let := (oldLift_homology_surjective f b Z pot s hs hpot hdim j (by omega)).subsingleton
    exact ModuleCat.isZero_of_subsingleton _
end PresentationGeometry.CellCoverExtension

namespace CWCellular
section
open Set Topology CWExtension CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

def topCycleMap (n : ℕ) : (absolute (C := C) (n+2)).homology (n+1) ⟶
    ModuleCat.of ℤ (LinearMap.ker (d (C := C) n).hom) :=
  ModuleCat.ofHom ((q (n+1) (n+1)).hom.codRestrict _ (by
    intro x
    change d n (q (n+1) (n+1) x) = 0
    exact congrArg (fun f => f x) (q_d (C := C) n)))

lemma topCycleMap_bijective (n : ℕ) : Function.Bijective (topCycleMap (C := C) n) := by
  constructor
  · intro x y h
    exact top_injective (n+1) (congrArg Subtype.val h)
  · intro z
    obtain ⟨x,hx⟩ := (top_image (C := C) n z.1).mp z.2
    exact ⟨x,Subtype.ext hx⟩

def topCycleIso (n : ℕ) : (absolute (C := C) (n+2)).homology (n+1) ≅
    ModuleCat.of ℤ (LinearMap.ker (d (C := C) n).hom) := by
  letI := (ConcreteCategory.isIso_iff_bijective _).mpr (topCycleMap_bijective (C := C) n)
  exact asIso (topCycleMap n)

lemma exact_of_homology_zero (n : ℕ)
    (h : Limits.IsZero ((chains C).homology (n+1))) :
    (ShortComplex.mk (d (C := C) (n+1)) (d n) (d_comp_d n)).Exact := by
  have := homology_toComplex_isIso (C := C) (n+3) (n+1) (by omega)
  have hz : Limits.IsZero ((absolute (C := C) (n+3)).homology (n+1)) :=
    h.of_iso (asIso (homologyMap (SingularChains.map (skelToComplex (n+3))) (n+1)))
  have : Epi (delta (C := C) (n+1)) := (shortExact (C := C) (n+2)).epi_δ _ _ rfl hz
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz'
  obtain ⟨x,hx⟩ := (top_image (C := C) n z).mp hz'
  obtain ⟨y,hy⟩ := (ModuleCat.epi_iff_surjective (delta (C := C) (n+1))).mp inferInstance x
  refine ⟨y,?_⟩
  change q (n+1) (n+1) (delta (n+1) y) = z
  rw [hy,hx]

lemma complex_exactAt (n : ℕ)
    (h : Limits.IsZero ((chains C).homology (n+1))) :
    (complex (C := C)).ExactAt (n+1) := by
  rw [exactAt_iff' _ (n+2) (n+1) n
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl)]
  have hd : ChainComplex.of.d (cell (C := C)) d (n+2) (n+1) = d (n+1) :=
    ChainComplex.of_d _ _ (n+1)
  simpa only [sc', shortComplexFunctor', complex, hd, ChainComplex.of_d] using exact_of_homology_zero n h

lemma contractible_exactAt [ContractibleSpace C] (n : ℕ) :
    (complex (C := C)).ExactAt (n+1) :=
  complex_exactAt n (SingularChains.contractible_homology_isZero (n+1) (by omega))

attribute [instance] AddCommGroup.toIntModule
end

section
open Set Topology CWExtension CategoryTheory HomologicalComplex SingularChains
attribute [-instance] AddCommGroup.toIntModule
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma q_zero_isIso : IsIso (q (C := C) 0 0) := by
  have := q_mono (C := C) 0 0 le_rfl
  have : Epi ((sequence (C := C) 0).g.f 0) :=
    (ModuleCat.epi_iff_surjective _).mpr (RelativeChains.projection_surjective _ _)
  have : Epi (q (C := C) 0 0) := epi_homologyMap_of_epi_of_not_rel _ _ (by
    intro j
    change ¬ j+1 = 0
    omega)
  exact isIso_of_mono_of_epi _

def zeroIso : (absolute (C := C) 1).homology 0 ≅ cell (C := C) 0 := by
  letI := q_zero_isIso (C := C)
  exact asIso (q 0 0)

def augmentation : cell (C := C) 0 ⟶ (chains C).homology 0 :=
  (zeroIso (C := C)).inv ≫ homologyMap (SingularChains.map (skelToComplex 1)) 0

lemma q_augmentation : q (C := C) 0 0 ≫ augmentation =
    homologyMap (SingularChains.map (skelToComplex 1)) 0 := by
  change (zeroIso (C := C)).hom ≫ ((zeroIso (C := C)).inv ≫ _) = _
  rw [← Category.assoc,Iso.hom_inv_id,Category.id_comp]

lemma incl_toComplex (n : ℕ) : SingularChains.map (skelIncl (C := C) n) ≫
    SingularChains.map (skelToComplex (n+1)) = SingularChains.map (skelToComplex n) := by
  rw [← SingularChains.map_comp]
  rfl

lemma d_augmentation : d (C := C) 0 ≫ augmentation = 0 := by
  rw [d,Category.assoc,q_augmentation]
  rw [← incl_toComplex 1,homologyMap_comp,← Category.assoc,← sequence_f]
  change ((shortExact (C := C) 1).δ 1 0 rfl ≫ homologyMap (sequence 1).f 0) ≫ _ = 0
  erw [(shortExact (C := C) 1).δ_comp 1 0 rfl,CategoryTheory.Limits.zero_comp]

lemma augmentation_exact : (ShortComplex.mk (d (C := C) 0) augmentation d_augmentation).Exact := by
  have := homology_toComplex_isIso (C := C) 2 0 (by omega)
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro z hz
  let x := (zeroIso (C := C)).inv z
  have hx : homologyMap (sequence (C := C) 1).f 0 x = 0 := by
    apply (ModuleCat.mono_iff_injective
      (homologyMap (SingularChains.map (skelToComplex (C := C) 2)) 0)).mp inferInstance
    erw [map_zero]
    change (homologyMap (sequence (C := C) 1).f 0 ≫
      homologyMap (SingularChains.map (skelToComplex 2)) 0) x = 0
    have he : homologyMap (sequence (C := C) 1).f 0 =
        homologyMap (SingularChains.map (skelIncl 1)) 0 :=
      congrArg (fun f : absolute (C := C) 1 ⟶ absolute 2 => homologyMap f 0) (sequence_f 1)
    erw [he,← homologyMap_comp,incl_toComplex]
    exact hz
  obtain ⟨y,hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    ((shortExact (C := C) 1).homology_exact₁ 1 0 rfl) x hx
  refine ⟨y,?_⟩
  change q 0 0 (delta 0 y) = z
  change delta 0 y = x at hy
  rw [hy]
  exact congrArg (fun f => f z) (zeroIso (C := C)).inv_hom_id

lemma augmentation_epi : Epi (augmentation (C := C)) := by
  have : Epi (homologyMap (sequence (C := C) 1).f 0) :=
    ((shortExact (C := C) 1).homology_exact₂ 0).epi_f
      ((CWSkeletalHomology.homology_isZero (C := C) 1 0 (by omega)).eq_of_tgt _ _)
  have : Epi (homologyMap (SingularChains.map (skelIncl (C := C) 1)) 0) := by
    rwa [← sequence_f]
  have := homology_toComplex_isIso (C := C) 2 0 (by omega)
  unfold augmentation
  rw [← incl_toComplex 1,homologyMap_comp]
  infer_instance

def contractibleZeroIso [ContractibleSpace C] : (chains C).homology 0 ≅ ModuleCat.of ℤ ℤ := by
  let e := (ContractibleSpace.hequiv_unit C).some
  haveI := SingularChains.homotopyEquiv_quasiIso e
  exact asIso (homologyMap (SingularChains.map e.toFun) 0) ≪≫ SingularChains.unique_homologyZeroIso

def integralAugmentation [ContractibleSpace C] : cell (C := C) 0 ⟶ ModuleCat.of ℤ ℤ :=
  augmentation ≫ (contractibleZeroIso (C := C)).hom

attribute [instance] AddCommGroup.toIntModule
end

open Set Topology CWExtension CategoryTheory HomologicalComplex
variable {X Y Z : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  [TopologicalSpace Z] [T2Space Z] {C : Set X} {D : Set Y} {E : Set Z}
  [CWComplex C] [CWComplex D] [CWComplex E]

structure SkeletalMap (C : Set X) (D : Set Y) [CWComplex C] [CWComplex D] where
  toMap : C(X,Y)
  maps : ∀ n : ℕ, MapsTo toMap (Skel C n) (Skel D n)

namespace SkeletalMap
variable (f : SkeletalMap C D)
def onSkel (n : ℕ) : C(Skel C n,Skel D n) :=
  ⟨fun x => ⟨f.toMap x,f.maps n x.2⟩,(f.toMap.continuous.comp continuous_subtype_val).subtype_mk _⟩

def absoluteMap (n : ℕ) : absolute (C := C) n ⟶ absolute (C := D) n :=
  SingularChains.map (f.onSkel n)

lemma lower_maps (n : ℕ) : MapsTo (f.onSkel (n+1)) (CWCollar.lower (C := C) n)
    (CWCollar.lower (C := D) n) := fun _ hx => f.maps n hx

def relativeMap (n : ℕ) : relative (C := C) n ⟶ relative (C := D) n :=
  RelativeChains.map _ _ (f.onSkel (n+1)) (f.lower_maps n)

def sequenceMap (n : ℕ) : sequence (C := C) n ⟶ sequence (C := D) n where
  τ₁ := f.absoluteMap n
  τ₂ := f.absoluteMap (n+1)
  τ₃ := f.relativeMap n
  comm₁₂ := by
    change f.absoluteMap n ≫ (sequence (C := D) n).f =
      (sequence (C := C) n).f ≫ f.absoluteMap (n+1)
    rw [sequence_f,sequence_f]
    unfold absoluteMap
    erw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl
  comm₂₃ := by
    ext k a
    rfl

def cellMap (n : ℕ) : cell (C := C) n ⟶ cell (C := D) n :=
  homologyMap (f.relativeMap n) n

lemma q_natural (n k : ℕ) : q (C := C) n k ≫ homologyMap (f.relativeMap n) k =
    homologyMap (f.absoluteMap (n+1)) k ≫ q (C := D) n k := by
  unfold q
  erw [← homologyMap_comp,← homologyMap_comp]
  exact congrArg (fun g => homologyMap g k) (f.sequenceMap n).comm₂₃.symm

lemma delta_natural (n : ℕ) : delta (C := C) n ≫ homologyMap (f.absoluteMap (n+1)) n =
    f.cellMap (n+1) ≫ delta (C := D) n :=
  HomologicalComplex.HomologySequence.δ_naturality (f.sequenceMap (n+1))
    (shortExact (C := C) (n+1)) (shortExact (C := D) (n+1)) (n+1) n rfl

lemma d_natural (n : ℕ) : d (C := C) n ≫ f.cellMap n = f.cellMap (n+1) ≫ d (C := D) n := by
  unfold d
  rw [Category.assoc]
  change delta n ≫ (q n n ≫ homologyMap (f.relativeMap n) n) = _
  rw [f.q_natural,← Category.assoc,f.delta_natural,Category.assoc]

def chainMap : complex (C := C) ⟶ complex (C := D) :=
  ChainComplex.ofHom (fun n => f.cellMap n) (fun n => by simpa only [complex,ChainComplex.of_d] using (f.d_natural n).symm)

end SkeletalMap
end CWCellular

attribute [-instance] AddCommGroup.toIntModule

end

end OAI
