import Mathlib
import OAI.GroupTheory.FiniteType.CWCellular

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace CWCellular
section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma skelIncl_homology_isIso (n k : ℕ) (hk : k+1 < n) :
    IsIso (homologyMap (SingularChains.map (skelIncl (C := C) n)) k) := by
  rw [← sequence_f]
  have hmono : Mono (homologyMap (sequence (C := C) n).f k) :=
    ((shortExact (C := C) n).homology_exact₁ (k+1) k rfl).mono_g
      ((CWSkeletalHomology.homology_isZero (C := C) n (k+1) (by omega)).eq_of_src _ _)
  have hepi : Epi (homologyMap (sequence (C := C) n).f k) :=
    ((shortExact (C := C) n).homology_exact₂ k).epi_f
      ((CWSkeletalHomology.homology_isZero (C := C) n k (by omega)).eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hmono hepi

lemma skelLE_homology_isIso {m n k : ℕ} (h : m ≤ n) (hk : k+1 < m) :
    IsIso (homologyMap (SingularChains.map (skelLE (C := C) h)) k) := by
  induction n,h using Nat.le_induction with
  | base =>
    have he : skelLE (C := C) (le_refl m) = ContinuousMap.id _ := rfl
    rw [he,SingularChains.map_id,homologyMap_id]
    infer_instance
  | succ n h ih =>
    have he : skelLE (C := C) (Nat.le.step h) = (skelIncl n).comp (skelLE h) := rfl
    rw [he,SingularChains.map_comp,homologyMap_comp]
    have := ih
    have := skelIncl_homology_isIso (C := C) n k (by omega)
    infer_instance

lemma toComplex_injective (n k : ℕ) :
    Function.Injective ((SingularChains.map (skelToComplex (C := C) n)).f k) := by
  intro a b hab
  apply SingularSubspace.inclusion_injective (Skel C n) k
  have he : (SingularSubspace.inclusionMap C).comp (skelToComplex n) =
      SingularSubspace.inclusionMap (Skel C n) := rfl
  rw [← he,SingularChains.map_comp,HomologicalComplex.comp_f]
  change (SingularChains.map (SingularSubspace.inclusionMap C)).f k
      ((SingularChains.map (skelToComplex n)).f k a) = _
  rw [hab]
  rfl

lemma toComplex_comp {m n : ℕ} (h : m ≤ n) :
    SingularChains.map (skelLE (C := C) h) ≫ SingularChains.map (skelToComplex n) =
      SingularChains.map (skelToComplex m) := by
  rw [← SingularChains.map_comp]
  rfl

lemma chain_lift (k : ℕ) (c : (chains C).X k) : ∃ n, ∃ b : (absolute (C := C) n).X k,
    (SingularChains.map (skelToComplex n)).f k b = c := by
  let S : Submodule ℤ ((chains C).X k) :=
    { carrier := {c | ∃ n, ∃ b : (absolute (C := C) n).X k,
        (SingularChains.map (skelToComplex n)).f k b = c}
      zero_mem' := ⟨0,0,map_zero _⟩
      add_mem' := by
        rintro a b ⟨m,a,rfl⟩ ⟨n,b,rfl⟩
        refine ⟨max m n,(SingularChains.map (skelLE (le_max_left m n))).f k a +
          (SingularChains.map (skelLE (le_max_right m n))).f k b,?_⟩
        rw [map_add]
        change (SingularChains.map (skelLE (le_max_left m n)) ≫
            SingularChains.map (skelToComplex (max m n))).f k a +
          (SingularChains.map (skelLE (le_max_right m n)) ≫
            SingularChains.map (skelToComplex (max m n))).f k b = _
        rw [toComplex_comp,toComplex_comp]
      smul_mem' := by
        rintro a b ⟨n,b,rfl⟩
        refine ⟨n, a • b, ?_⟩
        simpa only [← Int.cast_smul_eq_zsmul ℤ, Int.cast_id] using
          map_zsmul ((SingularChains.map (skelToComplex (C := C) n)).f k).hom a b }
  apply SingularSupport.induction_on S _ c
  intro f
  have hf : Continuous (fun x => (f x : X)) := continuous_subtype_val.comp f.continuous
  obtain ⟨n,hn⟩ := compact_subset_skel (isCompact_range hf) (by
    rintro _ ⟨x,rfl⟩; exact (f x).2)
  let g : C(Std k,Skel C n) := ⟨fun x => ⟨f x,hn (mem_range_self x)⟩,hf.subtype_mk _⟩
  refine ⟨n,SingularSupport.gen g,?_⟩
  rw [SingularSupport.map_gen]
  rfl

lemma chain_lift_above (k m : ℕ) (c : (chains C).X k) :
    ∃ n, ∃ _ : m ≤ n, ∃ b : (absolute (C := C) n).X k,
      (SingularChains.map (skelToComplex n)).f k b = c := by
  obtain ⟨n,b,hb⟩ := chain_lift k c
  refine ⟨max m n,le_max_left m n,(SingularChains.map (skelLE (le_max_right m n))).f k b,?_⟩
  change (SingularChains.map (skelLE (le_max_right m n)) ≫
    SingularChains.map (skelToComplex (max m n))).f k b = c
  rw [toComplex_comp,hb]

lemma chain_homologyMap_class {K L : ChainComplex (ModuleCat ℤ) ℕ} (f : K ⟶ L)
    (k : ℕ) (c : ModuleHomology.Cycles (K.sc k)) :
    homologyMap f k (ModuleHomology.classMap (K.sc k) c) =
      ModuleHomology.classMap (L.sc k)
        (ModuleHomology.cyclesMap ((shortComplexFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).map f) c) :=
  ModuleHomology.homologyMap_class _ _

lemma homology_toComplex_surjective (m k : ℕ) (hk : k+1 < m) :
    Function.Surjective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  intro a
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((chains C).sc k) a
  obtain ⟨n,h,b,hb⟩ := chain_lift_above k m c.1
  have hbcycle : (absolute (C := C) n).d k ((ComplexShape.down ℕ).next k) b = 0 := by
    apply toComplex_injective (C := C) n _
    rw [map_zero]
    have he := congrArg (fun f => f b) ((SingularChains.map (skelToComplex (C := C) n)).comm k ((ComplexShape.down ℕ).next k)).symm
    change (SingularChains.map (skelToComplex n)).f _
      ((absolute (C := C) n).d k _ b) = (chains C).d k _
      ((SingularChains.map (skelToComplex n)).f k b) at he
    rw [he,hb]
    exact c.2
  let b' : ModuleHomology.Cycles ((absolute (C := C) n).sc k) := ⟨b,hbcycle⟩
  have := skelLE_homology_isIso (C := C) h hk
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (homologyMap
    (SingularChains.map (skelLE (C := C) h)) k)).mp inferInstance
      (ModuleHomology.classMap ((absolute (C := C) n).sc k) b')
  refine ⟨z,?_⟩
  rw [← toComplex_comp h,homologyMap_comp]
  change homologyMap (SingularChains.map (skelToComplex n)) k
    (homologyMap (SingularChains.map (skelLE h)) k z) = _
  rw [hz]
  rw [chain_homologyMap_class]
  congr 1
  exact Subtype.ext hb

lemma homology_toComplex_injective (m k : ℕ) (hk : k+1 < m) :
    Function.Injective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((absolute (C := C) m).sc k) a
  erw [chain_homologyMap_class,ModuleHomology.classMap_zero_iff] at ha
  obtain ⟨b,hb⟩ := ha
  obtain ⟨n,h,b',hb'⟩ := chain_lift_above ((ComplexShape.down ℕ).prev k) m b
  have he : (absolute (C := C) n).d ((ComplexShape.down ℕ).prev k) k b' =
      (SingularChains.map (skelLE h)).f k c.1 := by
    apply toComplex_injective (C := C) n k
    have hd := congrArg (fun f => f b')
      ((SingularChains.map (skelToComplex (C := C) n)).comm ((ComplexShape.down ℕ).prev k) k).symm
    change (SingularChains.map (skelToComplex n)).f k
      ((absolute (C := C) n).d _ k b') = (chains C).d _ k
      ((SingularChains.map (skelToComplex n)).f _ b') at hd
    rw [hd,hb']
    change (chains C).d _ k b = (SingularChains.map (skelLE h) ≫
      SingularChains.map (skelToComplex n)).f k c.1
    rw [toComplex_comp]
    exact hb
  have := skelLE_homology_isIso (C := C) h hk
  apply (ModuleCat.mono_iff_injective (homologyMap (SingularChains.map (skelLE (C := C) h)) k)).mp
    inferInstance
  erw [map_zero,chain_homologyMap_class,ModuleHomology.classMap_zero_iff]
  exact ⟨b',he⟩

lemma homology_toComplex_isIso (m k : ℕ) (hk : k+1 < m) :
    IsIso (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨homology_toComplex_injective m k hk,homology_toComplex_surjective m k hk⟩

attribute [instance] AddCommGroup.toIntModule
end

section
attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X] [T2Space X] {C : Set X} [CWComplex C]

lemma skelIncl_homology_epi (n k : ℕ) (hk : k < n) :
    Epi (homologyMap (SingularChains.map (skelIncl (C := C) n)) k) := by
  rw [← sequence_f]
  exact ((shortExact (C := C) n).homology_exact₂ k).epi_f
    ((CWSkeletalHomology.homology_isZero (C := C) n k (by omega)).eq_of_tgt _ _)

lemma skelLE_homology_epi {m n k : ℕ} (h : m ≤ n) (hk : k < m) :
    Epi (homologyMap (SingularChains.map (skelLE (C := C) h)) k) := by
  induction n,h using Nat.le_induction with
  | base =>
    have he : skelLE (C := C) (le_refl m) = ContinuousMap.id _ := rfl
    rw [he,SingularChains.map_id,homologyMap_id]
    infer_instance
  | succ n h ih =>
    have he : skelLE (C := C) (Nat.le.step h) = (skelIncl n).comp (skelLE h) := rfl
    rw [he,SingularChains.map_comp,homologyMap_comp]
    have := ih
    have := skelIncl_homology_epi (C := C) n k (by omega)
    infer_instance

lemma homology_toComplex_surjective_top (m k : ℕ) (hk : k < m) :
    Function.Surjective (homologyMap (SingularChains.map (skelToComplex (C := C) m)) k) := by
  intro a
  obtain ⟨c,rfl⟩ := ModuleHomology.classMap_surjective ((chains C).sc k) a
  obtain ⟨n,h,b,hb⟩ := chain_lift_above k m c.1
  have hbcycle : (absolute (C := C) n).d k ((ComplexShape.down ℕ).next k) b = 0 := by
    apply toComplex_injective (C := C) n _
    rw [map_zero]
    have he := congrArg (fun f => f b) ((SingularChains.map (skelToComplex (C := C) n)).comm k ((ComplexShape.down ℕ).next k)).symm
    change (SingularChains.map (skelToComplex n)).f _
      ((absolute (C := C) n).d k _ b) = (chains C).d k _
      ((SingularChains.map (skelToComplex n)).f k b) at he
    rw [he,hb]
    exact c.2
  let b' : ModuleHomology.Cycles ((absolute (C := C) n).sc k) := ⟨b,hbcycle⟩
  have := skelLE_homology_epi (C := C) h hk
  obtain ⟨z,hz⟩ := (ModuleCat.epi_iff_surjective (homologyMap
    (SingularChains.map (skelLE (C := C) h)) k)).mp inferInstance
      (ModuleHomology.classMap ((absolute (C := C) n).sc k) b')
  refine ⟨z,?_⟩
  rw [← toComplex_comp h,homologyMap_comp]
  change homologyMap (SingularChains.map (skelToComplex n)) k
    (homologyMap (SingularChains.map (skelLE h)) k z) = _
  rw [hz]
  rw [chain_homologyMap_class]
  congr 1
  exact Subtype.ext hb

attribute [instance] AddCommGroup.toIntModule
end

attribute [-instance] AddCommGroup.toIntModule
open Set Topology CWExtension CategoryTheory HomologicalComplex SingularChains
variable {X A : Type} [TopologicalSpace X] [T2Space X] [TopologicalSpace A]
  [CWComplex (univ : Set X)] (f : C(A,X)) (he : IsEmbedding f)
  (m : ℕ) (hr : Set.range f = Skel (univ : Set X) m)

def skeletonHomeo : A ≃ₜ Skel (univ : Set X) m :=
  he.toHomeomorph.trans (Homeomorph.setCongr hr)

lemma skeleton_factor : (Homeomorph.Set.univ X : C((univ : Set X),X)).comp
      ((skelToComplex m).comp (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) = f := rfl

include he hr in
lemma homology_skeleton_surjective (k : ℕ) (hk : k < m) :
    Function.Surjective (homologyMap (map f) k) := by
  rw [← skeleton_factor f he m hr,map_comp,map_comp,homologyMap_comp,homologyMap_comp]
  let := map_iso (skeletonHomeo f he m hr)
  let := map_iso (Homeomorph.Set.univ X)
  have : IsIso (homologyMap (map (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) k) :=
    inferInstance
  have : IsIso (homologyMap (map (Homeomorph.Set.univ X : C((univ : Set X),X))) k) := inferInstance
  have h1 : Function.Surjective (homologyMap (map (skeletonHomeo f he m hr : C(A,Skel (univ : Set X) m))) k) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have h2 : Function.Surjective (homologyMap (map (skelToComplex (C := (univ : Set X)) m)) k) :=
    homology_toComplex_surjective_top (C := (univ : Set X)) m k hk
  have h3 : Function.Surjective (homologyMap (map (Homeomorph.Set.univ X : C((univ : Set X),X))) k) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  exact h3.comp (h2.comp h1)

include he hr in
lemma homology_skeleton_bijective (k : ℕ) (hk : k+1 < m) :
    Function.Bijective (homologyMap (map f) k) := by
  rw [← skeleton_factor f he m hr,map_comp,map_comp,homologyMap_comp,homologyMap_comp]
  let := map_iso (skeletonHomeo f he m hr)
  let := map_iso (Homeomorph.Set.univ X)
  have := homology_toComplex_isIso (C := (univ : Set X)) m k hk
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

attribute [instance] AddCommGroup.toIntModule
end CWCellular

end

end OAI
