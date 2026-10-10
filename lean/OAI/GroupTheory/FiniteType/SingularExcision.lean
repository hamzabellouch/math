import Mathlib
import OAI.GroupTheory.FiniteType.QuotientComplex

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
namespace SingularExcision
open Classical Set CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma eventually_split (A B : Set X) (hcover : interior A ∪ interior B = univ) {n : ℕ}
    (c : (chains X).X n) :
    ∀ᶠ k in Filter.atTop, iterate X n k c ∈
      SingularSupport.span (fun f => SingularSubspace.Within B f ∨ SingularSubspace.Within A f) := by
  let U : Bool → Set X := fun b => if b then interior A else interior B
  have hU : ∀ b, IsOpen (U b) := by intro b; cases b <;> exact isOpen_interior
  have hUc : ⋃ b, U b = univ := by
    ext x
    simp only [mem_iUnion,mem_univ,iff_true]
    have hx : x ∈ interior A ∪ interior B := hcover ▸ mem_univ x
    rcases hx with hx|hx
    · exact ⟨true,hx⟩
    · exact ⟨false,hx⟩
  filter_upwards [SmallChains.eventually_small U hU hUc c] with k hk
  apply SingularSupport.span_mono _ hk
  intro f hf
  obtain ⟨b,hb⟩ := hf
  cases b with
  | false => exact Or.inl (hb.trans interior_subset)
  | true => exact Or.inr (hb.trans interior_subset)

lemma split_chain (A B : Set X) (hcover : interior A ∪ interior B = univ) {n : ℕ}
    (c : (chains X).X n) : ∃ k, ∃ d : (chains B).X n,
      (RelativeChains.projection A).f n (iterate X n k c) =
        (RelativeChains.projection A).f n ((map (SingularSubspace.inclusionMap B)).f n d) := by
  obtain ⟨k,hk⟩ := (eventually_split A B hcover c).exists
  let t := SingularSupport.cut (SingularSubspace.Within B) (iterate X n k c)
  have ht : t ∈ SingularSubspace.group B n := SingularSupport.cut_mem _ _
  refine ⟨k,SingularSubspace.lift B n t,?_⟩
  rw [SingularSubspace.lift_inclusion_apply B ht,RelativeChains.projection_eq_iff]
  exact SingularSupport.sub_cut_mem hk

end SingularExcision

namespace RelativeChains
open Set CategoryTheory SingularChains SingularSubdivision
variable {X : Type} [TopologicalSpace X]

lemma inclusion_d (A B : Set X) (n m : ℕ)
    (c : (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).X n) :
    (inclusion A B).f m ((complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).d n m c) =
      (complex A).d n m ((inclusion A B).f n c) :=
  (congrArg (fun h : (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).X n ⟶ (complex A).X m => h c)
    ((inclusion A B).comm n m)).symm

end RelativeChains

namespace SingularExcision
open Set CategoryTheory SingularChains SingularSubdivision RelativeChains HomologicalComplex
variable {X : Type} [TopologicalSpace X]

abbrev scInclusion (A B : Set X) (n : ℕ) :
    (RelativeChains.complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).sc' (n+1) n (n-1) ⟶
      (RelativeChains.complex A).sc' (n+1) n (n-1) :=
  (shortComplexFunctor' (ModuleCat ℤ) (ComplexShape.down ℕ) (n+1) n (n-1)).map (inclusion A B)

lemma scInclusion_surjective (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    Function.Surjective (ShortComplex.homologyMap (scInclusion A B n)) := by
  apply ModuleHomology.homologyMap_surjective
  intro c
  obtain ⟨z,hz⟩ := projection_surjective A n c.1
  have hc : (chains X).d n (n-1) z ∈ SingularSubspace.group A (n-1) := by
    apply (projection_zero_iff A _ _).mp
    rw [← differential_projection,hz]
    exact c.2
  obtain ⟨k,d,hd⟩ := split_chain A B hcover z
  let A' := (SingularSubspace.inclusionMap B) ⁻¹' A
  have hd' : (inclusion A B).f n ((projection A').f n d) =
      (projection A).f n (iterate X n k z) := hd.symm
  have hdCycle : (RelativeChains.complex A').d n (n-1) ((projection A').f n d) = 0 := by
    apply inclusion_injective A B (n-1)
    rw [inclusion_d,hd',differential_projection,iterate_apply_comm,map_zero]
    exact (projection_zero_iff A _ _).mpr (SingularSubspace.iterate_mem A hc k)
  refine ⟨⟨(projection A').f n d,hdCycle⟩,(projection A).f (n+1) (sumPrism X n k z),?_⟩
  rw [← hz]
  change (RelativeChains.complex A).d (n+1) n ((projection A).f (n+1) (sumPrism X n k z)) =
    (projection A).f n z - (inclusion A B).f n ((projection A').f n d)
  rw [RelativeChains.cycle_difference A n k z hc,hd']

lemma scInclusion_injective (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    Function.Injective (ShortComplex.homologyMap (scInclusion A B n)) := by
  apply ModuleHomology.homologyMap_injective
  intro c hb
  let A' := (SingularSubspace.inclusionMap B) ⁻¹' A
  obtain ⟨z,hz⟩ := projection_surjective A' n c.1
  have hc : (chains B).d n (n-1) z ∈ SingularSubspace.group A' (n-1) := by
    apply (projection_zero_iff A' _ _).mp
    rw [← differential_projection,hz]
    exact c.2
  obtain ⟨v,hv⟩ := hb
  obtain ⟨b,hb⟩ := projection_surjective A (n+1) v
  have hb' : (projection A).f n ((chains X).d (n+1) n b) =
      (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap B)).f n z) := by
    rw [← differential_projection,hb,← inclusion_projection, hz]
    exact hv
  obtain ⟨k,d,hd⟩ := split_chain A B hcover b
  have hd' : (inclusion A B).f (n+1) ((projection A').f (n+1) d) =
      (projection A).f (n+1) (iterate X (n+1) k b) := hd.symm
  have hn := congrArg (fun h : (chains B).X n ⟶ (chains X).X n => h z)
    (iterate_map (SingularSubspace.inclusionMap B) n k)
  change (SingularChains.map (SingularSubspace.inclusionMap B)).f n (iterate B n k z) =
    iterate X n k ((SingularChains.map (SingularSubspace.inclusionMap B)).f n z) at hn
  have hbd : (RelativeChains.complex A').d (n+1) n ((projection A').f (n+1) d) =
      (projection A').f n (iterate B n k z) := by
    apply inclusion_injective A B n
    rw [inclusion_d,hd',differential_projection,iterate_apply_comm,inclusion_projection,hn]
    exact iterate_projection_eq A n k hb'
  refine ⟨(projection A').f (n+1) d + (projection A').f (n+1) (sumPrism B n k z),?_⟩
  change (RelativeChains.complex A').d (n+1) n
    ((projection A').f (n+1) d + (projection A').f (n+1) (sumPrism B n k z)) = c.1
  rw [map_add,hbd,RelativeChains.cycle_difference A' n k z hc]
  refine Eq.trans ?_ hz
  abel

theorem inclusion_quasiIsoAt (A B : Set X) (hcover : interior A ∪ interior B = univ) (n : ℕ) :
    QuasiIsoAt (inclusion A B) n := by
  have hp : (ComplexShape.down ℕ).prev n = n+1 := ComplexShape.prev_eq' _ (by rfl)
  have hn : (ComplexShape.down ℕ).next n = n-1 := by
    cases n with
    | zero => exact ComplexShape.next_eq_self' _ _ (by intro k; change ¬ k+1 = 0; omega)
    | succ n => exact ComplexShape.next_eq' _ (by change n+1 = n+1; rfl)
  rw [quasiIsoAt_iff' (inclusion A B) _ _ _ hp hn,ShortComplex.quasiIso_iff]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ⟨scInclusion_injective A B hcover n,scInclusion_surjective A B hcover n⟩

theorem inclusion_quasiIso (A B : Set X) (hcover : interior A ∪ interior B = univ) :
    QuasiIso (inclusion A B) := by
  constructor
  exact inclusion_quasiIsoAt A B hcover

theorem excise_closed (A Z : Set X) (hZ : IsClosed Z) (hZA : Z ⊆ interior A) :
    QuasiIso (inclusion A Zᶜ) := by
  apply inclusion_quasiIso
  rw [hZ.isOpen_compl.interior_eq]
  apply eq_univ_of_forall
  intro x
  by_cases hx : x ∈ Z
  · exact Or.inl (hZA hx)
  · exact Or.inr hx

end SingularExcision

namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def sequence (A : Set X) : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (SingularChains.map (SingularSubspace.inclusionMap A)) (projection A) (by
    ext n c
    change (projection A).f n ((SingularChains.map (SingularSubspace.inclusionMap A)).f n c) = 0
    exact (projection_zero_iff A n _).mpr (SingularSubspace.inclusion_mem A n c))

theorem shortExact (A : Set X) : (sequence A).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro c hc
    change (projection A).f n c = 0 at hc
    have hmem := (projection_zero_iff A n c).mp hc
    refine ⟨SingularSubspace.lift A n c,?_⟩
    exact SingularSubspace.lift_inclusion_apply A hmem
  · exact (ModuleCat.mono_iff_injective _).mpr (SingularSubspace.inclusion_injective A n)
  · exact (ModuleCat.epi_iff_surjective _).mpr (projection_surjective A n)

def connecting (A : Set X) (n : ℕ) : (complex A).homology (n+1) ⟶ (chains A).homology n :=
  (shortExact A).δ (n+1) n rfl

lemma connecting_isIso (A : Set X) (n : ℕ)
    (hi : Limits.IsZero ((chains X).homology (n+1))) (hj : Limits.IsZero ((chains X).homology n)) :
    IsIso (connecting A n) := (shortExact A).isIso_δ _ _ rfl hi hj

def restrictMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : C(A,B) :=
  ⟨fun a => ⟨f a,hf a.2⟩,(f.continuous.comp continuous_subtype_val).subtype_mk _⟩

def sequenceMap (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B) : sequence A ⟶ sequence B where
  τ₁ := SingularChains.map (restrictMap A B f hf)
  τ₂ := SingularChains.map f
  τ₃ := map A B f hf
  comm₁₂ := by
    change SingularChains.map (restrictMap A B f hf) ≫ SingularChains.map (SingularSubspace.inclusionMap B) =
      SingularChains.map (SingularSubspace.inclusionMap A) ≫ SingularChains.map f
    rw [← SingularChains.map_comp,← SingularChains.map_comp]
    rfl
  comm₂₃ := by
    ext n c
    rfl

lemma map_quasiIso (A : Set X) (B : Set Y) (f : C(X,Y)) (hf : MapsTo f A B)
    (hfa : QuasiIso (SingularChains.map (restrictMap A B f hf)))
    (hfX : QuasiIso (SingularChains.map f)) : QuasiIso (map A B f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (sequenceMap A B f hf)
    (shortExact A) (shortExact B) hfa hfX

end RelativeChains

namespace SingularChains
open CategoryTheory AlgebraicTopology HomologicalComplex
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def homotopyChainEquiv (e : ContinuousMap.HomotopyEquiv X Y) :
    _root_.HomotopyEquiv (chains X) (chains Y) where
  hom := map e.toFun
  inv := map e.invFun
  homotopyHomInvId := by
    rw [← map_comp,← map_id]
    exact (show TopCat.Homotopy (TopCat.ofHom (e.invFun.comp e.toFun))
      (TopCat.ofHom (ContinuousMap.id X)) from e.left_inv.some).singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)
  homotopyInvHomId := by
    rw [← map_comp,← map_id]
    exact (show TopCat.Homotopy (TopCat.ofHom (e.toFun.comp e.invFun))
      (TopCat.ofHom (ContinuousMap.id Y)) from e.right_inv.some).singularChainComplexFunctorObjMap (ModuleCat.of ℤ ℤ)

lemma homotopyEquiv_quasiIso (e : ContinuousMap.HomotopyEquiv X Y) : QuasiIso (map e.toFun) :=
  (homotopyChainEquiv e).quasiIso_hom

lemma contractible_homology_isZero [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    Limits.IsZero ((chains X).homology n) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  let h : QuasiIso (map e.toFun) := homotopyEquiv_quasiIso e
  let hi : IsIso (homologyMap (map e.toFun) n) := (quasiIsoAt_iff_isIso_homologyMap _ _).mp (h.quasiIsoAt n)
  have z : Limits.IsZero ((chains Unit).homology n) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace (ModuleCat ℤ) n
      (ModuleCat.of ℤ ℤ) (TopCat.of Unit) hn
  exact z.of_iso (asIso (homologyMap (map e.toFun) n))

lemma map_iso (e : X ≃ₜ Y) : IsIso (map (e : C(X,Y))) := by
  refine ⟨⟨map (e.symm : C(Y,X)),?_,?_⟩⟩ <;> rw [← map_comp]
  · convert map_id (X := X) using 1
    congr 1
    ext x
    exact e.symm_apply_apply x
  · convert map_id (X := Y) using 1
    congr 1
    ext x
    exact e.apply_symm_apply x

end SingularChains

end

end OAI
