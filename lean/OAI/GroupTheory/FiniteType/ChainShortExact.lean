import Mathlib
import OAI.GroupTheory.FiniteType.DiskSigmaCollar

namespace OAI

noncomputable section
open CategoryTheory AlgebraicTopology Limits
open scoped Simplicial
open Set Topology Metric
namespace ChainShortExact
open CategoryTheory HomologicalComplex Limits
variable {S : ShortComplex (ChainComplex (ModuleCat ℤ) ℕ)}

lemma quasiIso_g (hS : S.ShortExact) (h : ∀ n, IsZero (S.X₁.homology n)) : QuasiIso S.g := by
  refine ⟨fun n => (quasiIsoAt_iff_isIso_homologyMap _ _).mpr ?_⟩
  let : Mono (homologyMap S.g n) := (hS.homology_exact₂ n).mono_g ((h n).eq_of_src _ _)
  let : Epi (homologyMap S.g n) := by
    cases n with
    | zero =>
      let := hS.epi_g
      exact epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
    | succ n => exact (hS.homology_exact₃ (n+1) n rfl).epi_f ((h n).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

lemma zero_homology₃_zero (hS : S.ShortExact) (h : IsZero (S.X₂.homology 0)) :
    IsZero (S.X₃.homology 0) := by
  let := hS.epi_g
  let : Epi (homologyMap S.g 0) := epi_homologyMap_of_epi_of_not_rel S.g 0 (by intro j; simp)
  exact h.of_epi (homologyMap S.g 0)

end ChainShortExact

namespace RelativeChains
section
open Set CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma univ_homology_isZero (n : ℕ) : Limits.IsZero ((complex (univ : Set X)).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (univ_isZero n)).isZero_homology

lemma contractible_singleton_homology_isZero [ContractibleSpace X] (x : X) (n : ℕ) :
    Limits.IsZero ((complex ({x} : Set X)).homology n) := by
  let f : C(X,Unit) := ContinuousMap.const X ()
  let hf : MapsTo f ({x} : Set X) (univ : Set Unit) := fun _ _ => mem_univ _
  let : Unique (univ : Set Unit) :=
    { default := ⟨(),mem_univ _⟩, uniq := fun _ => Subsingleton.elim _ _ }
  have hfa : QuasiIso (SingularChains.map (restrictMap {x} univ f hf)) := by
    have he : restrictMap {x} univ f hf =
        ((Homeomorph.homeomorphOfUnique _ _ : ({x} : Set X) ≃ₜ (univ : Set Unit)) : C(_, _)) := by
      ext z
    rw [he]
    let := SingularChains.map_iso (Homeomorph.homeomorphOfUnique _ _ : ({x} : Set X) ≃ₜ (univ : Set Unit))
    infer_instance
  let hq : QuasiIso (map {x} univ f hf) := map_quasiIso _ _ _ _ hfa SingularChains.constant_quasiIso
  exact (univ_homology_isZero (X := Unit) n).of_iso (asIso (homologyMap (map {x} univ f hf) n))

lemma singleton_quotient_quasiIso (A : Set X) (x : A) [ContractibleSpace A] :
    QuasiIso (quotientMap (singleton_subset_iff.mpr x.2 : ({x.1} : Set X) ⊆ A)) := by
  apply ChainShortExact.quasiIso_g (triple_shortExact (singleton_subset_iff.mpr x.2))
  intro n
  have he : (SingularSubspace.inclusionMap A) ⁻¹' ({x.1} : Set X) = {x} := by
    ext z
    simp only [mem_preimage,mem_singleton_iff]
    exact Subtype.ext_iff.symm
  change Limits.IsZero ((complex ((SingularSubspace.inclusionMap A) ⁻¹' ({x.1} : Set X))).homology n)
  rw [he]
  exact contractible_singleton_homology_isZero x n

end

open Set CategoryTheory HomologicalComplex SingularChains
variable {X : Type} [TopologicalSpace X]

lemma preimage_singleton_inclusion {D : Set X} (x : D) :
    (SingularSubspace.inclusionMap D) ⁻¹' ({x.1} : Set X) = {x} := by
  ext z
  simp only [mem_preimage,mem_singleton_iff]
  exact Subtype.ext_iff.symm

def suspensionIso (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hcover : interior A ∪ interior B = univ)
    (x : (SingularSubspace.inclusionMap B) ⁻¹' A) (n : ℕ) :
    (complex ({x.1.1} : Set X)).homology (n+1) ≅
      (complex ({x} : Set ((SingularSubspace.inclusionMap B) ⁻¹' A))).homology n := by
  let xa : A := ⟨x.1.1,x.2⟩
  let h : ({x.1.1} : Set X) ⊆ A := singleton_subset_iff.mpr xa.2
  letI := singleton_quotient_quasiIso A xa
  letI := SingularExcision.inclusion_quasiIso A B hcover
  refine (asIso (homologyMap (quotientMap h) (n+1))) ≪≫
    (asIso (homologyMap (inclusion A B) (n+1))).symm ≪≫ ?_
  let h' : ({x.1} : Set B) ⊆ (SingularSubspace.inclusionMap B) ⁻¹' A :=
    singleton_subset_iff.mpr x.2
  have e := (triple_shortExact h').δIso (n+1) n rfl
    (contractible_singleton_homology_isZero x.1 (n+1)) (contractible_singleton_homology_isZero x.1 n)
  change (complex ((SingularSubspace.inclusionMap B) ⁻¹' A)).homology (n+1) ≅ _
  simpa only [triple,preimage_singleton_inclusion x] using e

lemma suspension_zero (A B : Set X) [ContractibleSpace A] [ContractibleSpace B]
    (hcover : interior A ∪ interior B = univ)
    (x : (SingularSubspace.inclusionMap B) ⁻¹' A) :
    Limits.IsZero ((complex ({x.1.1} : Set X)).homology 0) := by
  let xa : A := ⟨x.1.1,x.2⟩
  let h : ({x.1.1} : Set X) ⊆ A := singleton_subset_iff.mpr xa.2
  let := singleton_quotient_quasiIso A xa
  let := SingularExcision.inclusion_quasiIso A B hcover
  let h' : ({x.1} : Set B) ⊆ (SingularSubspace.inclusionMap B) ⁻¹' A :=
    singleton_subset_iff.mpr x.2
  have hz := ChainShortExact.zero_homology₃_zero (triple_shortExact h')
    (contractible_singleton_homology_isZero x.1 0)
  exact hz.of_iso ((asIso (homologyMap (quotientMap h) 0)) ≪≫
    (asIso (homologyMap (inclusion A B) 0)).symm)

end RelativeChains

namespace SingularSubspace
open Set CategoryTheory SingularChains
variable {X : Type} [TopologicalSpace X]

lemma constant_mem (x : X) (n : ℕ) (c : (chains X).X n) :
    (map (ContinuousMap.const X x)).f n c ∈ group ({x} : Set X) n := by
  let f := (map (ContinuousMap.const X x)).f n
  apply SingularSupport.induction_on ((group ({x} : Set X) n).comap f.hom) _ c
  intro g
  change (map (ContinuousMap.const X x)).f n (SingularSupport.gen g) ∈ group ({x} : Set X) n
  rw [SingularSupport.map_gen]
  exact SingularSupport.gen_mem _ (by rintro _ ⟨z,rfl⟩; rfl)

lemma constant_fixed (x : X) {n : ℕ} {c : (chains X).X n}
    (hc : c ∈ group ({x} : Set X) n) : (map (ContinuousMap.const X x)).f n c = c := by
  apply sub_eq_zero.mp
  change c ∈ LinearMap.ker (((map (ContinuousMap.const X x)).f n).hom - LinearMap.id)
  apply SingularSupport.map_mem (𝟙 _) _ hc
  intro f hf
  change (map (ContinuousMap.const X x)).f n (SingularSupport.gen f) - SingularSupport.gen f = 0
  rw [SingularSupport.map_gen]
  apply sub_eq_zero.mpr
  congr 1
  ext z
  exact (hf (mem_range_self z)).symm

end SingularSubspace

namespace RelativeChains
open Set CategoryTheory HomologicalComplex SingularChains
variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

def pointChange (x y : X) : complex ({x} : Set X) ⟶ complex ({y} : Set X) :=
  QuotientComplex.map _ _ (𝟙 _ - SingularChains.map (ContinuousMap.const X x)) (by
    intro n c hc
    change c - (SingularChains.map (ContinuousMap.const X x)).f n c ∈ SingularSubspace.group {y} n
    rw [SingularSubspace.constant_fixed x hc,sub_self]
    exact Submodule.zero_mem _)

@[simp] lemma pointChange_projection (x y : X) (n : ℕ) (c : (chains X).X n) :
    (pointChange x y).f n ((projection ({x} : Set X)).f n c) =
      (projection ({y} : Set X)).f n (c - (SingularChains.map (ContinuousMap.const X x)).f n c) := rfl

lemma pointChange_comp (x y z : X) : pointChange x y ≫ pointChange y z = pointChange x z := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective ({x} : Set X) n c
  change (pointChange y z).f n ((pointChange x y).f n ((projection {x}).f n c)) = _
  simp only [pointChange_projection,map_sub]
  have hconst : (SingularChains.map (ContinuousMap.const X y)).f n
      ((SingularChains.map (ContinuousMap.const X x)).f n c) =
      (SingularChains.map (ContinuousMap.const X y)).f n c := by
    have he : (ContinuousMap.const X y).comp (ContinuousMap.const X x) = ContinuousMap.const X y := rfl
    have h := congrArg (fun f : chains X ⟶ chains X => f.f n c) (SingularChains.map_comp (ContinuousMap.const X x) (ContinuousMap.const X y))
    rw [he] at h
    exact h.symm
  rw [hconst]
  abel

lemma pointChange_self (x : X) : pointChange x x = 𝟙 _ := by
  ext n c
  obtain ⟨c,rfl⟩ := projection_surjective ({x} : Set X) n c
  change (pointChange x x).f n ((projection {x}).f n c) = _
  rw [pointChange_projection,map_sub]
  rw [(projection_zero_iff _ _ _).mpr (SingularSubspace.constant_mem x n c),sub_zero]
  rfl

def pointChangeIso (x y : X) : complex ({x} : Set X) ≅ complex ({y} : Set X) where
  hom := pointChange x y
  inv := pointChange y x
  hom_inv_id := by rw [pointChange_comp,pointChange_self]
  inv_hom_id := by rw [pointChange_comp,pointChange_self]

def pointHomologyIso (x y : X) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (complex ({y} : Set X)).homology n :=
  (homologyFunctor _ _ n).mapIso (pointChangeIso x y)

lemma pointMap_quasiIso (f : C(X,Y)) (x : X) (hf : QuasiIso (SingularChains.map f)) :
    QuasiIso (map {x} {f x} f (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (f x))) := by
  apply map_quasiIso _ _ _ _ _ hf
  have he : restrictMap {x} {f x} f (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (f x)) =
      ((Homeomorph.homeomorphOfUnique ({x} : Set X) ({f x} : Set Y)) : C(_, _)) := by
    apply ContinuousMap.ext
    intro z
    exact Subsingleton.elim _ _
  rw [he]
  let := SingularChains.map_iso (Homeomorph.homeomorphOfUnique ({x} : Set X) ({f x} : Set Y))
  infer_instance

def pointHomotopyEquivIso (e : ContinuousMap.HomotopyEquiv X Y) (x : X) (n : ℕ) :
    (complex ({x} : Set X)).homology n ≅ (complex ({e x} : Set Y)).homology n := by
  letI := pointMap_quasiIso e.toFun x (SingularChains.homotopyEquiv_quasiIso e)
  exact asIso (homologyMap (map {x} {e x} e.toFun (by intro z hz; simpa only [mem_singleton_iff.mp hz] using mem_singleton (e x))) n)

end RelativeChains

namespace SingularChains
open CategoryTheory HomologicalComplex Limits AlgebraicTopology
variable {X : Type} [TopologicalSpace X]

lemma isEmpty_homology_isZero [IsEmpty X] (n : ℕ) : IsZero ((chains X).homology n) := by
  apply (HomologicalComplex.ExactAt.of_isZero (i := n) _).isZero_homology
  apply (IsZero.iff_id_eq_zero _).mpr
  apply hom_ext
  intro f
  exact isEmptyElim (f (Convexity.StdSimplex.single 0))

def unique_homologyZeroIso [Unique X] : (chains X).homology 0 ≅ ModuleCat.of ℤ ℤ :=
  (singularHomologyFunctorZeroOfTotallyDisconnectedSpace (ModuleCat ℤ) (ModuleCat.of ℤ ℤ) (TopCat.of X)) ≪≫
    coproductUniqueIso (fun _ : X => ModuleCat.of ℤ ℤ)

end SingularChains

end

end OAI
