import Mathlib
import OAI.GroupTheory.SimpleAmenable.Homology.FinitePrimitiveResolution
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.FinePatchAtlas
import OAI.GroupTheory.SimpleAmenable.CentralCovers.PrimitiveGlobalTemplates

namespace OAI

open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
section PrimitiveCentralLaws
namespace InitialCoverSystem.PatchAtlas
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m} {B : InitialCoverSystem a r m hm M}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))] (A : B.PatchAtlas)

theorem primitive_full_central {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (smallFamilyEval (B.smallPrimitiveInputs (by omega) P)).range := by
  apply (centralOn_range_iff_hasCentralLaw _ _ _ _ (actualPolygonTableHom_injective _)
    (B.fullPrimitiveProjection (by omega) P)).mpr
  exact A.primitive_family_actual_global_law ha hlarge hr P hmesh

theorem primitive_family_law_all {ι : Type} [Finite ι]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (P : ι → Fin 5 × (CutRing × CutRing))
    (hmesh : (1+|ordinary (cutTau^a)|)*(200/(A.geometry.mesh:ℝ))<ordinary A.rectangles.radius/4)
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I) :
    B.PrimitiveFamilyLaw I b hb P := by
  classical
  have hc := A.primitive_full_central ha hlarge hr P hmesh
  apply hc.mono
  by_cases hI : 5 ≤ I.card
  · exact B.primitiveFamily_range_full (by omega) P I hI b hb
  · have hsub : I ⊆ Finset.univ.erase b := by
      intro i hi
      exact Finset.mem_erase.mpr ⟨by intro he; subst i; exact hb hi,Finset.mem_univ i⟩
    obtain ⟨J,hIJ,hJ,hcard⟩ := Finset.exists_subsuperset_card_eq hsub (by omega : I.card≤5)
      (by simp only [Finset.card_erase_of_mem (Finset.mem_univ b),Finset.card_univ,Fintype.card_fin]; omega :
        5≤(Finset.univ.erase b : Finset (Fin (m+1))).card)
    have hbJ : b ∉ J := by intro h; exact (Finset.mem_erase.mp (hJ h)).1 rfl
    exact (B.primitiveFamily_range_inclusion hIJ b b hb hbJ P).trans
      (B.primitiveFamily_range_full (by omega) P J (by omega) b hbJ)

end InitialCoverSystem.PatchAtlas

theorem primitive_laws_eventually {a m : ℕ} {r : CutRing} {hm : 2 ≤ m}
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]
    (ha : 0<a) (hlarge : 25 ≤ m+1) (hr : 0<ordinary r ∧ ordinary r<1/2)
    (hSlope : 8000<ordinary (cutTau^a)) (hconj : |conjugate (cutTau^a)|<1/1000) :
    ∃ L : ℕ, ∀ M : ℕ, L≤M → ∀ B : InitialCoverSystem a r m hm M,
      ∀ (ι : Type) [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing))
      (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I),
      B.PrimitiveFamilyLaw I b hb P := by
  obtain ⟨L,hL⟩ := finePatchAtlas_eventually (hm := hm) (by omega) hr hSlope hconj
  refine ⟨L,fun M hM B => ?_⟩
  obtain ⟨A⟩ := hL M hM B
  intro ι hι P I b hb
  exact A.toPatchAtlas.primitive_family_law_all ha hlarge hr P A.far_mesh I b hb

end PrimitiveCentralLaws

theorem polygon_family_primitive_resolution {a : ℕ} {ι : Type} [Finite ι]
    (r : CutRing) (hr : 0<ordinary r ∧ ordinary r<1/2) (V : ι → polygonAlgebra a) :
    ∃ S : Finset (Fin 5 × (CutRing × CutRing)), ∀ i,
      ResolvedBy (fun p : S => (spatialTranslate p.val.2 (initialTest a r p.val.1)).val) (V i).val := by
  classical
  let _ := Fintype.ofFinite ι
  choose S hS using fun i => polygon_finite_primitive_resolution r hr (V i)
  refine ⟨Finset.univ.biUnion S,fun i x y he => hS i x y ?_⟩
  intro p
  exact he ⟨p.val,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,p.property⟩⟩

namespace InitialCoverSystem
variable {a m M : ℕ} {r : CutRing} {hm : 2 ≤ m}
    (B : InitialCoverSystem a r m hm M)
    [Group.IsPerfect (alternatingGroup (Fin (m+1)))]

def AllPrimitiveLaws : Prop :=
  ∀ (ι : Type) [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing))
    (I : Finset (Fin (m+1))) (b : Fin (m+1)) (hb : b ∉ I), B.PrimitiveFamilyLaw I b hb P

variable (hlarge : 15 < m+1) (h : B.AllPrimitiveLaws)

theorem fullGeometricSector_independent {ι κ : Type} [Finite ι] [Finite κ]
    (P : ι → Fin 5 × (CutRing × CutRing)) (Q : κ → Fin 5 × (CutRing × CutRing))
    (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val)
    (hV' : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) Q i).val) V.val) :
    B.fullGeometricSector hlarge P (fun I _ b hb => h ι P I b hb) V =
      B.fullGeometricSector hlarge Q (fun I _ b hb => h κ Q I b hb) V := by
  let R : ι ⊕ κ → Fin 5 × (CutRing × CutRing) := Sum.elim P Q
  rw [B.fullGeometricSector_subfamily hlarge R P Sum.inl rfl
      (fun I _ b hb => h _ R I b hb) _ V hV,
    B.fullGeometricSector_subfamily hlarge R Q Sum.inr rfl
      (fun I _ b hb => h _ R I b hb) _ V hV']

noncomputable def polygonStar (hr : 0<ordinary r ∧ ordinary r<1/2)
    (V : polygonAlgebra a) : TrackStar (Fin (m+1)) →*
      BoundedRelationCover M (alternatingGenerator a r m hm) :=
  let S := (polygon_finite_primitive_resolution r hr V).choose
  B.fullGeometricSector hlarge (fun p : S => p.val) (fun I _ b hb => h S (fun p => p.val) I b hb) V

theorem polygonStar_eq (hr : 0<ordinary r ∧ ordinary r<1/2)
    {ι : Type} [Finite ι] (P : ι → Fin 5 × (CutRing × CutRing)) (V : polygonAlgebra a)
    (hV : ResolvedBy (fun i => (primitiveTests (a := a) (r := r) P i).val) V.val) :
    B.polygonStar hlarge h hr V = B.fullGeometricSector hlarge P (fun I _ b hb => h ι P I b hb) V := by
  apply B.fullGeometricSector_independent hlarge h _ P V _ hV
  exact (polygon_finite_primitive_resolution r hr V).choose_spec

theorem polygonStar_projection (hr : 0<ordinary r ∧ ordinary r<1/2) (V : polygonAlgebra a) :
    (coverMap M (alternatingGenerator a r m hm)).comp (B.polygonStar hlarge h hr V) =
      (conditionalAlternatingHom V).comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  unfold polygonStar
  exact B.fullGeometricSector_projection hlarge _ _ V
    (polygon_finite_primitive_resolution r hr V).choose_spec

theorem polygonStar_supported (hr : 0<ordinary r ∧ ordinary r<1/2) (V : polygonAlgebra a) :
    SmallSupported (sourceAlignedGroup a r m hm M B.t) (B.polygonStar hlarge h hr V) := by
  unfold polygonStar
  exact B.fullGeometricSector_supported hlarge _ _ V
    (polygon_finite_primitive_resolution r hr V).choose_spec

theorem polygonStar_whole (hr : 0<ordinary r ∧ ordinary r<1/2) :
    B.polygonStar hlarge h hr (wholePolygon a) =
      B.c.comp (universalProjection (alternatingGroup (Fin (m+1)))) := by
  unfold polygonStar
  exact B.fullGeometricSector_whole hlarge _ _

theorem polygonStar_commute (hr : 0<ordinary r ∧ ordinary r<1/2)
    (V W : polygonAlgebra a) (hd : Disjoint V.val W.val) (s t : TrackStar (Fin (m+1))) :
    Commute (B.polygonStar hlarge h hr V s) (B.polygonStar hlarge h hr W t) := by
  let R : Bool → polygonAlgebra a := fun b => if b then W else V
  obtain ⟨S,hS⟩ := polygon_family_primitive_resolution r hr R
  have hV := hS false
  have hW := hS true
  change ResolvedBy _ V.val at hV
  change ResolvedBy _ W.val at hW
  rw [B.polygonStar_eq hlarge h hr (fun p : S => p.val) V hV,
    B.polygonStar_eq hlarge h hr (fun p : S => p.val) W hW]
  exact B.fullGeometricSector_commute hlarge _ _ V W hV hd s t

theorem polygonStar_union (hr : 0<ordinary r ∧ ordinary r<1/2)
    (V W : polygonAlgebra a) (hd : Disjoint V.val W.val) (s : TrackStar (Fin (m+1))) :
    B.polygonStar hlarge h hr (V ⊔ W) s =
      B.polygonStar hlarge h hr V s * B.polygonStar hlarge h hr W s := by
  let R : Bool → polygonAlgebra a := fun b => if b then W else V
  obtain ⟨S,hS⟩ := polygon_family_primitive_resolution r hr R
  have hV := hS false
  have hW := hS true
  change ResolvedBy _ V.val at hV
  change ResolvedBy _ W.val at hW
  have hU : ResolvedBy (fun p : S => (spatialTranslate p.val.2 (initialTest a r p.val.1)).val)
      (V ⊔ W).val := fun x y he => or_congr (hV x y he) (hW x y he)
  rw [B.polygonStar_eq hlarge h hr (fun p : S => p.val) (V ⊔ W) hU,
    B.polygonStar_eq hlarge h hr (fun p : S => p.val) V hV,
    B.polygonStar_eq hlarge h hr (fun p : S => p.val) W hW]
  exact B.fullGeometricSector_union hlarge _ _ V W hV hd s

theorem polygonStars_finite_central (hr : 0<ordinary r ∧ ordinary r<1/2)
    {ι : Type} [Finite ι] (V : ι → polygonAlgebra a) :
    CentralOn (coverMap M (alternatingGenerator a r m hm))
      (⨆ i, (B.polygonStar hlarge h hr (V i)).range) := by
  obtain ⟨S,hS⟩ := polygon_family_primitive_resolution r hr V
  apply (B.fullPrimitiveFamily_central hlarge (fun p : S => p.val)
    (fun I _ b hb => h S (fun p => p.val) I b hb)).mono
  apply iSup_le
  intro i
  rw [B.polygonStar_eq hlarge h hr (fun p : S => p.val) (V i) (hS i)]
  rintro x ⟨s,rfl⟩
  exact B.fullGeometricSector_mem hlarge _ _ (V i) s

end InitialCoverSystem

end SimpleAmenable

end OAI
