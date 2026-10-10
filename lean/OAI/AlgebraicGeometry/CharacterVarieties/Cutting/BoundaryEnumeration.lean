import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.RefinedDiagram

namespace OAI

/-!
# Based boundary enumeration and fresh-facet labels of the refined diagram.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.BasedCycleEnumeration
open scoped Classical
variable {α C : Type} (N : Equiv.Perm α) (s : C → Finset α) (a : C → α)
    (ha : ∀ c,a c∈s c) (hcycle : ∀ c,N.IsCycleOn (s c : Set α))
include ha hcycle in
lemma pow_mem (c : C) (k : ℕ) : (N^k) (a c)∈s c := by
  induction k with
  | zero => exact ha c
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact (hcycle c).1.mapsTo ih
noncomputable def entry (c : C) (i : Fin (s c).card) : α := (N^i.val) (a c)
include ha hcycle in
lemma entry_mem (c : C) (i : Fin (s c).card) : entry N s a c i∈s c :=
  pow_mem N s a ha hcycle c i.val
include ha hcycle in
lemma entry_injective (c : C) : Function.Injective (entry N s a c) := by
  intro i j he
  apply Fin.ext
  have h := ((hcycle c).pow_apply_eq_pow_apply (ha c)).mp he
  simpa only [Nat.ModEq,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using h
include ha hcycle in
lemma entry_surjective (c : C) (b : α) (hb : b∈s c) : ∃ i,entry N s a c i=b := by
  obtain ⟨k,hk,h⟩ := (hcycle c).exists_pow_eq (ha c) hb
  exact ⟨⟨k,hk⟩,h⟩
include ha hcycle in
lemma entry_next (c : C) (i : Fin (s c).card) : N (entry N s a c i)=
    entry N s a c ⟨(i.val+1) % (s c).card,Nat.mod_lt _ (Finset.card_pos.mpr ⟨a c,ha c⟩)⟩ := by
  change N ((N^i.val) (a c))=(N^((i.val+1) % (s c).card)) (a c)
  rw [←Equiv.Perm.mul_apply,←pow_succ']
  apply ((hcycle c).pow_apply_eq_pow_apply (ha c)).mpr
  exact Nat.mod_modEq _ _ |>.symm
variable (hdisj : ∀ c d,c≠d → Disjoint (s c) (s d))
    (hcover : ∀ b : α,∃ c,b∈s c)
include ha hcycle hdisj hcover in
lemma enumeration_bijective : Function.Bijective
    (fun z : (c : C) × Fin (s c).card => entry N s a z.1 z.2) := by
  constructor
  · rintro ⟨c,i⟩ ⟨d,j⟩ he
    change entry N s a c i=entry N s a d j at he
    have hcd : c=d := by
      by_contra hn
      exact Finset.disjoint_left.mp (hdisj c d hn)
        (entry_mem N s a ha hcycle c i) (he.symm ▸ entry_mem N s a ha hcycle d j)
    subst d
    exact congrArg (Sigma.mk c) (entry_injective N s a ha hcycle c he)
  · intro b
    obtain ⟨c,hc⟩ := hcover b
    obtain ⟨i,hi⟩ := entry_surjective N s a ha hcycle c b hc
    exact ⟨⟨c,i⟩,hi⟩
noncomputable def enumeration : ((c : C) × Fin (s c).card) ≃ α :=
  Equiv.ofBijective (fun z => entry N s a z.1 z.2)
    (enumeration_bijective N s a ha hcycle hdisj hcover)
lemma enumeration_apply (c : C) (i : Fin (s c).card) :
    enumeration N s a ha hcycle hdisj hcover ⟨c,i⟩=(N^i.val) (a c) := rfl
end IntegralCharacterVarieties.BasedCycleEnumeration

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    (B : RealizedBand (D.ports.facet ⟨q,none⟩) (D.ports.seamChildren q) (D.ports.seamChildren q))
noncomputable def graftCircleBase : D.GraftCircleLabel q B →
    Side (base D.ports q B).Seam (base D.ports q B).seamArity
  | .inl ⟨f,b⟩ => oldEmbedding D.ports q B (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩)
  | .inr (.inl _) => mirrorEntry D.ports q B ⟨0,Nat.zero_lt_succ _⟩
  | .inr (.inr r) => bandEmbedding D.ports q B (B.origStripSide r.val.val)
lemma graftCircleBase_mem (c : D.GraftCircleLabel q B) :
    D.graftCircleBase q B c∈D.graftCircle q B c := by
  rcases c with ⟨f,b⟩|(_|r)
  · exact D.old_mem_graftCircle q B f b _ (Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩)
  · exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  · refine Finset.mem_map.mpr ⟨_,?_,rfl⟩
    apply (B.mem_stripFinset _ _).mpr
    have h := B.stripCycle_mem_orig r.val.val
    rwa [B.stripForest.root_of_source r.val.val r.val.property] at h
noncomputable def graftCircleEntry (c : D.GraftCircleLabel q B) (i : Fin (D.graftCircle q B c).card) :=
  ((next D.ports q B)^i.val) (D.graftCircleBase q B c)
variable (hinj : Function.Injective B.shortRoot)
    (hno : ∀ z i,D.ports.facet ⟨z,some i⟩≠D.ports.facet ⟨q,none⟩)
/-- The entire actual graft boundary, based at the original old occurrence on
EVERY old circle, and at literal mirror/strip occurrences on new circles.
Unlike fromPorts, this equivalence retains the old marking and circle labels. -/
noncomputable def graftBoundaryEnumeration :
    ((c : D.GraftCircleLabel q B) × Fin (D.graftCircle q B c).card) ≃
      Side (base D.ports q B).Seam (base D.ports q B).seamArity :=
  BasedCycleEnumeration.enumeration (next D.ports q B) (D.graftCircle q B) (D.graftCircleBase q B)
    (D.graftCircleBase_mem q B) (D.graftCircle_isCycle q B hinj hno)
    (fun _ _ h => D.graftCircle_disjoint q B hinj hno h) (D.graftCircle_cover q B hno)
lemma graftBoundaryEnumeration_apply (c : D.GraftCircleLabel q B)
    (i : Fin (D.graftCircle q B c).card) :
    D.graftBoundaryEnumeration q B hinj hno ⟨c,i⟩=D.graftCircleEntry q B c i := rfl
lemma graftBoundaryEnumeration_next (c : D.GraftCircleLabel q B)
    (i : Fin (D.graftCircle q B c).card) :
    next D.ports q B (D.graftBoundaryEnumeration q B hinj hno ⟨c,i⟩)=
    D.graftBoundaryEnumeration q B hinj hno ⟨c,⟨(i.val+1)%(D.graftCircle q B c).card,
      Nat.mod_lt _ (Finset.card_pos.mpr (D.graftCircle_nonempty q B c))⟩⟩ :=
  BasedCycleEnumeration.entry_next (next D.ports q B) (D.graftCircle q B) (D.graftCircleBase q B)
    (D.graftCircleBase_mem q B) (D.graftCircle_isCycle q B hinj hno) c i
lemma graftBoundaryEnumeration_zero (c : D.GraftCircleLabel q B) :
    D.graftBoundaryEnumeration q B hinj hno ⟨c,⟨0,
      Finset.card_pos.mpr (D.graftCircle_nonempty q B c)⟩⟩=D.graftCircleBase q B c := rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence
variable {F S V G : Type} {arity : S → ℕ} (D : Diagram F S V arity)

def extendedBoundaryCount : F ⊕ G → ℕ := Sum.elim D.boundaryCount (fun _ => 0)
def extendedBoundaryLength : (f : F ⊕ G) → Fin (D.extendedBoundaryCount f) → ℕ
  | .inl f,b => D.boundaryLength f b
  | .inr _,b => Fin.elim0 b

def extendedBoundarySide : ((f : F ⊕ G) × (b : Fin (D.extendedBoundaryCount f)) ×
    Fin (D.extendedBoundaryLength f b)) ≃ Side S arity where
  toFun a := match a with
    | ⟨.inl f,b,i⟩ => D.boundarySide ⟨f,b,i⟩
    | ⟨.inr _,b,_⟩ => Fin.elim0 b
  invFun a := let z := D.boundarySide.symm a; ⟨.inl z.1,z.2.1,z.2.2⟩
  left_inv := by
    rintro ⟨f,b,i⟩
    cases f with
    | inl f =>
      exact congrArg (fun z : (f : F) × (b : Fin (D.boundaryCount f)) × Fin (D.boundaryLength f b) =>
        (⟨Sum.inl z.1,z.2.1,z.2.2⟩ : (f : F ⊕ G) × (b : Fin (D.extendedBoundaryCount f)) ×
          Fin (D.extendedBoundaryLength f b))) (D.boundarySide.symm_apply_apply ⟨f,b,i⟩)
    | inr g => exact Fin.elim0 b
  right_inv a := D.boundarySide.apply_symm_apply a

/-- Add the named fresh facet fibres before their boundary grafting. No old
surface, orientation, side, rank or boundary ordering is modified. -/
def extendFacets (newRank : G → ℕ) : Diagram (F ⊕ G) S V arity where
  ports := D.ports.mapFacet Sum.inl
  rank := Sum.elim D.rank newRank
  seamRank := D.seamRank
  genus := Sum.elim D.genus (fun _ => 0)
  boundaryCount := D.extendedBoundaryCount
  boundaryLength := D.extendedBoundaryLength
  boundaryPositive f b := by
    cases f with
    | inl f => exact D.boundaryPositive f b
    | inr g => exact Fin.elim0 b
  boundarySide := D.extendedBoundarySide
  boundaryFacet f b i := by
    cases f with
    | inl f => exact congrArg Sum.inl (D.boundaryFacet f b i)
    | inr g => exact Fin.elim0 b
  boundaryNext f b i := by
    cases f with
    | inl f => exact D.boundaryNext f b i
    | inr g => exact Fin.elim0 b

lemma extendFacets_boundarySet (newRank : G → ℕ) (f : F) (b : Fin (D.boundaryCount f)) :
    (D.extendFacets newRank).boundarySet (.inl f) b=D.boundarySet f b := rfl

lemma extendFacets_maximal_no_child_parent (newRank : G → ℕ) (q : S) (hp : D.Proper)
    (hn : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩)) :
    ∀ s i,(D.extendFacets newRank).ports.facet ⟨s,some i⟩≠
      (D.extendFacets newRank).ports.facet ⟨q,none⟩ := by
  intro s i he
  exact D.maximal_no_child_parent q hp hn s i (Sum.inl.inj he)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
noncomputable def refinedPreDiagram : Diagram (D.ports.RefinedBandFacet q d) S V arity :=
  D.extendFacets (fun x => D.ports.refinedRank q d D.rank (.inr x))
lemma refinedPreDiagram_rank (f : D.ports.RefinedBandFacet q d) :
    (D.refinedPreDiagram q d).rank f=D.ports.refinedRank q d D.rank f := by
  cases f <;> rfl
abbrev RefinedCircleLabel := (D.refinedPreDiagram q d).GraftCircleLabel q (D.ports.refinedBandForSeam q d)
noncomputable def refinedCircle (c : D.RefinedCircleLabel q d) :=
  (D.refinedPreDiagram q d).graftCircle q (D.ports.refinedBandForSeam q d) c
lemma refinedPreDiagram_no_child (hproper : D.Proper)
    (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩)) :
    ∀ s i,(D.refinedPreDiagram q d).ports.facet ⟨s,some i⟩≠
      (D.refinedPreDiagram q d).ports.facet ⟨q,none⟩ :=
  D.extendFacets_maximal_no_child_parent _ q hproper hmax
/-- Actual marked inverse-band boundary enumeration. Short-root injection is
proved from the atomic row/column topology; exclusion of principal children is
derived from the author's proper-seam and maximal-rank hypotheses. No cyclic
coverage, unique-strip, or fresh-parent-germ hypothesis is imposed. -/
noncomputable def refinedBoundaryEnumeration (hproper : D.Proper)
    (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩)) :
    ((c : D.RefinedCircleLabel q d) × Fin (D.refinedCircle q d c).card) ≃
      Side (base (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)).Seam
        (base (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)).seamArity := by
  exact (D.refinedPreDiagram q d).graftBoundaryEnumeration q (D.ports.refinedBandForSeam q d)
    (D.ports.refinedBandForSeam_shortRoot_injective q d) (D.refinedPreDiagram_no_child q d hproper hmax)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma bandEmbedding_color (a : Side B.doubleWiring.Seam B.doubleWiring.seamArity) :
    (A.graftBand q B).facet (bandEmbedding A q B a)=B.doubleAssembly.facet a := by
  rcases a with ⟨⟨⟨v,p⟩,hv⟩,c⟩
  rfl
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
namespace IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly
open scoped Classical
open VertexTable TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
noncomputable def refinedFreshEquiv : (A.refinedBandForSeam q d).FreshStrip ≃ d.atomicBand.FreshStrip where
  toFun x := ⟨x.val,by
    rcases x with ⟨z,hz⟩
    erw [A.refinedBandForSeam_shortRoot_eq q d] at hz
    convert! hz using 1⟩
  invFun x := ⟨x.val,by
    erw [A.refinedBandForSeam_shortRoot_eq q d]
    convert! x.property using 1⟩
  left_inv _ := rfl
  right_inv _ := rfl
lemma refinedFresh_original_color (x : (A.refinedBandForSeam q d).FreshStrip) :
    (A.refinedBandForSeam q d).doubleAssembly.facet
      ((A.refinedBandForSeam q d).origStripSide x.val.val)=.inr (A.refinedFreshEquiv q d x) := by
  rw [RealizedBand.doubleAssembly_origStrip]
  let h := RankShape.atomic_short_disjoint (n:=arity q) (m:=arity q)
  let c := d.stripContact (fun i => A.facet ⟨q,some i⟩) (fun i => A.facet ⟨q,some i⟩)
  let p := A.facet ⟨q,none⟩
  change (d.atomicBand.refinedDecoration h p c x.val.val.1).color x.val.val.2.val=_
  rw [←(d.atomicBand.refinedDecoration h p c x.val.val.1).corner x.val.val.2.val]
  change d.atomicBand.doubleFacet h p c (d.atomicBand.origStripSide x.val.val)=_
  unfold RealizedBand.doubleFacet
  erw [RealizedBand.sideStripRoot_of_orig]
  have hr : (⟨d.atomicBand.stripForest.root x.val.val,d.atomicBand.stripForest.root_external _⟩ : d.atomicBand.StripRoot)=
      (A.refinedFreshEquiv q d x).val := by
    apply Subtype.ext
    exact d.atomicBand.stripForest.root_of_source x.val.val x.val.property
  rw [hr]
  exact d.atomicBand.rootFacet_fresh h c (A.refinedFreshEquiv q d x)
end IntegralCharacterVarieties.OccurrenceIncidence.PortAssembly

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand
variable {F S V G : Type} {arity : S → ℕ} (D : Diagram F S V arity)
def extendedBoundaryIndex : ((f : F ⊕ G) × Fin (D.extendedBoundaryCount f)) ≃
    ((f : F) × Fin (D.boundaryCount f)) where
  toFun z := match z with
    | ⟨.inl f,b⟩ => ⟨f,b⟩
    | ⟨.inr _,b⟩ => Fin.elim0 b
  invFun z := ⟨.inl z.1,z.2⟩
  left_inv := by
    rintro ⟨f,b⟩
    cases f with
    | inl f => rfl
    | inr g => exact Fin.elim0 b
  right_inv _ := rfl
variable (q : S) {r : ℕ} (d : RankShape (arity q) (arity q) r)
noncomputable def refinedCircleLabelEquiv :
    CutCircleIndex.Label (G:=d.atomicBand.FreshStrip) D.boundaryCount ≃ D.RefinedCircleLabel q d :=
  Equiv.sumCongr (D.extendedBoundaryIndex.symm)
    (Equiv.sumCongr (Equiv.refl Unit) (D.ports.refinedFreshEquiv q d).symm)
noncomputable def refinedMarkedCount : D.ports.RefinedBandFacet q d → ℕ :=
  CutCircleIndex.count D.boundaryCount (D.ports.facet ⟨q,none⟩)
noncomputable def refinedMarkedLabel :
    ((f : D.ports.RefinedBandFacet q d) × Fin (D.refinedMarkedCount q d f)) ≃
      D.RefinedCircleLabel q d :=
  (CutCircleIndex.enumeration D.boundaryCount (D.ports.facet ⟨q,none⟩)).trans
    (D.refinedCircleLabelEquiv q d)
noncomputable def refinedMarkedLength (f : D.ports.RefinedBandFacet q d)
    (b : Fin (D.refinedMarkedCount q d f)) :=
  (D.refinedCircle q d (D.refinedMarkedLabel q d ⟨f,b⟩)).card
lemma refinedMarkedPositive (f) (b : Fin (D.refinedMarkedCount q d f)) :
    0<D.refinedMarkedLength q d f b :=
  Finset.card_pos.mpr ((D.refinedPreDiagram q d).graftCircle_nonempty q
    (D.ports.refinedBandForSeam q d) _)
noncomputable def refinedMarkedSide (hproper : D.Proper)
    (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩)) :
    ((f : D.ports.RefinedBandFacet q d) × (b : Fin (D.refinedMarkedCount q d f)) ×
      Fin (D.refinedMarkedLength q d f b)) ≃
        Side (D.ports.refinedAtomicGraft q d).toWiring.Seam
          (D.ports.refinedAtomicGraft q d).toWiring.seamArity :=
  ((Equiv.sigmaAssoc (fun f b => Fin (D.refinedMarkedLength q d f b))).symm.trans
      (Equiv.sigmaCongrLeft (β:=fun c => Fin (D.refinedCircle q d c).card)
        (D.refinedMarkedLabel q d))).trans (D.refinedBoundaryEnumeration q d hproper hmax)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end OAI
