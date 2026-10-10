import OAI.AlgebraicGeometry.CharacterVarieties.Frames.Mirror
import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.MarkedDiagram

namespace OAI

/-!
# Boundary words after band grafting

Ordered boundary words on the original and reflected band recover the
old principal and secondary boundary monodromies.
-/

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical Matrix
open SurfacePresentation.Diagram
variable {F R : Type} [CommRing R] (rank : F → ℕ)
def fiberCoefficient (f : F) {g : F} (x : FacetUnit (R:=R) rank g) : FacetUnit (R:=R) rank f :=
  if h : g=f then rebaseUnit (congrArg rank h) x else 1
lemma fiberCoefficient_one (f g : F) : fiberCoefficient rank f (1 : FacetUnit (R:=R) rank g)=1 := by
  unfold fiberCoefficient
  split_ifs
  · exact (rebaseUnit _).map_one
  · rfl
lemma fiberCoefficient_rebase (f : F) {g h : F} (e : g=h) (x : FacetUnit (R:=R) rank g) :
    fiberCoefficient rank f (rebaseUnit (congrArg rank e) x)=fiberCoefficient rank f x := by
  subst h
  rfl
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram BoundarySurgery
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))

def bandCoefficient (f : F) (a : Side (base A q B).Seam (base A q B).seamArity) : FacetUnit (R:=R) rank f :=
  fiberCoefficient rank f (bandValues A q B rank old short a)

lemma bandCoefficient_old (f : F) (a : Side S arity) :
    bandCoefficient A q B rank old short f (oldEmbedding A q B a)=fiberCoefficient rank f (old a) := by
  rcases a with ⟨s,i⟩
  have h := graftSideValues_old A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) rank old short s i
  have z := congrArg (fiberCoefficient rank f) h
  erw [fiberCoefficient_rebase rank f (graft_old_color A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) s i)] at z
  convert! z using 1

lemma bandCoefficient_strip (hshort : ∀ b i,short b (some i)=1) (f : F)
    (r : B.StripRoot) (z : Side B.doubleWiring.Seam B.doubleWiring.seamArity)
    (hz : z∈B.stripCycle r.val) :
    bandCoefficient A q B rank old short f (bandEmbedding A q B z)=1 := by
  unfold bandCoefficient
  rw [bandValues_strip A q B rank old short hshort r z hz]
  exact fiberCoefficient_one rank _ _

lemma bandCoefficient_shortCycle (hshort : ∀ b i,short b (some i)=1) (f : F) (j)
    (a) (ha : a∈shortCycle A q B j) : bandCoefficient A q B rank old short f a=1 := by
  obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp ha
  exact bandCoefficient_strip A q B rank old short hshort f _ z
    ((B.mem_stripFinset _ _).mp hz)

/-- A nonprincipal old boundary retains its based matrix product over the
coefficient ring. -/
theorem actual_secondary_matrix_word (hshort : ∀ b i,short b (some i)=1)
    (hinj : Function.Injective B.shortRoot) (f : F)
    (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∉s) (a : Side S arity) (ha : a∈s) :
    cycleWord (next A q B) (bandCoefficient A q B rank old short f)
      (oldEmbedding A q B a) (secondaryCircle A q B s).card=
    cycleWord A.vertexAssembly.corners.boundaryNext
      (fun a => fiberCoefficient rank f (old a)) a s.card := by
  have h := (actual_secondary_circle A q B s hs hq hinj
    (bandCoefficient A q B rank old short f)
    (bandCoefficient_shortCycle A q B rank old short hshort f)).2 a ha
  have he : bandCoefficient A q B rank old short f ∘ oldEmbedding A q B=
      fun a => fiberCoefficient rank f (old a) := by
    funext a
    exact bandCoefficient_old A q B rank old short f a
  rw [he] at h
  exact h
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

namespace IntegralCharacterVarieties.BoundarySurgery
open scoped Classical
open Equiv Equiv.Perm
variable {α β : Type} {G : Type*} [Group G]
    (N : Equiv.Perm α) (Z : Equiv.Perm β) (s : Finset α) (q : α)
    (hs : N.IsCycleOn (s : Set α)) (hq : q∈s)
    (f : α → β) {k : ℕ} (c : Fin (k+1) → β)
    (hold : ∀ a∈s,Z (f a)=if N a=q then c 0 else f (N a))
    (hstep : ∀ j : Fin k,Z (c j.castSucc)=c j.succ)
    (hlast : Z (c (Fin.last k))=f q)
include hs hq hold in
lemma chain_word_prefix (u : β → G) (n : ℕ) (hn : n ≤ s.card) :
    cycleWord Z u (f q) n=cycleWord N (u ∘ f) q n := by
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [chain_pow_old N Z s q hs hq f c hold i ((List.mem_range.mp hi).trans_le hn)]
  rfl
include hs hq hold hstep hlast in
lemma chain_word_allBases (u : β → G) (hu : ∀ i,u (c i)=1) (a : α) (ha : a∈s) :
    cycleWord Z u (f a) (s.card+(k+1))=cycleWord N (u ∘ f) a s.card := by
  obtain ⟨j,hj,hja⟩ := hs.exists_pow_eq hq ha
  have hz : (Z^j) (f q)=f a := (chain_pow_old N Z s q hs hq f c hold j hj).trans (congrArg f hja)
  rw [←hz,cycleWord_rotate _ _ _ _ _ (chain_pow_full N Z s q hs hq f c hold hstep hlast),
    chain_word_prefix N Z s q hs hq f c hold u j (le_of_lt hj),
    chain_cycleWord_identity N Z s q hs hq f c hold hstep u hu,
    ←cycleWord_rotate N (u ∘ f) q s.card j (hs.pow_card_apply hq),hja]
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical
open VertexTable BoundarySurgery
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma originalSide_injective : Function.Injective (originalSide A q B) := by
  intro i j h
  have hv := congrArg (fun a : Side (wiring A q B).Seam (wiring A q B).seamArity => a.1.val.1) h
  change Sum.inr (Sum.inl i)=Sum.inr (Sum.inl j) at hv
  exact Sum.inl.inj (Sum.inr.inj hv)
lemma principalCircle_card (s : Finset (Side S arity)) :
    (principalCircle A q B s).card=s.card+(B.length+1) := by
  have hd : Disjoint (s.map (oldEmbedding A q B)) (Finset.univ.image (originalSide A q B)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hb
    rw [←bandEmbedding_origPrincipal] at hi
    exact old_band_ne A q B x _ hi.symm
  erw [principalCircle,Finset.card_union_of_disjoint hd,Finset.card_map,
    Finset.card_image_of_injective _ (originalSide_injective A q B)]
  simp
lemma mirrorCircle_card : (mirrorCircle A q B).card=B.length+1 := by
  erw [mirrorCircle,Finset.card_image_of_injective _ (mirrorEntry_injective A q B)]
  simp
variable (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∈s)
    (hno : ∀ z i,A.facet ⟨z,some i⟩≠A.facet ⟨q,none⟩)
include hs hq hno in
lemma actual_principal_word_allBases {G : Type*} [Group G]
    (u : Side (wiring A q B).Seam (wiring A q B).seamArity → G)
    (hu : ∀ i,u (originalSide A q B i)=1) (a : Side S arity) (ha : a∈s) :
    cycleWord (next A q B) u (oldEmbedding A q B a) (principalCircle A q B s).card=
      cycleWord A.vertexAssembly.corners.boundaryNext (u ∘ oldEmbedding A q B) a s.card := by
  have he (b : Side S arity) (hb : b∈s) : oldEmbedding A q B b=oldSide A q B b.1 := by
    have h := oldPrincipal_parent A q s hs hq hno b hb
    rcases b with ⟨z,c⟩; dsimp only at h; subst c
    exact oldEmbedding_any_parent A q B z
  rw [principalCircle_card,he a ha]
  have hold := next_oldPrincipal A q B s hs hq hno
  have hword := chain_word_allBases A.vertexAssembly.corners.boundaryNext (next A q B) s
    ⟨q,none⟩ hs hq (fun b : Side S arity => oldSide A q B b.1)
    (originalSide A q B) (by
      intro b hb
      have hh := hold b hb
      by_cases hx : A.vertexAssembly.corners.boundaryNext b = (⟨q,none⟩ : Side S arity)
      · rw [ite_eq_left hx] at hh ⊢
        exact hh
      · rw [ite_eq_right hx] at hh ⊢
        exact hh) (next_original A q B) (next_original_last A q B) u hu a ha
  rw [hword]
  unfold cycleWord
  congr 2
  apply List.map_congr_left
  intro i hi
  change u (oldSide A q B _)=u (oldEmbedding A q B _)
  exact congrArg u (he _ (hs.1.mapsTo.iterate i ha)).symm
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft

noncomputable section
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram BoundarySurgery
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma bandCoefficient_original (hshort : short false none=1) (f : F) (i) :
    bandCoefficient A q B rank old short f (originalSide A q B i)=1 := by
  have h := congrArg (fiberCoefficient rank f) (originalValues_identity A q B rank old short hshort i)
  erw [originalValue,fiberCoefficient_rebase rank f (originalSide_color A q B i),fiberCoefficient_one] at h
  convert! h using 1
lemma actual_principal_matrix_word (hshort : short false none=1)
    (f : F) (s : Finset (Side S arity))
    (hs : A.vertexAssembly.corners.boundaryNext.IsCycleOn (s : Set (Side S arity)))
    (hq : (⟨q,none⟩ : Side S arity)∈s)
    (hno : ∀ z i,A.facet ⟨z,some i⟩≠A.facet ⟨q,none⟩)
    (a : Side S arity) (ha : a∈s) :
    cycleWord (next A q B) (bandCoefficient A q B rank old short f)
      (oldEmbedding A q B a) (principalCircle A q B s).card=
    cycleWord A.vertexAssembly.corners.boundaryNext
      (fun a => fiberCoefficient rank f (old a)) a s.card := by
  rw [actual_principal_word_allBases A q B s hs hq hno _
    (bandCoefficient_original A q B rank old short hshort f) a ha]
  congr 1
  funext a
  exact bandCoefficient_old A q B rank old short f a
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable BandGraft BoundarySurgery
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S)
    (B : RealizedBand (D.ports.facet ⟨q,none⟩) (D.ports.seamChildren q) (D.ports.seamChildren q))
    (old : D.SideValues (R:=R))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) D.rank (D.ports.facet ⟨q,i⟩))
lemma oldGraftCircle_word (hp : short false none=1) (hc : ∀ b i,short b (some i)=1)
    (hinj : Function.Injective B.shortRoot)
    (hno : ∀ s i,D.ports.facet ⟨s,some i⟩≠D.ports.facet ⟨q,none⟩)
    (f : F) (b : Fin (D.boundaryCount f)) :
    cycleWord (next D.ports q B) (bandCoefficient D.ports q B D.rank old short f)
      (D.graftCircleBase q B (.inl ⟨f,b⟩)) (D.oldGraftCircle q B f b).card=
    cycleWord D.ports.vertexAssembly.corners.boundaryNext (D.sideCoefficient old f)
      (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryLength f b) := by
  have ha : D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩∈D.boundarySet f b :=
    Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩
  by_cases hq : (⟨q,none⟩ : Side S arity)∈D.boundarySet f b
  · rw [oldGraftCircle,ite_eq_left hq]
    have h := actual_principal_matrix_word D.ports q B D.rank old short hp f _
      (D.boundarySet_isCycle f b) hq hno _ ha
    rw [D.boundarySet_card] at h
    exact h
  · rw [oldGraftCircle,ite_eq_right hq]
    have h := actual_secondary_matrix_word D.ports q B D.rank old short hc hinj f _
      (D.boundarySet_isCycle f b) hq _ ha
    rw [D.boundarySet_card] at h
    exact h
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand BoundarySurgery
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
/-- The old diagram with its ranks extended to the grafted facets. -/
noncomputable def refinedWordPreDiagram : Diagram (D.ports.RefinedBandFacet q d) S V arity :=
  { D.refinedPreDiagram q d with
    rank := D.ports.refinedRank q d D.rank
    seamRank := D.seamRank }
noncomputable def refinedOldBoundary (f : F) (b : Fin (D.boundaryCount f)) :
    Fin (D.refinedMarkedCount q d (.inl f)) :=
  b.castAdd (CutCircleIndex.extra (D.ports.facet ⟨q,none⟩) f)
noncomputable def refinedMirrorBoundary :
    Fin (D.refinedMarkedCount q d (.inl (D.ports.facet ⟨q,none⟩))) :=
  ⟨D.boundaryCount (D.ports.facet ⟨q,none⟩),by
    simp [refinedMarkedCount,CutCircleIndex.count,CutCircleIndex.extra]⟩
lemma refinedMarkedLabel_old (f : F) (b : Fin (D.boundaryCount f)) :
    D.refinedMarkedLabel q d ⟨.inl f,D.refinedOldBoundary q d f b⟩=.inl ⟨.inl f,b⟩ := by
  exact congrArg (D.refinedCircleLabelEquiv q d)
    (CutCircleIndex.enumeration_old D.boundaryCount (D.ports.facet ⟨q,none⟩) f b)
lemma refinedMarkedLabel_mirror :
    D.refinedMarkedLabel q d ⟨.inl (D.ports.facet ⟨q,none⟩),D.refinedMirrorBoundary q d⟩=.inr (.inl ()) := by
  exact congrArg (D.refinedCircleLabelEquiv q d)
    (CutCircleIndex.enumeration_mirror D.boundaryCount (D.ports.facet ⟨q,none⟩))
lemma refinedMarkedLabel_fresh (x : d.atomicBand.FreshStrip) :
    D.refinedMarkedLabel q d ⟨.inr x,⟨0,Nat.zero_lt_one⟩⟩=
      .inr (.inr ((D.ports.refinedFreshEquiv q d).symm x)) := rfl
lemma refinedWordPreCoefficient (old : D.SideValues (R:=R)) (f : F) (a : Side S arity) :
    (D.refinedWordPreDiagram q d).sideCoefficient old (.inl f) a=D.sideCoefficient old f a := by
  unfold sideCoefficient
  by_cases h : D.ports.facet a=f
  · have hh : (D.refinedWordPreDiagram q d).ports.facet a=.inl f := congrArg Sum.inl h
    rw [dite_eq_left hh,dite_eq_left h]
    rfl
  · have hh : (D.refinedWordPreDiagram q d).ports.facet a≠.inl f := fun hh => h (Sum.inl.inj hh)
    rw [dite_eq_right hh,dite_eq_right h]
    rfl
end IntegralCharacterVarieties.SurfacePresentation.Diagram

noncomputable section
namespace IntegralCharacterVarieties.BoundarySurgery
variable {α : Type} {G : Type*} [Group G] (N : Equiv.Perm α) {k : ℕ}
    (e : Fin (k+1) → α) (he : ∀ i,N (e i)=e (finRotate (k+1) i)) (u : α → G)
include he in
lemma cycleWord_of_cycleEntry : cycleWord N u (e 0) (k+1)=(List.ofFn (u ∘ e)).reverse.prod := by
  unfold cycleWord
  congr 2
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    rw [pow_cycleEntry N e he j (by simpa using hj)]
    rfl
end IntegralCharacterVarieties.BoundarySurgery
namespace IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
open scoped Classical Matrix
open VertexTable SurfacePresentation.Diagram BoundarySurgery
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]
    (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
    (rank : F → ℕ)
    (old : (s : Side S arity) → FacetUnit (R:=R) rank (A.facet s))
    (short : Bool → (i : Option (Fin (arity q))) → FacetUnit (R:=R) rank (A.facet ⟨q,i⟩))
lemma bandCoefficient_mirror (i) :
    bandCoefficient A q B rank old short (A.facet ⟨q,none⟩) (mirrorSide A q B i)=
      mirrorValue A q B rank old short i := by
  have h : fiberCoefficient rank (A.facet ⟨q,none⟩) (mirrorValue A q B rank old short i)=
      mirrorValue A q B rank old short i := by
    unfold fiberCoefficient
    rw [dite_eq_left rfl]
    rfl
  erw [← h,mirrorValue,fiberCoefficient_rebase rank _ (mirrorSide_color A q B i)]
  rfl
lemma mirrorCircle_word :
    cycleWord (next A q B) (bandCoefficient A q B rank old short (A.facet ⟨q,none⟩))
      (mirrorEntry A q B 0) (mirrorCircle A q B).card=short true none := by
  erw [mirrorCircle_card,cycleWord_of_cycleEntry _ _ (mirrorEntry_next A q B)]
  have h : bandCoefficient A q B rank old short (A.facet ⟨q,none⟩) ∘ mirrorEntry A q B=
      fun i => mirrorValue A q B rank old short i.rev := by
    funext i
    exact bandCoefficient_mirror A q B rank old short i.rev
  erw [h]
  exact mirrorValues_word A q B rank old short
lemma freshCircle_word (hc : ∀ b i,short b (some i)=1) (f : F) (x : B.FreshStrip) :
    cycleWord (next A q B) (bandCoefficient A q B rank old short f)
      (bandEmbedding A q B (B.origStripSide x.val.val)) (freshCircle A q B x).card=1 := by
  apply cycleWord_one_on _ _ _ (freshStrip_actual_circle A q B x)
  · refine Finset.mem_map.mpr ⟨_,?_,rfl⟩
    apply (B.mem_stripFinset _ _).mpr
    have h := B.stripCycle_mem_orig x.val.val
    rwa [B.stripForest.root_of_source x.val.val x.val.property] at h
  · intro a ha
    obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp ha
    exact bandCoefficient_strip A q B rank old short hc f x.val z ((B.mem_stripFinset _ _).mp hz)
end IntegralCharacterVarieties.OccurrenceIncidence.BandGraft
end

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical Matrix
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand BoundarySurgery MatrixExpression
variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
variable (φ : R →+* A) (frames : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).PortFrames (R:=A))
    (old : D.SideValues (R:=A)) (J Y : (Matrix (Fin (D.rank (D.ports.facet ⟨q,none⟩)))
      (Fin (D.rank (D.ports.facet ⟨q,none⟩))) A)ˣ) (handles : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).HandleValues (R:=A))
lemma refinedMarked_boundaryWord (f : D.ports.RefinedBandFacet q d) (b : Fin ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryCount f)) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord f b).eval φ (valuesFromPorts (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) frames (D.refinedCutSideValues q d hp hc hc' old J Y) handles)=
      cycleWord (next (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d))
        (bandCoefficient (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d) (D.ports.refinedRank q d D.rank)
          (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) f)
        ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d) (D.refinedMarkedLabel q d ⟨f,b⟩))
        (D.refinedCircle q d (D.refinedMarkedLabel q d ⟨f,b⟩)).card := by
  have h := @boundaryWord_cycleWord _ _ _ R A _ _ _ (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) φ (valuesFromPorts (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) frames (D.refinedCutSideValues q d hp hc hc' old J Y) handles) f b
  exact h

lemma refinedMarked_boundaryWord_old (f : F) (b : Fin (D.boundaryCount f)) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl f) (D.refinedOldBoundary q d f b)).eval φ (valuesFromPorts (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) frames (D.refinedCutSideValues q d hp hc hc' old J Y) handles)=
      cycleWord D.ports.vertexAssembly.corners.boundaryNext
        (D.sideCoefficient (D.cutOldSideValues q old J) f)
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩) (D.boundaryLength f b) := by
  have hw := D.refinedMarked_boundaryWord q d hp hc hc' hproper hmax φ frames old J Y handles
    (.inl f) (D.refinedOldBoundary q d f b)
  have hl := congrArg (fun c : D.RefinedCircleLabel q d =>
    cycleWord (next (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d))
      (bandCoefficient (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
        (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) (.inl f))
      ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d) c)
      (D.refinedCircle q d c).card) (D.refinedMarkedLabel_old q d f b)
  refine hw.trans (hl.trans ?_)
  have h := (D.refinedWordPreDiagram q d).oldGraftCircle_word q (D.ports.refinedBandForSeam q d)
    (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) rfl (fun _ _ => rfl)
    (D.ports.refinedBandForSeam_shortRoot_injective q d)
    (D.refinedPreDiagram_no_child q d hproper hmax) (.inl f) b
  have he : (D.refinedWordPreDiagram q d).sideCoefficient (D.cutOldSideValues q old J) (.inl f)=
      D.sideCoefficient (D.cutOldSideValues q old J) f := by
    funext a
    exact D.refinedWordPreCoefficient q d _ f a
  rw [he] at h
  exact h
lemma refinedMarked_boundaryWord_mirror :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inl (D.ports.facet ⟨q,none⟩)) (D.refinedMirrorBoundary q d)).eval φ (valuesFromPorts (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) frames (D.refinedCutSideValues q d hp hc hc' old J Y) handles)=Y := by
  have hw := D.refinedMarked_boundaryWord q d hp hc hc' hproper hmax φ frames old J Y handles
    (.inl (D.ports.facet ⟨q,none⟩)) (D.refinedMirrorBoundary q d)
  have hl := congrArg (fun c : D.RefinedCircleLabel q d =>
    cycleWord (next (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d))
      (bandCoefficient (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
        (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) (.inl (D.ports.facet ⟨q,none⟩)))
      ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d) c)
      (D.refinedCircle q d c).card) (D.refinedMarkedLabel_mirror q d)
  refine hw.trans (hl.trans ?_)
  exact mirrorCircle_word (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d) (D.ports.refinedRank q d D.rank)
    (D.cutOldSideValues q old J) (D.cutShortSideValues q Y)
lemma refinedMarked_boundaryWord_fresh (x : d.atomicBand.FreshStrip) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryWord (.inr x) ⟨0,Nat.zero_lt_one⟩).eval φ (valuesFromPorts (D.refinedMarkedDiagram q d hp hc hc' hproper hmax) frames (D.refinedCutSideValues q d hp hc hc' old J Y) handles)=1 := by
  have hw := D.refinedMarked_boundaryWord q d hp hc hc' hproper hmax φ frames old J Y handles
    (.inr x) ⟨0,Nat.zero_lt_one⟩
  have hl := congrArg (fun c : D.RefinedCircleLabel q d =>
    cycleWord (next (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d))
      (bandCoefficient (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
        (D.ports.refinedRank q d D.rank) (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) (.inr x))
      ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d) c)
      (D.refinedCircle q d c).card) (D.refinedMarkedLabel_fresh q d x)
  refine hw.trans (hl.trans ?_)
  exact freshCircle_word (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d) (D.ports.refinedRank q d D.rank)
    (D.cutOldSideValues q old J) (D.cutShortSideValues q Y) (fun _ _ => rfl) _ _
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
