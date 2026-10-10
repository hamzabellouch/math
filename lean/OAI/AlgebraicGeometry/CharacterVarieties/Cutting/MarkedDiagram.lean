import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.GraftValues

namespace OAI

/-!
# The marked inverse-band diagram and its facet colours.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
lemma refinedCircleBase_color (c : CutCircleIndex.Label (G:=d.atomicBand.FreshStrip) D.boundaryCount) :
    (D.ports.refinedAtomicGraft q d).facet
      ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d)
        (D.refinedCircleLabelEquiv q d c))=
      CutCircleIndex.facet D.boundaryCount (D.ports.facet ⟨q,none⟩) c := by
  rcases c with ⟨f,b⟩|(_|x)
  · change ((D.refinedPreDiagram q d).ports.graftBand q (D.ports.refinedBandForSeam q d)).facet
      (oldEmbedding (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
        (D.boundaryEntry f b ⟨0,D.boundaryPositive f b⟩))=Sum.inl f
    erw [oldEmbedding_color]
    exact congrArg Sum.inl (D.boundaryFacet f b ⟨0,D.boundaryPositive f b⟩)
  · exact mirrorSide_color (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d) _
  · change ((D.refinedPreDiagram q d).ports.graftBand q (D.ports.refinedBandForSeam q d)).facet
      (bandEmbedding (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
        ((D.ports.refinedBandForSeam q d).origStripSide
          ((D.ports.refinedFreshEquiv q d).symm x).val.val))=Sum.inr x
    erw [bandEmbedding_color,D.ports.refinedFresh_original_color]
    exact congrArg Sum.inr ((D.ports.refinedFreshEquiv q d).apply_symm_apply x)
lemma refinedMarkedBase_color (f : D.ports.RefinedBandFacet q d)
    (b : Fin (D.refinedMarkedCount q d f)) :
    (D.ports.refinedAtomicGraft q d).facet
      ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d)
        (D.refinedMarkedLabel q d ⟨f,b⟩))=f := by
  unfold refinedMarkedLabel
  erw [Equiv.trans_apply,D.refinedCircleBase_color]
  exact CutCircleIndex.enumeration_facet D.boundaryCount (D.ports.facet ⟨q,none⟩) f b
lemma refinedMarkedSide_apply (hproper : D.Proper)
    (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (f : D.ports.RefinedBandFacet q d) (b : Fin (D.refinedMarkedCount q d f))
    (i : Fin (D.refinedMarkedLength q d f b)) :
    D.refinedMarkedSide q d hproper hmax ⟨f,b,i⟩=
      ((D.refinedPreDiagram q d).graftCircleEntry q (D.ports.refinedBandForSeam q d)
        (D.refinedMarkedLabel q d ⟨f,b⟩) i) := rfl
lemma refinedMarkedSide_color (hproper : D.Proper)
    (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
    (f : D.ports.RefinedBandFacet q d) (b : Fin (D.refinedMarkedCount q d f))
    (i : Fin (D.refinedMarkedLength q d f b)) :
    (D.ports.refinedAtomicGraft q d).facet (D.refinedMarkedSide q d hproper hmax ⟨f,b,i⟩)=f := by
  rw [D.refinedMarkedSide_apply]
  exact (next_pow_color (D.refinedPreDiagram q d).ports q (D.ports.refinedBandForSeam q d)
    ((D.refinedPreDiagram q d).graftCircleBase q (D.ports.refinedBandForSeam q d)
      (D.refinedMarkedLabel q d ⟨f,b⟩)) i.val).trans (D.refinedMarkedBase_color q d f b)
end IntegralCharacterVarieties.SurfacePresentation.Diagram

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence VertexTable BandGraft TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))
lemma refinedMarkedSide_next (f : D.ports.RefinedBandFacet q d)
    (b : Fin (D.refinedMarkedCount q d f)) (i : Fin (D.refinedMarkedLength q d f b)) :
    (D.ports.refinedAtomicGraft q d).vertexAssembly.corners.boundaryNext
      (D.refinedMarkedSide q d hproper hmax ⟨f,b,i⟩)=
      D.refinedMarkedSide q d hproper hmax ⟨f,b,⟨(i.val+1)%(D.refinedMarkedLength q d f b),
        Nat.mod_lt _ (D.refinedMarkedPositive q d f b)⟩⟩ :=
  (D.refinedPreDiagram q d).graftBoundaryEnumeration_next q (D.ports.refinedBandForSeam q d)
    (D.ports.refinedBandForSeam_shortRoot_injective q d) (D.refinedPreDiagram_no_child q d hproper hmax)
    (D.refinedMarkedLabel q d ⟨f,b⟩) i
/-- The marked actual inverse-band diagram, retaining the order and starting
occurrence of every old boundary circle. Its mirror boundary is appended at the
selected parent; every fresh strip is precisely one genus-zero disk. Exhaustion
and incidence come from the literal graft successor, not an arbitrary template. -/
noncomputable def refinedMarkedDiagram := ({
  ports := D.ports.refinedAtomicGraft q d
  rank := D.ports.refinedRank q d D.rank
  seamRank := D.refinedAtomicGraft_seamRank q d hp hc hc'
  genus := D.refinedGenus q d
  boundaryCount := D.refinedMarkedCount q d
  boundaryLength := D.refinedMarkedLength q d
  boundaryPositive := D.refinedMarkedPositive q d
  boundarySide := D.refinedMarkedSide q d hproper hmax
  boundaryFacet := D.refinedMarkedSide_color q d hproper hmax
  boundaryNext := D.refinedMarkedSide_next q d hproper hmax
} : Diagram (D.ports.RefinedBandFacet q d) _ _ _)
lemma refinedMarkedDiagram_count_old (f : F) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryCount (.inl f)=
      D.boundaryCount f+(if f=D.ports.facet ⟨q,none⟩ then 1 else 0) := rfl
lemma refinedMarkedDiagram_count_fresh (x : d.atomicBand.FreshStrip) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).boundaryCount (.inr x)=1 := rfl
lemma refinedMarkedDiagram_genus_fresh (x : d.atomicBand.FreshStrip) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).genus (.inr x)=0 := rfl
lemma refinedMarkedDiagram_genus_selected :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).genus (.inl (D.ports.facet ⟨q,none⟩))=
      D.genus (D.ports.facet ⟨q,none⟩)-1 := by
  simp only [refinedMarkedDiagram,refinedGenus,ite_true]
lemma refinedMarkedDiagram_rank_inl (f : F) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).rank (.inl f)=D.rank f := rfl
lemma refinedMarkedDiagram_rank_fresh_lt
    (hlt : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)<r) (x : d.atomicBand.FreshStrip) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).rank (.inr x)<r :=
  D.ports.refinedRank_fresh_lt q d D.rank (fun i => (hc i) ▸ hlt i)
    (fun i => (hc' i) ▸ hlt i) x
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end OAI
