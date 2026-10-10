import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.MarkedDiagram

namespace OAI

noncomputable section
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence
variable {F S V R : Type} {arity : S → ℕ} [CommRing R]

structure BoundaryMarking (A : PortAssembly F S V arity) where
  count : F → ℕ
  length : (f : F) → Fin (count f) → ℕ
  positive : ∀ f b,0<length f b
  side : ((f : F) × (b : Fin (count f)) × Fin (length f b)) ≃ Side S arity
  facet : ∀ f b i,A.facet (side ⟨f,b,i⟩)=f
  next : ∀ f b i,A.vertexAssembly.corners.boundaryNext (side ⟨f,b,i⟩)=
    side ⟨f,b,⟨(i.val+1)%length f b,Nat.mod_lt _ (positive f b)⟩⟩

def withBoundaryMarking (D : Diagram F S V arity) (B : BoundaryMarking D.ports) :
    Diagram F S V arity := { D with
  boundaryCount := B.count
  boundaryLength := B.length
  boundaryPositive := B.positive
  boundarySide := B.side
  boundaryFacet := B.facet
  boundaryNext := B.next }

lemma frameValues_withBoundaryMarking (D : Diagram F S V arity)
    (B : BoundaryMarking D.ports) (f : D.PortFrames (R:=R)) (s : S) (b : Bool) :
    (D.withBoundaryMarking B).frameValues f s b=D.frameValues f s b := rfl

variable (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : TwoFlagBand.RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))

def cutBoundaryMarking : BoundaryMarking (D.ports.refinedAtomicGraft q d) where
  count := D.refinedMarkedCount q d
  length := D.refinedMarkedLength q d
  positive := D.refinedMarkedPositive q d
  side := D.refinedMarkedSide q d hproper hmax
  facet := D.refinedMarkedSide_color q d hproper hmax
  next := D.refinedMarkedSide_next q d hproper hmax

lemma marked_frameValues (f : (D.refinedCutDiagram q d hp hc hc').PortFrames (R:=R))
    (s : _) (b : Bool) :
    (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).frameValues f s b=
    (D.refinedCutDiagram q d hp hc hc').frameValues f s b :=
  (D.refinedCutDiagram q d hp hc hc').frameValues_withBoundaryMarking
    (D.cutBoundaryMarking q d hproper hmax) f s b
end IntegralCharacterVarieties.SurfacePresentation.Diagram
end

end OAI
