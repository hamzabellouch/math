import Mathlib

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea

/-- The signed words encode the relators `x²y⁻⁵` and `x²(yx⁻¹)³`. -/
def seedWord : Bool → List (Bool × Bool)
  | false => [(false, true), (false, true), (true, false), (true, false),
      (true, false), (true, false), (true, false)]
  | true => [(false, true), (false, true), (true, true), (false, false),
      (true, true), (false, false), (true, true), (false, false)]

def boundaryLength (relation : Bool) : ℕ := 3 * (seedWord relation).length

abbrev RoseVertex := Option (Bool × Fin 2)
abbrev SeedVertex := RoseVertex ⊕ Bool
abbrev CircleEdge := Bool × Fin 3
abbrev Sector := (relation : Bool) × Fin (boundaryLength relation)
abbrev SeedEdge := CircleEdge ⊕ Sector
abbrev SeedCell := SeedVertex ⊕ (SeedEdge ⊕ Sector)

def circleStart (edge : CircleEdge) : RoseVertex :=
  ![none, some (edge.1, 0), some (edge.1, 1)] edge.2

def circleEnd (edge : CircleEdge) : RoseVertex :=
  ![some (edge.1, 0), some (edge.1, 1), none] edge.2

def sectorLetter (sector : Sector) : Bool × Bool :=
  (seedWord sector.1).get ⟨sector.2.val / 3, by
    have bound := sector.2.isLt
    dsimp [boundaryLength] at bound
    omega⟩

def sectorCircleEdge (sector : Sector) : CircleEdge :=
  ((sectorLetter sector).1, if (sectorLetter sector).2 then
    ⟨sector.2.val % 3, Nat.mod_lt _ (by decide)⟩ else
    ⟨2 - sector.2.val % 3, by omega⟩)

def sectorStart (sector : Sector) : RoseVertex :=
  if (sectorLetter sector).2 then circleStart (sectorCircleEdge sector)
  else circleEnd (sectorCircleEdge sector)

def nextSector (sector : Sector) : Sector :=
  ⟨sector.1, ⟨(sector.2.val + 1) % boundaryLength sector.1,
    Nat.mod_lt _ (by have := sector.2.isLt; omega)⟩⟩

def edgeVertices : SeedEdge → Finset SeedVertex
  | .inl edge => {.inl (circleStart edge), .inl (circleEnd edge)}
  | .inr sector => {.inr sector.1, .inl (sectorStart sector)}

def sectorEdges (sector : Sector) : Finset SeedEdge :=
  {.inl (sectorCircleEdge sector), .inr sector, .inr (nextSector sector)}

def sectorVertices (sector : Sector) : Finset SeedVertex :=
  (sectorEdges sector).biUnion edgeVertices

def properFace : SeedCell → SeedCell → Prop
  | .inl vertex, .inr (.inl edge) => vertex ∈ edgeVertices edge
  | .inl vertex, .inr (.inr sector) => vertex ∈ sectorVertices sector
  | .inr (.inl edge), .inr (.inr sector) => edge ∈ sectorEdges sector
  | _, _ => False

/-- Comparability graph of the seven vertices, 51 edges and 45 sectors. -/
def seedGraph : SimpleGraph SeedCell where
  Adj first second := properFace first second ∨ properFace second first
  symm := ⟨fun _ _ adjacent => adjacent.elim Or.inr Or.inl⟩
  loopless := ⟨by
    intro cell
    rcases cell with vertex | cell
    · simp [properFace]
    · rcases cell with edge | sector <;> simp [properFace]⟩

def artinRelations {Vertex : Type*} (graph : SimpleGraph Vertex) : Set (FreeGroup Vertex) :=
  {word | ∃ first second, graph.Adj first second ∧
    word = FreeGroup.of first * FreeGroup.of second *
      (FreeGroup.of first)⁻¹ * (FreeGroup.of second)⁻¹}

abbrev ArtinGroup {Vertex : Type*} (graph : SimpleGraph Vertex) :=
  PresentedGroup (artinRelations graph)

def height {Vertex : Type*} (graph : SimpleGraph Vertex) :
    ArtinGroup graph →* Multiplicative ℤ :=
  PresentedGroup.toGroup (f := fun _ : Vertex => Multiplicative.ofAdd (1 : ℤ)) (by
    rintro word ⟨first, second, _, rfl⟩
    simp)

abbrev SourceGroup := (height seedGraph).ker

/-- Projective dimension of the trivial integral left group-ring module. -/
def cohomologicalDimension (GroupType : Type*) [Group GroupType] : WithBot ℕ∞ :=
  CategoryTheory.projectiveDimension
    (ModuleCat.of (MonoidAlgebra ℤ GroupType)
      (Representation.trivial ℤ GroupType ℤ).asModule)

universe u

/-- Ordinary classifying CW spaces, with no bound on the cardinality of their cells. -/
def HasClassifyingSpace (GroupType : Type*) [Group GroupType] (dimension : ℕ) : Prop :=
  ∃ (Space : Type u) (_ : TopologicalSpace Space) (_ : T2Space Space)
    (_ : Topology.CWComplex (Set.univ : Set Space)),
    (∀ degree : ℕ, dimension < degree →
      IsEmpty (Topology.CWComplex.cell (Set.univ : Set Space) degree)) ∧
    PathConnectedSpace Space ∧
    ∃ basepoint : Space, Nonempty (FundamentalGroup Space basepoint ≃* GroupType) ∧
    ∃ (Cover : Type u) (_ : TopologicalSpace Cover), ContractibleSpace Cover ∧
    ∃ projection : Cover → Space, IsCoveringMap projection ∧ Function.Surjective projection

theorem source_main :
    Group.FG SourceGroup ∧ Group.ResiduallyFinite SourceGroup ∧
    cohomologicalDimension SourceGroup = 2 ∧
    HasClassifyingSpace.{0} SourceGroup 3 ∧
    ¬ HasClassifyingSpace.{u} SourceGroup 2 := by
  sorry

end EilenbergGanea

end

end OAI
