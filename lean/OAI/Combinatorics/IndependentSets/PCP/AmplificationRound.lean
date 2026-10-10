import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.Gap

namespace OAI

noncomputable section

namespace IndependentSetsGames.Foundations.PCP.AmplificationRound

abbrev Label := QueryIncidence.Label 6
abbrev Addresses := PoweringLabels.PortWords Preprocessing.Port FinalConstants.walkLength
abbrev PoweredAlphabet :=
  PoweringLabels.PaddedLabel Preprocessing.Port FinalConstants.walkLength Label

instance : Fintype PoweredAlphabet := Fintype.ofFinite _
instance : DecidableEq PoweredAlphabet := Classical.decEq _

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Nonempty E]

abbrev PoweredDart (G : ConstraintGraph V E Label) :=
  PoweringTest.Dart (Preprocessing.Vertex G) Preprocessing.Port
    (2 * FinalConstants.endpointLength)

instance (G : ConstraintGraph V E Label) : DecidableEq (PoweredDart G) := Classical.decEq _

def selectors (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) (v : Preprocessing.Vertex G) :
    PoweringLabels.AddressSelector (Preprocessing.portGraph G)
      FinalConstants.walkLength v :=
  PoweringLabels.listSelector (Preprocessing.portGraph G) FinalConstants.walkLength
    v addresses complete

def powered (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) :
    ConstraintGraph (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet :=
  PoweringTest.poweredGraph (Preprocessing.portGraph G) (Preprocessing.graph G).accepts
    (2 * FinalConstants.endpointLength) (selectors addresses complete G)

abbrev Vertex (G : ConstraintGraph V E Label) :=
  QueryIncidence.Vertex
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet)
    (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)

abbrev Dart (G : ConstraintGraph V E Label) :=
  QueryIncidence.Dart (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) 6

instance (G : ConstraintGraph V E Label) : Fintype (Vertex G) := by
  letI : Fintype (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet) := inferInstance
  letI : Fintype
      (AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet) :=
    inferInstance
  change Fintype
    (AlphabetGraph.Event (PoweredDart G) PoweredAlphabet ⊕
      AlphabetGraph.Address (Preprocessing.Vertex G) (PoweredDart G) PoweredAlphabet)
  infer_instance
instance (G : ConstraintGraph V E Label) : Fintype (Dart G) := by
  change Fintype ((AlphabetGraph.Event (PoweredDart G) PoweredAlphabet × Fin 6) × Bool)
  infer_instance
instance (G : ConstraintGraph V E Label) : DecidableEq (Vertex G) := Classical.decEq _

def graph (addresses : List Addresses) (complete : ∀ w, w ∈ addresses)
    (G : ConstraintGraph V E Label) : ConstraintGraph (Vertex G) (Dart G) Label :=
  AlphabetGraph.graph (powered addresses complete G)

omit [Nonempty E] in
theorem powered_completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (powered addresses complete G).Satisfiable := by
  obtain ⟨assignment, hassignment⟩ := Preprocessing.completeness G satisfied
  refine ⟨PoweringOpinions.honestLabels (Preprocessing.portGraph G)
    FinalConstants.walkLength assignment, ?_⟩
  apply PoweringTest.perfect_completeness (Preprocessing.portGraph G)
    (Preprocessing.graph G).accepts (2 * FinalConstants.endpointLength)
    (selectors addresses complete G) assignment
  intro e
  exact hassignment e

omit [Nonempty E] in
theorem completeness (addresses : List Addresses)
    (complete : ∀ w, w ∈ addresses) (G : ConstraintGraph V E Label)
    (satisfied : G.Satisfiable) : (graph addresses complete G).Satisfiable :=
  AlphabetGraph.perfect_completeness _
    (powered_completeness addresses complete G satisfied)

end IndependentSetsGames.Foundations.PCP.AmplificationRound
end

end OAI
