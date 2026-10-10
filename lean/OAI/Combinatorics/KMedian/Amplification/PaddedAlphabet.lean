import Mathlib
import OAI.Combinatorics.KMedian.Machines.VertexMap
import OAI.Combinatorics.KMedian.PCP.BinaryReduction

namespace OAI

section Inline_PCPPaddedAlphabet
namespace MetricKMedian.PCP.AlphabetReduction
open Finset
open scoped BigOperators Classical

variable {V E K : Type} [Fintype V] [Fintype E] [Fintype K] [DecidableEq K]
abbrev RelationInterior (R : Relations K) :=
  BitVector (LocalRelation.Vars (R : LocalRelation.Relation K)) ⊕
    BitVector (LocalRelation.Vars (R : LocalRelation.Relation K) × LocalRelation.Vars (R : LocalRelation.Relation K))
abbrev UniversalInterior (K : Type) [Fintype K] [DecidableEq K] :=
  (R : Relations K) × RelationInterior R
abbrev PaddedPosition (V E K : Type) [Fintype K] [DecidableEq K] :=
  (V × BitVector K) ⊕ (E × UniversalInterior K)
abbrev PaddedNode (V E K : Type) [Fintype K] [DecidableEq K] :=
  PaddedPosition V E K ⊕ (E × EdgeSample K)
noncomputable instance paddedNodeFintype : Fintype (PaddedNode V E K) := by
  classical
  letI : Fintype (PaddedPosition V E K) := inferInstance
  letI : Fintype (E × EdgeSample K) := inferInstance
  exact inferInstanceAs (Fintype (PaddedPosition V E K ⊕ (E × EdgeSample K)))
variable (C : BinaryCSP V E (BitVector K))
def interiorEmbed : ((e : E) × Interior C e) ↪ (E × UniversalInterior K) :=
  (Function.Embedding.sigmaMap (Function.Embedding.refl E)
    (fun e => Function.Embedding.sigmaMk (β := RelationInterior) (C.allowed e))).trans (Equiv.sigmaEquivProd _ _).toEmbedding
def positionEmbed : Position C ↪ PaddedPosition V E K :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (interiorEmbed C)
def nodeEmbed : (Position C ⊕ Test (E := E) (K := K)) ↪ PaddedNode V E K :=
  Function.Embedding.sumMap (positionEmbed C) (Function.Embedding.refl _)
def paddedBinary : BinaryCSP (PaddedNode V E K) (Test (E := E) (K := K) × Fin 4) IncidenceReduction.Label :=
  (binary C).mapVertices (nodeEmbed C)
omit [Fintype V] [Fintype E] in
lemma padded_complete (x : V → BitVector K) (hx : C.Satisfies x) :
    ∃ a, (paddedBinary C).Satisfies a := by
  obtain ⟨a,ha⟩ := binary_complete C x hx
  exact ⟨_,(binary C).mapVertices_complete (nodeEmbed C) a ha⟩
omit [Fintype V] in
lemma padded_sound (a : PaddedNode V E K → IncidenceReduction.Label) :
    C.rejection (decoded C (IncidenceReduction.decoded (a ∘ nodeEmbed C)))/384 ≤
      (paddedBinary C).rejection a := binary_sound C (a ∘ nodeEmbed C)
lemma universalInterior_card : Fintype.card (UniversalInterior K)=interiorBound K := by
  rw [Fintype.card_sigma]
  rfl
lemma padded_node_card : Fintype.card (PaddedNode V E K)=
    Fintype.card V*Fintype.card (BitVector K)+
      Fintype.card E*(interiorBound K+Fintype.card (EdgeSample K)) := by
  simp only [PaddedNode,PaddedPosition,Fintype.card_sum,Fintype.card_prod,universalInterior_card]
  ring
end MetricKMedian.PCP.AlphabetReduction

end Inline_PCPPaddedAlphabet

end OAI
