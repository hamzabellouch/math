import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Module.LinearMap.End
import OAI.Computability.UniqueGames.Reduction.ActualCanonicalLemmas
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Reduction.EncodingLemmas
import OAI.Computability.UniqueGames.Reduction.ExplicitLemmas
import OAI.Computability.UniqueGames.Reduction.GapSemanticsLemmas
import OAI.Computability.UniqueGames.Reduction.NoiseEnumerationLemmas

namespace OAI

section

/-! Actual finite translation game of Definition 4.6.  All questions, linear
maps, noise indices and linear functionals occur once in the outcome list.
Equal noise vectors retain their index multiplicity. -/

namespace UniqueGamesTheorem.Reduction.ActualGame

open UniqueGamesTheorem.Integration.BinaryLinear
open ActualSource
open Foundations.Target
open scoped BigOperators

def names (S : Source) (i : Fin S.occurrences) (j : Fin 3) : Fin S.variables :=
  if j = 0 then (S.equation i).first
  else if j = 1 then (S.equation i).second else (S.equation i).third

def rhs (S : Source) (i : Fin S.occurrences) : F2 := ofBit (S.equation i).rhs

abbrev Question (S : Source) (k : Nat) := Fin k → Fin S.occurrences
abbrev Map (k s d : Nat) := ActualHomogeneous.E k →ₗ[F2] ActualSource.Ambient s d
abbrev Dual (k : Nat) := ActualHomogeneous.E k →ₗ[F2] F2
abbrev Query (S : Source) (k s d : Nat) := Question S k × Map k s d

noncomputable instance mapFintype (k s d : Nat) : Fintype (Map k s d) :=
  Fintype.ofInjective (fun X : Map k s d => (X : ActualHomogeneous.E k →
    ActualSource.Ambient s d)) DFunLike.coe_injective

noncomputable instance dualFintype (k : Nat) : Fintype (Dual k) :=
  Fintype.ofInjective (fun X : Dual k => (X : ActualHomogeneous.E k → F2))
    DFunLike.coe_injective

def canonical (S : Source) (k s d : Nat) (q : Query S k s d) :=
  ActualCanonical.canonical q.1 (names S) (rhs S) q.2

abbrev Vertex (S : Source) (k s d : Nat) := ActualOrbit.Vertex (canonical S k s d)
abbrev TwoSidedVertex (S : Source) (k s d : Nat) := Bool × Vertex S k s d

def vertex (S : Source) (k s d : Nat) (q : Query S k s d) : Vertex S k s d :=
  ActualOrbit.vertex (canonical S k s d) q

def offset (S : Source) (k s d : Nat) (q : Query S k s d) : Alphabet s :=
  ActualOrbit.offset (canonical S k s d) q

def shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) : Query S k s d :=
  (q.1, q.2 + ActualHomogeneous.tau.smulRight (c, (0 : Vector d)))

theorem canonical_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    canonical S k s d (shiftQuery S k s d c q) =
      ((canonical S k s d q).1 + (c, 0), (canonical S k s d q).2) :=
  ActualCanonical.canonical_shift _ _ _ _ _

@[simp] theorem vertex_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    vertex S k s d (shiftQuery S k s d c q) = vertex S k s d q := by
  apply (ActualOrbit.vertex_eq_iff _ _ _).2
  simp only [ActualOrbit.body, canonical_shiftQuery, Prod.snd_add, add_zero]

@[simp] theorem offset_shiftQuery (S : Source) (k s d : Nat) (c : Alphabet s)
    (q : Query S k s d) :
    offset S k s d (shiftQuery S k s d c q) = offset S k s d q + c := by
  simp only [offset, ActualOrbit.offset, canonical_shiftQuery, Prod.fst_add]

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (TwoSidedVertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (vertexCount S k s d) :=
  ActualOrbit.vertexEquiv (canonical S k s d)

theorem vertexCount_eq_twice (S : Source) (k s d : Nat) :
    vertexCount S k s d = 2 * Fintype.card (Vertex S k s d) := by
  simp [vertexCount, TwoSidedVertex]

/-- Each product element is a separate edge occurrence. -/
abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

def leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d := ω.1

def rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Query S k s d :=
  (ω.1.1, ω.1.2 + ω.2.2.smulRight (g.noise ω.2.1))

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

theorem edge_source_ne_target (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) :
    (edge S k g ω).source ≠ (edge S k g ω).target := by
  intro h
  have h' := (vertexEncoding S k s d).injective h
  have hside : false = true := congrArg Prod.fst h'
  exact Bool.false_ne_true hside

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    List (Outcome S k g) := Finset.univ.toList

@[simp] theorem mem_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) : ω ∈ outcomes S k g := by
  simp [outcomes]

theorem outcomes_nodup (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    (outcomes S k g).Nodup := Finset.nodup_toList _

@[simp] theorem outcomes_length (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) : (outcomes S k g).length = Fintype.card (Outcome S k g) := by
  simp [outcomes]

noncomputable def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    Foundations.Target.Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (outcomes S k g).map (edge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : edge S k g ω ∈ (outcomes S k g).map (edge S k g) :=
      List.mem_map.mpr ⟨ω, mem_outcomes S k g ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstance_constraints_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) :
    (outputInstance S k g).constraints.length = Fintype.card (Outcome S k g) := by
  simp [outputInstance]

noncomputable def sideLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d (side, v)))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  let v := (vertexEncoding S k s d).symm i
  Encoding.alphabetEquiv s (labels v.1 v.2)

@[simp] theorem sideLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Bool → Vertex S k s d → Alphabet s) (side : Bool) :
    sideLabel S k s d (labelingOf S k s d labels) side = labels side := by
  funext v
  simp [sideLabel, labelingOf]

noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool)
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (sideLabel S k s d labeling side) q

theorem unfolded_equivariant (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (side : Bool)
    (q : Query S k s d) (c : Alphabet s) :
    unfolded S k s d labeling side (shiftQuery S k s d c q) =
      unfolded S k s d labeling side q + c := by
  change sideLabel S k s d labeling side (vertex S k s d (shiftQuery S k s d c q)) +
    offset S k s d (shiftQuery S k s d c q) = _
  rw [vertex_shiftQuery, offset_shiftQuery]
  exact (add_assoc _ _ _).symm

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling false (leftQuery S k g ω) =
      unfolded S k s d labeling true (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (sideLabel S k s d labeling false (vertex S k s d (leftQuery S k g ω)))
    (sideLabel S k s d labeling true (vertex S k s d (rightQuery S k g ω)))
  simp only [sideLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (sideLabel S k s d labeling false) (sideLabel S k s d labeling true) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  Finset.univ.expect (fun ω : Outcome S k g =>
    if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0)

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      Finset.univ.expect (fun ω : Outcome S k g =>
        if unfolded S k s d labeling false (leftQuery S k g ω) =
            unfolded S k s d labeling true (rightQuery S k g ω)
        then (1 : ℚ) else 0) := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

private theorem countSatisfied_map {n q : Nat} {I : Type*}
    (labeling : Fin n → Fin q) (edges : I → Constraint n q) (xs : List I) :
    countSatisfied labeling (xs.map edges) =
      (xs.map (fun x => if (edges x).satisfied labeling then 1 else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, countSatisfied, List.sum_cons, ih]

theorem countSatisfied_eq_sum (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    countSatisfied labeling (outputInstance S k g).constraints =
      ∑ ω : Outcome S k g, if (edge S k g ω).satisfied labeling then 1 else 0 := by
  change countSatisfied labeling ((outcomes S k g).map (edge S k g)) = _
  rw [countSatisfied_map]
  exact Finset.sum_map_toList _ _

/-- The expectation is exactly the satisfied fraction of the explicit edge list. -/
theorem acceptanceProbability_eq_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      (countSatisfied labeling (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [acceptanceProbability, Fintype.expect_eq_sum_div_card,
    outputInstance_constraints_length, countSatisfied_eq_sum]
  congr 1
  simp

/-! ## Executable enumeration and vertex numbering -/

def orbitBodyDecidableEq (S : Source) (k s d : Nat) :
    DecidableEq (Vector d × (Fin k → ActualCanonical.Record
      (Fin S.variables) (Fin S.occurrences) (ActualSource.Ambient s d))) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

def explicitBodies (S : Source) (k s d : Nat) := by
  letI := orbitBodyDecidableEq S k s d
  exact Encoding.imageVertices (ActualEnumeration.queries S.occurrences k s d)
    (ActualOrbit.body (canonical S k s d))

def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  2 * (explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    TwoSidedVertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := orbitBodyDecidableEq S k s d
  exact (Equiv.prodCongr (Equiv.refl Bool)
    (ActualOrbit.explicitVertexEquiv (canonical S k s d)
      (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries)).trans
    (Encoding.sideEquiv _)

noncomputable def semanticToExplicitVertices (S : Source) (k s d : Nat) :
    Fin (vertexCount S k s d) ≃ Fin (explicitVertexCount S k s d) :=
  (vertexEncoding S k s d).symm.trans (explicitVertexEncoding S k s d)

@[simp] theorem semanticToExplicitVertices_apply (S : Source) (k s d : Nat)
    (v : TwoSidedVertex S k s d) :
    semanticToExplicitVertices S k s d (vertexEncoding S k s d v) =
      explicitVertexEncoding S k s d v := by
  simp [semanticToExplicitVertices]

theorem explicitVertexCount_eq (S : Source) (k s d : Nat) :
    explicitVertexCount S k s d = vertexCount S k s d := by
  simpa using (Fintype.card_congr (semanticToExplicitVertices S k s d)).symm

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (false, vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (true, vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

theorem explicitEdge_eq_rename (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) :
    explicitEdge S k g ω = Integration.InstanceEquivalences.renameConstraint
      (semanticToExplicitVertices S k s d) (edge S k g ω) := by
  simp only [explicitEdge, Integration.InstanceEquivalences.renameConstraint, edge,
    semanticToExplicitVertices_apply]

def explicitOutcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (en : NoiseEnumeration g) : List (Outcome S k g) :=
  ActualEnumeration.indexedOutcomes S.occurrences k s d en.indices

theorem explicitOutcomes_nodup (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Nodup :=
  ActualEnumeration.nodup_indexedOutcomes en.nodup _ _ _ _

@[simp] theorem mem_explicitOutcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) (ω : Outcome S k g) :
    ω ∈ explicitOutcomes S k g en :=
  ActualEnumeration.mem_indexedOutcomes en.complete ω

theorem explicitOutcomes_perm_outcomes (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (explicitOutcomes S k g en).Perm (outcomes S k g) := by
  apply (List.perm_ext_iff_of_nodup (explicitOutcomes_nodup S k g en)
    (outcomes_nodup S k g)).2
  intro ω
  simp

/-- This construction computes its vertex numbering, all outcomes, and every
forward/inverse permutation entry from the explicitly supplied finite data. -/
def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Foundations.Target.Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map, explicitOutcomes,
    ActualEnumeration.length_indexedOutcomes]

theorem explicitConstraints_perm_renamed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.Perm
      ((outputInstance S k g).constraints.map
        (Integration.InstanceEquivalences.renameConstraint (semanticToExplicitVertices S k s d))) := by
  simpa only [outputInstanceWithEnumeration, outputInstance, List.map_map,
    Function.comp_def, ← explicitEdge_eq_rename] using
    (explicitOutcomes_perm_outcomes S k g en).map (explicitEdge S k g)

theorem completeAt_outputInstanceWithEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    CompleteAt error (outputInstanceWithEnumeration S k g en) ↔
      CompleteAt error (outputInstance S k g) :=
  Integration.InstanceEquivalences.completeAt_iff_of_rename_perm error
    (outputInstance S k g) (outputInstanceWithEnumeration S k g en)
    (semanticToExplicitVertices S k s d) (explicitConstraints_perm_renamed S k g en)

theorem soundAt_outputInstanceWithEnumeration_iff (error : RationalError)
    (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    SoundAt error (outputInstanceWithEnumeration S k g en) ↔
      SoundAt error (outputInstance S k g) :=
  Integration.InstanceEquivalences.soundAt_iff_of_rename_perm error
    (outputInstance S k g) (outputInstanceWithEnumeration S k g en)
    (semanticToExplicitVertices S k s d) (explicitConstraints_perm_renamed S k g en)

end UniqueGamesTheorem.Reduction.ActualGame

end

end OAI
