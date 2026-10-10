import Mathlib
import OAI.Computability.MaxCut.Encoding.TableKeys
import OAI.Computability.MaxCut.Games.NoiseEnumeration

namespace OAI

namespace MaxCutGames.Decoder.TableKeysGame

open MaxCutGames.Integration.BinaryLinear MaxCutGames.Reduction
open ActualSource Foundations.Target
open scoped BigOperators

abbrev Question (S : Source) (k : Nat) := ActualGame.Question S k
abbrev Map (k s d : Nat) := ActualGame.Map k s d
abbrev Dual (k : Nat) := ActualGame.Dual k
abbrev Query (S : Source) (k s d : Nat) := ActualGame.Query S k s d
abbrev canonical (S : Source) (k s d : Nat) := ActualGame.canonical S k s d

/-- One realized key orbit, with no prover-side copy. -/
abbrev Vertex (S : Source) (k s d : Nat) := ActualGame.Vertex S k s d
abbrev vertex (S : Source) (k s d : Nat) := ActualGame.vertex S k s d
abbrev offset (S : Source) (k s d : Nat) := ActualGame.offset S k s d
abbrev shiftQuery (S : Source) (k s d : Nat) := ActualGame.shiftQuery S k s d

noncomputable def vertexCount (S : Source) (k s d : Nat) : Nat :=
  Fintype.card (Vertex S k s d)

noncomputable def vertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (vertexCount S k s d) := Fintype.equivFin _

/-- All four sampling choices remain separate occurrence indices. -/
abbrev Outcome (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  Query S k s d × g.NoiseIndex × Dual k

abbrev leftQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.leftQuery S k g
abbrev rightQuery (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.rightQuery S k g

noncomputable def edge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (vertexCount S k s d) (2^s) where
  source := vertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := vertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

noncomputable def outcomes (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :=
  ActualGame.outcomes S k g

noncomputable def outputInstance (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d) :
    Instance (2^s) where
  vertices := vertexCount S k s d
  constraints := (outcomes S k g).map (edge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : edge S k g ω ∈ (outcomes S k g).map (edge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_outcomes S k g ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstance_constraints_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) :
    (outputInstance S k g).constraints.length = Fintype.card (Outcome S k g) := by
  simp [outputInstance, outcomes]

noncomputable def vertexLabel (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    Vertex S k s d → Alphabet s := fun v =>
  (Encoding.alphabetEquiv s).symm (labeling (vertexEncoding S k s d v))

noncomputable def labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    Fin (vertexCount S k s d) → Fin (2^s) := fun i =>
  Encoding.alphabetEquiv s (labels ((vertexEncoding S k s d).symm i))

@[simp] theorem vertexLabel_labelingOf (S : Source) (k s d : Nat)
    (labels : Vertex S k s d → Alphabet s) :
    vertexLabel S k s d (labelingOf S k s d labels) = labels := by
  funext v
  simp [vertexLabel, labelingOf]

/-- Restore the removed alphabet component of the affine intercept. -/
noncomputable def unfolded (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) : Alphabet s :=
  ActualOrbit.unfold (canonical S k s d) (vertexLabel S k s d labeling) q

theorem unfolded_equivariant (S : Source) (k s d : Nat)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s))
    (q : Query S k s d) (c : Alphabet s) :
    unfolded S k s d labeling (shiftQuery S k s d c q) =
      unfolded S k s d labeling q + c := by
  change vertexLabel S k s d labeling
      (ActualGame.vertex S k s d (ActualGame.shiftQuery S k s d c q)) +
    ActualGame.offset S k s d (ActualGame.shiftQuery S k s d c q) = _
  rw [ActualGame.vertex_shiftQuery, ActualGame.offset_shiftQuery]
  exact (add_assoc _ _ _).symm

theorem edge_satisfied_iff (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (labeling : Fin (vertexCount S k s d) → Fin (2^s)) (ω : Outcome S k g) :
    (edge S k g ω).satisfied labeling = true ↔
      unfolded S k s d labeling (leftQuery S k g ω) =
        unfolded S k s d labeling (rightQuery S k g ω) := by
  rw [Constraint.satisfied, decide_eq_true_eq]
  have h := Encoding.translationTable_satisfied_iff
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))
    (vertexLabel S k s d labeling (vertex S k s d (leftQuery S k g ω)))
    (vertexLabel S k s d labeling (vertex S k s d (rightQuery S k g ω)))
  simp only [vertexLabel, Encoding.alphabetEquiv_apply_symm_apply] at h
  exact h.trans (ActualOrbit.constraint_iff_unfolded (canonical S k s d)
    (vertexLabel S k s d labeling) (vertexLabel S k s d labeling) _ _)

noncomputable def acceptanceProbability (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) : ℚ :=
  𝔼 ω : Outcome S k g, if (edge S k g ω).satisfied labeling then (1 : ℚ) else 0

theorem acceptanceProbability_eq_test (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      𝔼 ω : Outcome S k g,
        if unfolded S k s d labeling (leftQuery S k g ω) =
            unfolded S k s d labeling (rightQuery S k g ω)
        then (1 : ℚ) else 0 := by
  unfold acceptanceProbability
  apply Finset.expect_congr rfl
  intro ω _
  simp only [edge_satisfied_iff]

private theorem countSatisfied_map_inline_TableKeysGame {n q : Nat} {I : Type*}
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
  rw [countSatisfied_map_inline_TableKeysGame]
  exact Finset.sum_map_toList _ _

/-- The test probability is the satisfied fraction of the actual occurrence list. -/
theorem acceptanceProbability_eq_count (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (labeling : Fin (vertexCount S k s d) → Fin (2^s)) :
    acceptanceProbability S k g labeling =
      (countSatisfied labeling (outputInstance S k g).constraints : ℚ) /
        (outputInstance S k g).constraints.length := by
  rw [acceptanceProbability, Fintype.expect_eq_sum_div_card,
    outputInstance_constraints_length, countSatisfied_eq_sum]
  congr 1
  simp

/-- Exhaustive numbering of the same single-orbit vertex type. -/
def explicitVertexCount (S : Source) (k s d : Nat) : Nat :=
  (ActualGame.explicitBodies S k s d).length

def explicitVertexEncoding (S : Source) (k s d : Nat) :
    Vertex S k s d ≃ Fin (explicitVertexCount S k s d) := by
  letI := ActualGame.orbitBodyDecidableEq S k s d
  exact ActualOrbit.explicitVertexEquiv (canonical S k s d)
    (ActualEnumeration.queries S.occurrences k s d) ActualEnumeration.mem_queries

noncomputable def semanticToExplicitVertices (S : Source) (k s d : Nat) :
    Fin (vertexCount S k s d) ≃ Fin (explicitVertexCount S k s d) :=
  (vertexEncoding S k s d).symm.trans (explicitVertexEncoding S k s d)

@[simp] theorem semanticToExplicitVertices_apply (S : Source) (k s d : Nat)
    (v : Vertex S k s d) :
    semanticToExplicitVertices S k s d (vertexEncoding S k s d v) =
      explicitVertexEncoding S k s d v := by
  simp [semanticToExplicitVertices]

theorem explicitVertexCount_eq (S : Source) (k s d : Nat) :
    explicitVertexCount S k s d = vertexCount S k s d := by
  simpa using (Fintype.card_congr (semanticToExplicitVertices S k s d)).symm

def explicitEdge (S : Source) (k : Nat) {s d : Nat} (g : SplitGadget s d)
    (ω : Outcome S k g) : Constraint (explicitVertexCount S k s d) (2^s) where
  source := explicitVertexEncoding S k s d (vertex S k s d (leftQuery S k g ω))
  target := explicitVertexEncoding S k s d (vertex S k s d (rightQuery S k g ω))
  permutation := Encoding.translationTable
    (offset S k s d (leftQuery S k g ω)) (offset S k s d (rightQuery S k g ω))

theorem explicitEdge_eq_rename (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : Outcome S k g) :
    explicitEdge S k g ω = Integration.InstanceEquivalences.renameConstraint
      (semanticToExplicitVertices S k s d) (edge S k g ω) := by
  simp only [explicitEdge, Integration.InstanceEquivalences.renameConstraint, edge,
    semanticToExplicitVertices_apply]

/-- Executable finite output, still allowing loops and parallel occurrences. -/
def outputInstanceWithEnumeration (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) : Instance (2^s) where
  vertices := explicitVertexCount S k s d
  constraints := (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g)
  nonempty := by
    intro h
    let ω : Outcome S k g := Classical.choice inferInstance
    have hm : explicitEdge S k g ω ∈
        (ActualGame.explicitOutcomes S k g en).map (explicitEdge S k g) :=
      List.mem_map.mpr ⟨ω, ActualGame.mem_explicitOutcomes S k g en ω, rfl⟩
    rw [h] at hm
    exact List.not_mem_nil hm

@[simp] theorem outputInstanceWithEnumeration_length (S : Source) (k : Nat)
    {s d : Nat} (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.length =
      Explicit.edgeCount S.occurrences k (s+d) en.indices.length := by
  simp only [outputInstanceWithEnumeration, List.length_map,
    ActualGame.explicitOutcomes, ActualEnumeration.length_indexedOutcomes]

theorem explicitConstraints_perm_renamed (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    (outputInstanceWithEnumeration S k g en).constraints.Perm
      ((outputInstance S k g).constraints.map
        (Integration.InstanceEquivalences.renameConstraint (semanticToExplicitVertices S k s d))) := by
  simpa only [outputInstanceWithEnumeration, outputInstance, List.map_map,
    Function.comp_def, ← explicitEdge_eq_rename, outcomes] using
    (ActualGame.explicitOutcomes_perm_outcomes S k g en).map (explicitEdge S k g)

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

end MaxCutGames.Decoder.TableKeysGame

/-!
Restore actual orbit labels as a total function of the entire reduced key.
The arbitrary value at unrealized orbit bodies is used only to make this
function total; every table queried by the verifier and by the sparse
experiment is proved to be an actual realization.  Folding holds even for
the total extension, because the removed intercept is always restored.
-/

namespace MaxCutGames.Decoder.TableKeysRestoration

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section
attribute [local instance] Classical.propDecidable

section OrbitExtension

variable {Q T : Type} {s d : Nat}

def extendedLabel (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (body : Vector d × T) : Alphabet s :=
  if h : ∃ q, ActualOrbit.body can q = body then label ⟨body, h⟩ else 0

theorem extendedLabel_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    extendedLabel can label (ActualOrbit.body can q) = label (ActualOrbit.vertex can q) := by
  rw [extendedLabel, dite_eq_left ⟨q, rfl⟩]
  rfl

/-- Restore the full affine intercept after labeling the orbit body. -/
def restoredData (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) : Alphabet s :=
  extendedLabel can label (D.1.2, D.2) + D.1.1

theorem restoredData_actual (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (q : Q) :
    restoredData can label (can q) = ActualOrbit.unfold can label q := by
  change extendedLabel can label (ActualOrbit.body can q) + ActualOrbit.offset can q = _
  rw [extendedLabel_actual]
  rfl

theorem restoredData_shift (can : Q → Ambient s d × T)
    (label : ActualOrbit.Vertex can → Alphabet s) (D : Ambient s d × T) (c : Alphabet s) :
    restoredData can label (D.1 + (c, 0), D.2) = restoredData can label D + c := by
  simp only [restoredData, Prod.fst_add, Prod.snd_add, add_zero]
  exact (add_assoc _ _ _).symm

end OrbitExtension

/-- The actual verifier labeling, viewed as a function of exact affine keys. -/
def keyAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.«variables») (Fin S.occurrences) (Ambient s d)) : Alphabet s :=
  restoredData (TableKeysGame.canonical S k s d)
    (TableKeysGame.vertexLabel S k s d labeling) D

theorem keyAnswer_actual (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (q : TableKeysGame.Query S k s d) :
    keyAnswer S k s d labeling (TableKeysGame.canonical S k s d q) =
      TableKeysGame.unfolded S k s d labeling q :=
  restoredData_actual _ _ q

theorem keyAnswer_shift (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (D : TableKeys.Key k (Fin S.«variables») (Fin S.occurrences) (Ambient s d))
    (c : Alphabet s) :
    keyAnswer S k s d labeling (D.1 + (c, 0), D.2) = keyAnswer S k s d labeling D + c :=
  restoredData_shift _ _ D c

def projectedAnswer (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) : Alphabet s :=
  keyAnswer S k s d labeling
    (TableKeys.projectedKey J (ActualGame.names S) (ActualGame.rhs S) O Y)

/-- No extra consistency predicate: projected answers equal full-query answers
for every table and every compatible hidden extension. -/
theorem projectedAnswer_pullback (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (occ : Fin k → Fin S.occurrences)
    (slot : Fin k → PartnerProjection.Slot)
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) :
    projectedAnswer S k s d labeling J
        (RawPrivateTable.supported J (ActualGame.names S) occ slot) Y =
      TableKeysGame.unfolded S k s d labeling
        (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot)) := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_pullback]
  exact keyAnswer_actual S k s d labeling
    (occ, Y.comp (RawPrivateTable.projection J (ActualGame.rhs S) occ slot))

/-- The visible table has the exact same affine folding law, with its genuine
homogeneous coordinate rather than an assumed or reconstructed first bit. -/
theorem projectedAnswer_fold (S : Source) (k s d : Nat)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (O : RawPrivateTable.SupportedV J (ActualGame.names S))
    (Y : RawPartnerTarget.RawPoint J →ₗ[F2] Ambient s d) (c : Alphabet s) :
    projectedAnswer S k s d labeling J O
        (Y + (TableKeys.visibleTau J).smulRight (c, (0 : Vector d))) =
      projectedAnswer S k s d labeling J O Y + c := by
  unfold projectedAnswer
  rw [TableKeys.projectedKey_shift, keyAnswer_shift]

end

end MaxCutGames.Decoder.TableKeysRestoration

/-!
The private row table obtained from an actual single-orbit labeling.  Its
parameters are only the visible question, public row map, visible row value,
and complement table.  Neither a hidden full question nor a selected affine
witness is supplied to its definition.  Affine target intercepts remain
explicit when the matrix is expressed in private kernel coordinates.
-/

namespace MaxCutGames.Decoder.TableKeysPrivateRow

open MaxCutGames.Integration.BinaryLinear
open MaxCutGames.Reduction
open MaxCutGames.Soundness
open ActualSource

noncomputable section

variable {R : Type} [AddCommGroup R] [Module F2 R]
variable {k s d : Nat}

theorem assemble_prod_shift (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (M₀ : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) (h : A.ker) :
    (AdviceFibers.assemble A M₀ (N + (TableKeys.visibleTau J).smulRight h)).prod T =
      (AdviceFibers.assemble A M₀ N).prod T +
        (TableKeys.visibleTau J).smulRight ((h : Alphabet s), (0 : Vector d)) := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change M₀ x + ((N x : Alphabet s) + TableKeys.visibleTau J x • (h : Alphabet s)) =
      (M₀ x + (N x : Alphabet s)) + TableKeys.visibleTau J x • (h : Alphabet s)
    exact (add_assoc _ _ _).symm
  · change T x = T x + TableKeys.visibleTau J x • (0 : Vector d)
    simp

/-- The right player's actual private table, formed from visible row advice. -/
def rowAnswer (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k))
    (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) : Alphabet s :=
  TableKeysRestoration.projectedAnswer S k s d labeling J Q
    ((AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N).prod T)

/-- Folding on the hidden kernel is a consequence of the exact key action. -/
theorem rowAnswer_fold (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker) (h : A.ker) :
    rowAnswer S labeling J Q A rows T (N + (TableKeys.visibleTau J).smulRight h) =
      rowAnswer S labeling J Q A rows T N + (h : Alphabet s) := by
  unfold rowAnswer
  rw [assemble_prod_shift, TableKeysRestoration.projectedAnswer_fold]

/-- At the actual hidden matrix this row table is exactly the projected table
used by the verifier, with the same complement and the same complete key. -/
theorem rowAnswer_actual (S : Source)
    (labeling : Fin (TableKeysGame.vertexCount S k s d) → Fin (2^s))
    (J : Finset (Fin k)) (Q : RawPrivateTable.SupportedV J (ActualGame.names S))
    (A : Alphabet s →ₗ[F2] R)
    (M : RawPartnerTarget.RawPoint J →ₗ[F2] Alphabet s)
    (T : RawPartnerTarget.RawPoint J →ₗ[F2] Vector d) :
    rowAnswer S labeling J Q A (AdviceFibers.observe A M) T
        (AdviceFibers.hiddenCoordinate A M) =
      TableKeysRestoration.projectedAnswer S k s d labeling J Q (M.prod T) := by
  have h := (AdviceFibers.observationEquiv A).left_inv M
  change AdviceFibers.assemble A (AdviceFibers.observedBase A (AdviceFibers.observe A M))
      (AdviceFibers.hiddenCoordinate A M) = M at h
  unfold rowAnswer
  rw [h]

/-- This intercept is determined once the visible base and affine witness are
fixed; it is not silently erased when decoding from a row fiber. -/
def targetIntercept (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) : Alphabet s :=
  AdviceFibers.observedBase A rows z + u

theorem affine_target_on_row (J : Finset (Fin k)) (A : Alphabet s →ₗ[F2] R)
    (rows : AdviceFibers.ObservedRow (E := RawPartnerTarget.RawPoint J) A)
    (N : RawPartnerTarget.RawPoint J →ₗ[F2] A.ker)
    (z : RawPartnerTarget.RawPoint J) (u : Alphabet s) :
    AdviceFibers.assemble A (AdviceFibers.observedBase A rows) N z + u =
      (N z : Alphabet s) + targetIntercept J A rows z u :=
  AdviceFibers.assemble_affine_target A (AdviceFibers.observedBase A rows) N z u

end

end MaxCutGames.Decoder.TableKeysPrivateRow

end OAI
