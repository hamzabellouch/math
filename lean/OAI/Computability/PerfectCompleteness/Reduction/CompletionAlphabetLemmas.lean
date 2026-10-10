import OAI.Computability.PerfectCompleteness.Algebra.HierarchicalMatrixTable
import OAI.Computability.PerfectCompleteness.Decoding.Projection
import OAI.Computability.PerfectCompleteness.Foundations.HierarchicalArrays
import OAI.Computability.PerfectCompleteness.Machines.EncodingLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionOutputLemmas
import OAI.Computability.PerfectCompleteness.Sampling.CompletionProbability

namespace OAI


namespace PerfectCompleteness.CompletionAlphabet

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open WeightRounding CompletionSoundness CompletionParameters

def size (cap : Nat) (δ : ℚ) : Nat := max (cap + 1) ⌈(6 : ℚ) / δ⌉₊

theorem size_positive (cap : Nat) (δ : ℚ) : 0 < size cap δ := by
  have h : cap + 1 ≤ size cap δ := le_max_left _ _
  omega

theorem cap_le_size (cap : Nat) (δ : ℚ) : cap ≤ size cap δ :=
  (Nat.le_succ cap).trans (le_max_left _ _)

theorem size_budget (cap : Nat) (δ : ℚ) (hδ : 0 < δ) :
    (6 : ℝ) ≤ (δ : ℝ) * size cap δ := by
  have hceil : (6 : ℚ) / δ ≤ (⌈(6 : ℚ) / δ⌉₊ : ℚ) := Nat.le_ceil _
  have hsize : (⌈(6 : ℚ) / δ⌉₊ : ℚ) ≤ (size cap δ : ℚ) := by
    exact_mod_cast (le_max_right (cap + 1) ⌈(6 : ℚ) / δ⌉₊)
  have hprod : (6 : ℚ) ≤ δ * size cap δ := by
    have h := (div_le_iff₀ hδ).1 (hceil.trans hsize)
    simpa only [mul_comm] using h
  exact_mod_cast hprod

theorem exists_target {m l r : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
    [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
    [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
    (G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R)
    (w : PositiveWeights m)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)
    (cap : Nat) (hleft : ∀ x, Fintype.card (L x) ≤ cap)
    (hright : ∀ y, Fintype.card (R y) ≤ cap)
    (δ : ℚ) (hδ : 0 < δ) :
    let q := size cap δ
    let M := ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q)
    ∃ target : Instance q,
      target.leftVertices = l ∧ target.rightVertices = r ∧
      target.edges.length ≤ M ∧
      (Encoding.gameBits target).length ≤
        l + r + q + M + 4 + M * (l + r + 2 * q * q + 2 * q + 2) ∧
      (G.value = 1 → PerfectlyComplete target) ∧
      (G.value ≤ (δ : ℝ) / 3 → target.value ≤ (δ : ℝ)) := by
  let q := size cap δ
  let M := ⌈(3 : ℚ) / δ⌉₊ * m * (2 * q)
  have hleftq : ∀ x, Fintype.card (L x) ≤ q :=
    fun x => (hleft x).trans (cap_le_size cap δ)
  have hrightq : ∀ y, Fintype.card (R y) ≤ q :=
    fun y => (hright y).trans (cap_le_size cap δ)
  obtain ⟨target, hl, hr, he, hc, hs⟩ := CompletionParameters.exists_target
    G w hweights hsmall hleftq hrightq δ hδ (size_positive cap δ) (size_budget cap δ hδ)
  refine ⟨target, hl, hr, he, ?_, hc, hs⟩
  have hb := Encoding.gameBits_length_le_of_edge_count target M he
  simpa only [hl, hr] using hb

end PerfectCompleteness.CompletionAlphabet


namespace PerfectCompleteness
open CompletionProbability

theorem exists_completion_tables {l q : Nat}
    (legal : Fin l ↪ Fin (2 * q)) (p : Fin l → Fin q)
    (hsmall : ∀ b, Fintype.card {a : Fin l // p a = b} ≤ 2) :
    ∃ n : Nat, 0 < n ∧ ∃ tables : Fin n → ProjectionTable q,
      (∀ seed a, (tables seed).images[legal a] = p a) ∧
      ∀ (a : Illegal legal) (b : Fin q),
        uniformProbability (fun seed => (tables seed).images[a.val] = b) ≤
          2 / (2 * q - l : Nat) := by
  classical
  obtain ⟨n, hn, sampler, hext, hexact, hprob⟩ :=
    exists_completion_sampler legal p
      (by intro b; simpa only [← Nat.card_eq_fintype_card] using hsmall b) (by simp)
  let tables : Fin n → ProjectionTable q := fun seed =>
    ProjectionTable.ofMap (sampler seed) (by
      simpa only [← Nat.card_eq_fintype_card] using hexact seed)
  refine ⟨n, hn, tables, ?_, ?_⟩
  · intro seed a
    simpa [tables, ProjectionTable.ofMap] using hext seed a
  · intro a b
    simpa [tables, ProjectionTable.ofMap] using (hprob a b).2

end PerfectCompleteness


namespace PerfectCompleteness.HierarchicalGame

open HierarchicalArrays
open UniqueGamesTheorem.Foundations.Games

structure Family {v m : Nat} (clauses : Fin m → SourceClause.NormalizedClause v)
    (branch : Nat → Nat) (n t : Nat) (rows : Nat → Nat) (E : Type*) where
  endpoints : E → RecursiveSpaces.Slots branch n → Fin t → SourceKeys.Endpoint v m
  arrays : ∀ e, Arrays (sourceSlots clauses (endpoints e)) rows
  selected : E → Nodes branch n
  direction : ∀ e, Block rows (selected e)
  nonzero : ∀ e, direction e ≠ 0

noncomputable section

variable {v m n t : Nat} {clauses : Fin m → SourceClause.NormalizedClause v}
  {branch rows : Nat → Nat} {E : Type*}
  (F : Family clauses branch n t rows E)

def toBlockFamily : CanonicalGame.BlockFamily clauses
    (TreeCanonical.locationCount branch n t) E (Nodes branch n)
    (fun node : Nodes branch n => Block rows node) PUnit.{1} where
  presentation e := HierarchicalArrays.presentation clauses (F.endpoints e) rows (F.arrays e)
  selected := F.selected
  direction := F.direction
  nonzero := F.nonzero

abbrev LeftVertex := CanonicalGame.LeftVertex (toBlockFamily F)
abbrev RightVertex := CanonicalGame.RightVertex (toBlockFamily F)
abbrev LeftLabel (q : LeftVertex F) := CanonicalGame.LeftLabel (toBlockFamily F) q
abbrev RightLabel (q : RightVertex F) := CanonicalGame.RightLabel (toBlockFamily F) q

abbrev leftAt (e : E) : LeftVertex F := CanonicalGame.leftAt (toBlockFamily F) e
abbrev rightAt (e : E) : RightVertex F := CanonicalGame.rightAt (toBlockFamily F) e

theorem leftVertex_finite [Finite E] : Finite (LeftVertex F) := by infer_instance
theorem rightVertex_finite [Finite E] : Finite (RightVertex F) := by infer_instance
theorem leftLabel_finite (q : LeftVertex F) : Finite (LeftLabel F q) := by infer_instance
theorem rightLabel_finite (q : RightVertex F) : Finite (RightLabel F q) := by infer_instance

theorem leftKey_eq (e : E) :
    CanonicalGame.leftKey (toBlockFamily F) e =
      TreeCanonical.key .left (sourceSlots clauses (F.endpoints e)) (fullJoint (F.arrays e)) := rfl

theorem rightKey_eq (e : E) :
    CanonicalGame.rightKey (toBlockFamily F) e =
      TreeCanonical.key .right (sourceSlots clauses (F.endpoints e))
        (BlockQuotient.projectBlock (F.selected e) (F.direction e) ∘ fullJoint (F.arrays e)) := rfl

abbrev edge (e : E) (P : LeftLabel F (leftAt F e)) : RightLabel F (rightAt F e) :=
  CanonicalGame.edge (toBlockFamily F) e P

theorem edge_eq_iff (e : E) (P : LeftLabel F (leftAt F e))
    (Q : RightLabel F (rightAt F e)) :
    edge F e P = Q ↔
      BlockQuotient.projectBlock (F.selected e) (F.direction e)
          (TreeCanonical.restore (sourceSlots clauses (F.endpoints e)) (fullJoint (F.arrays e)) P) =
        TreeCanonical.restore (sourceSlots clauses (F.endpoints e))
          (BlockQuotient.projectBlock (F.selected e) (F.direction e) ∘ fullJoint (F.arrays e)) Q := by
  change CanonicalKeys.Label
    (TreeCanonical.numberedSlots (sourceSlots clauses (F.endpoints e)))
    (BlockQuotient.projectBlock (F.selected e) (F.direction e) ∘
      TreeCanonical.numberedFunction (sourceSlots clauses (F.endpoints e))
        (fullJoint (F.arrays e))) at Q
  exact CanonicalEdges.coarsen_eq_iff
    (TreeCanonical.numberedSlots (sourceSlots clauses (F.endpoints e)))
    (TreeCanonical.numberedFunction (sourceSlots clauses (F.endpoints e)) (fullJoint (F.arrays e)))
    (BlockQuotient.projectBlock (F.selected e) (F.direction e)) P Q

theorem edge_at_most_two (e : E) (Q : RightLabel F (rightAt F e)) :
    Nat.card {P : LeftLabel F (leftAt F e) // edge F e P = Q} ≤ 2 :=
  CanonicalGame.edge_at_most_two (toBlockFamily F) e Q

def game [Fintype E] (μ : FiniteDistribution E) :
    CompletionSoundness.LegalProjectionGame E (LeftVertex F) (RightVertex F)
      (LeftLabel F) (RightLabel F) :=
  CanonicalGame.game (toBlockFamily F) μ

def satisfyingStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    CompletionSoundness.LegalStrategy (LeftLabel F) (RightLabel F) :=
  CanonicalGame.satisfyingStrategy (toBlockFamily F) assignment hsat

theorem edge_satisfyingStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    edge F e ((satisfyingStrategy F assignment hsat).1 (leftAt F e)) =
      (satisfyingStrategy F assignment hsat).2 (rightAt F e) :=
  CanonicalGame.edge_strategy (toBlockFamily F) assignment hsat e

theorem success_satisfyingStrategy [Fintype E] (μ : FiniteDistribution E)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game F μ).success (satisfyingStrategy F assignment hsat) = 1 :=
  CanonicalGame.success_satisfyingStrategy (toBlockFamily F) μ assignment hsat

theorem value_eq_one [Fintype E]
    [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
    [∀ q, Fintype (LeftLabel F q)] [∀ q, Fintype (RightLabel F q)]
    (μ : FiniteDistribution E) (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) : (game F μ).value = 1 := by
  apply le_antisymm
  · obtain ⟨strategy, hs⟩ := (game F μ).exists_optimal_strategy
    rw [← hs]
    exact (game F μ).occurrences.probability_le_one _
  · have h := (game F μ).success_le_value (satisfyingStrategy F assignment hsat)
    simpa only [success_satisfyingStrategy F μ assignment hsat] using h

end

end PerfectCompleteness.HierarchicalGame


namespace PerfectCompleteness.HierarchicalGameTable

noncomputable section

open HierarchicalArrays

variable {v m n t : Nat} {clauses : Fin m → SourceClause.NormalizedClause v}
  {branch rows : Nat → Nat} {E : Type*}
  (F : HierarchicalGame.Family clauses branch n t rows E)
  (s : CompletionSoundness.LegalStrategy (HierarchicalGame.LeftLabel F)
    (HierarchicalGame.RightLabel F))

def strategy : KeyStrategy.Strategy (TreeCanonical.locationCount branch n t) :=
  CanonicalGameStrategy.extend (HierarchicalGame.toBlockFamily F) s

def background (e : E) :
    HierarchicalMatrixTable.Background (rows := rows)
      (sourceSlots clauses (F.endpoints e)) (F.selected e) :=
  HierarchicalMatrixTable.backgroundOf (sourceSlots clauses (F.endpoints e))
    (F.selected e) (F.arrays e)

def matrix (e : E) :
    HierarchicalMatrixTable.Matrix (rows := rows)
      (sourceSlots clauses (F.endpoints e)) (F.selected e) :=
  NodeEmbedding.matrix (F.arrays e) (F.selected e)

theorem accepts_iff (e : E) :
    CanonicalMatrixTable.Accepts
      (TreeCanonical.numberedSlots (sourceSlots clauses (F.endpoints e)))
      (NodeEmbedding.RowSpace (sourceSlots clauses (F.endpoints e)) (F.selected e))
      (HierarchicalMatrixTable.other (sourceSlots clauses (F.endpoints e))
        (F.selected e) (background F e))
      (strategy F s) (F.direction e) (matrix F e) ↔
      HierarchicalGame.edge F e (s.1 (HierarchicalGame.leftAt F e)) =
        s.2 (HierarchicalGame.rightAt F e) := by
  unfold background matrix
  rw [HierarchicalMatrixTable.accepts_iff_canonical,
    HierarchicalMatrixTable.displayed_original]
  exact CanonicalGameStrategy.accepts_extend_iff (HierarchicalGame.toBlockFamily F) s e

end
end PerfectCompleteness.HierarchicalGameTable

end OAI
