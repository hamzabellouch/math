import OAI.Computability.PerfectCompleteness.Decoding.Projection
import OAI.Computability.PerfectCompleteness.Foundations.KeyFiniteness
import OAI.Computability.PerfectCompleteness.Foundations.LinearEvaluationLemmas
import OAI.Computability.PerfectCompleteness.Foundations.QuotientTableAgreementLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionSoundness
import OAI.Computability.PerfectCompleteness.Reduction.SourceCompleteness
import OAI.Computability.PerfectCompleteness.Reduction.TargetGameLemmas

namespace OAI


namespace PerfectCompleteness.CanonicalGame

open SourceClause MixedSupport CanonicalKeys BlockQuotient SourceCompleteness
open UniqueGamesTheorem.Foundations.Games CompletionSoundness

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)]

structure BlockFamily (clauses : Fin m → NormalizedClause v) (n : Nat)
    (E I : Type*) (V : I → Type*) (B : Type*)
    [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)] where
  presentation : E → Presentation clauses n (JointOutput V B)
  selected : E → I
  direction : ∀ e, V (selected e)
  nonzero : ∀ e, direction e ≠ 0

variable {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)

abbrev RightOutput (e : E) :=
  DirectionQuotient.Space (F.direction e) × (OtherBlocks V (F.selected e) × B)

def rightPresentation (e : E) : Presentation clauses n (RightOutput F e) :=
  (F.presentation e).postcompose (projectBlock (F.selected e) (F.direction e))

def leftKey (e : E) : Key n := presentationKey .left (F.presentation e)

def rightKey (e : E) : Key n := presentationKey .right (rightPresentation F e)

abbrev LeftVertex := ↥(Set.range (leftKey F))
abbrev RightVertex := ↥(Set.range (rightKey F))

def leftAt (e : E) : LeftVertex F := ⟨leftKey F e, ⟨e, rfl⟩⟩
def rightAt (e : E) : RightVertex F := ⟨rightKey F e, ⟨e, rfl⟩⟩

abbrev LeftLabel (q : LeftVertex F) := KeyLabel q.val
abbrev RightLabel (q : RightVertex F) := KeyLabel q.val

instance leftVertex_finite [Finite E] : Finite (LeftVertex F) := by
  apply Finite.of_surjective (leftAt F)
  rintro ⟨k, e, rfl⟩
  exact ⟨e, rfl⟩

instance rightVertex_finite [Finite E] : Finite (RightVertex F) := by
  apply Finite.of_surjective (rightAt F)
  rintro ⟨k, e, rfl⟩
  exact ⟨e, rfl⟩

instance leftLabel_nonempty (q : LeftVertex F) : Nonempty (LeftLabel F q) := by
  rcases q with ⟨k, e, rfl⟩
  exact keyLabel_nonempty .left _ (F.presentation e).joint

instance rightLabel_nonempty (q : RightVertex F) : Nonempty (RightLabel F q) := by
  rcases q with ⟨k, e, rfl⟩
  exact keyLabel_nonempty .right _ (rightPresentation F e).joint

def edge (e : E) (P : LeftLabel F (leftAt F e)) : RightLabel F (rightAt F e) :=
  CanonicalEdges.coarsen
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (projectBlock (F.selected e) (F.direction e)) P

theorem edge_at_most_two [Finite I] [∀ i, Finite (V i)] [Finite B]
    (e : E) (Q : RightLabel F (rightAt F e)) :
    Nat.card {P : LeftLabel F (leftAt F e) // edge F e P = Q} ≤ 2 :=
  coarsenBlock_at_most_two
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (F.selected e) (F.direction e) (F.nonzero e) Q

def game [Fintype E] (μ : FiniteDistribution E) :
    LegalProjectionGame E (LeftVertex F) (RightVertex F) (LeftLabel F) (RightLabel F) where
  occurrences := μ
  left := leftAt F
  right := rightAt F
  projection := edge F

def leftAmbientVertex (q : LeftVertex F) :
    SourceCompleteness.Vertex .left clauses n (JointOutput V B) :=
  ⟨q.val, by
    obtain ⟨e, he⟩ := q.property
    exact ⟨F.presentation e, he⟩⟩

def rightAmbientVertex (q : RightVertex F) :
    SourceCompleteness.Vertex .right clauses n (RightOutput F q.property.choose) :=
  ⟨q.val, ⟨rightPresentation F q.property.choose, q.property.choose_spec⟩⟩

def leftStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (q : LeftVertex F) : LeftLabel F q :=
  SourceCompleteness.strategy assignment hsat (leftAmbientVertex F q)

def rightStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (q : RightVertex F) : RightLabel F q :=
  SourceCompleteness.strategy assignment hsat (rightAmbientVertex F q)

omit [DecidableEq I] in
theorem leftStrategy_at (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    leftStrategy F assignment hsat (leftAt F e) =
      SourceCompleteness.evaluatedLabel assignment hsat (F.presentation e) := by
  apply Subtype.ext
  exact SourceCompleteness.strategy_value_eq assignment hsat
    (leftAmbientVertex F (leftAt F e)) (F.presentation e) rfl

theorem rightStrategy_at (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    rightStrategy F assignment hsat (rightAt F e) =
      SourceCompleteness.evaluatedLabel assignment hsat (rightPresentation F e) := by
  apply Subtype.ext
  exact SourceCompleteness.strategy_value_eq assignment hsat
    (rightAmbientVertex F (rightAt F e)) (rightPresentation F e) rfl

def satisfyingStrategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    LegalStrategy (LeftLabel F) (RightLabel F) :=
  ⟨leftStrategy F assignment hsat, rightStrategy F assignment hsat⟩

theorem edge_strategy (assignment : Fin v → Bool)
    (hsat : ∀ c, (clauses c).clause.eval assignment = true) (e : E) :
    edge F e (leftStrategy F assignment hsat (leftAt F e)) =
      rightStrategy F assignment hsat (rightAt F e) := by
  apply Subtype.ext
  have hc := CanonicalEdges.coarsen_evaluateLabel
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
    (projectBlock (F.selected e) (F.direction e))
    (SourceKeys.realizingAssignment clauses assignment hsat (F.presentation e).endpoints)
  calc
    (edge F e (leftStrategy F assignment hsat (leftAt F e))).val =
        (edge F e (SourceCompleteness.evaluatedLabel assignment hsat (F.presentation e))).val :=
      congrArg (fun P : LeftLabel F (leftAt F e) => (edge F e P).val)
        (leftStrategy_at F assignment hsat e)
    _ = (SourceCompleteness.evaluatedLabel assignment hsat (rightPresentation F e)).val :=
      congrArg (fun P : RightLabel F (rightAt F e) => P.val) hc
    _ = (rightStrategy F assignment hsat (rightAt F e)).val :=
      congrArg (fun P : RightLabel F (rightAt F e) => P.val)
        (rightStrategy_at F assignment hsat e).symm

theorem success_satisfyingStrategy [Fintype E] (μ : FiniteDistribution E)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game F μ).success (satisfyingStrategy F assignment hsat) = 1 := by
  have hw : (game F μ).wins (satisfyingStrategy F assignment hsat) = fun _ => true := by
    funext e
    change @decide (edge F e (leftStrategy F assignment hsat (leftAt F e)) =
      rightStrategy F assignment hsat (rightAt F e)) (Classical.propDecidable _) = true
    exact (@decide_eq_true_iff _ (Classical.propDecidable _)).mpr
      (edge_strategy F assignment hsat e)
  change μ.probability ((game F μ).wins (satisfyingStrategy F assignment hsat)) = 1
  rw [hw]
  exact μ.probability_true

end

end PerfectCompleteness.CanonicalGame


namespace PerfectCompleteness.CanonicalGameStrategy

open SourceClause MixedSupport CanonicalKeys BlockQuotient CanonicalGame
open CompletionSoundness
open scoped Classical

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)] [∀ i, Module DirectionQuotient.F2 (V i)]
  {clauses : Fin m → NormalizedClause v} (F : BlockFamily clauses n E I V B)

theorem left_right_disjoint : Disjoint (Set.range (leftKey F)) (Set.range (rightKey F)) := by
  apply Set.disjoint_left.mpr
  rintro k ⟨e, he⟩ ⟨e', he'⟩
  have hs : Side.left = Side.right :=
    congrArg (fun q : Key n => q.side) (he.trans he'.symm)
  cases hs

def support : Set (Key n) := Set.range (leftKey F) ∪ Set.range (rightKey F)

def onSupport (s : LegalStrategy (LeftLabel F) (RightLabel F))
    (k : ↥(support F)) : KeyLabel k.val :=
  if h : k.val ∈ Set.range (leftKey F) then s.1 ⟨k.val, h⟩
  else s.2 ⟨k.val, k.property.resolve_left h⟩

def extend (s : LegalStrategy (LeftLabel F) (RightLabel F)) : KeyStrategy.Strategy n :=
  KeyStrategy.extend (support F) (onSupport F s)

theorem extend_left_val (s : LegalStrategy (LeftLabel F) (RightLabel F))
    (q : LeftVertex F) (k : KeyStrategy.NonemptyKey n) (hk : k.val = q.val) :
    (extend F s k).val = (s.1 q).val := by
  have hL : k.val ∈ Set.range (leftKey F) := by
    rw [hk]
    exact q.property
  have h := KeyStrategy.extend_val (support F) (onSupport F s) k (Or.inl hL)
  have hs : (onSupport F s ⟨k.val, Or.inl hL⟩).val =
      (s.1 ⟨k.val, hL⟩).val := by
    simp only [onSupport, dite_eq_left hL]
  exact h.trans (hs.trans (congrArg (fun q : LeftVertex F => (s.1 q).val) (Subtype.ext hk)))

theorem extend_right_val (s : LegalStrategy (LeftLabel F) (RightLabel F))
    (q : RightVertex F) (k : KeyStrategy.NonemptyKey n) (hk : k.val = q.val) :
    (extend F s k).val = (s.2 q).val := by
  have hR : k.val ∈ Set.range (rightKey F) := by
    rw [hk]
    exact q.property
  have hL : k.val ∉ Set.range (leftKey F) := by
    intro h
    exact (Set.disjoint_left.mp (left_right_disjoint F)) h hR
  have h := KeyStrategy.extend_val (support F) (onSupport F s) k (Or.inr hR)
  have hs : (onSupport F s ⟨k.val, Or.inr hR⟩).val =
      (s.2 ⟨k.val, hR⟩).val := by
    simp only [onSupport, dite_eq_right hL]
  exact h.trans (hs.trans (congrArg (fun q : RightVertex F => (s.2 q).val) (Subtype.ext hk)))

theorem label_extend_left (s : LegalStrategy (LeftLabel F) (RightLabel F)) (e : E) :
    KeyStrategy.label (extend F s) .left
        (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint =
      s.1 (leftAt F e) := by
  apply Subtype.ext
  exact extend_left_val F s (leftAt F e) _ rfl

theorem label_extend_right (s : LegalStrategy (LeftLabel F) (RightLabel F)) (e : E) :
    KeyStrategy.label (extend F s) .right
        (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
        (rightPresentation F e).joint = s.2 (rightAt F e) := by
  apply Subtype.ext
  exact extend_right_val F s (rightAt F e) _ rfl

theorem response_extend_left (s : LegalStrategy (LeftLabel F) (RightLabel F)) (e : E) :
    KeyStrategy.response (extend F s) .left
        (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint =
      restore (SourceKeys.slot clauses ∘ (F.presentation e).endpoints)
        (F.presentation e).joint (s.1 (leftAt F e)) :=
  congrArg (restore (SourceKeys.slot clauses ∘ (F.presentation e).endpoints)
    (F.presentation e).joint) (label_extend_left F s e)

theorem response_extend_right (s : LegalStrategy (LeftLabel F) (RightLabel F)) (e : E) :
    KeyStrategy.response (extend F s) .right
        (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
        (rightPresentation F e).joint =
      restore (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
        (rightPresentation F e).joint (s.2 (rightAt F e)) :=
  congrArg (restore (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
    (rightPresentation F e).joint) (label_extend_right F s e)

theorem accepts_extend_iff (s : LegalStrategy (LeftLabel F) (RightLabel F)) (e : E) :
    CanonicalEdges.coarsen
        (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint
        (projectBlock (F.selected e) (F.direction e))
        (KeyStrategy.label (extend F s) .left
          (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint) =
      KeyStrategy.label (extend F s) .right
        (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
        (rightPresentation F e).joint ↔
      edge F e (s.1 (leftAt F e)) = s.2 (rightAt F e) := by
  rw [label_extend_left F s e, label_extend_right F s e]
  rfl

end

end PerfectCompleteness.CanonicalGameStrategy


namespace PerfectCompleteness.CompletionRounding

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open WeightRounding CompletionSoundness
open CompletionSoundness.LegalProjectionGame

noncomputable section

abbrev SeededOccurrences {m : Nat} (n : Fin m → Nat) := Σ e : Fin m, Fin (n e)

theorem seeded_weights_total {m : Nat} (w : PositiveWeights m)
    (n : Fin m → Nat) (hn : ∀ e, 0 < n e) :
    (∑ s : SeededOccurrences n, w.weight s.1 / (n s.1 : ℚ)) = 1 := by
  rw [Fintype.sum_sigma]
  calc
    _ = ∑ e, w.weight e := by
      apply Finset.sum_congr rfl
      intro e _
      change (∑ seed : Fin (n e), w.weight e / (n e : ℚ)) = w.weight e
      have hne : (n e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hn e))
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_div_cancel₀ (w.weight e) hne
    _ = 1 := w.total

def enumeratedWeights {m : Nat} (w : PositiveWeights m)
    (n : Fin m → Nat) (hn : ∀ e, 0 < n e)
    (enum : SeededOccurrences n ≃ Fin (Fintype.card (SeededOccurrences n))) :
    PositiveWeights (Fintype.card (SeededOccurrences n)) where
  weight i := w.weight (enum.symm i).1 / (n (enum.symm i).1 : ℚ)
  positive i := div_pos (w.positive _) (by exact_mod_cast hn (enum.symm i).1)
  total := (enum.symm.sum_comp
    (fun s : SeededOccurrences n => w.weight s.1 / (n s.1 : ℚ))).trans
      (seeded_weights_total w n hn)

theorem probability_one_forall_of_positive {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (hpositive : ∀ x, 0 < μ.weight x)
    (event : Ω → Bool) (hone : μ.probability event = 1) : ∀ x, event x = true := by
  intro x
  by_contra hx
  have hle (y : Ω) : (if event y then μ.weight y else 0) ≤ μ.weight y := by
    split
    · exact le_rfl
    · exact μ.nonnegative y
  have hlt : μ.probability event < ∑ y, μ.weight y := by
    unfold FiniteDistribution.probability
    apply Finset.sum_lt_sum (fun y _ => hle y)
    refine ⟨x, Finset.mem_univ _, ?_⟩
    simpa only [ite_eq_right hx] using hpositive x
  have hbad : (1 : ℝ) < 1 := by simpa only [hone, μ.normalized] using hlt
  exact (lt_irrefl (1 : ℝ)) hbad

variable {m l r q : Nat} {L : Fin l → Type*} {R : Fin r → Type*}
  [∀ x, Fintype (L x)]
  {G : LegalProjectionGame (Fin m) (Fin l) (Fin r) L R}
  {legalL : ∀ x, L x ↪ Fin (2 * q)} {legalR : ∀ y, R y ↪ Fin q}

abbrev CompletedOccurrence (F : G.CompletionFamily legalL legalR) :=
  SeededOccurrences F.size

def enumeration (F : G.CompletionFamily legalL legalR) :
    CompletedOccurrence F ≃ Fin (Fintype.card (CompletedOccurrence F)) :=
  Fintype.equivFin (CompletedOccurrence F)

def weights (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR) :
    PositiveWeights (Fintype.card (CompletedOccurrence F)) :=
  enumeratedWeights w F.size F.positive (enumeration F)

def entries (F : G.CompletionFamily legalL legalR)
    (i : Fin (Fintype.card (CompletedOccurrence F))) : Edge l r q :=
  let es := (enumeration F).symm i
  { left := G.left es.1
    right := G.right es.1
    projection := ProjectionTable.ofMap (F.map es.1 es.2) (by
      simpa only [← Nat.card_eq_fintype_card] using F.exact_two es.1 es.2) }

theorem entries_satisfied (F : G.CompletionFamily legalL legalR)
    (i : Fin (Fintype.card (CompletedOccurrence F)))
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    (entries F i).satisfied a b = F.game.wins (a, b) ((enumeration F).symm i) := by
  simp only [entries, Edge.satisfied, ProjectionTable.ofMap_apply,
    CompletionFamily.game, completedGame, OccurrenceGame.wins, OccurrenceGame.ofProjection]
  exact decide_eq_decide.mpr Iff.rfl

theorem weight_cast (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (i : Fin (Fintype.card (CompletedOccurrence F))) :
    ((weights w F).weight i : ℝ) =
      (sigmaLaw G.occurrences F.seedLaw).weight ((enumeration F).symm i) := by
  simp only [weights, enumeratedWeights, sigmaLaw, CompletionFamily.seedLaw,
    FiniteDistribution.uniform, Fintype.card_fin, hweights, div_eq_mul_inv,
    Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, one_mul]

theorem weightedSuccess_eq_completed (w : PositiveWeights m)
    (F : G.CompletionFamily legalL legalR)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (a : Fin l → Fin (2 * q)) (b : Fin r → Fin q) :
    (RoundedTarget.weightedSuccess (weights w F) (entries F) a b : ℝ) =
      F.game.success (a, b) := by
  unfold RoundedTarget.weightedSuccess PositiveWeights.weightedAcceptance
  rw [Rat.cast_sum]
  calc
    _ = ∑ i, if F.game.wins (a, b) ((enumeration F).symm i) then
        (sigmaLaw G.occurrences F.seedLaw).weight ((enumeration F).symm i) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← entries_satisfied F i a b]
      by_cases hi : (entries F i).satisfied a b = true
      · simp only [ite_eq_left hi]
        exact weight_cast w F hweights i
      · simp only [ite_eq_right hi, Rat.cast_zero]
    _ = ∑ es : CompletedOccurrence F, if F.game.wins (a, b) es then
        (sigmaLaw G.occurrences F.seedLaw).weight es else 0 := by
      simpa only using (enumeration F).symm.sum_comp
        (fun es : CompletedOccurrence F => if F.game.wins (a, b) es = true then
          (sigmaLaw G.occurrences F.seedLaw).weight es else (0 : ℝ))
    _ = F.game.success (a, b) := rfl

def output (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (δ : ℚ) (hδ : 0 < δ) : Instance q :=
  RoundedTarget.paper (weights w F) (entries F) δ hδ

theorem support_card (F : G.CompletionFamily legalL legalR) :
    Fintype.card (CompletedOccurrence F) = ∑ e, F.size e := by
  simp only [CompletedOccurrence, SeededOccurrences, Fintype.card_sigma, Fintype.card_fin]

theorem output_edge_count (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (δ : ℚ) (hδ : 0 < δ) :
    (output w F δ hδ).edges.length = paperScale (∑ e, F.size e) δ := by
  rw [output, RoundedTarget.paper_edge_length, support_card]

theorem output_edge_count_le (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (δ : ℚ) (hδ : 0 < δ) :
    (output w F δ hδ).edges.length ≤ ⌈(3 : ℚ) / δ⌉₊ * ∑ e, F.size e := by
  simpa only [output, support_card] using
    RoundedTarget.paper_edge_length_le_linear (weights w F) (entries F) δ hδ

variable [∀ y, Fintype (R y)] [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]

theorem output_value_le (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) :
    (output w F δ hδ).value ≤
      G.value + G.occurrences.expectation
        (fun e => 2 / (2 * q - Fintype.card (L (G.left e)) : Nat)) + (δ : ℝ) / 3 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin (2 * q)) := ⟨⟨0, Nat.mul_pos (by decide) hq⟩⟩
  have hround := RoundedTarget.paper_value_le (weights w F) (entries F) δ hδ hq
    F.game.value (fun a b => by
      rw [weightedSuccess_eq_completed w F hweights]
      exact F.game.success_le_value (a, b))
  have hcomplete := F.value_le
  simp only [Fintype.card_fin] at hcomplete
  exact hround.trans (add_le_add hcomplete (le_refl _))

theorem output_value_le_of_residual_bound (w : PositiveWeights m)
    (F : G.CompletionFamily legalL legalR)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (η : ℝ)
    (hη : ∀ e, 2 / (2 * q - Fintype.card (L (G.left e)) : Nat) ≤ η) :
    (output w F δ hδ).value ≤ G.value + η + (δ : ℝ) / 3 := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  let : Nonempty (Fin (2 * q)) := ⟨⟨0, Nat.mul_pos (by decide) hq⟩⟩
  have hround := RoundedTarget.paper_value_le (weights w F) (entries F) δ hδ hq
    F.game.value (fun a b => by
      rw [weightedSuccess_eq_completed w F hweights]
      exact F.game.success_le_value (a, b))
  have hcomplete := F.value_le_of_bound η (by simpa only [Fintype.card_fin] using hη)
  exact hround.trans (add_le_add hcomplete (le_refl _))

theorem output_value_eq_one (w : PositiveWeights m) (F : G.CompletionFamily legalL legalR)
    (hweights : ∀ e, G.occurrences.weight e = (w.weight e : ℝ))
    (δ : ℚ) (hδ : 0 < δ) (hq : 0 < q) (hcomplete : G.value = 1) :
    (output w F δ hδ).value = 1 := by
  obtain ⟨s, hs⟩ := G.exists_optimal_strategy
  have hpositive : ∀ e, 0 < G.occurrences.weight e := by
    intro e
    rw [hweights]
    exact_mod_cast w.positive e
  have hwins := probability_one_forall_of_positive G.occurrences hpositive
    (G.wins s) (hs.trans hcomplete)
  apply RoundedTarget.paper_complete_value_eq_one (weights w F) (entries F) δ hδ hq
  refine ⟨liftStrategy legalL legalR s, ?_⟩
  intro i
  rw [entries_satisfied]
  let es : CompletedOccurrence F := (enumeration F).symm i
  simp only [CompletionFamily.game, completedGame, OccurrenceGame.wins,
    OccurrenceGame.ofProjection, liftStrategy]
  apply (@decide_eq_true_iff _ (Classical.propDecidable _)).mpr
  change F.map es.1 es.2 (legalL (G.left es.1) (s.1 (G.left es.1))) =
    legalR (G.right es.1) (s.2 (G.right es.1))
  rw [F.agrees]
  exact congrArg (legalR (G.right es.1)) (of_decide_eq_true (hwins es.1))


end
end PerfectCompleteness.CompletionRounding


noncomputable section

open scoped Classical

namespace PerfectCompleteness.CompletionProbability

variable {L A B : Type*}

theorem exists_completion_sampler_bounded [Fintype L] [Fintype A] [Fintype B]
    (legal : L ↪ A) (p : L → B)
    (hsmall : ∀ b, Fintype.card {l : L // p l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ n : ℕ, 0 < n ∧ n ≤ max 1 (Fintype.card A - Fintype.card L) ∧
      ∃ sampler : Fin n → A → B,
        (∀ seed l, sampler seed (legal l) = p l) ∧
        (∀ seed b, Fintype.card {a : A // sampler seed a = b} = 2) ∧
        ∀ (a : Illegal legal) (b : B),
          uniformProbability (fun seed => sampler seed a.val = b) =
            ((2 - Fintype.card {l : L // p l = b} : ℕ) : ℝ) /
              (Fintype.card A - Fintype.card L : ℕ) ∧
          uniformProbability (fun seed => sampler seed a.val = b) ≤
            2 / (Fintype.card A - Fintype.card L : ℕ) := by
  obtain ⟨pHat, hext, hexact⟩ :=
    Completion.exists_exact_two_completion legal p hsmall hcard
  by_cases hz : Fintype.card (Illegal legal) = 0
  · refine ⟨1, Nat.zero_lt_one,
      le_max_left 1 (Fintype.card A - Fintype.card L), (fun _ => pHat), ?_, ?_, ?_⟩
    · intro seed l
      exact hext l
    · intro seed b
      exact hexact b
    · intro a b
      have hp : 0 < Fintype.card (Illegal legal) := Fintype.card_pos_iff.mpr ⟨a⟩
      exact False.elim (Nat.ne_of_gt hp hz)
  · let : NeZero (Fintype.card (Illegal legal)) := ⟨hz⟩
    let enum := Fintype.equivFin (Illegal legal)
    refine ⟨Fintype.card (Illegal legal), Nat.pos_of_ne_zero hz,
      (card_illegal legal).le.trans
        (le_max_right 1 (Fintype.card A - Fintype.card L)),
      sample legal pHat enum, ?_, ?_, ?_⟩
    · intro seed l
      simpa only [sample_legal] using hext l
    · intro seed b
      exact sample_exact_two legal pHat enum hexact seed b
    · intro a b
      exact ⟨sample_probability_residual legal p pHat enum hext hexact a b,
        sample_probability_le legal pHat enum hexact a b⟩

end PerfectCompleteness.CompletionProbability

namespace PerfectCompleteness.CompletionSoundness.LegalProjectionGame

open CompletionProbability

variable {E Q₁ Q₂ : Type*} {L : Q₁ → Type*} {R : Q₂ → Type*}
  [Fintype E] [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)]
  {A B : Type*} [Fintype A] [Fintype B]
  (G : LegalProjectionGame E Q₁ Q₂ L R)

omit [Fintype Q₁] [Fintype Q₂] in
theorem exists_completionFamily_bounded
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    ∃ F : G.CompletionFamily legalL legalR,
      ∀ e, F.size e ≤ max 1 (Fintype.card A - Fintype.card (L (G.left e))) := by
  have hexists (e : E) := exists_completion_sampler_bounded (legalL (G.left e))
    (fun l => legalR (G.right e) (G.projection e l))
    (embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e)) hcard
  choose n hn hsize sampler hext hexact hprob using hexists
  let F : G.CompletionFamily legalL legalR := {
    size := n
    positive := hn
    map := sampler
    agrees := hext
    exact_two := hexact
    illegal_probability := by
      intro e a b
      simpa only [← Nat.card_eq_fintype_card] using (hprob e a b).2
  }
  exact ⟨F, hsize⟩

end PerfectCompleteness.CompletionSoundness.LegalProjectionGame

end

end OAI
