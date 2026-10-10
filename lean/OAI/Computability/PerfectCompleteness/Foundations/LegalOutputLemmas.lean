import OAI.Computability.PerfectCompleteness.Foundations.DependentPredictionDifferenceLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CanonicalGameLemmas
import OAI.Computability.PerfectCompleteness.Reduction.CompletionAlphabetLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BoundedListSamplingLemmas

namespace OAI


namespace PerfectCompleteness.LegalOutput

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness LegalEnumeration

noncomputable section

theorem exists_uniform_target {E Q₁ Q₂ : Type*}
    [Fintype E] [Nonempty E] [Fintype Q₁] [Fintype Q₂]
    {L : Q₁ → Type*} {R : Q₂ → Type*}
    [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
    [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
    (G : LegalProjectionGame E Q₁ Q₂ L R)
    (huniform : G.occurrences = FiniteDistribution.uniform E)
    (hsmall : ∀ e b, Fintype.card {a : L (G.left e) // G.projection e a = b} ≤ 2)
    (cap : Nat) (hleft : ∀ x, Fintype.card (L x) ≤ cap)
    (hright : ∀ y, Fintype.card (R y) ≤ cap)
    (δ : ℚ) (hδ : 0 < δ) :
    let q := CompletionAlphabet.size cap δ
    let M := ⌈(3 : ℚ) / δ⌉₊ * Fintype.card E * (2 * q)
    ∃ target : Instance q,
      target.leftVertices = Fintype.card Q₁ ∧
      target.rightVertices = Fintype.card Q₂ ∧
      target.edges.length ≤ M ∧
      (Encoding.gameBits target).length ≤
        Fintype.card Q₁ + Fintype.card Q₂ + q + M + 4 +
          M * (Fintype.card Q₁ + Fintype.card Q₂ + 2 * q * q + 2 * q + 2) ∧
      (G.value = 1 → PerfectlyComplete target) ∧
      (G.value ≤ (δ : ℝ) / 3 → target.value ≤ (δ : ℝ)) := by
  have hw : ∀ i, (numbered G).occurrences.weight i =
      ((LegalUniform.uniformWeights E).weight i : ℝ) :=
    LegalUniform.equivFin_uniform_weight G.occurrences huniform
  have hl : ∀ i, Fintype.card (NumberedLabels L i) ≤ cap :=
    fun i => hleft ((Fintype.equivFin Q₁).symm i)
  have hr : ∀ i, Fintype.card (NumberedLabels R i) ≤ cap :=
    fun i => hright ((Fintype.equivFin Q₂).symm i)
  obtain ⟨target, htL, htR, htE, htBits, hc, hs⟩ := CompletionAlphabet.exists_target
    (numbered G) (LegalUniform.uniformWeights E) hw (numbered_at_most_two G hsmall)
    cap hl hr δ hδ
  refine ⟨target, htL, htR, htE, htBits, ?_, ?_⟩
  · intro h
    apply hc
    rw [numbered_value]
    exact h
  · intro h
    apply hs
    rw [numbered_value]
    exact h

end
end PerfectCompleteness.LegalOutput


namespace PerfectCompleteness.CanonicalOutput

open scoped Classical
open UniqueGamesTheorem.Foundations.Games
open SourceClause MixedSupport CanonicalKeys BlockQuotient CanonicalGame
open CompletionSoundness

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  [Finite I] [∀ i, Finite (V i)] [Finite B]
  {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)

omit [DecidableEq I] in
theorem leftLabel_card_le_output (q : LeftVertex F) :
    Nat.card (LeftLabel F q) ≤ Nat.card (JointOutput V B) := by
  rcases q with ⟨k, e, rfl⟩
  exact card_keyLabel_le_output .left
    (SourceKeys.slot clauses ∘ (F.presentation e).endpoints) (F.presentation e).joint

theorem rightLabel_card_le_output (q : RightVertex F) :
    Nat.card (RightLabel F q) ≤ Nat.card (JointOutput V B) := by
  rcases q with ⟨k, e, rfl⟩
  let : Finite (RightOutput F e) := Finite.of_surjective
    (projectBlock (B := B) (F.selected e) (F.direction e))
    (projectBlock_surjective (F.selected e) (F.direction e))
  have hlabel := card_keyLabel_le_output .right
    (SourceKeys.slot clauses ∘ (rightPresentation F e).endpoints)
    (rightPresentation F e).joint
  exact hlabel.trans (Nat.card_le_card_of_surjective
    (projectBlock (B := B) (F.selected e) (F.direction e))
    (projectBlock_surjective (F.selected e) (F.direction e)))

variable [Fintype E] [Nonempty E]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

include F in
omit [DecidableEq I] [Fintype E] [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)] in
theorem output_card_positive : 0 < Nat.card (JointOutput V B) := by
  let e : E := Classical.choice inferInstance
  have hpos : 0 < Nat.card (LeftLabel F (leftAt F e)) := Nat.card_pos
  exact hpos.trans_le (leftLabel_card_le_output F (leftAt F e))

omit [Finite I] [∀ i, Finite (V i)] [Finite B] [Nonempty E] in
theorem game_value_of_satisfying (μ : FiniteDistribution E)
    (assignment : Fin v → Bool) (hsat : ∀ c, (clauses c).clause.eval assignment = true) :
    (game F μ).value = 1 := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (game F μ).exists_optimal_strategy
    rw [← hs]
    exact μ.probability_le_one _
  · calc
      1 = (game F μ).success (satisfyingStrategy F assignment hsat) :=
        (success_satisfyingStrategy F μ assignment hsat).symm
      _ ≤ (game F μ).value := (game F μ).success_le_value _

theorem exists_uniform_target (δ : ℚ) (hδ : 0 < δ) :
    let q := CompletionAlphabet.size (Nat.card (JointOutput V B)) δ
    let M := ⌈(3 : ℚ) / δ⌉₊ * Fintype.card E * (2 * q)
    ∃ target : Instance q,
      2 ≤ q ∧
      target.leftVertices = Fintype.card (LeftVertex F) ∧
      target.rightVertices = Fintype.card (RightVertex F) ∧
      target.edges.length ≤ M ∧
      (Encoding.gameBits target).length ≤
        Fintype.card (LeftVertex F) + Fintype.card (RightVertex F) + q + M + 4 +
          M * (Fintype.card (LeftVertex F) + Fintype.card (RightVertex F) +
            2 * q * q + 2 * q + 2) ∧
      ((∃ assignment : Fin v → Bool,
          ∀ c, (clauses c).clause.eval assignment = true) → PerfectlyComplete target) ∧
      ((game F (FiniteDistribution.uniform E)).value ≤ (δ : ℝ) / 3 →
        target.value ≤ (δ : ℝ)) := by
  have hl : ∀ x, Fintype.card (LeftLabel F x) ≤ Nat.card (JointOutput V B) := by
    intro x
    simpa only [← Nat.card_eq_fintype_card] using leftLabel_card_le_output F x
  have hr : ∀ y, Fintype.card (RightLabel F y) ≤ Nat.card (JointOutput V B) := by
    intro y
    simpa only [← Nat.card_eq_fintype_card] using rightLabel_card_le_output F y
  obtain ⟨target, htL, htR, htE, htBits, hc, hs⟩ := LegalOutput.exists_uniform_target
    (game F (FiniteDistribution.uniform E)) rfl
    (by
      intro e b
      change Fintype.card {a : LeftLabel F (leftAt F e) // edge F e a = b} ≤ 2
      rw [Fintype.card_eq_nat_card]
      exact edge_at_most_two F e b)
    (Nat.card (JointOutput V B)) hl hr δ hδ
  have hq : 2 ≤ CompletionAlphabet.size (Nat.card (JointOutput V B)) δ := by
    have hpos := output_card_positive F
    have hmax : Nat.card (JointOutput V B) + 1 ≤
        CompletionAlphabet.size (Nat.card (JointOutput V B)) δ := le_max_left _ _
    omega
  refine ⟨target, hq, htL, htR, htE, htBits, ?_, hs⟩
  rintro ⟨assignment, hsat⟩
  apply hc
  exact game_value_of_satisfying F (FiniteDistribution.uniform E) assignment hsat

end
end PerfectCompleteness.CanonicalOutput

end OAI
