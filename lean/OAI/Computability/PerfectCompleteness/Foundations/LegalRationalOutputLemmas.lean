import OAI.Computability.PerfectCompleteness.Foundations.LegalOutputLemmas
import OAI.Computability.PerfectCompleteness.Sampling.BoundedListSamplingLemmas

namespace OAI


namespace PerfectCompleteness.LegalRationalOutput

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionSoundness LegalEnumeration

noncomputable section

theorem exists_rational_target {E Q₁ Q₂ : Type*}
    [Fintype E] [Fintype Q₁] [Fintype Q₂]
    {L : Q₁ → Type*} {R : Q₂ → Type*}
    [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
    [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
    (G : LegalProjectionGame E Q₁ Q₂ L R)
    (f : E → ℚ) (hpositive : ∀ e, 0 < f e) (htotal : ∑ e, f e = 1)
    (hweights : ∀ e, G.occurrences.weight e = (f e : ℝ))
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
  let w := LegalUniform.enumeratedWeights f hpositive htotal (Fintype.equivFin E)
  have hw : ∀ i, (numbered G).occurrences.weight i = (w.weight i : ℝ) :=
    LegalUniform.transport_weight_eq_enumerated G.occurrences f hpositive htotal
      hweights (Fintype.equivFin E)
  have hl : ∀ i, Fintype.card (NumberedLabels L i) ≤ cap :=
    fun i => hleft ((Fintype.equivFin Q₁).symm i)
  have hr : ∀ i, Fintype.card (NumberedLabels R i) ≤ cap :=
    fun i => hright ((Fintype.equivFin Q₂).symm i)
  obtain ⟨target, htL, htR, htE, htBits, hc, hs⟩ := CompletionAlphabet.exists_target
    (numbered G) w hw (numbered_at_most_two G hsmall) cap hl hr δ hδ
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
end PerfectCompleteness.LegalRationalOutput


namespace PerfectCompleteness.CanonicalRationalOutput

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open SourceClause MixedSupport CanonicalKeys BlockQuotient CanonicalGame CanonicalOutput

noncomputable section

variable {v m n : Nat} {E I B : Type*} {V : I → Type*}
  [DecidableEq I] [∀ i, AddCommGroup (V i)]
  [∀ i, Module DirectionQuotient.F2 (V i)]
  [Finite I] [∀ i, Finite (V i)] [Finite B]
  {clauses : Fin m → NormalizedClause v}
  (F : BlockFamily clauses n E I V B)
  [Fintype E] [Nonempty E]
  [Fintype (LeftVertex F)] [Fintype (RightVertex F)]
  [∀ x, Fintype (LeftLabel F x)] [∀ y, Fintype (RightLabel F y)]

theorem exists_target (μ : FiniteDistribution E) (weights : E → ℚ)
    (hpositive : ∀ e, 0 < weights e) (htotal : ∑ e, weights e = 1)
    (hweights : ∀ e, μ.weight e = (weights e : ℝ)) (δ : ℚ) (hδ : 0 < δ) :
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
      ((game F μ).value ≤ (δ : ℝ) / 3 → target.value ≤ (δ : ℝ)) := by
  have hl : ∀ x, Fintype.card (LeftLabel F x) ≤ Nat.card (JointOutput V B) := by
    intro x
    simpa only [← Nat.card_eq_fintype_card] using leftLabel_card_le_output F x
  have hr : ∀ y, Fintype.card (RightLabel F y) ≤ Nat.card (JointOutput V B) := by
    intro y
    simpa only [← Nat.card_eq_fintype_card] using rightLabel_card_le_output F y
  obtain ⟨target, htL, htR, htE, htBits, hc, hs⟩ :=
    LegalRationalOutput.exists_rational_target (game F μ) weights hpositive htotal hweights
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
  exact game_value_of_satisfying F μ assignment hsat

end
end PerfectCompleteness.CanonicalRationalOutput

end OAI
