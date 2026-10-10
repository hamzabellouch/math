import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import OAI.Computability.PerfectCompleteness.Reduction.OccurrenceGame
import OAI.Computability.PerfectCompleteness.Sampling.CompletionProbability

namespace OAI


namespace PerfectCompleteness.CompletionSoundness

open scoped BigOperators Classical
open UniqueGamesTheorem.Foundations.Games
open CompletionProbability

noncomputable section

section SeedLaws
variable {E : Type*} {Seed : E → Type*}
  [Fintype E] [∀ e, Fintype (Seed e)]

def sigmaLaw (μ : FiniteDistribution E) (ν : ∀ e, FiniteDistribution (Seed e)) :
    FiniteDistribution (Σ e, Seed e) where
  weight es := μ.weight es.1 * (ν es.1).weight es.2
  nonnegative es := mul_nonneg (μ.nonnegative es.1) ((ν es.1).nonnegative es.2)
  normalized := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ e, μ.weight e := by
        apply Finset.sum_congr rfl
        intro e _
        change (∑ seed : Seed e, μ.weight e * (ν e).weight seed) = μ.weight e
        rw [← Finset.mul_sum, (ν e).normalized, mul_one]
      _ = 1 := μ.normalized

theorem sigmaLaw_probability (μ : FiniteDistribution E)
    (ν : ∀ e, FiniteDistribution (Seed e)) (event : (Σ e, Seed e) → Bool) :
    (sigmaLaw μ ν).probability event =
      μ.expectation (fun e => (ν e).probability (fun seed => event ⟨e, seed⟩)) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    sigmaLaw, Fintype.sum_sigma, Finset.mul_sum, mul_ite, mul_zero]

theorem sigmaLaw_probability_first (μ : FiniteDistribution E)
    (ν : ∀ e, FiniteDistribution (Seed e)) (event : E → Bool) :
    (sigmaLaw μ ν).probability (fun es => event es.1) = μ.probability event := by
  rw [sigmaLaw_probability]
  simp only [FiniteDistribution.expectation, FiniteDistribution.probability]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : event e = true <;> simp [he, (ν e).normalized]

end SeedLaws

theorem probability_uniform_eq_uniformProbability {Ω : Type*}
    [Fintype Ω] [Nonempty Ω] (event : Ω → Prop) :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (event x)) =
      uniformProbability event := by
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = (∑ x, if event x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) :=
      FiniteDistribution.expectation_uniform _
    _ = uniformProbability event := by
      simp only [uniformProbability, Fintype.card_subtype, Finset.sum_boole]

theorem probability_decide_const {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (P : Prop) :
    μ.probability (fun _ => decide P) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]

def roundLabel {L A : Type*} (legal : L ↪ A) (default : L) (a : A) : L :=
  if h : ∃ l, legal l = a then Classical.choose h else default

@[simp] theorem roundLabel_legal {L A : Type*} (legal : L ↪ A)
    (default l : L) : roundLabel legal default (legal l) = l := by
  have h : ∃ l', legal l' = legal l := ⟨l, rfl⟩
  simp only [roundLabel, dite_eq_left h]
  exact legal.injective (Classical.choose_spec h)

theorem seed_acceptance_le {L R A B Ω : Type*} [Fintype Ω]
    (ν : FiniteDistribution Ω) (legalL : L ↪ A) (legalR : R ↪ B)
    (defaultL : L) (defaultR : R) (p : L → R) (complete : Ω → A → B)
    (agrees : ∀ seed l, complete seed (legalL l) = legalR (p l))
    (ε : ℝ) (hε : 0 ≤ ε)
    (marginal : ∀ a, a ∉ Set.range legalL → ∀ b,
      ν.probability (fun seed => decide (complete seed a = b)) ≤ ε)
    (a : A) (b : B) :
    ν.probability (fun seed => decide (complete seed a = b)) ≤
      (if p (roundLabel legalL defaultL a) = roundLabel legalR defaultR b then 1 else 0) + ε := by
  by_cases ha : a ∈ Set.range legalL
  · obtain ⟨l, rfl⟩ := ha
    have hdom : ν.probability (fun seed => decide (complete seed (legalL l) = b)) ≤
        ν.probability (fun _ =>
          decide (p (roundLabel legalL defaultL (legalL l)) =
            roundLabel legalR defaultR b)) := by
      apply ν.probability_mono
      intro seed hwin
      have hw : complete seed (legalL l) = b := of_decide_eq_true hwin
      have hb : legalR (p l) = b := (agrees seed l).symm.trans hw
      apply decide_eq_true_iff.mpr
      rw [roundLabel_legal, ← hb, roundLabel_legal]
    rw [probability_decide_const] at hdom
    exact hdom.trans (le_add_of_nonneg_right hε)
  · have h := marginal a ha b
    have hind : (0 : ℝ) ≤
        if p (roundLabel legalL defaultL a) = roundLabel legalR defaultR b then 1 else 0 := by
      split <;> norm_num
    exact h.trans (le_add_of_nonneg_left hind)

structure LegalProjectionGame (E Q₁ Q₂ : Type*)
    (L : Q₁ → Type*) (R : Q₂ → Type*) [Fintype E] where
  occurrences : FiniteDistribution E
  left : E → Q₁
  right : E → Q₂
  projection : ∀ e, L (left e) → R (right e)

abbrev LegalStrategy {Q₁ Q₂ : Type*} (L : Q₁ → Type*) (R : Q₂ → Type*) :=
  (∀ x, L x) × (∀ y, R y)

namespace LegalProjectionGame

variable {E Q₁ Q₂ : Type*} {L : Q₁ → Type*} {R : Q₂ → Type*}
  [Fintype E] (G : LegalProjectionGame E Q₁ Q₂ L R)

def wins (s : LegalStrategy L R) (e : E) : Bool :=
  decide (G.projection e (s.1 (G.left e)) = s.2 (G.right e))

def success (s : LegalStrategy L R) : ℝ := G.occurrences.probability (G.wins s)

section Value
variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]

def value : ℝ := Finset.univ.sup' Finset.univ_nonempty G.success

theorem success_le_value (s : LegalStrategy L R) : G.success s ≤ G.value :=
  Finset.le_sup' G.success (Finset.mem_univ s)

theorem exists_optimal_strategy : ∃ s : LegalStrategy L R, G.success s = G.value := by
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (LegalStrategy L R))) Finset.univ_nonempty G.success
  exact ⟨s, hs.symm⟩

end Value

section Completion
variable [Fintype Q₁] [Fintype Q₂]
  {A B : Type*} [Fintype A] [Fintype B]
  {Seed : E → Type*} [∀ e, Fintype (Seed e)]

def completedGame (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B) :
    OccurrenceGame (Σ e, Seed e) Q₁ Q₂ A B :=
  OccurrenceGame.ofProjection (sigmaLaw G.occurrences ν)
    (fun es => G.left es.1) (fun es => G.right es.1)
    (fun es => complete es.1 es.2)

theorem completed_success (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B) (s : Strategy Q₁ Q₂ A B) :
    (G.completedGame ν complete).success s =
      G.occurrences.expectation (fun e => (ν e).probability
        (fun seed => decide (complete e seed (s.1 (G.left e)) = s.2 (G.right e)))) := by
  change (sigmaLaw G.occurrences ν).probability _ = _
  exact sigmaLaw_probability G.occurrences ν _

def roundStrategy (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (defaultL : ∀ x, L x) (defaultR : ∀ y, R y)
    (s : Strategy Q₁ Q₂ A B) : LegalStrategy L R :=
  (fun x => roundLabel (legalL x) (defaultL x) (s.1 x),
   fun y => roundLabel (legalR y) (defaultR y) (s.2 y))

def liftStrategy (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (s : LegalStrategy L R) : Strategy Q₁ Q₂ A B :=
  (fun x => legalL x (s.1 x), fun y => legalR y (s.2 y))

theorem completed_success_le (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (defaultL : ∀ x, L x) (defaultR : ∀ y, R y)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e)
    (s : Strategy Q₁ Q₂ A B) :
    (G.completedGame ν complete).success s ≤
      G.success (roundStrategy legalL legalR defaultL defaultR s) + G.occurrences.expectation ε := by
  rw [G.completed_success]
  unfold FiniteDistribution.expectation success wins FiniteDistribution.probability
  calc
    _ ≤ ∑ e, G.occurrences.weight e *
        ((if G.projection e (roundLabel (legalL (G.left e)) (defaultL (G.left e))
            (s.1 (G.left e))) = roundLabel (legalR (G.right e)) (defaultR (G.right e))
            (s.2 (G.right e)) then 1 else 0) + ε e) := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left
        (seed_acceptance_le (ν e) (legalL (G.left e)) (legalR (G.right e))
          (defaultL (G.left e)) (defaultR (G.right e)) (G.projection e) (complete e)
          (agrees e) (ε e) (hε e) (marginal e) _ _) (G.occurrences.nonnegative e)
    _ = _ := by
      simp only [roundStrategy, mul_add, Finset.sum_add_distrib, mul_ite,
        mul_one, mul_zero]
      apply congrArg (fun z : ℝ => z + ∑ e, G.occurrences.weight e * ε e)
      apply Finset.sum_congr rfl
      intro e _
      by_cases h : G.projection e
          (roundLabel (legalL (G.left e)) (defaultL (G.left e)) (s.1 (G.left e))) =
          roundLabel (legalR (G.right e)) (defaultR (G.right e)) (s.2 (G.right e))
      · simp [h]
      · simp [h]

theorem completed_success_lift (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (s : LegalStrategy L R) :
    (G.completedGame ν complete).success (liftStrategy legalL legalR s) = G.success s := by
  change (sigmaLaw G.occurrences ν).probability
    (fun es => decide (complete es.1 es.2 (legalL (G.left es.1) (s.1 (G.left es.1))) =
      legalR (G.right es.1) (s.2 (G.right es.1)))) = G.success s
  have hpoint : (fun es : Σ e, Seed e =>
      decide (complete es.1 es.2 (legalL (G.left es.1) (s.1 (G.left es.1))) =
        legalR (G.right es.1) (s.2 (G.right es.1)))) =
      (fun es => G.wins s es.1) := by
    funext es
    simp only [agrees, wins, (legalR (G.right es.1)).injective.eq_iff]
  rw [hpoint, sigmaLaw_probability_first]
  rfl

variable [∀ x, Fintype (L x)] [∀ y, Fintype (R y)]
  [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)] [Nonempty A] [Nonempty B]

theorem completed_value_le (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e) :
    (G.completedGame ν complete).value ≤ G.value + G.occurrences.expectation ε := by
  apply ((G.completedGame ν complete).value_le_iff _).2
  intro s
  let defaultL : ∀ x, L x := fun x => Classical.choice inferInstance
  let defaultR : ∀ y, R y := fun y => Classical.choice inferInstance
  exact (G.completed_success_le ν complete legalL legalR defaultL defaultR agrees ε hε marginal s).trans
    (add_le_add (G.success_le_value _) (le_refl _))

theorem completed_value_le_of_bound (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (ε : E → ℝ) (hε : ∀ e, 0 ≤ ε e)
    (marginal : ∀ e a, a ∉ Set.range (legalL (G.left e)) → ∀ b,
      (ν e).probability (fun seed => decide (complete e seed a = b)) ≤ ε e)
    (δ : ℝ) (hδ : ∀ e, ε e ≤ δ) :
    (G.completedGame ν complete).value ≤ G.value + δ := by
  apply (G.completed_value_le ν complete legalL legalR agrees ε hε marginal).trans
  apply add_le_add (le_refl G.value)
  unfold FiniteDistribution.expectation
  calc
    _ ≤ ∑ e, G.occurrences.weight e * δ := by
      apply Finset.sum_le_sum
      intro e _
      exact mul_le_mul_of_nonneg_left (hδ e) (G.occurrences.nonnegative e)
    _ = δ := by rw [← Finset.sum_mul, G.occurrences.normalized, one_mul]

theorem completed_value_eq_one (ν : ∀ e, FiniteDistribution (Seed e))
    (complete : ∀ e, Seed e → A → B)
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (agrees : ∀ e seed l, complete e seed (legalL (G.left e) l) =
      legalR (G.right e) (G.projection e l))
    (hcomplete : G.value = 1) : (G.completedGame ν complete).value = 1 := by
  apply le_antisymm (G.completedGame ν complete).value_le_one
  obtain ⟨s, hs⟩ := G.exists_optimal_strategy
  calc
    1 = G.success s := (hs.trans hcomplete).symm
    _ = (G.completedGame ν complete).success (liftStrategy legalL legalR s) :=
      (G.completed_success_lift ν complete legalL legalR agrees s).symm
    _ ≤ _ := (G.completedGame ν complete).success_le_value _

end Completion

variable [Fintype Q₁] [Fintype Q₂] [∀ x, Fintype (L x)]
  {A B : Type*} [Fintype A] [Fintype B]

theorem embedded_fiber_le_two {L₀ R₀ B₀ : Type*} [Fintype L₀]
    (j : R₀ ↪ B₀) (p : L₀ → R₀)
    (hsmall : ∀ r, Fintype.card {l : L₀ // p l = r} ≤ 2) (b : B₀) :
    Fintype.card {l : L₀ // j (p l) = b} ≤ 2 := by
  by_cases hb : ∃ r : R₀, j r = b
  · obtain ⟨r, rfl⟩ := hb
    let e : {l : L₀ // j (p l) = j r} ≃ {l : L₀ // p l = r} :=
      Equiv.subtypeEquivRight (fun l =>
        ⟨fun h => j.injective h, fun h => congrArg j h⟩)
    exact (Fintype.card_congr e).le.trans (hsmall r)
  · have hzero : Fintype.card {l : L₀ // j (p l) = b} = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun l => hb ⟨p l.val, l.property⟩⟩
    rw [hzero]
    exact Nat.zero_le 2

structure CompletionFamily (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B) where
  size : E → Nat
  positive : ∀ e, 0 < size e
  map : ∀ e, Fin (size e) → A → B
  agrees : ∀ e seed l, map e seed (legalL (G.left e) l) =
    legalR (G.right e) (G.projection e l)
  exact_two : ∀ e seed b, Fintype.card {a : A // map e seed a = b} = 2
  illegal_probability : ∀ e (a : Illegal (legalL (G.left e))) (b : B),
    uniformProbability (fun seed => map e seed a.val = b) ≤
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat)

omit [Fintype Q₁] [Fintype Q₂] in
theorem completionFamily_nonempty
    (legalL : ∀ x, L x ↪ A) (legalR : ∀ y, R y ↪ B)
    (hsmall : ∀ e b, Fintype.card {l : L (G.left e) // G.projection e l = b} ≤ 2)
    (hcard : Fintype.card A = 2 * Fintype.card B) :
    Nonempty (G.CompletionFamily legalL legalR) := by
  have hexists (e : E) := exists_completion_sampler (legalL (G.left e))
    (fun l => legalR (G.right e) (G.projection e l))
    (embedded_fiber_le_two (legalR (G.right e)) (G.projection e) (hsmall e)) hcard
  choose n hn sampler hext hexact hprob using hexists
  refine ⟨{
    size := n
    positive := hn
    map := sampler
    agrees := hext
    exact_two := hexact
    illegal_probability := ?_ }⟩
  intro e a b
  simpa only [← Nat.card_eq_fintype_card] using (hprob e a b).2

namespace CompletionFamily
variable {G} {legalL : ∀ x, L x ↪ A} {legalR : ∀ y, R y ↪ B}

def seedLaw (F : G.CompletionFamily legalL legalR) (e : E) :
    FiniteDistribution (Fin (F.size e)) := by
  letI : Nonempty (Fin (F.size e)) := ⟨⟨0, F.positive e⟩⟩
  exact FiniteDistribution.uniform (Fin (F.size e))

def game (F : G.CompletionFamily legalL legalR) :
    OccurrenceGame (Σ e, Fin (F.size e)) Q₁ Q₂ A B :=
  G.completedGame F.seedLaw F.map

omit [Fintype Q₁] [Fintype Q₂] [Fintype B] in
theorem marginal (F : G.CompletionFamily legalL legalR) (e : E)
    (a : A) (ha : a ∉ Set.range (legalL (G.left e))) (b : B) :
    (F.seedLaw e).probability (fun seed => decide (F.map e seed a = b)) ≤
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat) := by
  let : Nonempty (Fin (F.size e)) := ⟨⟨0, F.positive e⟩⟩
  change (FiniteDistribution.uniform (Fin (F.size e))).probability _ ≤ _
  rw [probability_uniform_eq_uniformProbability]
  exact F.illegal_probability e ⟨a, ha⟩ b

variable [∀ y, Fintype (R y)] [∀ x, Nonempty (L x)] [∀ y, Nonempty (R y)]
  [Nonempty A] [Nonempty B]

theorem value_le (F : G.CompletionFamily legalL legalR) :
    F.game.value ≤ G.value + G.occurrences.expectation
      (fun e => 2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat)) := by
  apply G.completed_value_le F.seedLaw F.map legalL legalR F.agrees
  · intro e
    exact div_nonneg (by norm_num) (Nat.cast_nonneg _)
  · exact F.marginal

theorem value_le_of_bound (F : G.CompletionFamily legalL legalR)
    (δ : ℝ) (hδ : ∀ e,
      2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat) ≤ δ) :
    F.game.value ≤ G.value + δ := by
  apply G.completed_value_le_of_bound F.seedLaw F.map legalL legalR F.agrees
      (fun e => 2 / (Fintype.card A - Fintype.card (L (G.left e)) : Nat))
      (fun e => div_nonneg (by norm_num) (Nat.cast_nonneg _)) F.marginal δ hδ

theorem value_eq_one (F : G.CompletionFamily legalL legalR) (hcomplete : G.value = 1) :
    F.game.value = 1 :=
  G.completed_value_eq_one F.seedLaw F.map legalL legalR F.agrees hcomplete

end CompletionFamily

end LegalProjectionGame

end
end PerfectCompleteness.CompletionSoundness

end OAI
