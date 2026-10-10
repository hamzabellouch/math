import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticRateLemmas
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas

namespace OAI

section

/-!
The weighted equation-versus-variable game for a three-variable parity system.
An occurrence is sampled with its given weight and one of its three positions is
sampled uniformly. Alice sees the occurrence and Bob sees only the variable
name. Distinct positions make the predicate a partial projection. The loss of a
factor of three in the gap is proved directly by counting the three positions.
No PCP hardness statement or parallel-repetition bound is a premise here.
-/

namespace UniqueGamesTheorem.Clean.IncidenceGap

open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Soundness.IncidenceExtraction (Incidence Triple xorTriple)
open scoped BigOperators

noncomputable section

variable {O N : Type} [Fintype O] [Fintype N]

local instance accepts_decidable (g : Incidence O N) (o : O) (i : Fin 3)
    (a : Triple) (b : Bool) : Decidable (g.accepts o i a b) :=
  inferInstanceAs (Decidable (xorTriple a = g.rhs o ∧ a i = b))

/-- Independent occurrence and uniform retained-position sampling. -/
def slotLaw (ω : FiniteDistribution O) : FiniteDistribution (O × Fin 3) :=
  ω.product (FiniteDistribution.uniform (Fin 3))

@[simp] theorem slotLaw_weight (ω : FiniteDistribution O) (o : O) (i : Fin 3) :
    (slotLaw ω).weight (o, i) = ω.weight o / 3 := by
  simp [slotLaw, FiniteDistribution.product, FiniteDistribution.uniform, div_eq_mul_inv]

/-- The retained position is internal; the actual right question is its name. -/
def incidenceLaw (g : Incidence O N) (ω : FiniteDistribution O) :
    FiniteDistribution (O × N) :=
  (slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))

def game (g : Incidence O N) (ω : FiniteDistribution O) : Game O N Triple Bool := by
  classical
  exact { questions := incidenceLaw g ω
          accepts := fun o n a b => decide (g.namedAccepts o n a b) }

@[simp] theorem game_accepts_iff (g : Incidence O N) (ω : FiniteDistribution O)
    (o : O) (n : N) (a : Triple) (b : Bool) :
    (game g ω).accepts o n a b = true ↔ g.namedAccepts o n a b := by
  classical
  simp [game]

theorem game_isProjection (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    UniqueGamesTheorem.Repetition.IsProjection (game g ω) := by
  intro o n a b b' hb hb'
  obtain ⟨i, hi, _, hai⟩ := (game_accepts_iff g ω o n a b).mp hb
  obtain ⟨j, hj, _, haj⟩ := (game_accepts_iff g ω o n a b').mp hb'
  have hij := distinct o i j (hi.trans hj.symm)
  subst j
  exact hai.symm.trans haj

/-- The actual weighted satisfaction probability of the parity equations. -/
def paritySuccess (g : Incidence O N) (ω : FiniteDistribution O) (b : N → Bool) : ℝ :=
  ω.probability (fun o => decide (xorTriple (fun i => b (g.name o i)) = g.rhs o))

/-- The attained optimum over all assignments to the names. -/
def parityValue (g : Incidence O N) (ω : FiniteDistribution O) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty (paritySuccess g ω)

theorem paritySuccess_le_parityValue (g : Incidence O N) (ω : FiniteDistribution O)
    (b : N → Bool) : paritySuccess g ω b ≤ parityValue g ω := by
  classical
  exact Finset.le_sup' (paritySuccess g ω) (Finset.mem_univ b)

/-- If Bob violates the equation, at most two of Alice's three coordinates can
agree with him while satisfying the required parity. -/
theorem local_count_bound (a b : Triple) (rhs : Bool) :
    (∑ i : Fin 3, if xorTriple a = rhs ∧ a i = b i then (1 : ℝ) else 0) ≤
      2 + if xorTriple b = rhs then (1 : ℝ) else 0 := by
  rw [Fin.sum_univ_three]
  by_cases ha : xorTriple a = rhs
  · by_cases hb : xorTriple b = rhs
    · simp only [ha, hb, true_and, ite_true]
      split_ifs <;> norm_num
    · by_cases h0 : a 0 = b 0 <;> by_cases h1 : a 1 = b 1 <;>
        by_cases h2 : a 2 = b 2 <;> simp_all [xorTriple] <;> norm_num
  · simp only [ha, false_and, ite_false, zero_add]
    split_ifs <;> norm_num

theorem game_success_eq_slot_average (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) =
      ∑ o, ω.weight o * ((∑ i : Fin 3,
        if g.accepts o i (a o) (b (g.name o i)) then (1 : ℝ) else 0) / 3) := by
  classical
  unfold Game.success
  change ((slotLaw ω).pushforward (fun q => (q.1, g.name q.1 q.2))).probability _ = _
  rw [FiniteDistribution.probability_pushforward]
  simp only [FiniteDistribution.probability, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Game.wins, game, decide_eq_true_eq, slotLaw_weight,
    Incidence.namedAccepts_iff_accepts g distinct]
  by_cases h : g.accepts o i (a o) (b (g.name o i)) <;> simp [h, div_eq_mul_inv]

/-- The assignment itself supplies both local answer functions. Its incidence
success equals its parity satisfaction probability exactly. -/
theorem game_success_honest_eq_paritySuccess
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (b : N → Bool) :
    (game g ω).success ((fun o i => b (g.name o i)), b) = paritySuccess g ω b := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  unfold paritySuccess FiniteDistribution.probability
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : xorTriple (fun i => b (g.name o i)) = g.rhs o <;>
    simp [Incidence.accepts, h]

theorem parityValue_le_game_value
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    parityValue g ω ≤ (game g ω).value := by
  classical
  unfold parityValue
  apply Finset.sup'_le
  intro b _
  rw [← game_success_honest_eq_paritySuccess g ω distinct b]
  exact Game.success_le_value _ _

theorem game_success_le_two_add_parity_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (a : O → Triple) (b : N → Bool) :
    (game g ω).success (a, b) ≤ (2 + paritySuccess g ω b) / 3 := by
  classical
  rw [game_success_eq_slot_average g ω distinct]
  calc
    _ ≤ ∑ o, ω.weight o * ((2 + if xorTriple (fun i => b (g.name o i)) =
        g.rhs o then (1 : ℝ) else 0) / 3) := by
      apply Finset.sum_le_sum
      intro o _
      apply mul_le_mul_of_nonneg_left _ (ω.nonnegative o)
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 3)
      exact local_count_bound (a o) (fun i => b (g.name o i)) (g.rhs o)
    _ = (2 + paritySuccess g ω b) / 3 := by
      simp_rw [← mul_div_assoc, mul_add]
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, ω.normalized]
      simp only [one_mul, paritySuccess, FiniteDistribution.probability,
        decide_eq_true_eq, mul_ite, mul_one, mul_zero]

theorem game_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (game g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  have hv := paritySuccess_le_parityValue g ω s.2
  linarith

theorem game_value_le_one_sub_gap_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (gap : ℝ) (hgap : ∀ b : N → Bool, paritySuccess g ω b ≤ 1 - gap) :
    (game g ω).value ≤ 1 - gap / 3 := by
  apply (Game.value_le_iff _ _).mpr
  intro s
  have h := game_success_le_two_add_parity_third g ω distinct s.1 s.2
  linarith [hgap s.2]

theorem game_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (game g ω).value ≤ (14 : ℝ) / 15 := by
  have h := game_value_le_one_sub_third g ω distinct
  linarith

/-- Two bits encode the four satisfying answers for an occurrence. -/
def satisfyingTriple (rhs : Bool) (a : Bool × Bool) : Triple :=
  fun i => if i = 0 then a.1 else if i = 1 then a.2 else (a.1 ^^ a.2) ^^ rhs

theorem satisfyingTriple_valid (rhs : Bool) (a : Bool × Bool) :
    xorTriple (satisfyingTriple rhs a) = rhs := by
  have h : ∀ x y z : Bool, ((x ^^ y) ^^ ((x ^^ y) ^^ z)) = z := by decide
  exact h a.1 a.2 rhs

theorem satisfyingTriple_of_valid (a : Triple) (rhs : Bool)
    (valid : xorTriple a = rhs) : satisfyingTriple rhs (a 0, a 1) = a := by
  have h : ∀ x y z : Bool, ((x ^^ y) ^^ ((x ^^ y) ^^ z)) = z := by decide
  funext i
  fin_cases i
  · rfl
  · rfl
  · change ((a 0 ^^ a 1) ^^ rhs) = a 2
    rw [← valid]
    exact h (a 0) (a 1) (a 2)

def fourAnswerGame (g : Incidence O N) (ω : FiniteDistribution O) :
    Game O N (Bool × Bool) Bool where
  questions := incidenceLaw g ω
  accepts o n a b := (game g ω).accepts o n (satisfyingTriple (g.rhs o) a) b

theorem four_answer_card : Fintype.card (Bool × Bool) = 4 := by decide

theorem fourAnswerGame_isProjection
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    UniqueGamesTheorem.Repetition.IsProjection (fourAnswerGame g ω) := by
  intro o n a b b' hb hb'
  exact game_isProjection g ω distinct o n (satisfyingTriple (g.rhs o) a) b b' hb hb'

theorem fourAnswerGame_accepts_encode
    (g : Incidence O N) (ω : FiniteDistribution O)
    (o : O) (n : N) (a : Triple) (b : Bool)
    (h : (game g ω).accepts o n a b = true) :
    (fourAnswerGame g ω).accepts o n (a 0, a 1) b = true := by
  have valid : xorTriple a = g.rhs o := by
    obtain ⟨_, _, hv, _⟩ := (game_accepts_iff g ω o n a b).mp h
    exact hv
  change (game g ω).accepts o n (satisfyingTriple (g.rhs o) (a 0, a 1)) b = true
  rw [satisfyingTriple_of_valid a (g.rhs o) valid]
  exact h

/-- Rejecting invalid ambient triples does not change the optimum. Both
directions transport local answer functions; no extra question is revealed. -/
theorem fourAnswerGame_value_eq (g : Incidence O N) (ω : FiniteDistribution O) :
    (fourAnswerGame g ω).value = (game g ω).value := by
  apply le_antisymm
  · apply (Game.value_le_iff _ _).mpr
    intro s
    change (game g ω).success
      ((fun o => satisfyingTriple (g.rhs o) (s.1 o)), s.2) ≤ (game g ω).value
    exact Game.success_le_value _ _
  · apply (Game.value_le_iff _ _).mpr
    intro s
    calc
      (game g ω).success s ≤
          (fourAnswerGame g ω).success ((fun o => (s.1 o 0, s.1 o 1)), s.2) := by
        apply FiniteDistribution.probability_mono
        intro q h
        exact fourAnswerGame_accepts_encode g ω q.1 q.2 (s.1 q.1) (s.2 q.2) h
      _ ≤ (fourAnswerGame g ω).value := Game.success_le_value _ _

theorem fourAnswerGame_value_le_one_sub_third
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    (fourAnswerGame g ω).value ≤ 1 - (1 - parityValue g ω) / 3 := by
  rw [fourAnswerGame_value_eq]
  exact game_value_le_one_sub_third g ω distinct

theorem fourAnswerGame_value_le_fourteen_fifteenths
    (g : Incidence O N) (ω : FiniteDistribution O)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (hopt : parityValue g ω ≤ (4 : ℝ) / 5) :
    (fourAnswerGame g ω).value ≤ (14 : ℝ) / 15 := by
  rw [fourAnswerGame_value_eq]
  exact game_value_le_fourteen_fifteenths g ω distinct hopt

end
end UniqueGamesTheorem.Clean.IncidenceGap

end

end OAI
