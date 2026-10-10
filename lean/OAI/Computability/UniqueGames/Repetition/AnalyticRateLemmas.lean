import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Positivity
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas

namespace OAI

section

/-!
Elementary scalar estimates used to convert a collision-norm bound into the
alphabet-independent repetition rate. These statements concern real numbers;
they do not assume or assert any repetition theorem for games.
-/

namespace UniqueGamesTheorem.Repetition

/-- The squared DS expression loses at least one eighth of the squared gap. -/
theorem dsRatio_le_one_sub_gap_sq_div_eight {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    2 * Real.sqrt (1 - gap) / (2 - gap) ≤ 1 - gap ^ 2 / 8 := by
  let s := Real.sqrt (1 - gap)
  have hs₀ : 0 ≤ s := Real.sqrt_nonneg _
  have hs₂ : s ^ 2 = 1 - gap := Real.sq_sqrt (by linarith)
  have hs₁ : s ≤ 1 := by
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hgap : gap = 1 - s ^ 2 := by linarith
  have hpoly : 0 ≤ s ^ 3 + 3 * s ^ 2 + 5 * s + 7 := by positivity
  have hcert := mul_nonneg (pow_nonneg (show 0 ≤ 1 - s by linarith) 3) hpoly
  change 2 * s / (2 - gap) ≤ 1 - gap ^ 2 / 8
  apply (div_le_iff₀ (show 0 < 2 - gap by linarith)).mpr
  rw [hgap]
  nlinarith only [hcert]

/-- Passing from a squared contraction to the designated scalar rate. -/
theorem le_dsRate_of_sq_le {gap c : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hc : c ^ 2 ≤ 1 - gap ^ 2 / 8) : c ≤ dsRate gap := by
  have hrate₀ := dsRate_nonneg hgap₀ hgap₁
  have hrate₂ : 1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
    dsimp [dsRate]
    nlinarith only [sq_nonneg (gap ^ 2)]
  exact le_of_sq_le_sq (hc.trans hrate₂) hrate₀

/-- A squared DS bound implies the repetition rate directly. -/
theorem le_dsRate_of_sq_le_dsRatio {gap c : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (hc : c ^ 2 ≤ 2 * Real.sqrt (1 - gap) / (2 - gap)) :
    c ≤ dsRate gap :=
  le_dsRate_of_sq_le hgap₀ hgap₁
    (hc.trans (dsRatio_le_one_sub_gap_sq_div_eight hgap₀ hgap₁))

/-- The full DS scalar expression lies below the repetition rate. -/
theorem sqrt_dsRatio_le_dsRate {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1) :
    Real.sqrt (2 * Real.sqrt (1 - gap) / (2 - gap)) ≤ dsRate gap := by
  apply le_dsRate_of_sq_le_dsRatio hgap₀ hgap₁
  have hden₀ : 0 ≤ 2 - gap := by linarith
  exact (Real.sq_sqrt (by positivity)).le

/-- The near-one rounding estimate forces a quadratic loss in the gap. -/
theorem gap_sq_div_eight_le_of_le_two_sqrt {gap η : ℝ}
    (hgap₀ : 0 ≤ gap) (hη₀ : 0 ≤ η)
    (hgap : gap ≤ 2 * Real.sqrt (2 * η)) : gap ^ 2 / 8 ≤ η := by
  have hs₀ := Real.sqrt_nonneg (2 * η)
  have hs₂ := Real.sq_sqrt (show 0 ≤ 2 * η by positivity)
  have hsq : gap ^ 2 ≤ (2 * Real.sqrt (2 * η)) ^ 2 :=
    (sq_le_sq₀ hgap₀ (by positivity)).mpr hgap
  nlinarith only [hs₂, hsq]

end UniqueGamesTheorem.Repetition

end

section

namespace UniqueGamesTheorem.Repetition

theorem sequence_le_power {r : ℝ} (hr : 0 ≤ r) (c : ℕ → ℝ)
    (hzero : c 0 ≤ 1) (hstep : ∀ n, c (n + 1) ≤ r * c n) :
    ∀ n, c n ≤ r ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      calc
        c (n + 1) ≤ r * c n := hstep n
        _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left ih hr
        _ = r ^ (n + 1) := by rw [pow_succ, mul_comm]

theorem squared_rate_le_dsRate_sq {gap : ℝ}
    (_hgap₀ : 0 ≤ gap) (_hgap₁ : gap ≤ 1) :
    1 - gap ^ 2 / 8 ≤ dsRate gap ^ 2 := by
  dsimp [dsRate]
  nlinarith only [sq_nonneg (gap ^ 2)]

theorem rate_of_squared_collision_recurrence {gap : ℝ}
    (hgap₀ : 0 ≤ gap) (hgap₁ : gap ≤ 1)
    (c v : ℕ → ℝ) (hzero : c 0 ≤ 1)
    (hstep : ∀ n, c (n + 1) ≤ (1 - gap ^ 2 / 8) * c n)
    (hvalue : ∀ n, v n ^ 2 ≤ c n) :
    ∀ n, v n ≤ dsRate gap ^ n := by
  have hr : 0 ≤ 1 - gap ^ 2 / 8 := by nlinarith
  have hpow := sequence_le_power hr c hzero hstep
  intro n
  apply le_of_sq_le_sq _ (pow_nonneg (dsRate_nonneg hgap₀ hgap₁) n)
  calc
    v n ^ 2 ≤ c n := hvalue n
    _ ≤ (1 - gap ^ 2 / 8) ^ n := hpow n
    _ ≤ (dsRate gap ^ 2) ^ n :=
      pow_le_pow_left₀ hr (squared_rate_le_dsRate_sq hgap₀ hgap₁) n
    _ = (dsRate gap ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

end UniqueGamesTheorem.Repetition

end

section

/-!
Projection constraints and independent products on the existing classical game
API. A strategy receives only its own full question, even in a product game.
The projection property is an actual uniqueness property of the acceptance
predicate; it is not a premise asserting a repetition bound.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

/-- The left answer determines at most one accepting right answer. Partial
projection predicates are included, as are total projection maps. -/
def IsProjection (G : Game Q₁ Q₂ A₁ A₂) : Prop :=
  ∀ x y a b b', G.accepts x y a b = true →
    G.accepts x y a b' = true → b = b'

theorem IsProjection.of_accepts_iff (G : Game Q₁ Q₂ A₁ A₂)
    (project : Q₁ → Q₂ → A₁ → A₂)
    (h : ∀ x y a b, G.accepts x y a b = true ↔ project x y a = b) :
    IsProjection G := by
  intro x y a b b' hb hb'
  exact ((h x y a b).mp hb).symm.trans ((h x y a b').mp hb')

/-- Parallel repetition preserves projection constraints, including at n = 0.
There is no restriction that a repeated strategy act coordinatewise. -/
theorem IsProjection.repetition {G : Game Q₁ Q₂ A₁ A₂}
    (hG : IsProjection G) (n : Nat) : IsProjection (G.repetition n) := by
  intro x y a b b' hb hb'
  have h₁ := (G.repetition_accepts_iff n x y a b).mp hb
  have h₂ := (G.repetition_accepts_iff n x y a b').mp hb'
  funext i
  exact hG (x i) (y i) (a i) (b i) (b' i) (h₁ i) (h₂ i)

/-- Total projection maps give ordinary finite classical games. Question
weights may be arbitrary nonnegative real weights summing to one. -/
def ofProjection (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) : Game Q₁ Q₂ A₁ A₂ := by
  classical
  exact { questions := questions, accepts := fun x y a b => decide (project x y a = b) }

@[simp] theorem ofProjection_accepts_iff
    (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) (x : Q₁) (y : Q₂) (a : A₁) (b : A₂) :
    (ofProjection questions project).accepts x y a b = true ↔ project x y a = b := by
  classical
  simp [ofProjection]

theorem ofProjection_isProjection (questions : FiniteDistribution (Q₁ × Q₂))
    (project : Q₁ → Q₂ → A₁ → A₂) : IsProjection (ofProjection questions project) :=
  IsProjection.of_accepts_iff _ project (ofProjection_accepts_iff questions project)

/-- Regroup independently sampled question pairs into the two local questions. -/
def productQuestionEquiv :
    ((Q₁ × Q₂) × (R₁ × R₂)) ≃ ((Q₁ × R₁) × (Q₂ × R₂)) where
  toFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  invFun q := ((q.1.1, q.2.1), (q.1.2, q.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Independent conjunction product. Each answer may depend on the full local
pair of questions; locality is inherited from `Game` and `Strategy`. -/
def product (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    Game (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  questions := (G.questions.product H.questions).transport productQuestionEquiv
  accepts x y a b := G.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2

@[simp] theorem product_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (q : (Q₁ × R₁) × (Q₂ × R₂)) :
    (product G H).questions.weight q =
      G.questions.weight (q.1.1, q.2.1) * H.questions.weight (q.1.2, q.2.2) := rfl

@[simp] theorem product_accepts_iff
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (x : Q₁ × R₁) (y : Q₂ × R₂) (a : A₁ × B₁) (b : A₂ × B₂) :
    (product G H).accepts x y a b = true ↔
      G.accepts x.1 y.1 a.1 b.1 = true ∧ H.accepts x.2 y.2 a.2 b.2 = true := by
  simp [product]

theorem IsProjection.product {G : Game Q₁ Q₂ A₁ A₂} {H : Game R₁ R₂ B₁ B₂}
    (hG : IsProjection G) (hH : IsProjection H) : IsProjection (product G H) := by
  intro x y a b b' hb hb'
  have h₁ := (product_accepts_iff G H x y a b).mp hb
  have h₂ := (product_accepts_iff G H x y a b').mp hb'
  exact Prod.ext (hG _ _ _ _ _ h₁.1 h₂.1) (hH _ _ _ _ _ h₁.2 h₂.2)

def productStrategy (s : Strategy Q₁ Q₂ A₁ A₂) (t : Strategy R₁ R₂ B₁ B₂) :
    Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) :=
  (fun q => (s.1 q.1, t.1 q.2), fun q => (s.2 q.1, t.2 q.2))

/-- The independent product of two strategies has exactly multiplicative
success. This gives a lower bound for the maximum, not a decay upper bound. -/
theorem success_productStrategy (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) (t : Strategy R₁ R₂ B₁ B₂) :
    (product G H).success (productStrategy s t) = G.success s * H.success t := by
  unfold Game.success
  change ((G.questions.product H.questions).transport productQuestionEquiv).probability _ = _
  rw [FiniteDistribution.probability_transport]
  change (G.questions.product H.questions).probability
    (fun q => G.wins s q.1 && H.wins t q.2) = _
  simp only [FiniteDistribution.probability, FiniteDistribution.product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  by_cases hq : G.wins s q = true <;>
    by_cases hr : H.wins t r = true <;> simp [hq, hr]

theorem mul_value_le_product_value [Nonempty A₁] [Nonempty A₂]
    [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    G.value * H.value ≤ (product G H).value := by
  obtain ⟨s, hs⟩ := G.exists_optimal_strategy
  obtain ⟨t, ht⟩ := H.exists_optimal_strategy
  rw [← hs, ← ht, ← success_productStrategy]
  exact (product G H).success_le_value (productStrategy s t)

end
end UniqueGamesTheorem.Repetition

end

end OAI
