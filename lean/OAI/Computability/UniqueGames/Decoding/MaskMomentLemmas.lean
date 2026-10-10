import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.SamplingLemmas
import OAI.Computability.UniqueGames.Games.FinishBoundsLemmas

namespace OAI

section

namespace UniqueGamesTheorem.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

/-- `true` is the singleton branch. -/
def bernoulli (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp₀, sub_nonneg.mpr hp₁]
  normalized := by simp

/-- The exact mask, including the empty mask at `k = 0`. -/
def maskCount {k : ℕ} (mask : Fin k → Bool) : ℕ :=
  (Finset.univ.filter fun i => mask i = true).card

theorem product_mask {k : ℕ} (mask : Fin k → Bool) (ρ : ℝ) :
    (∏ i, if mask i then ρ else 1) = ρ ^ maskCount mask := by
  classical
  simp [maskCount, Finset.prod_ite]

/-- The finite product identity underlying the binomial generating function. -/
theorem iid_product_moment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) (k : ℕ) :
    (μ.iid k).expectation (fun x => ∏ i, f (x i)) = μ.expectation f ^ k := by
  classical
  unfold FiniteDistribution.expectation FiniteDistribution.iid
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]

theorem bernoulli_mask_moment (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (k : ℕ) (ρ : ℝ) :
    ((bernoulli p hp₀ hp₁).iid k).expectation (fun mask => ρ ^ maskCount mask) =
      (1 - p * (1 - ρ)) ^ k := by
  calc
    _ = ((bernoulli p hp₀ hp₁).iid k).expectation
        (fun mask => ∏ i, if mask i then ρ else 1) :=
      FiniteDistribution.expectation_congr _ (fun mask => (product_mask mask ρ).symm)
    _ = ((bernoulli p hp₀ hp₁).expectation (fun b => if b then ρ else 1)) ^ k :=
      iid_product_moment (bernoulli p hp₀ hp₁) (fun b : Bool => if b then ρ else 1) k
    _ = _ := by
      congr 1
      simp [FiniteDistribution.expectation, bernoulli]
      ring

variable {E : Type*} [Fintype E] [Nonempty E]

def cleanProbability (β : ℝ) (E : Type*) [Fintype E] : ℝ :=
  β / (Fintype.card E : ℝ)

omit [Nonempty E] in
theorem cleanProbability_nonneg {β : ℝ} (hβ₀ : 0 ≤ β) :
    0 ≤ cleanProbability β E :=
  div_nonneg hβ₀ (Nat.cast_nonneg _)

theorem cleanProbability_le_one {β : ℝ} (hβ₁ : β ≤ 1) :
    cleanProbability β E ≤ 1 := by
  have hc : (1 : ℝ) ≤ Fintype.card E := by
    exact_mod_cast Fintype.card_pos (α := E)
  apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hc)).mpr
  simpa using hβ₁.trans hc

/-- Independent singleton choice and uniform advice slope. -/
def singletonSlopeLaw (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) :
    FiniteDistribution (Bool × E) :=
  (bernoulli β hβ₀ hβ₁).product (FiniteDistribution.uniform E)

/-- `origin` is instantiated by the zero advice slope. Keeping it explicit also
shows that every specified slope has exactly the same chance. -/
def cleanBit (origin : E) (sample : Bool × E) : Bool := by
  classical
  exact sample.1 && decide (sample.2 = origin)

theorem clean_pushforward (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (origin : E) :
    (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin) =
      bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁) := by
  classical
  let μ := (singletonSlopeLaw (E := E) β hβ₀ hβ₁).pushforward (cleanBit origin)
  have ht : μ.weight true = cleanProbability β E := by
    simp [μ, FiniteDistribution.pushforward, singletonSlopeLaw,
      FiniteDistribution.product, Fintype.sum_prod_type,
      bernoulli, cleanBit, FiniteDistribution.uniform, cleanProbability, div_eq_mul_inv]
  apply FiniteDistribution.eq_of_weight_eq
  intro b
  cases b with
  | false =>
      change μ.weight false = 1 - cleanProbability β E
      have hn := μ.normalized
      simp only [Fintype.sum_bool] at hn
      linarith
  | true => exact ht

/-- In particular, the *whole* mask has the independent Bernoulli law. -/
theorem clean_mask_law (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).pushforward
        (fun sample i => cleanBit origin (sample i)) =
      (bernoulli (cleanProbability β E)
        (cleanProbability_nonneg hβ₀) (cleanProbability_le_one hβ₁)).iid k := by
  rw [← FiniteDistribution.iid_pushforward, clean_pushforward]

theorem clean_mask_moment (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) (ρ : ℝ) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => ρ ^ maskCount (fun i => cleanBit origin (sample i))) =
      (1 - cleanProbability β E * (1 - ρ)) ^ k := by
  rw [← FiniteDistribution.expectation_pushforward
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k)
    (fun sample i => cleanBit origin (sample i)) (fun mask => ρ ^ maskCount mask)]
  rw [clean_mask_law, bernoulli_mask_moment]

theorem cleanProbability_ge_of_card_le {β : ℝ} (hβ₀ : 0 ≤ β) {N : ℝ}
    (hcard : (Fintype.card E : ℝ) ≤ N) :
    β / N ≤ cleanProbability β E := by
  exact div_le_div_of_nonneg_left hβ₀
    (Nat.cast_pos.mpr Fintype.card_pos) hcard

theorem cleanProbability_ge_dimension {β : ℝ} (hβ₀ : 0 ≤ β) (dimW rs : ℕ)
    (hcard : Fintype.card E ≤ 2 ^ (dimW + rs)) :
    β * (2 : ℝ) ^ (-((dimW + rs : ℕ) : ℤ)) ≤ cleanProbability β E := by
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv]
  apply cleanProbability_ge_of_card_le hβ₀
  exact_mod_cast hcard

/-- Larger clean probability decreases the moment for a rate in `[0,1]`. -/
theorem mask_rate_antitone {p q ρ : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (hqp : q ≤ p) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) (k : ℕ) :
    (1 - p * (1 - ρ)) ^ k ≤ (1 - q * (1 - ρ)) ^ k := by
  have hl : 0 ≤ 1 - p * (1 - ρ) := by
    nlinarith [mul_nonneg hp₀ hρ₀]
  apply pow_le_pow_left₀ hl
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hqp (sub_nonneg.mpr hρ₁)) 1

/-- Section 5's numerical specialization. A bound on the number of possible
advice slopes gives a uniform bound over every fixed advice map. -/
theorem clean_mask_moment_le (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) {N : ℝ} (hcard : (Fintype.card E : ℝ) ≤ N) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / N) / 3600) ^ k := by
  rw [clean_mask_moment]
  have h := mask_rate_antitone (cleanProbability_nonneg (E := E) hβ₀)
    (cleanProbability_le_one (E := E) hβ₁)
    (cleanProbability_ge_of_card_le hβ₀ hcard)
    (ρ := 1 - (1 : ℝ) / 3600) (by norm_num) (by norm_num) k
  convert h using 1
  congr 1
  ring

/-- `2^(dim W + r_s)` is chosen before the particular advice-map rank. -/
theorem clean_mask_moment_le_dimension (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k dimW rs : ℕ) (hcard : Fintype.card E ≤ 2 ^ (dimW + rs)) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      (1 - (β / (2 : ℝ) ^ (dimW + rs)) / 3600) ^ k := by
  apply clean_mask_moment_le β hβ₀ hβ₁ origin k
  exact_mod_cast hcard

/-- The exponential estimate uses nonnegativity of `1 - x` before raising to
a natural power. It also covers the empty mask. -/
theorem mask_rate_le_exp {x : ℝ} (hx : x ≤ 1) (k : ℕ) :
    (1 - x) ^ k ≤ Real.exp (-(k : ℝ) * x) := by
  calc
    (1 - x) ^ k ≤ Real.exp (-x) ^ k :=
      pow_le_pow_left₀ (sub_nonneg.mpr hx) (Real.one_sub_le_exp_neg x) k
    _ = Real.exp (-(k : ℝ) * x) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

theorem clean_mask_moment_le_exp (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (origin : E) (k : ℕ) {N : ℝ} (hcard : (Fintype.card E : ℝ) ≤ N) :
    ((singletonSlopeLaw (E := E) β hβ₀ hβ₁).iid k).expectation
        (fun sample => (1 - (1 : ℝ) / 3600) ^
          maskCount (fun i => cleanBit origin (sample i))) ≤
      Real.exp (-(k : ℝ) * (β / N) / 3600) := by
  have hN : 1 ≤ N := by
    have hc : (1 : ℝ) ≤ Fintype.card E := by
      exact_mod_cast Fintype.card_pos (α := E)
    exact hc.trans hcard
  have hq : β / N ≤ 1 := (div_le_iff₀ (by linarith)).mpr (by simpa using hβ₁.trans hN)
  have hx : β / N / 3600 ≤ 1 := (div_le_iff₀ (by norm_num)).mpr (by linarith)
  have h := (clean_mask_moment_le β hβ₀ hβ₁ origin k hcard).trans
    (mask_rate_le_exp hx k)
  simpa only [mul_div_assoc] using h

theorem cube_singleton_probability_nonneg (n : ℕ) : 0 ≤ (1 / (n : ℝ)) ^ 2 :=
  sq_nonneg _

theorem cube_singleton_probability_le_one {n : ℕ} (hn : 1 ≤ n) :
    (1 / (n : ℝ)) ^ 2 ≤ 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq₀ : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hq₁ : 1 / (n : ℝ) ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr (by simpa using hn')
  nlinarith [mul_nonneg hq₀ (sub_nonneg.mpr hq₁)]

/-- On cubes, `k = n^3` and `beta = n^(-2)`, so `k * beta = n`.
The advice-space size bound `N` is fixed independently of `n`. -/
theorem cube_mask_rate_le_exp {n : ℕ} (hn : 1 ≤ n) {N : ℝ} (hN : 1 ≤ N) :
    (1 - ((1 / (n : ℝ)) ^ 2 / N) / 3600) ^ (n ^ 3) ≤
      Real.exp (-(n : ℝ) / (3600 * N)) := by
  have hn₀ : (n : ℝ) ≠ 0 := by
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hN₀ : N ≠ 0 := by linarith
  have hq : (1 / (n : ℝ)) ^ 2 / N ≤ 1 :=
    (div_le_iff₀ (by linarith)).mpr
      (by simpa using (cube_singleton_probability_le_one hn).trans hN)
  have hx : (1 / (n : ℝ)) ^ 2 / N / 3600 ≤ 1 :=
    (div_le_iff₀ (by norm_num)).mpr (by linarith)
  have he : -((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600) =
      -(n : ℝ) / (3600 * N) := by
    simp only [Nat.cast_pow]
    field_simp [hn₀, hN₀]
  calc
    _ ≤ Real.exp (-((n ^ 3 : ℕ) : ℝ) * ((1 / (n : ℝ)) ^ 2 / N / 3600)) :=
      mask_rate_le_exp hx (n ^ 3)
    _ = _ := congrArg Real.exp he

/-- A repetition cube can be selected after fixing only the advice-space size
bound and the required error. This is a scalar fact, not a game-value theorem. -/
theorem exists_cube_exponential_lt {N error : ℝ} (hN : 0 < N) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧ Real.exp (-(n : ℝ) / (3600 * N)) < error := by
  let rate := Real.exp (-(1 / (3600 * N)))
  have hrate₀ : 0 ≤ rate := (Real.exp_pos _).le
  have hrate₁ : rate < 1 := Real.exp_lt_one_iff.mpr
    (neg_lt_zero.mpr (one_div_pos.mpr (mul_pos (by norm_num) hN)))
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hrate₀ hrate₁
  obtain ⟨m, hm⟩ := (ht.eventually (gt_mem_nhds herror)).exists
  refine ⟨m + 1, Nat.succ_le_succ (Nat.zero_le m), ?_⟩
  have hp : rate ^ (m + 1) < error :=
    lt_of_le_of_lt (by
      rw [pow_succ]
      exact mul_le_of_le_one_right (pow_nonneg hrate₀ m) hrate₁.le) hm
  have he : Real.exp (-((m + 1 : ℕ) : ℝ) / (3600 * N)) = rate ^ (m + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [he]

theorem exists_cube_mask_rate_lt {N error : ℝ} (hN : 1 ≤ N) (herror : 0 < error) :
    ∃ n : ℕ, 1 ≤ n ∧
      (1 - ((1 / (n : ℝ)) ^ 2 / N) / 3600) ^ (n ^ 3) < error := by
  obtain ⟨n, hn, he⟩ := exists_cube_exponential_lt (by linarith : 0 < N) herror
  exact ⟨n, hn, (cube_mask_rate_le_exp hn hN).trans_lt he⟩

end
end UniqueGamesTheorem.Clean

end

section

/-!
Assembling private decoders from an actual finite advice experiment.

The left response law accepts only the left observation and the right law only
the right observation. Their samples are independent conditional on those
observations. A positive conditional agreement bound on a positive-mass event
therefore gives ordinary deterministic local strategies, by finite averaging.
No hidden matrix, witness, or opposite-player observation is an argument of
either response law.
-/

namespace UniqueGamesTheorem.Decoder.StrategyAssembly

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Ω Q₁ Q₂ A₁ A₂ : Type*}
variable [Fintype Ω] [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def observedGame (law : FiniteDistribution Ω) (leftObservation : Ω → Q₁)
    (rightObservation : Ω → Q₂) (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool) :
    Game Q₁ Q₂ A₁ A₂ where
  questions := law.pushforward (fun ω => (leftObservation ω, rightObservation ω))
  accepts := accepts

def conditionalAgreement (left : Q₁ → FiniteDistribution A₁)
    (right : Q₂ → FiniteDistribution A₂)
    (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool) (q₁ : Q₁) (q₂ : Q₂) : ℝ :=
  ((left q₁).product (right q₂)).probability (fun a => accepts q₁ q₂ a.1 a.2)

omit [Fintype Q₁] [Fintype Q₂] in
theorem conditionalAgreement_nonnegative (left : Q₁ → FiniteDistribution A₁)
    (right : Q₂ → FiniteDistribution A₂)
    (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool) (q₁ : Q₁) (q₂ : Q₂) :
    0 ≤ conditionalAgreement left right accepts q₁ q₂ :=
  FiniteDistribution.probability_nonnegative _ _

omit [Fintype Q₁] [Fintype Q₂] in
theorem conditionalAgreement_le_one (left : Q₁ → FiniteDistribution A₁)
    (right : Q₂ → FiniteDistribution A₂)
    (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool) (q₁ : Q₁) (q₂ : Q₂) :
    conditionalAgreement left right accepts q₁ q₂ ≤ 1 :=
  FiniteDistribution.probability_le_one _ _

theorem stochasticSuccess_eq_actual_expectation
    [DecidableEq Q₁] [DecidableEq Q₂]
    (law : FiniteDistribution Ω) (leftObservation : Ω → Q₁)
    (rightObservation : Ω → Q₂) (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool)
    (left : Q₁ → FiniteDistribution A₁) (right : Q₂ → FiniteDistribution A₂) :
    (observedGame law leftObservation rightObservation accepts).stochasticSuccess left right =
      law.expectation (fun ω => conditionalAgreement left right accepts
        (leftObservation ω) (rightObservation ω)) := by
  unfold Game.stochasticSuccess observedGame
  rw [FiniteDistribution.expectation_pushforward]
  apply FiniteDistribution.expectation_congr
  intro ω
  simp only [conditionalAgreement, FiniteDistribution.probability,
    FiniteDistribution.product, FiniteDistribution.expectation, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  by_cases h : accepts (leftObservation ω) (rightObservation ω) a b = true <;> simp [h]

/-- Averaging conditional independent decoder success over the actual advice
draw multiplies the two positive lower bounds. -/
theorem good_data_mass_lower
    [DecidableEq Q₁] [DecidableEq Q₂]
    (law : FiniteDistribution Ω) (leftObservation : Ω → Q₁)
    (rightObservation : Ω → Q₂) (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool)
    (left : Q₁ → FiniteDistribution A₁) (right : Q₂ → FiniteDistribution A₂)
    (good : Ω → Bool) (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂)
    (hmass : γ₁ ≤ law.probability good)
    (hagreement : ∀ ω, good ω = true → γ₂ ≤
      conditionalAgreement left right accepts (leftObservation ω) (rightObservation ω)) :
    γ₁ * γ₂ ≤
      (observedGame law leftObservation rightObservation accepts).stochasticSuccess left right := by
  rw [stochasticSuccess_eq_actual_expectation]
  have hweighted : law.probability good * γ₂ ≤ law.expectation
      (fun ω => conditionalAgreement left right accepts
        (leftObservation ω) (rightObservation ω)) := by
    unfold FiniteDistribution.probability FiniteDistribution.expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ω _
    by_cases hgood : good ω = true
    · simp only [hgood, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left (hagreement ω hgood) (law.nonnegative ω)
    · simp only [hgood, Bool.false_eq_true, ↓reduceIte, zero_mul]
      exact mul_nonneg (law.nonnegative ω) (conditionalAgreement_nonnegative _ _ _ _ _)
  exact (mul_le_mul_of_nonneg_right hmass hγ₂).trans hweighted

/-- The final strategies receive precisely their local observations. Private
sampling is eliminated by the existing finite response-table construction. -/
theorem exists_local_deterministic_strategies
    [DecidableEq Q₁] [DecidableEq Q₂] [Nonempty A₁] [Nonempty A₂]
    (law : FiniteDistribution Ω) (leftObservation : Ω → Q₁)
    (rightObservation : Ω → Q₂) (accepts : Q₁ → Q₂ → A₁ → A₂ → Bool)
    (left : Q₁ → FiniteDistribution A₁) (right : Q₂ → FiniteDistribution A₂)
    (good : Ω → Bool) (γ₁ γ₂ : ℝ) (hγ₂ : 0 ≤ γ₂)
    (hmass : γ₁ ≤ law.probability good)
    (hagreement : ∀ ω, good ω = true → γ₂ ≤
      conditionalAgreement left right accepts (leftObservation ω) (rightObservation ω)) :
    ∃ leftStrategy : Q₁ → A₁, ∃ rightStrategy : Q₂ → A₂,
      γ₁ * γ₂ ≤ law.probability (fun ω => accepts
        (leftObservation ω) (rightObservation ω)
        (leftStrategy (leftObservation ω)) (rightStrategy (rightObservation ω))) := by
  let G := observedGame law leftObservation rightObservation accepts
  obtain ⟨strategy, hstrategy⟩ := G.exists_deterministic_ge_stochastic left right
  refine ⟨strategy.1, strategy.2, ?_⟩
  have h := (good_data_mass_lower law leftObservation rightObservation accepts
    left right good γ₁ γ₂ hγ₂ hmass hagreement).trans hstrategy
  simpa only [G, Game.success, observedGame, FiniteDistribution.probability_pushforward,
    Game.wins] using h

end
end UniqueGamesTheorem.Decoder.StrategyAssembly

end

end OAI
