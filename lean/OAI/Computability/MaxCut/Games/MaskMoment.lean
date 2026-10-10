import Mathlib
import OAI.Computability.MaxCut.PCP.DistributionMaps

namespace OAI

namespace MaxCutGames.Clean

open Foundations.Games
open scoped BigOperators

noncomputable section

/-- `true` is the singleton branch. -/
def bernoulli (p : ℝ) (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    FiniteDistribution Bool where
  weight b := if b then p else 1 - p
  nonnegative b := by cases b <;> simp [hp₀, sub_nonneg.mpr hp₁]
  normalized := by simp []

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
  convert h using 1 ; congr 1 ; ring

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
end MaxCutGames.Clean

/-!
# Averaging the actual sparse clean experiment

The explicit seed has an independent singleton coin and uniform single-column
advice at each position. Additional independent data supply the intercept and
both full-block columns. Unused columns are sampled and discarded, allowing a
fixed finite product sample space. A local strategy may depend on the fixed
seed; the bound consequently also covers the original, less informed players.

The only mathematical rate input below is the stated bound on the actual
ordinary repeated game. No conditional distribution, local reconstruction,
mask distribution, or averaging assertion is assumed.
-/

namespace MaxCutGames.Clean.Experiment

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw

noncomputable section

variable {R O N : Type} [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev Coefficient (R : Type) := ZeroInformation.Bits R
abbrev Additional (k : ℕ) (R : Type) := Coefficient R × (Fin k → Coefficient R × Coefficient R)
abbrev SparseSeed (k : ℕ) (R : Type) := Fin k → Bool × Coefficient R

def singletonSet {k : ℕ} (seed : SparseSeed k R) : Finset (Fin k) :=
  Finset.univ.filter fun i => (seed i).1 = true

def coefficients {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    RawCoefficients (singletonSet seed) (Coefficient R) :=
  fun slot => match slot with
  | none => extra.1
  | some (.inl (i, j)) => if j = 0 then (extra.2 i.val).1 else (extra.2 i.val).2
  | some (.inr i) => (seed i.val).2

omit [DecidableEq R] in
/-- The actual zero coefficient set is exactly the clean mask counted by the
Bernoulli law. The homogeneous intercept and full columns never enter it. -/
theorem zeroSet_eq_cleanMask {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    zeroSet (singletonSet seed) (coefficients extra seed) =
      Finset.univ.filter (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i) = true) := by
  classical
  ext i
  rw [mem_zeroSet]
  simp [singletonSet, coefficients, cleanBit]
  intro _
  rfl

omit [DecidableEq R] in
theorem zeroSet_card {k : ℕ} (extra : Additional k R) (seed : SparseSeed k R) :
    (zeroSet (singletonSet seed) (coefficients extra seed)).card =
      maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i)) := by
  rw [zeroSet_eq_cleanMask]
  rfl

abbrev LocalStrategies (k : ℕ) (R O N : Type) :=
  OuterStrategy (P := Fin k) (R := R) (O := O) (N := N)

/-- Exact nested finite expectation of the advice-agreement experiment. -/
def success (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N) : ℝ :=
  extraLaw.expectation fun extra =>
    ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation fun seed =>
      UpperBound.fixedAdviceSuccess μ (singletonSet seed) g (coefficients extra seed)
        (strategy extra seed)

private theorem expectation_mono_inline_Experiment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const_inline_Experiment {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (c : ℝ) : μ.expectation (fun _ => c) = c := by
  rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]

/-- Exact clean-coordinate upper bound for arbitrary weighted occurrences.
The sole external theorem input `rate` concerns the genuine classical repeated
game, so its alphabet dependence cannot be concealed in this interface. -/
theorem success_le_of_repetition (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (strategy : Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    success k μ g extraLaw β hβ₀ hβ₁ strategy ≤
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k := by
  unfold success
  calc
    _ ≤ extraLaw.expectation (fun _ =>
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k) := by
      apply expectation_mono_inline_Experiment
      intro extra
      calc
        _ ≤ ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation
            (fun seed => ρ ^ maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i))) := by
          apply expectation_mono_inline_Experiment
          intro seed
          have bound := (UpperBound.fixed_advice_success_le_repeated_value μ
            (singletonSet seed) g (coefficients extra seed) (strategy extra seed) distinct).trans (rate _)
          simpa only [zeroSet_card] using bound
        _ = _ := clean_mask_moment β hβ₀ hβ₁ (ZeroInformation.zero : Coefficient R) k ρ
    _ = _ := expectation_const_inline_Experiment _ _

/-- Uniform finite private/shared strategy seeds are also covered by the same
constant bound; the seed is sampled before the questions. -/
theorem randomized_success_le_of_repetition {Seed : Type*} [Fintype Seed]
    (k : ℕ) (μ : FiniteDistribution (O × Fin 3))
    (g : IncidenceExtraction.Incidence O N)
    (extraLaw : FiniteDistribution (Additional k R))
    (β : ℝ) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (seedLaw : FiniteDistribution Seed)
    (strategy : Seed → Additional k R → SparseSeed k R → LocalStrategies k R O N)
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (ρ : ℝ)
    (rate : ∀ n, ((incidenceGame g (μ.pushforward (incidence g.name))).repetition n).value ≤ ρ ^ n) :
    seedLaw.expectation (fun seed => success k μ g extraLaw β hβ₀ hβ₁ (strategy seed)) ≤
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k := by
  calc
    _ ≤ seedLaw.expectation (fun _ =>
      (1 - (β / (Fintype.card (Coefficient R) : ℝ)) * (1 - ρ)) ^ k) :=
      expectation_mono_inline_Experiment _ (fun seed =>
        success_le_of_repetition k μ g extraLaw β hβ₀ hβ₁ (strategy seed) distinct ρ rate)
    _ = _ := expectation_const_inline_Experiment _ _

end
end MaxCutGames.Clean.Experiment

/-!
# Exact overlap bound for independently sampled uniform fixed-size subsets

All expectations below are explicit rational sums over `Finset.powersetCard`.
The marginal inclusion probability is derived from the exact binomial count
of subsets containing a prescribed singleton. No probabilistic estimate is an
assumption. This is the active-set overlap bound used in Lemma 6.3.
-/

namespace MaxCutGames.Soundness.SubsetIntersection

open scoped BigOperators

/-- The actual finite sample space of all `t`-subsets of `Fin k`. -/
def subsets (k t : ℕ) : Finset (Finset (Fin k)) :=
  (Finset.univ : Finset (Fin k)).powersetCard t

/-- Uniform expectation, implemented by its normalized finite sum. -/
def uniformMean (k t : ℕ) (f : Finset (Fin k) → ℚ) : ℚ :=
  (∑ a ∈ subsets k t, f a) / (subsets k t).card

/-- Independent draws use the product of the two uniform laws. -/
def independentMean (k t : ℕ) (f : Finset (Fin k) → Finset (Fin k) → ℚ) : ℚ :=
  uniformMean k t fun a => uniformMean k t fun b => f a b

def memberIndicator {k : ℕ} (i : Fin k) (a : Finset (Fin k)) : ℚ :=
  if i ∈ a then 1 else 0

def overlapProbability (k t : ℕ) : ℚ :=
  independentMean k t fun a b => if (a ∩ b).Nonempty then 1 else 0

/-- The nested expectations are exactly the normalized sum on the product
sample space, whose cardinality is the square of the single-draw cardinality. -/
theorem independentMean_eq_double_sum (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℚ) :
    independentMean k t f =
      (∑ a ∈ subsets k t, ∑ b ∈ subsets k t, f a b) / ((subsets k t).card : ℚ)^2 := by
  unfold independentMean uniformMean
  simp only [div_eq_mul_inv, ← Finset.sum_mul, pow_two, mul_inv_rev]
  ring

theorem uniformMean_mul_left (k t : ℕ) (c : ℚ) (f : Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => c * f a) = c * uniformMean k t f := by
  unfold uniformMean
  rw [← Finset.mul_sum]
  ring

theorem uniformMean_mul_right (k t : ℕ) (c : ℚ) (f : Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => f a * c) = uniformMean k t f * c := by
  unfold uniformMean
  rw [← Finset.sum_mul]
  ring

/-- Independence is proved from the actual two normalized finite sums. -/
theorem independentMean_product (k t : ℕ) (f g : Finset (Fin k) → ℚ) :
    independentMean k t (fun a b => f a * g b) = uniformMean k t f * uniformMean k t g := by
  simp only [independentMean, uniformMean_mul_left, uniformMean_mul_right]

theorem subsets_card (k t : ℕ) : (subsets k t).card = k.choose t := by
  simp [subsets]

theorem subsets_nonempty {k t : ℕ} (htk : t ≤ k) : (subsets k t).Nonempty := by
  apply Finset.powersetCard_nonempty.mpr
  simpa using htk

theorem subsets_card_ne_zero {k t : ℕ} (htk : t ≤ k) :
    ((subsets k t).card : ℚ) ≠ 0 := by
  exact_mod_cast (Finset.card_ne_zero.mpr (subsets_nonempty htk))

/-- Count the sampled subsets containing one specified coordinate. -/
theorem count_containing {k t : ℕ} (ht : 0 < t) (i : Fin k) :
    ((subsets k t).filter (fun a => i ∈ a)).card =
      (k - 1).choose (t - 1) := by
  simpa [subsets] using
    (Finset.card_filter_powersetCard_subset ({i} : Finset (Fin k)) Finset.univ t
      (by simp) (by simpa using Nat.succ_le_of_lt ht))

theorem choose_predecessor_ratio {k t : ℕ} (hk : 0 < k) (ht : 0 < t) (htk : t ≤ k) :
    ((k - 1).choose (t - 1) : ℚ) / k.choose t = (t : ℚ) / k := by
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hc0 : (k.choose t : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos htk))
  have hrel : k * (k - 1).choose (t - 1) = k.choose t * t := by
    simpa [Nat.sub_add_cancel hk, Nat.sub_add_cancel ht] using
      (Nat.add_one_mul_choose_eq (k - 1) (t - 1))
  apply (div_eq_div_iff hc0 hk0).2
  exact_mod_cast (by simpa [Nat.mul_comm] using hrel)

/-- Exact marginal probability: a coordinate belongs to a uniform `t`-subset
with probability `t / k`. This also includes `t = 0`. -/
theorem inclusion_probability {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) (i : Fin k) :
    uniformMean k t (memberIndicator i) = (t : ℚ) / k := by
  by_cases ht : t = 0
  · subst t
    simp [uniformMean, subsets, memberIndicator]
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    unfold uniformMean memberIndicator
    rw [Finset.sum_boole, count_containing htpos i, subsets_card]
    exact choose_predecessor_ratio hk htpos htk

/-- A coordinate belongs to both independent draws with the product probability. -/
theorem independent_inclusion_probability {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) (i : Fin k) :
    independentMean k t (fun a b => memberIndicator i a * memberIndicator i b) =
      ((t : ℚ) / k)^2 := by
  rw [independentMean_product, inclusion_probability hk htk]
  ring

theorem uniformMean_congr {k t : ℕ} {f g : Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, f a = g a) : uniformMean k t f = uniformMean k t g := by
  unfold uniformMean
  rw [Finset.sum_congr rfl h]

theorem uniformMean_const {k t : ℕ} (htk : t ≤ k) (c : ℚ) :
    uniformMean k t (fun _ => c) = c := by
  have hn := subsets_card_ne_zero htk
  simp only [uniformMean, Finset.sum_const, nsmul_eq_mul]
  field_simp

theorem uniformMean_finset_sum {k t : ℕ} {α : Type*} (s : Finset α)
    (f : α → Finset (Fin k) → ℚ) :
    uniformMean k t (fun a => ∑ i ∈ s, f i a) =
      ∑ i ∈ s, uniformMean k t (f i) := by
  unfold uniformMean
  rw [Finset.sum_comm]
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem uniformMean_mono {k t : ℕ} {f g : Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, f a ≤ g a) : uniformMean k t f ≤ uniformMean k t g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum h)
  exact Nat.cast_nonneg _

theorem independentMean_mono {k t : ℕ} {f g : Finset (Fin k) → Finset (Fin k) → ℚ}
    (h : ∀ a ∈ subsets k t, ∀ b ∈ subsets k t, f a b ≤ g a b) :
    independentMean k t f ≤ independentMean k t g := by
  apply uniformMean_mono
  intro a ha
  apply uniformMean_mono
  exact h a ha

theorem intersection_card_indicator {k : ℕ} (a b : Finset (Fin k)) :
    ((a ∩ b).card : ℚ) = ∑ i ∈ a, memberIndicator i b := by
  simp [memberIndicator]

/-- Conditional expectation against any fixed first set, directly from the
proved marginal inclusion probability of the independent second draw. -/
theorem expected_intersection_fixed {k t : ℕ} (hk : 0 < k) (htk : t ≤ k)
    (a : Finset (Fin k)) :
    uniformMean k t (fun b => ((a ∩ b).card : ℚ)) = a.card * ((t : ℚ) / k) := by
  simp_rw [intersection_card_indicator]
  rw [uniformMean_finset_sum]
  simp [inclusion_probability hk htk, nsmul_eq_mul]

/-- Exact expected intersection size for independent uniform `t`-subsets. -/
theorem expected_intersection {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    independentMean k t (fun a b => ((a ∩ b).card : ℚ)) = (t : ℚ)^2 / k := by
  unfold independentMean
  simp_rw [expected_intersection_fixed hk htk]
  calc
    uniformMean k t (fun a => a.card * ((t : ℚ) / k)) =
        uniformMean k t (fun _ => (t : ℚ) * ((t : ℚ) / k)) := by
      apply uniformMean_congr
      intro a ha
      have hcard : a.card = t := (Finset.mem_powersetCard.mp ha).2
      rw [hcard]
    _ = (t : ℚ) * ((t : ℚ) / k) := uniformMean_const htk _
    _ = (t : ℚ)^2 / k := by ring

/-- The pointwise first-moment bound for a nonempty intersection. -/
theorem nonempty_indicator_le_card {k : ℕ} (a b : Finset (Fin k)) :
    (if (a ∩ b).Nonempty then (1 : ℚ) else 0) ≤ (a ∩ b).card := by
  split_ifs with h
  · exact_mod_cast (Finset.card_pos.mpr h)
  · exact Nat.cast_nonneg _

/-- The uniform-subset overlap bound used in the map-law comparison. -/
theorem overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    overlapProbability k t ≤ (t : ℚ)^2 / k := by
  calc
    overlapProbability k t ≤ independentMean k t (fun a b => ((a ∩ b).card : ℚ)) :=
      independentMean_mono (fun a _ b _ => nonempty_indicator_le_card a b)
    _ = (t : ℚ)^2 / k := expected_intersection hk htk

end MaxCutGames.Soundness.SubsetIntersection

namespace MaxCutGames.Soundness.PartnerSampling

open scoped BigOperators
open SubsetIntersection (subsets)

/-- The literal support of the uniform active-set sample. -/
abbrev ActiveSet (k t : ℕ) := ↥(subsets k t)

/-- Each retained coordinate receives an independent slot in `Fin 3`. -/
abbrev Partner (k t : ℕ) := Σ a : ActiveSet k t, (↥a.val → Fin 3)

theorem activeSet_card {k t : ℕ} (a : ActiveSet k t) : a.val.card = t :=
  (Finset.mem_powersetCard.mp a.property).2

theorem slotTuples_card {k t : ℕ} (a : ActiveSet k t) :
    Fintype.card (↥a.val → Fin 3) = 3 ^ t := by
  simp [activeSet_card a]

/-- Equal-size fibers prove that slot sampling does not change subset weights. -/
theorem partner_card (k t : ℕ) :
    Fintype.card (Partner k t) = (subsets k t).card * 3 ^ t := by
  rw [Fintype.card_sigma]
  simp only [slotTuples_card, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_coe, Nat.cast_id]

theorem partner_nonempty {k t : ℕ} (htk : t ≤ k) : Nonempty (Partner k t) := by
  obtain ⟨a, ha⟩ := SubsetIntersection.subsets_nonempty htk
  exact ⟨⟨⟨a, ha⟩, fun _ => 0⟩⟩

theorem uniformMean_real_cast (k t : ℕ) (f : Finset (Fin k) → ℚ) :
    (SubsetIntersection.uniformMean k t f : ℝ) =
      (𝔼 a ∈ subsets k t, (f a : ℝ)) := by
  rw [Finset.expect_eq_sum_div_card]
  simp [SubsetIntersection.uniformMean]

theorem independentMean_real_cast (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℚ) :
    (SubsetIntersection.independentMean k t f : ℝ) =
      (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t, (f a b : ℝ)) := by
  simp only [SubsetIntersection.independentMean, uniformMean_real_cast]

/-- Real `Finset.expect` form of the already-proved rational subset bound. -/
theorem subset_overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t,
      if (a ∩ b).Nonempty then (1 : ℝ) else 0) ≤ (t : ℝ)^2 / k := by
  have h : (SubsetIntersection.overlapProbability k t : ℝ) ≤ (t : ℝ)^2 / k := by
    have h := SubsetIntersection.overlap_probability_le hk htk
    have hh := (Rat.cast_le (K := ℝ)).mpr h
    simpa using hh
  simpa only [SubsetIntersection.overlapProbability, independentMean_real_cast,
    apply_ite, Rat.cast_one, Rat.cast_zero] using h

theorem activeSet_expect (k t : ℕ) (f : Finset (Fin k) → ℝ) :
    (𝔼 a : ActiveSet k t, f a.val) = (𝔼 a ∈ subsets k t, f a) := by
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ, Fintype.card_coe,
    Finset.sum_coe_sort]

/-- The uniform full-partner law projects to the uniform active-subset law. -/
theorem partner_expect_activeSet (k t : ℕ) (f : ActiveSet k t → ℝ) :
    (𝔼 p : Partner k t, f p.1) = (𝔼 a : ActiveSet k t, f a) := by
  have hsum : (∑ p : Partner k t, f p.1) = (3 : ℝ)^t * ∑ a : ActiveSet k t, f a := by
    rw [Fintype.sum_sigma]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, slotTuples_card,
      Nat.cast_pow, Nat.cast_ofNat]
    rw [Finset.mul_sum]
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card, hsum, partner_card]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Fintype.card_coe]
  have hc : (3 : ℝ)^t ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [mul_comm] using
    (mul_div_mul_left (∑ a : ActiveSet k t, f a) ((subsets k t).card : ℝ) hc)

theorem partner_expect_active (k t : ℕ) (f : Finset (Fin k) → ℝ) :
    (𝔼 p : Partner k t, f p.1.val) = (𝔼 a ∈ subsets k t, f a) := by
  rw [partner_expect_activeSet k t (fun a => f a.val), activeSet_expect]

theorem partner_pair_expect_active (k t : ℕ)
    (f : Finset (Fin k) → Finset (Fin k) → ℝ) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t, f p.1.val q.1.val) =
      (𝔼 a ∈ subsets k t, 𝔼 b ∈ subsets k t, f a b) := by
  calc
    _ = 𝔼 p : Partner k t, 𝔼 b ∈ subsets k t, f p.1.val b := by
      apply Finset.expect_congr rfl
      intro p _
      exact partner_expect_active k t (fun b => f p.1.val b)
    _ = _ := partner_expect_active k t (fun a => 𝔼 b ∈ subsets k t, f a b)

/-- The independently drawn full partners obey the same active-overlap bound. -/
theorem partner_active_overlap_probability_le {k t : ℕ} (hk : 0 < k) (htk : t ≤ k) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      if (p.1.val ∩ q.1.val).Nonempty then (1 : ℝ) else 0) ≤ (t : ℝ)^2 / k := by
  rw [partner_pair_expect_active k t (fun a b => if (a ∩ b).Nonempty then (1 : ℝ) else 0)]
  exact subset_overlap_probability_le hk htk

def active {k t : ℕ} (p : Partner k t) (j : Fin k) : Bool :=
  decide (j ∈ p.1.val)

def decodeSlot (i : Fin 3) : PartnerProjection.Slot :=
  if i.val = 0 then .first else if i.val = 1 then .second else .third

def slots {k t : ℕ} (p : Partner k t) (j : Fin k) : PartnerProjection.Slot :=
  if hj : j ∈ p.1.val then decodeSlot (p.2 ⟨j, hj⟩) else .first

noncomputable def kernel {k t : ℕ} (rhs : Fin k → Bool) (p : Partner k t) :
    Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs) :=
  (PartnerLinear.projection rhs (active p) (slots p)).ker

def activeSubtypeEquiv {k t : ℕ} (p : Partner k t) :
    PartnerLinear.Active (active p) ≃ ↥p.1.val :=
  Equiv.subtypeEquivRight (fun j => by simp [active])

theorem kernel_finrank {k t : ℕ} (rhs : Fin k → Bool) (p : Partner k t) :
    Module.finrank (ZMod 2) (kernel rhs p) = t := by
  rw [kernel, PartnerLinear.projection_ker_finrank]
  calc
    Fintype.card (PartnerLinear.Active (active p)) = Fintype.card ↥p.1.val :=
      Fintype.card_congr (activeSubtypeEquiv p)
    _ = t := by simpa using activeSet_card p.1

theorem kernel_inf_finrank_le {k t : ℕ} (rhs : Fin k → Bool) (p q : Partner k t) :
    Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)) ≤ t := by
  calc
    Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)) ≤
        Module.finrank (ZMod 2) (kernel rhs p) := Submodule.finrank_mono inf_le_left
    _ = t := kernel_finrank rhs p

theorem kernel_inf_eq_bot_of_no_overlap {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t)
    (h : ¬ (p.1.val ∩ q.1.val).Nonempty) :
    kernel rhs p ⊓ kernel rhs q = ⊥ := by
  apply PartnerLinear.disjoint_projection_kernels
    rhs (active p) (slots p) (active q) (slots q)
  intro j hj
  have hp : j ∈ p.1.val := by simpa [active] using hj
  have hq : j ∉ q.1.val := by
    intro hq
    exact h ⟨j, Finset.mem_inter.mpr ⟨hp, hq⟩⟩
  simp [active, hq]

def activeOverlap {k t : ℕ} (p q : Partner k t) : ℝ :=
  if (p.1.val ∩ q.1.val).Nonempty then 1 else 0

noncomputable def kernelCollision {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t) : ℝ := by
  classical
  exact if kernel rhs p ⊓ kernel rhs q ≠ ⊥ then 1 else 0

theorem kernelCollision_le_activeOverlap {k t : ℕ}
    (rhs : Fin k → Bool) (p q : Partner k t) :
    kernelCollision rhs p q ≤ activeOverlap p q := by
  classical
  by_cases h : (p.1.val ∩ q.1.val).Nonempty
  · simp only [activeOverlap, ite_eq_left h, kernelCollision]
    split_ifs <;> norm_num
  · have hb := kernel_inf_eq_bot_of_no_overlap rhs p q h
    simp [kernelCollision, activeOverlap, h, hb]

theorem kernel_collision_probability_le {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      kernelCollision rhs p q) ≤ (t : ℝ)^2 / k := by
  calc
    (𝔼 p : Partner k t, 𝔼 q : Partner k t, kernelCollision rhs p q) ≤
        (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) := by
      apply Finset.expect_le_expect
      intro p _
      apply Finset.expect_le_expect
      intro q _
      exact kernelCollision_le_activeOverlap rhs p q
    _ ≤ (t : ℝ)^2 / k := partner_active_overlap_probability_le hk htk

theorem kernel_overlap_weight_pointwise {k t : ℕ}
    (rhs : Fin k → Bool) (m : ℕ) (p q : Partner k t) :
    (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs))) ≤
      1 + activeOverlap p q * (2 : ℝ) ^ (m * t) := by
  have hcap :
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs))) ≤
        (2 : ℝ) ^ (m * t) := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    exact Nat.mul_le_mul_left m (kernel_inf_finrank_le rhs p q)
  by_cases h : (p.1.val ∩ q.1.val).Nonempty
  · simp only [activeOverlap, ite_eq_left h, one_mul]
    linarith
  · have hb := kernel_inf_eq_bot_of_no_overlap rhs p q h
    rw [hb]
    simp [activeOverlap, h]

theorem kernel_overlap_weight_le {k t : ℕ}
    (hk : 0 < k) (htk : t ≤ k) (rhs : Fin k → Bool) (m : ℕ) :
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)))) ≤
      1 + ((t : ℝ)^2 / k) * (2 : ℝ) ^ (m * t) := by
  let : Nonempty (Partner k t) := partner_nonempty htk
  have hmean :
      (𝔼 p : Partner k t, 𝔼 q : Partner k t,
        (1 + activeOverlap p q * (2 : ℝ) ^ (m * t))) =
      1 + (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) *
        (2 : ℝ) ^ (m * t) := by
    simp_rw [Finset.expect_add_distrib, ← Finset.expect_mul, Fintype.expect_const]
  calc
    (𝔼 p : Partner k t, 𝔼 q : Partner k t,
      (2 : ℝ) ^ (m * Module.finrank (ZMod 2) ↥(kernel rhs p ⊓ kernel rhs q : Submodule (ZMod 2) (PartnerProjection.SourcePoint rhs)))) ≤
        (𝔼 p : Partner k t, 𝔼 q : Partner k t,
          (1 + activeOverlap p q * (2 : ℝ) ^ (m * t))) := by
      apply Finset.expect_le_expect
      intro p _
      apply Finset.expect_le_expect
      intro q _
      exact kernel_overlap_weight_pointwise rhs m p q
    _ = 1 + (𝔼 p : Partner k t, 𝔼 q : Partner k t, activeOverlap p q) *
        (2 : ℝ) ^ (m * t) := hmean
    _ ≤ 1 + ((t : ℝ)^2 / k) * (2 : ℝ) ^ (m * t) := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right
      · exact partner_active_overlap_probability_le hk htk
      · exact pow_nonneg (by norm_num) _

end MaxCutGames.Soundness.PartnerSampling

end OAI
