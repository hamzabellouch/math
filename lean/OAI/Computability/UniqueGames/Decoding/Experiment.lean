import OAI.Computability.UniqueGames.Decoding.MaskMomentLemmas
import OAI.Computability.UniqueGames.Decoding.UpperBound

namespace OAI

section

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

namespace UniqueGamesTheorem.Clean.Experiment

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

private theorem expectation_mono {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    μ.expectation f ≤ μ.expectation g := by
  unfold FiniteDistribution.expectation
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

private theorem expectation_const {Ω : Type*} [Fintype Ω]
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
      apply expectation_mono
      intro extra
      calc
        _ ≤ ((singletonSlopeLaw (E := Coefficient R) β hβ₀ hβ₁).iid k).expectation
            (fun seed => ρ ^ maskCount (fun i => cleanBit (ZeroInformation.zero : Coefficient R) (seed i))) := by
          apply expectation_mono
          intro seed
          have bound := (UpperBound.fixed_advice_success_le_repeated_value μ
            (singletonSet seed) g (coefficients extra seed) (strategy extra seed) distinct).trans (rate _)
          simpa only [zeroSet_card] using bound
        _ = _ := clean_mask_moment β hβ₀ hβ₁ (ZeroInformation.zero : Coefficient R) k ρ
    _ = _ := expectation_const _ _

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
      expectation_mono _ (fun seed =>
        success_le_of_repetition k μ g extraLaw β hβ₀ hβ₁ (strategy seed) distinct ρ rate)
    _ = _ := expectation_const _ _

end
end UniqueGamesTheorem.Clean.Experiment

end

end OAI
