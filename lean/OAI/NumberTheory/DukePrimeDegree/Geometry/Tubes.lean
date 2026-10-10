import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

namespace OAI

/-!
# From ball covers to entropy-producing tube estimates

A cover by balls with a dimension gap between their mass exponent and
covering number gives exponential tube decay. The entropy implication
uses the constant-sequence specialization of
Einsiedler--Lindenstrauss--Michel--Venkatesh (2009), Corollary 3.3,
with its two-sided flow tubes.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

variable {X : Type*} [MeasurableSpace X]

/-- A tube covered by `O(r^{-(n-1)})` balls, each of mass `O(r^n)`,
has mass `O(r)`.  The cardinality assumption is multiplied through by
`r^(n-1)` to avoid division and retain the exact dimension gap. -/
theorem tube_mass_le_of_ball_cover
    (μ : Measure X) (tube : Set X) {J : Type*} [Fintype J]
    (balls : J → Set X) (hcover : tube ⊆ ⋃ j, balls j)
    (n : ℕ) (hn : 1 ≤ n) (r Cball Ccover : ℝ)
    (hr : 0 ≤ r) (hCball : 0 ≤ Cball)
    (hball : ∀ j, μ (balls j) ≤ ENNReal.ofReal (Cball * r ^ n))
    (hcard : (Fintype.card J : ℝ) * r ^ (n - 1) ≤ Ccover) :
    μ tube ≤ ENNReal.ofReal (Cball * Ccover * r) := by
  have hpow : r ^ n = r ^ (n - 1) * r := by
    calc
      r ^ n = r ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel hn]
      _ = r ^ (n - 1) * r := pow_succ _ _
  have hnumeric : (Fintype.card J : ℝ) * (Cball * r ^ n) ≤ Cball * Ccover * r := by
    calc
      (Fintype.card J : ℝ) * (Cball * r ^ n) =
          Cball * ((Fintype.card J : ℝ) * r ^ (n - 1)) * r := by rw [hpow]; ring
      _ ≤ Cball * Ccover * r :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hCball) hr
  calc
    μ tube ≤ μ (⋃ j, balls j) := measure_mono hcover
    _ ≤ ∑ j, μ (balls j) := measure_iUnion_fintype_le μ balls
    _ ≤ ∑ _j : J, ENNReal.ofReal (Cball * r ^ n) := Finset.sum_le_sum fun j _ => hball j
    _ = ENNReal.ofReal ((Fintype.card J : ℝ) * (Cball * r ^ n)) := by
      simp [ENNReal.ofReal_mul, ENNReal.ofReal_natCast, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (Cball * Ccover * r) := ENNReal.ofReal_le_ofReal hnumeric

variable [TopologicalSpace X]

/-- Uniform exponential tube bounds on each compact set.  The constants
are finite but may depend on the compact set. -/
def HasTubeDecay (μ : Measure X) (tube : ℝ → X → Set X) (rate : ℝ) : Prop :=
  ∀ K : Set X, IsCompact K → ∃ C : ℝ≥0∞, C ≠ ∞ ∧
    ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
      μ (tube t x) ≤ C * ENNReal.ofReal (Real.exp (-rate * t))

lemma HasTubeDecay.mono_rate {μ : Measure X} {tube : ℝ → X → Set X}
    {a b : ℝ} (h : HasTubeDecay μ tube a) (hba : b ≤ a) :
    HasTubeDecay μ tube b := by
  intro K hK
  obtain ⟨C, hC, hbound⟩ := h K hK
  refine ⟨C, hC, fun t ht x hx => (hbound t ht x hx).trans ?_⟩
  apply mul_le_mul_right
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg hba) ht

/-- Domination by a finite multiple preserves tube decay. -/
lemma HasTubeDecay.of_le_smul {μ ν : Measure X} {tube : ℝ → X → Set X}
    {rate : ℝ} (h : HasTubeDecay μ tube rate)
    (c : ℝ≥0∞) (hc : c ≠ ∞) (hν : ν ≤ c • μ) :
    HasTubeDecay ν tube rate := by
  intro K hK
  obtain ⟨C, hC, hbound⟩ := h K hK
  refine ⟨c * C, ENNReal.mul_ne_top hc hC, ?_⟩
  intro t ht x hx
  calc
    ν (tube t x) ≤ (c • μ) (tube t x) := hν (tube t x)
    _ = c * μ (tube t x) := rfl
    _ ≤ c * (C * ENNReal.ofReal (Real.exp (-rate * t))) :=
      mul_le_mul_right (hbound t ht x hx) c
    _ = (c * C) * ENNReal.ofReal (Real.exp (-rate * t)) := (mul_assoc _ _ _).symm

/-- Exact specialization of the preceding finite-cover estimate with
radius `exp(-rate*t)`.  The cover cardinalities and ball estimates are
geometric hypotheses, separate from the published entropy criterion. -/
theorem tube_decay_of_ball_covers
    (μ : Measure X) (tube : ℝ → X → Set X)
    (n : ℕ) (hn : 1 ≤ n) (rate : ℝ)
    (hcovers : ∀ K : Set X, IsCompact K →
      ∃ Cball Ccover : ℝ, 0 ≤ Cball ∧ 0 ≤ Ccover ∧
        ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
          ∃ (J : Type) (_ : Fintype J) (balls : J → Set X),
            tube t x ⊆ ⋃ j, balls j ∧
            (∀ j, μ (balls j) ≤ ENNReal.ofReal (Cball * Real.exp (-rate * t) ^ n)) ∧
            (Fintype.card J : ℝ) * Real.exp (-rate * t) ^ (n - 1) ≤ Ccover) :
    HasTubeDecay μ tube rate := by
  intro K hK
  obtain ⟨Cball, Ccover, hCball, hCcover, hcover⟩ := hcovers K hK
  refine ⟨ENNReal.ofReal (Cball * Ccover), ENNReal.ofReal_ne_top, ?_⟩
  intro t ht x hx
  obtain ⟨J, hJ, balls, hcov, hballs, hcard⟩ := hcover t ht x hx
  let := hJ
  have hm := tube_mass_le_of_ball_cover μ (tube t x) balls hcov n hn
    (Real.exp (-rate * t)) Cball Ccover (Real.exp_pos _).le hCball hballs hcard
  simpa only [ENNReal.ofReal_mul (mul_nonneg hCball hCcover)] using hm

/-- The constant-sequence specialization of ELMV's tube criterion,
using the flow and two-sided neighborhoods of Corollary 3.3. -/
theorem entropy_lower_bound_of_tube_decay
    (μ : Measure X) (flow : ℝ → X → X) (tube : ℝ → X → Set X)
    (entropy : Measure X → ℝ≥0∞) (rate : ℝ) (hrate : 0 < rate)
    (hprob : IsProbabilityMeasure μ)
    (hinv : ∀ t, Measure.map (flow t) μ = μ)
    (hdecay : HasTubeDecay μ tube rate)
    (elmv : ∀ (ν : Measure X) (η : ℝ), IsProbabilityMeasure ν →
      (∀ t, Measure.map (flow t) ν = ν) → 0 < η →
      HasTubeDecay ν tube (2 * η) → ENNReal.ofReal η ≤ entropy ν) :
    ENNReal.ofReal (rate / 3) ≤ entropy μ := by
  apply elmv μ (rate / 3) hprob hinv (div_pos hrate (by norm_num))
  apply hdecay.mono_rate
  linarith

end DukePrimeDegree

end OAI
