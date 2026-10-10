import OAI.NumberTheory.DukePrimeDegree.Entropy.Entropy
import OAI.NumberTheory.DukePrimeDegree.Entropy.MetricEntropy
import OAI.NumberTheory.DukePrimeDegree.Geometry.Tubes
import Mathlib.Dynamics.Ergodic.Action.Basic

namespace OAI

/-!
# Conditional dynamical reduction for the prime-degree packet theorem

A ball cover with a dimension gap gives exponential tube decay. Entropy
in almost every ergodic component, followed by prime-degree rigidity,
then identifies the mixture with Haar probability.

The dynamical criteria are specialized as follows:
* ELMV (2009), Corollary 3.3: a flow-invariant probability with
  compact-uniform two-sided tube bound `exp(-2ηt)` has entropy at least `η`.
* Rokhlin (1967), Theorem 9.8: entropy of a normalized restriction of an
  invariant component decomposition is its component entropy integral.
* EKL (2006), Theorem 1.3 and Corollary 1.4: a diagonal-invariant ergodic
  probability with positive entropy on the prime-degree lattice space
  is Haar probability.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

variable {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  [TopologicalSpace X]

/-- The constant-sequence specialization of the published two-sided tube
criterion. The application must use the source's actual flow and tubes. -/
def ELMVConstantSequenceCriterion (flow : ℝ → X → X)
    (tube : ℝ → X → Set X) : Prop :=
  ∀ (ν : Measure X) (η : ℝ), IsProbabilityMeasure ν →
    (∀ t, Measure.map (flow t) ν = ν) → 0 < η →
    HasTubeDecay ν tube (2 * η) →
    ENNReal.ofReal η ≤ metricEntropy (flow 1) ν

/-- The restriction case of the published entropy integral formula. -/
def RokhlinRestrictionFormula (τ : Measure Z) (κ : Z → Measure X)
    (flow : ℝ → X → X) : Prop :=
  ∀ s, MeasurableSet s → τ s ≠ 0 →
    metricEntropy (flow 1) (restrictedMixture τ κ s) =
      (τ s)⁻¹ * ∫⁻ z in s, metricEntropy (flow 1) (κ z) ∂τ

/-- Covers by balls with mass exponent `n` and covering exponent `n-1`. -/
def BallTubeCovers (μ : Measure X) (tube : ℝ → X → Set X)
    (n : ℕ) (rate : ℝ) : Prop :=
  ∀ K : Set X, IsCompact K →
    ∃ Cball Ccover : ℝ, 0 ≤ Cball ∧ 0 ≤ Ccover ∧
      ∀ t : ℝ, 0 ≤ t → ∀ x ∈ K,
        ∃ (J : Type) (_ : Fintype J) (balls : J → Set X),
          tube t x ⊆ ⋃ j, balls j ∧
          (∀ j, μ (balls j) ≤ ENNReal.ofReal (Cball * Real.exp (-rate * t) ^ n)) ∧
          (Fintype.card J : ℝ) * Real.exp (-rate * t) ^ (n - 1) ≤ Ccover

/-- Every component has positive entropy almost everywhere, using the
actual Kolmogorov--Sinai entropy definition and precisely stated inputs. -/
theorem ae_positive_metricEntropy_of_ballTubeCovers
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (hκ : Measurable κ)
    (hprob : ∀ z, IsProbabilityMeasure (κ z))
    (flow : ℝ → X → X) (hflow : ∀ t, Measurable (flow t))
    (hinv : ∀ t z, Measure.map (flow t) (κ z) = κ z)
    (tube : ℝ → X → Set X) (n : ℕ) (hn : 1 ≤ n)
    (rate : ℝ) (hrate : 0 < rate)
    (covers : BallTubeCovers (τ.bind κ) tube n rate)
    (hentropy : Measurable (fun z => metricEntropy (flow 1) (κ z)))
    (rokhlin : RokhlinRestrictionFormula τ κ flow)
    (elmv : ELMVConstantSequenceCriterion flow tube) :
    ∀ᵐ z ∂τ, 0 < metricEntropy (flow 1) (κ z) := by
  have hdecay := tube_decay_of_ball_covers (τ.bind κ) tube n hn rate covers
  apply ae_positive_component_entropy τ κ hκ hprob flow hflow hinv
    (metricEntropy (flow 1)) hentropy rokhlin
  intro ξ hξ hξinv hdom
  obtain ⟨c, hc, hdom⟩ := hdom
  have hdecayξ := hdecay.of_le_smul c hc hdom
  have hlower := entropy_lower_bound_of_tube_decay ξ flow tube
    (metricEntropy (flow 1)) rate hrate hξ hξinv hdecayξ elmv
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos hrate (by norm_num))) hlower

/-- The final dynamical reduction: positive entropy in almost every
component, followed by rigidity and integration, identifies the mixture.
The group action and the EKL implication must be specialized to the
prime-degree homogeneous lattice space before this applies to packets. -/
theorem mixture_eq_of_ballTubeCovers
    (G : Type*) [Group G] [MulAction G X]
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (hκ : Measurable κ)
    (hprob : ∀ z, IsProbabilityMeasure (κ z))
    (hergodic : ∀ᵐ z ∂τ, ErgodicSMul G X (κ z))
    (flow : ℝ → X → X) (hflow : ∀ t, Measurable (flow t))
    (hinv : ∀ t z, Measure.map (flow t) (κ z) = κ z)
    (tube : ℝ → X → Set X) (n : ℕ) (hn : 1 ≤ n)
    (rate : ℝ) (hrate : 0 < rate)
    (covers : BallTubeCovers (τ.bind κ) tube n rate)
    (hentropy : Measurable (fun z => metricEntropy (flow 1) (κ z)))
    (rokhlin : RokhlinRestrictionFormula τ κ flow)
    (elmv : ELMVConstantSequenceCriterion flow tube)
    (haar : Measure X)
    (ekl : ∀ ν : Measure X, IsProbabilityMeasure ν →
      ErgodicSMul G X ν → 0 < metricEntropy (flow 1) ν → ν = haar) :
    τ.bind κ = haar := by
  have hpositive := ae_positive_metricEntropy_of_ballTubeCovers τ κ hκ hprob
    flow hflow hinv tube n hn rate hrate covers hentropy rokhlin elmv
  apply bind_eq_of_positive_entropy_rigidity τ κ (metricEntropy (flow 1)) haar hpositive
  filter_upwards [hergodic] with z hz
  exact ekl (κ z) (hprob z) hz

end DukePrimeDegree

end OAI
