import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

namespace OAI

/-!
# The ergodic-component step for prime-degree torus packets

The entropy functional is a parameter whose restricted-mixture formula
is the specialization of Rokhlin,
*Lectures on the entropy theory of measure-preserving transformations*
(1967), Theorem 9.8. The measurable probability kernel and its
restricted-mixture formula are hypotheses; the decomposition theorem of
Greschonig--Schmidt (2000), Theorem 5.2, gives such kernels for invariant
probabilities.

In particular, a lower bound for the entropy of a measure alone is not
used to infer positive entropy in almost every component.  The lower
bound must hold for every invariant probability dominated by a finite
multiple of that measure.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace DukePrimeDegree

variable {X Z I : Type*} [MeasurableSpace X] [MeasurableSpace Z]

/-- The probability obtained by retaining a positive-measure collection
of components and renormalizing. -/
noncomputable def restrictedMixture (τ : Measure Z) (κ : Z → Measure X)
    (s : Set Z) : Measure X :=
  (τ s)⁻¹ • (τ.restrict s).bind κ

lemma restricted_bind_le (τ : Measure Z) (κ : Z → Measure X)
    (hκ : Measurable κ) (s : Set Z) :
    (τ.restrict s).bind κ ≤ τ.bind κ := by
  apply Measure.le_iff.mpr
  intro a ha
  rw [Measure.bind_apply ha hκ.aemeasurable,
    Measure.bind_apply ha hκ.aemeasurable]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

lemma restrictedMixture_le (τ : Measure Z) (κ : Z → Measure X)
    (hκ : Measurable κ) (s : Set Z) :
    restrictedMixture τ κ s ≤ (τ s)⁻¹ • τ.bind κ := by
  apply Measure.le_iff.mpr
  intro a ha
  change (τ s)⁻¹ * ((τ.restrict s).bind κ) a ≤ (τ s)⁻¹ * (τ.bind κ) a
  exact mul_le_mul_right (Measure.le_iff.mp (restricted_bind_le τ κ hκ s) a ha) _

lemma restrictedMixture_probability (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (hκ : Measurable κ)
    (hprob : ∀ z, IsProbabilityMeasure (κ z)) (s : Set Z) (hs : τ s ≠ 0) :
    IsProbabilityMeasure (restrictedMixture τ κ s) := by
  constructor
  have hk : ∀ z, κ z univ = 1 := fun z => (hprob z).measure_univ
  simp only [restrictedMixture, Measure.smul_apply, smul_eq_mul,
    Measure.bind_apply MeasurableSet.univ hκ.aemeasurable, hk,
    lintegral_const, Measure.restrict_apply_univ, one_mul]
  exact ENNReal.inv_mul_cancel hs (measure_ne_top τ s)

/-- Taking mixtures commutes with a measurable transformation that fixes
every component. -/
lemma map_bind_eq_of_component_invariant (τ : Measure Z) (κ : Z → Measure X)
    (hκ : Measurable κ) (T : X → X) (hT : Measurable T)
    (hinv : ∀ z, Measure.map T (κ z) = κ z) :
    Measure.map T (τ.bind κ) = τ.bind κ := by
  ext a ha
  rw [Measure.map_apply hT ha,
    Measure.bind_apply (hT ha) hκ.aemeasurable,
    Measure.bind_apply ha hκ.aemeasurable]
  apply lintegral_congr
  intro z
  simpa only [Measure.map_apply hT ha] using congrArg (fun ν : Measure X => ν a) (hinv z)

lemma restrictedMixture_invariant (τ : Measure Z) (κ : Z → Measure X)
    (hκ : Measurable κ) (s : Set Z)
    (T : X → X) (hT : Measurable T)
    (hinv : ∀ z, Measure.map T (κ z) = κ z) :
    Measure.map T (restrictedMixture τ κ s) = restrictedMixture τ κ s := by
  rw [restrictedMixture, Measure.map_smul _ hT.aemeasurable]
  congr 1
  exact map_bind_eq_of_component_invariant _ κ hκ T hT hinv

/-- The domination argument for the zero-entropy components.

`hformula` is only the restriction case of the published entropy integral
formula.  `hpositive` is the manuscript's preceding ball-to-entropy result,
which has to be established separately.  The proof constructs the
normalized zero-entropy submixture, proves its domination and invariance,
and obtains a contradiction. -/
theorem ae_positive_component_entropy
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (hκ : Measurable κ)
    (hprob : ∀ z, IsProbabilityMeasure (κ z))
    (T : I → X → X) (hT : ∀ i, Measurable (T i))
    (hinv : ∀ i z, Measure.map (T i) (κ z) = κ z)
    (entropy : Measure X → ℝ≥0∞)
    (hentropy : Measurable (fun z => entropy (κ z)))
    (hformula : ∀ s, MeasurableSet s → τ s ≠ 0 →
      entropy (restrictedMixture τ κ s) =
        (τ s)⁻¹ * ∫⁻ z in s, entropy (κ z) ∂τ)
    (hpositive : ∀ ξ : Measure X, IsProbabilityMeasure ξ →
      (∀ i, Measure.map (T i) ξ = ξ) →
      (∃ c : ℝ≥0∞, c ≠ ∞ ∧ ξ ≤ c • τ.bind κ) → 0 < entropy ξ) :
    ∀ᵐ z ∂τ, 0 < entropy (κ z) := by
  let s : Set Z := {z | entropy (κ z) = 0}
  have hs : MeasurableSet s := hentropy (measurableSet_singleton 0)
  have hzero : τ s = 0 := by
    by_contra hmass
    have hprob' := restrictedMixture_probability τ κ hκ hprob s hmass
    have hinv' : ∀ i, Measure.map (T i) (restrictedMixture τ κ s) =
        restrictedMixture τ κ s := fun i =>
      restrictedMixture_invariant τ κ hκ s (T i) (hT i) (hinv i)
    have hpos := hpositive (restrictedMixture τ κ s) hprob' hinv'
      ⟨(τ s)⁻¹, ENNReal.inv_ne_top.mpr hmass, restrictedMixture_le τ κ hκ s⟩
    have hIntegral : ∫⁻ z in s, entropy (κ z) ∂τ = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [ae_restrict_mem hs] with z hz
      exact hz
    have hent : entropy (restrictedMixture τ κ s) = 0 := by
      rw [hformula s hs hmass, hIntegral, mul_zero]
    exact (ne_of_gt hpos) hent
  rw [ae_iff]
  simpa only [not_lt, nonpos_iff_eq_zero] using hzero

/-- A probability mixture of almost-everywhere identical components is
that same probability.  This is the final integration step after the
prime-degree rigidity theorem identifies the ergodic components. -/
theorem bind_eq_of_ae_eq (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (m : Measure X) (heq : ∀ᵐ z ∂τ, κ z = m) :
    τ.bind κ = m := by
  rw [Measure.bind_congr_right heq, Measure.bind_const, measure_univ, one_smul]

/-- Combine the preceding component argument with the application-specific
rigidity implication.  For torus packets, `hrigid` is supplied by
Einsiedler--Katok--Lindenstrauss (2006), Theorem 1.3 and Corollary 1.4,
after checking prime degree and ergodicity. -/
theorem bind_eq_of_positive_entropy_rigidity
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Z → Measure X) (entropy : Measure X → ℝ≥0∞) (m : Measure X)
    (hpositive : ∀ᵐ z ∂τ, 0 < entropy (κ z))
    (hrigid : ∀ᵐ z ∂τ, 0 < entropy (κ z) → κ z = m) :
    τ.bind κ = m := by
  apply bind_eq_of_ae_eq τ κ m
  filter_upwards [hpositive, hrigid] with z hz hr
  exact hr hz

end DukePrimeDegree

end OAI
