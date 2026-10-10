import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

/-! Measure-family duality and probability lifting.

* Ambrosio–Di Marino–Savaré, JEMS 17 (2015), 1817–1853,
  DOI 10.4171/JEMS/546, Theorem 5.1 (p. 1830), Corollary 5.2(b)
  (p. 1833): positive modulus of a Suslin image yields a probability
  plan on finite measures with an L² barycenter. `MeasureImageDuality`
  is the p = 2 consequence for a Borel image of a standard Borel space.
* Bogachev, *Measure Theory*, vol. II (2007), Theorem 6.9.1 gives a
  measure-dependent measurable selector. `MeasurePlanLifting` states
  its probability-lifting consequence, used in the proof of ADMS,
  Theorem 7.2, p. 1839.

The two propositions separate measure-space duality from probability
lifting; neither assumes a compact-support conclusion.
-/

open Set MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace CircleDomainRigidity

variable (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
  [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]

/-- Pointwise admissibility, including infinite values on reference-null sets. -/
def measureFamilyModulus (σ : Measure Z) (K : A → FiniteMeasure Z) : ℝ≥0∞ :=
  ⨅ (h : Z → ℝ≥0∞) (_ : Measurable h)
    (_ : ∀ a, 1 ≤ ∫⁻ z, h z ∂(K a : Measure Z)), ∫⁻ z, h z ^ 2 ∂σ

/-- The measure-image conclusion of ADMS Theorem 5.1 and Corollary 5.2(b). -/
def MeasureImageDuality (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] : Prop :=
  ∀ (K : A → FiniteMeasure Z), Measurable K →
  ∀ (σ : Measure Z), IsFiniteMeasure σ →
  ∀ (c : ℝ≥0), 0 < c → (c : ℝ≥0∞) < measureFamilyModulus A Z σ K →
  ∃ (η : ProbabilityMeasure (FiniteMeasure Z)) (q : Z → ℝ≥0∞),
    Measurable q ∧
    (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ range K) ∧
    (∀ E, MeasurableSet E →
      (∫⁻ v, (v : Measure Z) E ∂(η : Measure (FiniteMeasure Z))) = σ.withDensity q E) ∧
    (∫⁻ z, q z ^ 2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹

/-- The probability-lifting consequence of the cited measurable selector. -/
def MeasurePlanLifting (A Z : Type*) [MeasurableSpace A] [StandardBorelSpace A]
    [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z] : Prop :=
  ∀ (K : A → FiniteMeasure Z), Measurable K →
  ∀ (η : ProbabilityMeasure (FiniteMeasure Z)),
    (∀ᵐ v ∂(η : Measure (FiniteMeasure Z)), v ∈ range K) →
    ∃ P : ProbabilityMeasure A, P.map K = η

theorem indexed_measure_duality (hdual : MeasureImageDuality A Z)
    (hlift : MeasurePlanLifting A Z) (K : A → FiniteMeasure Z) (hK : Measurable K)
    (σ : Measure Z) [IsFiniteMeasure σ] (c : ℝ≥0) (hc : 0 < c)
    (hmod : (c : ℝ≥0∞) < measureFamilyModulus A Z σ K) :
    ∃ (P : ProbabilityMeasure A) (q : Z → ℝ≥0∞), Measurable q ∧
      (∀ E, MeasurableSet E →
        (∫⁻ a, (K a : Measure Z) E ∂(P : Measure A)) = σ.withDensity q E) ∧
      (∫⁻ z, q z ^ 2 ∂σ) ≤ (c : ℝ≥0∞)⁻¹ := by
  obtain ⟨η, q, hq, hrange, hbar, henergy⟩ := hdual K hK σ inferInstance c hc hmod
  obtain ⟨P, hP⟩ := hlift K hK η hrange
  refine ⟨P, q, hq, ?_, henergy⟩
  intro E hE
  have hev : Measurable (fun v : FiniteMeasure Z => (v : Measure Z) E) :=
    (Measure.measurable_coe hE).comp measurable_subtype_coe
  have hb := hbar E hE
  rw [← hP, ProbabilityMeasure.toMeasure_map, lintegral_map hev hK] at hb
  exact hb

end CircleDomainRigidity

end

end OAI
