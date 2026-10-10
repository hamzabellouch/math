import OAI.GroupTheory.PolycyclicRecognition.Algebra.OccupationWeakLimit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! # Actual probability laws of independent chart samples -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Filter Set
open scoped Topology

/-- Uniform sampling from an actual measurable cell of positive finite mass. -/
def cellProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (S : Set Z) (hzero : μ S ≠ 0) (hfin : μ S ≠ ⊤) :
    ProbabilityMeasure Z :=
  ⟨(μ S)⁻¹ • μ.restrict S, by
    constructor
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hzero hfin⟩

theorem integral_cellProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (S : Set Z) (hzero : μ S ≠ 0) (hfin : μ S ≠ ⊤)
    (f : Z → ℝ) :
    (∫ z, f z ∂(cellProbabilityMeasure μ S hzero hfin : Measure Z)) =
      (μ S).toReal⁻¹ * ∫ z in S, f z ∂μ := by
  change (∫ z, f z ∂((μ S)⁻¹ • μ.restrict S)) = _
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_inv, smul_eq_mul]

/-- A nonnegative integrable density of mass one defines a probability. -/
def densityProbabilityMeasure {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ρ : Z → ℝ) (hi : Integrable ρ μ)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂μ = 1) : ProbabilityMeasure Z :=
  ⟨μ.withDensity (fun z => ENNReal.ofReal (ρ z)), by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hp), hmass]
    exact ENNReal.ofReal_one⟩

/-- Integrating against that probability is the ordinary density-weighted
integral, including for scale-dependent observables. -/
theorem integral_densityProbabilityMeasure
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ρ : Z → ℝ) (hi : Integrable ρ μ)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂μ = 1)
    (f : Z → ℝ) :
    (∫ z, f z ∂(densityProbabilityMeasure μ ρ hi hp hmass : Measure Z)) =
      ∫ z, ρ z * f z ∂μ := by
  change (∫ z, f z ∂μ.withDensity (fun z => ENNReal.ofReal (ρ z))) = _
  rw [integral_withDensity_eq_integral_toReal_smul₀
    hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hp _), smul_eq_mul]

/-- A density sample lies almost surely in every set outside which the
density vanishes. In particular its compact support carries the law. -/
theorem ae_mem_densityProbabilityMeasure
    {Z : Type*} [MeasurableSpace Z]
    (μ : Measure Z) (ρ : Z → ℝ) (hi : Integrable ρ μ)
    (hp : ∀ z, 0 ≤ ρ z) (hmass : ∫ z, ρ z ∂μ = 1)
    (K : Set Z) (hK : ∀ z, z ∉ K → ρ z = 0) :
    ∀ᵐ z ∂(densityProbabilityMeasure μ ρ hi hp hmass : Measure Z), z ∈ K := by
  change ∀ᵐ z ∂μ.withDensity (fun z => ENNReal.ofReal (ρ z)), z ∈ K
  rw [ae_withDensity_iff' hi.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
  exact Eventually.of_forall (fun z hz => by
    by_contra hn
    exact hz (by rw [hK z hn, ENNReal.ofReal_zero]))

/-- The law of a measurable chart sampled independently in its two factors. -/
def productOccupationLaw {A D X : Type*}
    [MeasurableSpace A] [MeasurableSpace D] [MeasurableSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D) (p : A × D → X) :
    ProbabilityMeasure X :=
  ProbabilityMeasure.map
    (⟨(μ : Measure A).prod (ν : Measure D), inferInstance⟩ : ProbabilityMeasure (A × D)) p

/-- Fubini's formula for a bounded continuous observable of a chart sample. -/
theorem integral_productOccupationLaw
    {A D X : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p) (f : C(X, ℝ)) :
    (∫ x, f x ∂(productOccupationLaw μ ν p : Measure X)) =
      ∫ a, ∫ d, f (p (a, d)) ∂(ν : Measure D) ∂(μ : Measure A) := by
  change (∫ x, f x ∂Measure.map p ((μ : Measure A).prod (ν : Measure D))) = _
  rw [integral_map hp.aemeasurable f.continuous.aestronglyMeasurable]
  apply integral_prod
  exact Integrable.of_bound (f.continuous.measurable.comp hp).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm (p z)))

/-- The same formula with the other factor outside. -/
theorem integral_productOccupationLaw_symm
    {A D X : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p) (f : C(X, ℝ)) :
    (∫ x, f x ∂(productOccupationLaw μ ν p : Measure X)) =
      ∫ d, ∫ a, f (p (a, d)) ∂(μ : Measure A) ∂(ν : Measure D) := by
  change (∫ x, f x ∂Measure.map p ((μ : Measure A).prod (ν : Measure D))) = _
  rw [integral_map hp.aemeasurable f.continuous.aestronglyMeasurable]
  apply integral_prod_symm
  exact Integrable.of_bound (f.continuous.measurable.comp hp).aestronglyMeasurable
    ‖f‖ (Eventually.of_forall (fun z => f.norm_coe_le_norm (p z)))

/-- Exact translated-law error formula. In particular, estimates only on
the support of the second sampling measure suffice after this identity. -/
theorem productOccupationLaw_error_eq
    {A D X G : Type*} [MeasurableSpace A] [MeasurableSpace D]
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [SMul G X] [ContinuousConstSMul G X]
    (μ : ProbabilityMeasure A) (ν : ProbabilityMeasure D)
    (p : A × D → X) (hp : Measurable p) (g : G) (f : C(X, ℝ)) :
    (∫ x, f (g • x) ∂(productOccupationLaw μ ν p : Measure X)) -
        ∫ x, f x ∂(productOccupationLaw μ ν p : Measure X) =
      ∫ d, ((∫ a, f (g • p (a, d)) ∂(μ : Measure A)) -
        ∫ a, f (p (a, d)) ∂(μ : Measure A)) ∂(ν : Measure D) := by
  let fg : C(X, ℝ) := ⟨fun x => f (g • x),
    f.continuous.comp (continuous_const_smul g)⟩
  have hfi (q : C(X, ℝ)) : Integrable (fun z : A × D => q (p z))
      ((μ : Measure A).prod (ν : Measure D)) :=
    Integrable.of_bound (q.continuous.measurable.comp hp).aestronglyMeasurable
      ‖q‖ (Eventually.of_forall (fun z => q.norm_coe_le_norm _))
  rw [show (fun x => f (g • x)) = (fg : X → ℝ) from rfl,
    integral_productOccupationLaw_symm μ ν p hp fg,
    integral_productOccupationLaw_symm μ ν p hp f,
    ← integral_sub (hfi fg).integral_prod_right (hfi f).integral_prod_right]
  rfl

end PolycyclicRecognition

end

end OAI
