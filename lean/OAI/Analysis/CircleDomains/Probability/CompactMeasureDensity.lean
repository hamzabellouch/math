import OAI.Analysis.CircleDomains.Sobolev.CompactMeasureL2Plan
import OAI.Analysis.CircleDomains.Probability.CompactMeasureBarycenter
import OAI.Analysis.CircleDomains.Sobolev.L2PositiveTests
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace OAI

/-! The compact-family plan has the actual nonnegative Borel L² density
of its barycenter. The identity is proved on Borel sets, not just tests. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma L2_ofReal_energy_eq
    {Z : Type*} [MeasurableSpace Z] (σ : Measure Z)
    (g : Lp ℝ 2 σ) (hg : ∀ᵐ z ∂σ, 0 ≤ g z) :
    (∫⁻ z, (ENNReal.ofReal (g z))^2 ∂σ) = ENNReal.ofReal (‖g‖^2) := by
  calc
    (∫⁻ z, (ENNReal.ofReal (g z))^2 ∂σ) =
        ∫⁻ z, ENNReal.ofReal ((g z)^2) ∂σ := by
      apply lintegral_congr_ae
      filter_upwards [hg] with z hz
      exact (ENNReal.ofReal_pow hz 2).symm
    _ = ENNReal.ofReal (∫ z, (g z)^2 ∂σ) :=
      (ofReal_integral_eq_lintegral_ofReal (Lp.memLp g).integrable_sq
        (Eventually.of_forall (fun z => sq_nonneg (g z)))).symm
    _ = ENNReal.ofReal (‖g‖^2) := by
      congr 1
      rw [← real_inner_self_eq_norm_sq g, L2.inner_def]
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by simp [pow_two])

lemma compactMeasureBarycenter_eq_withDensity
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) [CompactSpace S] (P : ProbabilityMeasure S)
    (g : Lp ℝ 2 σ)
    (hrep : ∀ f : Z →ᵇ ℝ,
      (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) =
        ∫ z, g z * f z ∂σ) :
    (∀ᵐ z ∂σ, 0 ≤ g z) ∧
      compactMeasureBarycenter P = σ.withDensity (fun z => ENNReal.ofReal (g z)) := by
  have hg : ∀ᵐ z ∂σ, 0 ≤ g z := by
    apply L2_nonneg_of_boundedContinuous_tests σ g
    intro f hf
    rw [← hrep f]
    exact integral_nonneg (fun v => integral_nonneg hf)
  refine ⟨hg,?_⟩
  let : IsFiniteMeasure (compactMeasureBarycenter P) := compactMeasureBarycenter_finite hS P
  have hgi : Integrable g σ := (Lp.memLp g).integrable (by norm_num)
  let : IsFiniteMeasure (σ.withDensity (fun z => ENNReal.ofReal (g z))) :=
    isFiniteMeasure_withDensity ((lintegral_ofReal_ne_top_iff_integrable
      (Lp.aestronglyMeasurable g) hg).mpr hgi)
  apply ext_of_forall_lintegral_eq_of_IsFiniteMeasure
  intro f
  apply (ENNReal.toReal_eq_toReal_iff'
    (BoundedContinuousFunction.lintegral_lt_top_of_nnreal (compactMeasureBarycenter P) f).ne
    (BoundedContinuousFunction.lintegral_lt_top_of_nnreal
      (σ.withDensity (fun z => ENNReal.ofReal (g z))) f).ne).mp
  rw [BoundedContinuousFunction.toReal_lintegral_coe_eq_integral,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral]
  let fR : Z →ᵇ ℝ := ⟨⟨fun z => (f z : ℝ), NNReal.continuous_coe.comp f.continuous⟩,
    f.map_bounded'⟩
  change (∫ z, fR z ∂compactMeasureBarycenter P) =
    ∫ z, fR z ∂σ.withDensity (fun z => ENNReal.ofReal (g z))
  rw [compactMeasureBarycenter_integral_nonneg P fR (fun z => (f z).coe_nonneg), hrep fR,
    integral_withDensity_eq_integral_toReal_smul (Lp.stronglyMeasurable g).measurable.ennreal_ofReal
      (Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hg] with z hz
  simp only [ENNReal.toReal_ofReal hz,smul_eq_mul]

lemma exists_compact_measure_density_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (P : ProbabilityMeasure S) (q : Z → ℝ≥0∞), Measurable q ∧
      compactMeasureBarycenter P = σ.withDensity q ∧
      (∫⁻ z, q z^2 ∂σ) ≤ ENNReal.ofReal (c⁻¹^2) := by
  obtain ⟨P,g,hgn,hrep⟩ := exists_compact_measure_L2_test_plan σ hS hne hz c hc hmod
  obtain ⟨hg,hbar⟩ := compactMeasureBarycenter_eq_withDensity σ hS P g hrep
  refine ⟨P,fun z => ENNReal.ofReal (g z), (Lp.stronglyMeasurable g).measurable.ennreal_ofReal,
    hbar,?_⟩
  rw [L2_ofReal_energy_eq σ g hg]
  apply ENNReal.ofReal_le_ofReal
  exact pow_le_pow_left₀ (norm_nonneg g) hgn 2

end CircleDomainRigidity

end

end OAI
