import OAI.Analysis.CircleDomains.Probability.CompactMeasureDensity

namespace OAI

/-! A compact plan satisfying the continuous L² test bound has the actual
Borel barycenter density with the same norm bound. -/
open Set Filter MeasureTheory
open scoped BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma compact_plan_density_of_test_bound
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) [CompactSpace S] (P : ProbabilityMeasure S)
    {c : ℝ} (hc : 0 < c)
    (htest : ∀ f : Z →ᵇ ℝ,
      c * (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤
        ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖) :
    ∃ q : Z → ℝ≥0∞, Measurable q ∧ compactMeasureBarycenter P = σ.withDensity q ∧
      (∫⁻ z, q z^2 ∂σ) ≤ ENNReal.ofReal (c⁻¹^2) := by
  have hI (f : Z →ᵇ ℝ) : Integrable
      (fun v : S => compactMeasureTestOperator S f v) (P : Measure S) := by
    apply (integrable_const ‖compactMeasureTestOperator S f‖).mono'
      ((measurable_finiteMeasure_integral f).comp measurable_subtype_coe).aestronglyMeasurable
    exact Eventually.of_forall (fun v => (compactMeasureTestOperator S f).norm_coe_le_norm v)
  let F : (Z →ᵇ ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => ∫ v : S, compactMeasureTestOperator S f v ∂(P : Measure S)
      map_add' := by
        intro f g
        simp only [map_add,ContinuousMap.add_apply]
        exact integral_add (hI f) (hI g)
      map_smul' := by
        intro r f
        simp only [map_smul,ContinuousMap.smul_apply,smul_eq_mul]
        exact integral_const_mul r _ }
  have hF (f : Z →ᵇ ℝ) : F f ≤ c⁻¹ * ‖BoundedContinuousFunction.toLp 2 σ ℝ f‖ := by
    have hb := mul_le_mul_of_nonneg_left (htest f) (inv_nonneg.mpr hc.le)
    change (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤ _
    simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hb
  obtain ⟨g,hg,hrep⟩ := exists_L2_pairing_of_boundedContinuous_bound σ F
    (inv_nonneg.mpr hc.le) hF
  obtain ⟨hg0,hbar⟩ := compactMeasureBarycenter_eq_withDensity σ hS P g (fun f => (hrep f).symm)
  refine ⟨fun z => ENNReal.ofReal (g z), (Lp.stronglyMeasurable g).measurable.ennreal_ofReal,
    hbar,?_⟩
  rw [L2_ofReal_energy_eq σ g hg0]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg g) hg 2)

end CircleDomainRigidity

end

end OAI
