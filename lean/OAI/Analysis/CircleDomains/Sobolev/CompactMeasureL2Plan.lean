import OAI.Analysis.CircleDomains.Probability.CompactMeasureSeparation
import OAI.Analysis.CircleDomains.Sobolev.BoundedContinuousL2Dual

namespace OAI

/-! The compact-family plan has an actual L² representing function on
bounded continuous tests. Positivity and Borel-set barycenter identities
are established separately from this linear representation step. -/
open Set Filter MeasureTheory
open scoped CompactlySupported BoundedContinuousFunction ENNReal
noncomputable section
namespace CircleDomainRigidity

local instance : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

lemma exists_compact_measure_L2_test_plan
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (σ : Measure Z) [IsFiniteMeasure σ] {S : Set (FiniteMeasure Z)}
    (hS : IsCompact S) (hne : S.Nonempty) (hz : (0 : FiniteMeasure Z) ∉ S)
    [CompactSpace S] (c : ℝ) (hc : 0 < c)
    (hmod : ENNReal.ofReal (c^2) < measureFamilyModulus S Z σ (fun v => v.val)) :
    ∃ (P : ProbabilityMeasure S) (g : Lp ℝ 2 σ), ‖g‖ ≤ c⁻¹ ∧
      ∀ f : Z →ᵇ ℝ,
        (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) =
          ∫ z, g z * f z ∂σ := by
  obtain ⟨P,hP⟩ := exists_compact_measure_test_plan σ hS hne hz c hc hmod
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
    have hb := mul_le_mul_of_nonneg_left (hP f) (inv_nonneg.mpr hc.le)
    change (∫ v : S, (∫ z, f z ∂(v.val : Measure Z)) ∂(P : Measure S)) ≤ _
    simpa only [← mul_assoc,inv_mul_cancel₀ hc.ne',one_mul] using hb
  obtain ⟨g,hg,hrep⟩ := exists_L2_pairing_of_boundedContinuous_bound σ F
    (inv_nonneg.mpr hc.le) hF
  exact ⟨P,g,hg,fun f => (hrep f).symm⟩

end CircleDomainRigidity

end

end OAI
