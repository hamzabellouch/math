import Mathlib
import OAI.Geometry.TamingCompatibility.Concentration.PhysicalConcentrationDensity
import OAI.Geometry.TamingCompatibility.Concentration.ConcentrationGlobalError
import OAI.Geometry.TamingCompatibility.DifferentialForms.ScalarBoundaryIntegrals
import OAI.Geometry.TamingCompatibility.Charts.ManifoldBoundaryBounds

namespace OAI

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
  (D : ∀ p : A.centers, HodgeChart.Data J α ht p.val)
  (hD : ∀ p, tsupport (A.partition p) ⊆ (D p).source)
  (G : ∀ p : A.centers, GeometricChart.Data J α ht p.val)
  (hG : ∀ p, tsupport (A.partition p) ⊆ (G p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable

structure ConcentrationActivationData
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) (Q : L2 A J α hs ht true) where
  radius : ℕ → ℝ
  radius_pos : ∀ n, 0 < radius n
  radius_le : ∀ n, radius n ≤ 1
  radius_limit : Tendsto radius atTop (𝓝 0)
  cutoff : ℕ → X → ℝ
  nonneg : ∀ n x, 0 ≤ cutoff n x
  smooth : ∀ n, ContMDiff Model 𝓘(ℝ,ℝ) ∞ (cutoff n)
  null : geometricVolume A J α (exceptional cutoff) = 0
  density_zero : ∀ x ∉ exceptional cutoff,
    Tendsto (fun n => globalConcentration A J α hs ht E μ (radius n) x) atTop (𝓝 0)
  unit_boundary : ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    (∫ u : MetricUnit (hermitianMetric J α hs ht),
      |eval (ManifoldForms.wedgeOne (scalarDifferential (cutoff n)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)| ∂μ) ≤ C*stepSize n
  Q_boundary : ∀ θ : smoothForms X 1, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
    (∫ x, ‖l2Coefficients A J α hs ht E hE Q x‖ *
      ‖normalizedFrameEncode A J α ht E x
        (ManifoldForms.wedgeOne (scalarDifferential (cutoff n)) θ.val x)‖ ∂geometricVolume A J α) ≤ C*stepSize n

include hE hD hG in
lemma concentrationActivationData_nonempty
    (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0)
    (Q : L2 A J α hs ht true)
    (hT : ∀ a : smoothForms X 2, IsClosed a.val →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ a + ⟪Q,smoothL2 A J α hs ht true a⟫ = 0) :
    Nonempty (ConcentrationActivationData A J α hs ht E hE μ Q) := by
  obtain ⟨eP,heP,hiP,h0P,hbP⟩ := globalConcentration_current_control A J α hs ht E hE D hD G hG μ hann Q hT
  obtain ⟨eQ,heQ,hiQ,h0Q,hbQ⟩ := globalConcentration_Q_control A J α hs ht E hE μ hann Q
  obtain ⟨r,hr,hr0,hrb⟩ := exists_activation_scales
    (fun r => ∫ u, eP r u ∂μ) (fun r => ∫ x, eQ r x ∂geometricVolume A J α)
    (fun r => ∫ x, globalConcentration A J α hs ht E μ r x ∂geometricVolume A J α)
    h0P h0Q (globalConcentration_volume_limit A J α hs ht E hE μ)
  let f := fun n => globalConcentration A J α hs ht E μ (r n)
  have hf (n) := globalConcentration_smooth A J α hs ht E μ (hr n).1
  have hfn (n) := globalConcentration_nonneg A J α hs ht E μ (r n)
  let c := fun n x => logActivation (stepSize n) (thresholdScale n) (f n x)
  have hc (n) : ContMDiff Model 𝓘(ℝ,ℝ) ∞ (c n) := contMDiff_logActivation (hf n) (thresholdScale_pos n) (hfn n)
  have hcn (n) (x) : 0 ≤ c n x := logActivation_nonneg (stepSize_pos n).le (thresholdScale_pos n) (hfn n x)
  let := geometricVolume_finite A J α hs ht
  have hci (n) : Integrable (c n) (geometricVolume A J α) :=
    (hc n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcv (n) : (∫ x, c n x ∂geometricVolume A J α) ≤ stepSize n := by
    apply (logActivation_integral_bound (geometricVolume A J α) (f n) _ _ (stepSize_pos n).le
      (thresholdScale_pos n) (hfn n) (globalConcentration_integrable A J α hs ht E μ (hr n).1) (hci n)).trans
    have hh := mul_le_mul_of_nonneg_left (hrb n).2.2
      (div_nonneg (stepSize_pos n).le (thresholdScale_pos n).le)
    simpa only [div_mul_cancel₀ _ (thresholdScale_pos n).ne'] using hh
  refine ⟨⟨r,fun n => (hr n).1,fun n => (hr n).2,hr0,c,hcn,hc,
    exceptional_null_of_integrals c hcn (fun n => (hc n).continuous.measurable)
      (geometricVolume A J α) hci stepSize summable_stepSize hcv,?_,?_,?_⟩⟩
  · intro x hx
    have hsum : Summable (fun n => c n x) := not_not.mp hx
    exact tendsto_of_summable_activation hsum (fun n => hfn n x) tendsto_stepSize
      (fun n hn => logActivation_step_threshold n hn)
  · intro θ
    obtain ⟨C,hC,hb⟩ := hbP θ
    refine ⟨2*C,by positivity,fun n => ?_⟩
    apply activation_boundary_integral μ (fun u => f n u.val.proj) (eP (r n))
      (fun u => |eval (ManifoldForms.wedgeOne (scalarDifferential (c n)) θ.val)
        u.val.proj u.val.2 (J.endomorphism u.val.proj u.val.2)|)
      (stepSize n) (thresholdScale n) C (stepSize_pos n).le (thresholdScale_pos n) hC
      (fun u => hfn n u.val.proj) (heP _ (hr n).1) (hiP _ (hr n).1) (hrb n).1
      (unit_boundary_integrable J α hs ht μ (c n) (hc n) θ)
    intro u
    rw [show c n = fun x => logActivation (stepSize n) (thresholdScale n) (f n x) from rfl,
      log_boundary_eval J _ ((hf n).mdifferentiable (by simp)) (hfn n) (stepSize_pos n).le (thresholdScale_pos n)]
    exact mul_le_mul_of_nonneg_left (hb _ (hr n).1 u) (div_nonneg (stepSize_pos n).le (add_nonneg (thresholdScale_pos n).le (hfn n u.val.proj)))
  · intro θ
    obtain ⟨C,hC,hb⟩ := hbQ θ
    refine ⟨C,hC,fun n => ?_⟩
    apply activation_error_integral (geometricVolume A J α) (f n) (eQ (r n))
      (fun x => ‖l2Coefficients A J α hs ht E hE Q x‖ *
        ‖normalizedFrameEncode A J α ht E x (ManifoldForms.wedgeOne (scalarDifferential (c n)) θ.val x)‖)
      (stepSize n) (thresholdScale n) C (stepSize_pos n).le (thresholdScale_pos n) hC
      (hfn n) (heQ _ (hr n).1) (hiQ _ (hr n).1) (hrb n).2.1
      (coefficient_boundary_integrable A J α hs ht E hE Q (c n) (hc n) θ)
    intro x
    rw [show c n = fun x => logActivation (stepSize n) (thresholdScale n) (f n x) from rfl,
      log_boundary_norm A J α ht E _ ((hf n).mdifferentiable (by simp)) (hfn n) (stepSize_pos n).le (thresholdScale_pos n)]
    have hh := mul_le_mul_of_nonneg_left (hb _ (hr n).1 (hr n).2 x)
      (div_nonneg (stepSize_pos n).le (add_nonneg (thresholdScale_pos n).le (hfn n x)))
    nlinarith
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

section

noncomputable section
namespace TamingCompatibility.GeometricHilbert.GeometricNormalCharts
open Bundle ManifoldForms ManifoldHodge ManifoldLocalization ManifoldVolume Set _root_.MeasureTheory _root_.OAI.MeasureTheory Filter SummableCutoff
open scoped Manifold ContDiff RealInnerProductSpace Topology ENNReal
variable {X : Type*} [TopologicalSpace X] [ChartedSpace Space X] [IsManifold Model ∞ X]
  [T2Space X] [CompactSpace X] [ConnectedSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
variable (A : FiniteCharts X) (J : AlmostComplexStructure X) (α : TwoForm X)
  (hs : IsSmooth α) (ht : Tames α J)
  (E : ∀ p : A.centers, ParametrixData J α ht p.val)
  (hE : ∀ p, tsupport (A.partition p) ⊆ (E p).source)
attribute [local instance] unitMeasurable unitBorel unitT2 unitSecondCountable
variable (μ : Measure (MetricUnit (hermitianMetric J α hs ht))) [IsProbabilityMeasure μ]
  (Q : L2 A J α hs ht true) (S : ConcentrationActivationData A J α hs ht E hE μ Q)

omit [SecondCountableTopology X] in
lemma concentration_physical_tail (x : X) (hx : x ∉ exceptional S.cutoff) :
    Tendsto (fun n => physicalProfileMass J α hs ht μ (S.radius n) x/(S.radius n)^2)
      atTop (𝓝 0) := by
  obtain ⟨C,B,hC,hB,hbound⟩ := physicalProfile_globalConcentration A J α hs ht E hE μ
  have hl : Tendsto (fun n => C*globalConcentration A J α hs ht E μ (S.radius n) x+B*(S.radius n)^4)
      atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (4:ℕ) ≠ 0),add_zero] using
      ((S.density_zero x hx).const_mul C).add ((S.radius_limit.pow 4).const_mul B)
  apply squeeze_zero (fun n => div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ x) (sq_nonneg _)) _ hl
  intro n
  simpa only [one_div,mul_comm _ (physicalProfileMass J α hs ht μ _ x),←div_eq_mul_inv] using
    hbound x (S.radius n) (S.radius_pos n)

lemma concentration_double_physical_tail
    (hann : ∀ β : smoothForms X 2, IsClosed β.val → IsInvariant β.val J →
      unitMeasureCurrent J (hermitianMetric J α hs ht) μ β = 0) :
    let ν := μ.restrict ((fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ)
    Tendsto (fun n => ∫ v, physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2 ∂ν)
      atTop (𝓝 0) := by
  dsimp only
  let Z := (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) ⁻¹' (exceptional S.cutoff)ᶜ
  let ν := μ.restrict Z
  have hp : Continuous (fun u : MetricUnit (hermitianMetric J α hs ht) => u.val.proj) :=
    (FiberBundle.continuous_proj Space (TangentSpace Model : X → Type)).comp continuous_subtype_val
  have hZ : MeasurableSet Z :=
    (measurable_exceptional S.cutoff S.nonneg (fun n => (S.smooth n).continuous.measurable)).compl.preimage hp.measurable
  obtain ⟨C,hC,hbound⟩ := separating_probability_real_shell J α hs ht μ hann
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun v : MetricUnit (hermitianMetric J α hs ht) => physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2) ν :=
    ((hermitian_real_shell_measurable J α hs ht μ (S.radius n)).comp hp.measurable).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ v ∂ν,
      ‖physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2‖ ≤ C := by
    apply Eventually.of_forall
    intro v
    rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg (physicalProfileMass_nonneg J α hs ht μ _ _) (sq_nonneg _))]
    exact hbound v.val.proj (S.radius n) (S.radius_pos n)
  have hl : ∀ᵐ v ∂ν, Tendsto (fun n => physicalProfileMass J α hs ht μ (S.radius n) v.val.proj/(S.radius n)^2)
      atTop (𝓝 (0:ℝ)) := by
    filter_upwards [ae_restrict_mem hZ] with v hv
    exact concentration_physical_tail A J α hs ht E hE μ Q S v.val.proj hv
  simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ => C) hm
    (integrable_const C) hb hl
end TamingCompatibility.GeometricHilbert.GeometricNormalCharts

end
end

end OAI
