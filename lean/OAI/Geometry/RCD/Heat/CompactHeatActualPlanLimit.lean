import OAI.Geometry.RCD.Heat.CompactHeatLimitPlanIdentification
import OAI.Geometry.RCD.Heat.CompactHeatPreservedLawLimit
import OAI.Geometry.RCD.Transport.CalibratedRCDPlan

namespace OAI

/-! # One calibrated geodesic plan is the actual heat limit at every interior time -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X}
  {hn : 2 ≤ n} {p : X} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ε : ℕ → ℝ} {hε : ∀ k, 0 < ε k}
  (D : hX.CompactHeatScalingData hn p μ ν ε hε)
attribute [local instance] pathBorel pathBorelSpace

theorem exists_actual_heat_limit_plan (a₀ : S) (b₀ : T) (hK : K ≤ 0)
    (hε1 : ∀ k, ε k ≤ 1) (hε0 : Tendsto ε atTop (𝓝 0))
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ a:S, dist p a ≤ R) (hT : ∀ b:T, dist p b ≤ R) :
    ∃ (π : ProbabilityMeasure C(Time,X)) (j : ℕ → ℕ) (F : ℝ≥0∞) (A : ℝ),
      StrictMono j ∧ F ≠ ∞ ∧ (∀ᵐ γ ∂(π : Measure C(Time,X)), IsGeodesic γ) ∧
      IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
        ((π : Measure C(Time,X)).map (fun γ => (γ 0,γ 1))) ∧
      Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) (π : Measure C(Time,X)) ∧
      (∀ s : Time, (π.map (fun γ => γ s) : Measure X) ≤ F • hausdorff n X) ∧
      hX.CompactHeatConverges hn p μ D.left ε hε p (D.index ∘ j) D.forward.potential ∧
      hX.CompactHeatConverges hn p ν D.right ε hε p (D.index ∘ j) D.backward.potential ∧
      (∀ t : Ioo (0:ℝ) 1,
        Tendsto (fun k => D.interpolationLaw (D.index (j k)) t) atTop
          (𝓝 (π.map (fun γ => γ ⟨t,t.property.1.le,t.property.2.le⟩))) ∧
        ∀ f : X → ℝ, Integrable f (hausdorff n X) →
          Tendsto (fun k => ∫ x, D.interpolationDensity (D.index (j k)) t x*f x ∂hausdorff n X)
            atTop (𝓝 (∫ x, f x ∂(π.map (fun γ => γ ⟨t,t.property.1.le,t.property.2.le⟩) : Measure X)))) ∧
      ∀ᵐ γ ∂(π : Measure C(Time,X)), ∀ s : Time, 0 < (s:ℝ) → (s:ℝ) < 1 →
        D.forward.potential ((s:ℝ)/2) (γ s)=
          (D.backward.potential (1/2) a₀-D.backward.potential (1/2) (γ 0))-
            (s:ℝ)*dist (γ 0) (γ 1)^2-A := by
  let B : ℝ≥0∞ := (C₀:ℝ≥0∞)+(C₁:ℝ≥0∞)
  have hB : B ≠ ∞ := ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top,ENNReal.coe_ne_top⟩
  have hb₀ : μ.map Subtype.val ≤ B • hausdorff n X := by
    rw [hμ,← withDensity_const]
    apply withDensity_mono
    filter_upwards [hC₀] with x hx
    exact (ENNReal.ofReal_le_coe.mpr ((le_abs_self _).trans hx)).trans le_self_add
  have hb₁ : ν.map Subtype.val ≤ B • hausdorff n X := by
    rw [hν,← withDensity_const]
    apply withDensity_mono
    filter_upwards [hC₁] with x hx
    exact (ENNReal.ofReal_le_coe.mpr ((le_abs_self _).trans hx)).trans le_add_self
  obtain ⟨π,A,hπ,hg,hopt,hlen,hcomp,hcal⟩ := D.exists_calibrated_plan a₀ b₀ hK hε1 hε0
    (zero_le_one.trans hR) hS hT hB hb₀ hb₁
  let := hπ
  obtain ⟨M,Q,j,_hM,hj,_hQ,hfor,hback,hlim⟩ := D.preserved_action_law_limit hK hε1
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT
  let F := compressionBudget K n (2*R) B
  have hF : F ≠ ∞ := compressionBudget_ne_top K n (2*R) hB
  let plan : ProbabilityMeasure (ContinuousMap Time X) := ⟨π,hπ⟩
  refine ⟨plan,j,F,A,hj,hF,hg,hopt,hlen,hcomp,hfor,hback,?_,hcal⟩
  intro t
  have he := D.interpolation_limit_eq_compressed_plan a₀ b₀ hK hε1 hε0
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT t j hj (Q t)
    (hlim t).1 ENNReal.ofReal_ne_top (hlim t).2.1 π hg hopt hF hcomp
  have he' : Q t=ProbabilityMeasure.map plan
      (fun (γ : ContinuousMap Time X) => γ (⟨t,t.property.1.le,t.property.2.le⟩ : Time)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact he
  refine ⟨he' ▸ (hlim t).1,?_⟩
  intro f hf
  have hh := (hlim t).2.2 f hf
  rwa [he'] at hh

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
