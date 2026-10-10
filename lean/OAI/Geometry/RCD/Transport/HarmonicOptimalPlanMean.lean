import OAI.Geometry.RCD.Transport.CompactHarmonicAffinePlan
import OAI.Geometry.RCD.Transport.CompressedFiniteUnique

namespace OAI

/-! # Original harmonic-coordinate means on every compressed optimal plan -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {n : ℕ} (hX : NoncollapsedRCD 0 n X) (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {S T : Set X} [CompactSpace S] [CompactSpace T]
  {μ : Measure S} {ν : Measure T} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
attribute [local instance] pathBorel pathBorelSpace

include hn in
theorem compact_harmonic_mean_on_optimal_plan (a₀ : S) (b₀ : T)
    (ρ₀ ρ₁ : X → ℝ) (hm₀ : Measurable ρ₀) (hm₁ : Measurable ρ₁)
    (hp₀ : ∀ x, 0 ≤ ρ₀ x) (hp₁ : ∀ x, 0 ≤ ρ₁ x) {C₀ C₁ : ℝ≥0}
    (hC₀ : ∀ᵐ x ∂hausdorff n X, |ρ₀ x| ≤ C₀)
    (hC₁ : ∀ᵐ x ∂hausdorff n X, |ρ₁ x| ≤ C₁)
    (hμ : μ.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₀ x)))
    (hν : ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ₁ x)))
    {R : ℝ} (hR : 1 ≤ R) (hS : ∀ y:S, dist p y ≤ R) (hT : ∀ y:T, dist p y ≤ R)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))))
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hcomp : ∀ t : Time, π.map (fun γ => γ t) ≤ C • hausdorff n X)
    (u : SobolevSpace (hausdorff n X) hX.quadratic) (d : Lp ℝ 2 (hausdorff n X))
    (hd : IsWeakLaplacian (hausdorff n X) hX.quadratic u d)
    (U : X → ℝ) (L A : ℝ≥0) (hU : LipschitzWith L U) (hUc : HasCompactSupport U)
    (hu : SobolevSpace.toLp (hausdorff n X) hX.quadratic u =ᵐ[hausdorff n X] U)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic u x| ≤ A)
    {b : ℝ} (hb : 24*R < b)
    (hd0 : d =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => 0) (c : ℝ)
    (hc : localGamma (hausdorff n X) hX.quadratic u u
      =ᵐ[(hausdorff n X).restrict (ball p b)] fun _ => c) :
    ∀ t : Time, (∫ γ, U (γ t) ∂π) =
      (1-(t:ℝ))*(∫ x : S, U x ∂μ)+(t:ℝ)*(∫ x : T, U x ∂ν) := by
  have he1 (k : ℕ) : heatStep k ≤ 1 := by
    unfold heatStep
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨D⟩ := hX.exists_compact_heat_scaling_data hn p le_rfl a₀ b₀ μ ν
    ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν heatStep heatStep_pos he1 heatStep_tendsto
    (zero_le_one.trans hR) hS hT
  obtain ⟨ρ,B,hB,hgρ,hpρ,hcρ,haff⟩ := D.exists_original_harmonic_affine_plan a₀ b₀
    he1 heatStep_tendsto ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁ hC₀ hC₁ hμ hν hR hS hT
  have hs₀ : ∀ᵐ x ∂μ.map Subtype.val, dist x p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hS y
  have hs₁ : ∀ᵐ x ∂ν.map Subtype.val, dist x p ≤ R := by
    apply (ae_map_iff measurable_subtype_coe.aemeasurable
      (measurableSet_le (by fun_prop) measurable_const)).mpr
    exact Eventually.of_forall fun y => by simpa only [dist_comm] using hT y
  have heq := hX.compressed_plan_unique_finite hn p (zero_le_one.trans hR)
    π (ρ : Measure C(Time,X)) hgeo hgρ hopt hpρ hC hB hcomp hcρ hs₀ hs₁
  intro t
  rw [heq,← integral_map (measurable_path_eval t).aemeasurable hU.continuous.aestronglyMeasurable]
  exact haff u d hd U L A hU hUc hu hA hb hd0 c hc t

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
