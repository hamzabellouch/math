import OAI.Geometry.RCD.Heat.LocalScaledLogSource

namespace OAI

/-! # Global identification from compact local logarithmic sources -/

open Set Filter MeasureTheory Metric
open scoped NNReal BoundedContinuousFunction
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] [SecondCountableTopology X] (μ : Measure X)
  [IsFiniteMeasureOnCompacts μ] (Q : QuadraticCheegerEnergy μ)

theorem global_scaled_log_source_lower (p : X) (u : SobolevSpace μ Q) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ Q u d) (U : X → ℝ) (hU : Continuous U)
    (hu : SobolevSpace.toLp μ Q u =ᵐ[μ] U) (hp : ∀ x, 0 < U x)
    (A L : ℝ≥0) (hA : ∀ x, |U x| ≤ A)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ Q u x ≤ L)
    (κ : ℝ) (B : X → ℝ)
    (hlocal : ∀ Ω : Set X, IsCompact Ω →
      ∃ (w : SobolevSpace μ Q) (q : Lp ℝ 2 μ), IsWeakLaplacian μ Q w q ∧
        (SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω] fun x => κ*Real.log (U x)) ∧
        ∀ᵐ x ∂μ.restrict Ω, B x ≤ q x) :
    ∀ᵐ x ∂μ, B x ≤ κ*(d x/U x-localGamma μ Q u u x/(U x)^2) := by
  suffices hball : ∀ k : ℕ, ∀ᵐ x ∂μ.restrict (ball p ((k:ℝ)+1)),
      B x ≤ κ*(d x/U x-localGamma μ Q u u x/(U x)^2) by
    have hfull := (ae_restrict_iUnion_iff _ _).mpr hball
    rwa [iUnion_ball_nat_succ,Measure.restrict_univ] at hfull
  intro k
  let r : ℝ := (k:ℝ)+1
  have hr : 0 < r := by dsimp only [r]; positivity
  let Ω := closedBall p (2*r)
  have hΩ : IsCompact Ω := isCompact_closedBall _ _
  have hSΩ : ball p r ⊆ Ω := ball_subset_closedBall.trans
    (closedBall_subset_closedBall (by linarith))
  obtain ⟨a,ha,haU⟩ := hΩ.exists_forall_le' hU.continuousOn (fun x _ => hp x)
  have hv : ∀ᵐ x ∂μ.restrict Ω, SobolevSpace.toLp μ Q u x ∈ Icc a (max a A) := by
    filter_upwards [ae_restrict_of_ae hu,ae_restrict_mem hΩ.measurableSet] with x hx hmem
    rw [hx]
    exact ⟨haU x hmem,((le_abs_self _).trans (hA x)).trans (le_max_right _ _)⟩
  obtain ⟨w,q,hq,hw,hbound⟩ := hlocal Ω hΩ
  have hw' : SobolevSpace.toLp μ Q w =ᵐ[μ.restrict Ω]
      fun x => κ*Real.log (SobolevSpace.toLp μ Q u x) := by
    filter_upwards [hw,ae_restrict_of_ae hu] with x hx hy
    rw [hx,hy]
  let χ : X →ᵇ ℝ := ofCompactSupport (radialCutoff p r)
    (radialCutoff_lipschitz p hr).continuous (radialCutoff_hasCompactSupport p hr)
  have hχΩ : tsupport (χ : X → ℝ) ⊆ Ω := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    by_contra hm
    have hz := radialCutoff_eq_zero p hr (le_of_not_ge (by
      simpa only [Ω,mem_closedBall,dist_comm] using hm))
    exact hx hz
  have heq := local_scaled_log_source μ Q hΩ measurableSet_ball hSΩ u w d q hd hq
    L hL ha (le_max_left _ _) hv κ hw' χ (radialCutoff_lipschitz p hr)
    (radialCutoff_hasCompactSupport p hr) hχΩ
    (fun x => (radialCutoff_bounds p r x).1)
    (fun x hx => radialCutoff_eq_one p hr
      (show dist p x < r by simpa only [mem_ball,dist_comm] using hx).le)
  filter_upwards [heq,ae_restrict_of_ae_restrict_of_subset hSΩ hbound,
    ae_restrict_of_ae hu] with x hx hy hz
  rw [hx,hz] at hy
  exact hy

end RegularPointCoordinates

end

end OAI
