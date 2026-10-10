import OAI.Geometry.RCD.Sobolev.RadialSobolevTimeMeasurable
import OAI.Geometry.RCD.Sobolev.RadialLocalSobolevLimit

namespace OAI

/-! # A measurable local Sobolev limit outside one time null set -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X Y : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
  (Q : QuadraticCheegerEnergy μ) [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)]
  [TopologicalSpace Y] [FirstCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y]

theorem radial_sobolev_measurable_limit (ν : Measure Y) (Z : Set Y)
    (hZ : ∀ᵐ t ∂ν, t ∈ Z) (z : X) {r : ℝ} (hr : 0 < r)
    (H : ℕ → Y → X → ℝ) (g : Y → X → ℝ) (L A : ℝ≥0)
    (hHl : ∀ k t, LipschitzOnWith L (H k t) (closedBall z (2*r)))
    (hHb : ∀ k t, ∀ x ∈ closedBall z (2*r), |H k t x| ≤ A)
    (hHc : ∀ k, ∀ x ∈ closedBall z (2*r), Continuous (fun t => H k t x))
    (hgl : ∀ t ∈ Z, LipschitzOnWith L (g t) (closedBall z (2*r)))
    (hgb : ∀ t ∈ Z, ∀ x ∈ closedBall z (2*r), |g t x| ≤ A)
    (hconv : ∀ t ∈ Z, ∀ x ∈ closedBall z (2*r),
      Tendsto (fun k => H k t x) atTop (𝓝 (g t x))) :
    ∃ (u : ℕ → Y → SobolevSpace μ Q) (v : Y → SobolevSpace μ Q) (C : ℝ),
      0 ≤ C ∧ (∀ k, StronglyMeasurable (u k)) ∧ AEStronglyMeasurable v ν ∧
      (∀ k t, ‖u k t‖ ≤ C) ∧ (∀ t, ‖v t‖ ≤ C) ∧
      (∀ k t, SobolevSpace.toLp μ Q (u k t) =ᵐ[μ] fun x => radialCutoff z r x*H k t x) ∧
      (∀ t ∈ Z, SobolevSpace.toLp μ Q (v t) =ᵐ[μ] fun x => radialCutoff z r x*g t x) ∧
      (∀ᵐ t ∂ν, Tendsto (fun k => SobolevSpace.toLp μ Q (u k t)) atTop
        (𝓝 (SobolevSpace.toLp μ Q (v t)))) := by
  classical
  let u := fun k t => radialLocalSobolev μ Q z hr (hHl k t) (hHb k t)
  let v := fun t => if ht : t ∈ Z then radialLocalSobolev μ Q z hr (hgl t ht) (hgb t ht) else 0
  have hu (k : ℕ) : StronglyMeasurable (u k) :=
    radialLocalSobolev_stronglyMeasurable μ Q z hr (H k) L A (hHl k) (hHb k) (hHc k)
  have hc : ∀ᵐ t ∂ν, Tendsto (fun k => SobolevSpace.toLp μ Q (u k t)) atTop
      (𝓝 (SobolevSpace.toLp μ Q (v t))) := by
    filter_upwards [hZ] with t ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact radialLocalSobolev_L2_limit μ Q z hr (fun k => H k t) (g t) L A
      (fun k => hHl k t) (hgl t ht) (fun k => hHb k t) (hgb t ht) (hconv t ht)
  obtain ⟨C,hC,hbound⟩ := radialLocalSobolev_uniform_bound μ Q z hr L A
  refine ⟨u,v,C,hC,hu,sobolev_limit_aestronglyMeasurable μ Q ν u v
    (fun k => (hu k).aestronglyMeasurable) hc,fun k t => hbound _ (hHl k t) (hHb k t),?_,
    fun k t => radialLocalSobolev_coe μ Q z hr (hHl k t) (hHb k t),?_,hc⟩
  · intro t
    by_cases ht : t ∈ Z
    · simpa only [v,dite_eq_left ht] using hbound _ (hgl t ht) (hgb t ht)
    · simpa only [v,dite_eq_right ht,norm_zero] using hC
  · intro t ht
    dsimp only [v]
    rw [dite_eq_left ht]
    exact radialLocalSobolev_coe μ Q z hr (hgl t ht) (hgb t ht)

end RegularPointCoordinates

end

end OAI
