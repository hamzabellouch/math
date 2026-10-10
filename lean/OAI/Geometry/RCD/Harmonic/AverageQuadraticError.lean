import OAI.Analysis.RCDHeat.ExistingAnalytic

namespace OAI

/-! # Passing an additive transport error from averages to continuous values -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {μ : Measure X} [IsLocallyFiniteMeasure μ]
  [IsUnifLocDoublingMeasure μ] [μ.IsOpenPosMeasure]

theorem quadratic_comparison_of_average_bound_add
    (u v U V : X → ℝ) (hu : LocallyIntegrable u μ) (hv : LocallyIntegrable v μ)
    (hU : Continuous U) (hV : Continuous V) (heU : u =ᵐ[μ] U) (heV : v =ᵐ[μ] V)
    (c e : ℝ) (h : ∀ x y : X, ∀ r : ℝ, 0 < r →
      (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
        c*(dist x y + 2*r)^2+e) :
    ∀ x y, U x-V y ≤ c*dist x y^2+e := by
  let S := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, u z ∂μ)
    (𝓝[>] 0) (𝓝 (U x))}
  let T := {x : X | Tendsto (fun r : ℝ => ⨍z in closedBall x r, v z ∂μ)
    (𝓝[>] 0) (𝓝 (V x))}
  have hS : ∀ᵐ x ∂μ, x ∈ S := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hu (1:ℝ),heU] with x hx he
    change Tendsto _ _ (𝓝 (U x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hT : ∀ᵐ x ∂μ, x ∈ T := by
    filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average μ hv (1:ℝ),heV] with x hx he
    change Tendsto _ _ (𝓝 (V x))
    rw [←he]
    exact hx (fun _ : ℝ => x) id tendsto_id (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      simp only [mem_closedBall,dist_self,one_mul]
      exact le_of_lt hr)
  have hST : ∀ x ∈ S, ∀ y ∈ T, U x-V y ≤ c*dist x y^2+e := by
    intro x hx y hy
    have hc : Tendsto (fun r : ℝ => c*(dist x y+2*r)^2+e) (𝓝[>] 0)
        (𝓝 (c*dist x y^2+e)) := by
      have hh : Continuous (fun r : ℝ => c*(dist x y+2*r)^2+e) := by fun_prop
      simpa using (hh.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    have hb : ∀ᶠ r in 𝓝[>] (0:ℝ),
        (⨍z in closedBall x r, u z ∂μ) - (⨍z in closedBall y r, v z ∂μ) ≤
          c*(dist x y+2*r)^2+e := by
      filter_upwards [self_mem_nhdsWithin] with r hr using h x y r hr
    exact le_of_tendsto_of_tendsto (hx.sub hy) hc hb
  have hd : Dense (S ×ˢ T) := (Measure.dense_of_ae hS).prod (Measure.dense_of_ae hT)
  have hc : IsClosed {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2+e} :=
    isClosed_le ((hU.comp continuous_fst).sub (hV.comp continuous_snd)) (by fun_prop)
  have hs : closure (S ×ˢ T) ⊆ {z : X×X | U z.1-V z.2 ≤ c*dist z.1 z.2^2+e} :=
    hc.closure_subset_iff.mpr (fun z hz => hST z.1 hz.1 z.2 hz.2)
  intro x y
  exact hs (hd (x,y))

end RegularPointCoordinates

end OAI
