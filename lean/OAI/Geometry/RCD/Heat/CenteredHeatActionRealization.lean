import OAI.Geometry.RCD.Heat.SmallNoiseActionLipschitz
import OAI.Geometry.RCD.Harmonic.CenteredCompactDirection

namespace OAI

/-! # Compact centered action directions with scale-sensitive bounds -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem centered_heat_action_realization :
    ∃ D : ℝ, 0 < D ∧
      ∀ {S : Set X} [CompactSpace S] (ν : Measure S) [IsProbabilityMeasure ν]
      (ρ : X → ℝ) (_hρ : Measurable ρ) (_hρ0 : ∀ x, 0 ≤ ρ x) {B : ℝ≥0},
      (∀ᵐ x ∂hausdorff n X, |ρ x| ≤ B) →
      ν.map Subtype.val=(hausdorff n X).withDensity (fun x => ENNReal.ofReal (ρ x)) →
      ∀ (F : ℕ → C(S,ℝ)), (∀ k y, 0 < F k y) →
      ∀ (ε : ℕ → ℝ) (hε : ∀ k, 0 < ε k), (∀ k, ε k ≤ 1) →
      Tendsto ε atTop (𝓝 0) →
      ∀ (z : X) (ι : ℕ → ℕ) (H : ℝ → X → ℝ), Tendsto ι atTop atTop →
      hX.CompactHeatConverges hn p ν F ε hε z ι H →
      ∀ {R r δ : ℝ}, 0 ≤ R → (∀ y:S, dist z y ≤ R) → 0 < r → 0 < δ →
      ∀ t∈Ioo δ 1,
      let L : ℝ≥0 := ⟨Real.sqrt (Real.exp |K| * (16*D*(R+32*r)^2/δ^2)),Real.sqrt_nonneg _⟩
      ∃ (v : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ),
        LipschitzWith (3*L) V ∧ HasCompactSupport V ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V) ∧
        (∀ x, |V x| ≤ 2*r*(L:ℝ)) ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic v
          =ᵐ[(hausdorff n X).restrict (closedBall z r)] fun x => H t x-H t z) := by
  obtain ⟨D,hD,hLip⟩ := hX.small_noise_action_lipschitz hn p
  refine ⟨D,hD,?_⟩
  intro S _ ν _ ρ hρ hρ0 B hB hν F hF ε hε hε1 hε0 z ι H hι hconv R r δ hR hdist hr hδ t ht
  have hh := hLip ν ρ hρ hρ0 hB hν F hF ε hε hε1 hε0 z ι H hι hconv
    hR hdist (show 0 < 2*r by positivity) hδ t ht
  rw [show R+16*(2*r)=R+32*r by ring] at hh
  exact centered_compact_direction (hausdorff n X) hX.quadratic z hr (H t) _ hh

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
