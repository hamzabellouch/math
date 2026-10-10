import OAI.Geometry.RCD.Heat.CompactHeatDensityGaussianTail
import OAI.Geometry.RCD.Heat.GaussianDensityTailMoments

namespace OAI

/-! # Uniform tail moments of the original compact heat interpolation -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal
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

theorem interpolationDensity_tail_moments (hε1 : ∀ k, ε k ≤ 1)
    (z : X) {R : ℝ} (hR : 1 ≤ R)
    (hS : ∀ a : S, dist z a ≤ R) (hT : ∀ b : T, dist z b ≤ R) :
    ∃ L : ℝ, 0 < L ∧ ∀ (k : ℕ) (t : Ioo (0:ℝ) 1) (q : ℕ), 2 ≤ q →
      IntegrableOn (fun x => (D.interpolationDensity k t x)^q*(dist x z)^2)
        (ball z L)ᶜ (hausdorff n X) ∧
      (∫ x in (ball z L)ᶜ, (D.interpolationDensity k t x)^q*(dist x z)^2
        ∂hausdorff n X) ≤ 1 := by
  obtain ⟨B,L,hB,_hL,htail⟩ := D.interpolationDensity_gaussian_tail hε1 z hR hS hT
  obtain ⟨V,A,hV,hA,hvol⟩ := hX.exponential_volume K n hn z
  have hG : Integrable (fun x => Real.exp (-(dist x z)^2/40)*(dist x z)^2)
      (hausdorff n X) := by
    have he : (fun x => Real.exp (-(dist x z)^2/40)*(dist x z)^2) =
        (fun x => Real.exp (-((1:ℝ)/40)*(dist z x)^2)*(dist z x)^2) := by
      funext x
      rw [dist_comm x z]
      congr 2
      ring
    rw [he]
    exact gaussian_second_moment_integrable (hausdorff n X) z hV hA
      (by norm_num : 0 < (1:ℝ)/40) hvol
  obtain ⟨L',hL',hbound⟩ := gaussian_density_tail_moments
    (ρ := fun i : ℕ × Ioo (0:ℝ) 1 => D.interpolationDensity i.1 i.2) z hB
    (fun i => (D.interpolationDensity_continuous i.1 i.2).measurable)
    (fun i x => (D.interpolationDensity_pos i.1 i.2 x).le)
    (fun i x hx => htail i.1 i.2 x hx) hG
  exact ⟨L',hL',fun k t q hq => hbound (k,t) q hq⟩

end RegularPointCoordinates.NoncollapsedRCD.CompactHeatScalingData

end

end OAI
