import OAI.Geometry.RCD.Transport.DistancePoissonOptimalMean
import OAI.Geometry.RCD.Metric.DominatedCompactProbability

namespace OAI

/-! # Poisson quadratic means for bounded ambient endpoint laws -/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]
  {K : ℝ} {n : ℕ} {hX : NoncollapsedRCD K n X} {hn : 2≤n} [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]
  {κ B J C : ℝ} {p : ℕ → X} {r : ℕ → ℝ} {hr : ∀ k, 0<r k}
  {F : DistancePoissonFamily (hausdorff n X) hX.quadratic n κ B J C p r hr}
  (W : DistancePoissonMeanData F)
attribute [local instance] pathBorel pathBorelSpace

theorem DistancePoissonMeanData.bounded_mean_estimate (p₀ : X) (k : ℕ)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2) (hr1 : r k≤1)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {Bπ : ℝ≥0∞} (hBπ : Bπ≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤Bπ • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x (p k)≤r k/512)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x (p k)≤r k/512) :
    let Z t := ∫ γ, W.representative k (γ t) ∂π
    ∀ (l h t : Time), 0<(l:ℝ) → (l:ℝ)<h → (h:ℝ)<1 → (t:ℝ)∈Icc (l:ℝ) h →
      |Z t-Z l-((Z h-Z l)/((h:ℝ)-l))*((t:ℝ)-l)-
        (∫ γ, dist (γ 0) (γ 1)^2 ∂π)*((t:ℝ)-l)*((t:ℝ)-h)/2|≤
      (poissonMeanConstant K (hX.centeredActionBound hn p₀) l*((h:ℝ)-l)^2)*
        (r k)^2*Bπ.toReal*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*
          Real.sqrt (W.budget K k) := by
  let m := hausdorff n X
  let S := closedBall (p k) (r k/512)
  have hSm : MeasurableSet S := measurableSet_closedBall
  let : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall (p k) (r k/512))
  have hs (t : Time) (ht : ∀ᵐ x ∂π.map (fun γ => γ t), dist x (p k)≤r k/512) :
      ∀ᵐ x ∂π.map (fun γ => γ t), x∈S := by simpa only [S,mem_closedBall] using ht
  obtain ⟨μ,ρ₀,C₀,hprob₀,hμ,hm₀,hp₀,hC₀,hd₀⟩ := dominated_supported_probability_law
    m (π.map (fun γ => γ 0)) S hSm (hs 0 hs₀) hBπ (hcomp 0)
  obtain ⟨ν,ρ₁,C₁,hprob₁,hν,hm₁,hp₁,hC₁,hd₁⟩ := dominated_supported_probability_law
    m (π.map (fun γ => γ 1)) S hSm (hs 1 hs₁) hBπ (hcomp 1)
  let := hprob₀
  let := hprob₁
  obtain ⟨a₀⟩ := nonempty_of_isProbabilityMeasure μ
  obtain ⟨b₀⟩ := nonempty_of_isProbabilityMeasure ν
  have hopt' : IsOptimalCoupling (μ.map Subtype.val) (ν.map Subtype.val)
      (π.map (fun γ => (γ 0,γ 1))) := by rw [hμ,hν]; exact hopt
  exact W.optimal_mean_estimate k p₀ a₀ b₀ hK hκ hBJ hr1 ρ₀ ρ₁ hm₀ hm₁ hp₀ hp₁
    hC₀ hC₁ hd₀ hd₁
    (fun y => by simpa only [S,mem_closedBall,dist_comm] using y.property)
    (fun y => by simpa only [S,mem_closedBall,dist_comm] using y.property)
    π hgeo hopt' hBπ hcomp

end RegularPointCoordinates

end

end OAI
