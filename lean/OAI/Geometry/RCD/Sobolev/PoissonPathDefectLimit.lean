import OAI.Geometry.RCD.Sobolev.PoissonPathDefectBound

namespace OAI

/-! # Vanishing normalized absolute path error for Poisson replacements -/

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

include hn in
theorem DistancePoissonMeanData.normalized_path_error_tendsto_zero (p₀ : X)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2) (hr1 : ∀ k, r k≤1)
    (hV : ∀ k, 0<(hausdorff n X).real (ball (p k) (r k)))
    (hr0 : Tendsto r atTop (𝓝 0))
    (hmass : Tendsto (fun k => (F.source k).real (ball (p k) (r k))/
      (hausdorff n X).real (ball (p k) (r k))) atTop (𝓝 0))
    (π : ℕ → Measure C(Time,X)) [∀ k, IsProbabilityMeasure (π k)]
    (hgeo : ∀ k, ∀ᵐ γ ∂π k, IsGeodesic γ)
    (hopt : ∀ k, IsOptimalCoupling ((π k).map (fun γ => γ 0)) ((π k).map (fun γ => γ 1))
      ((π k).map (fun γ => (γ 0,γ 1))))
    (Bπ : ℕ → ℝ≥0∞) (hBπ : ∀ k, Bπ k≠∞)
    (hcomp : ∀ k (t : Time), (π k).map (fun γ => γ t)≤Bπ k • hausdorff n X)
    (hs₀ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 0), dist x (p k)≤r k/512)
    (hs₁ : ∀ k, ∀ᵐ x ∂(π k).map (fun γ => γ 1), dist x (p k)≤r k/512)
    {Cπ : ℝ} (hcompression : ∀ k, (Bπ k).toReal*(hausdorff n X).real (ball (p k) (r k))≤Cπ)
    (l h t : Time) (hl : 0<(l:ℝ)) (hlh : (l:ℝ)<h) (hh : (h:ℝ)<1)
    (ht : (t:ℝ)∈Icc (l:ℝ) h) :
    Tendsto (fun k => (∫ γ, |interiorQuadraticDefect (W.representative k) l h t γ| ∂π k)/(r k)^2)
      atTop (𝓝 0) := by
  apply normalized_quadratic_mean_error_tendsto_zero r
    (fun k => (hausdorff n X).real (ball (p k) (r k))) (W.budget K)
    (fun k => (Bπ k).toReal) _ hr hV (W.budget_nonneg hK hBJ)
    (show 0≤2*(poissonMeanConstant K (hX.centeredActionBound hn p₀) l*((h:ℝ)-l)^2) by
      unfold poissonMeanConstant
      positivity)
    hcompression (W.normalized_budget_tendsto_zero hK hBJ hV hr0 hmass)
  intro k
  rw [abs_of_nonneg (integral_nonneg fun γ => abs_nonneg _)]
  have he := W.path_defect_bound (hX := hX) (hn := hn) p₀ k hK hκ hBJ (hr1 k) (π k) (hgeo k) (hopt k)
    (hBπ k) (hcomp k) (hs₀ k) (hs₁ k) l h t hl hlh hh ht
  exact he.trans_eq (by ring)

end RegularPointCoordinates

end

end OAI
