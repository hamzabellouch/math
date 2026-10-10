import OAI.Geometry.RCD.Sobolev.DistancePoissonBoundedMean
import OAI.Geometry.RCD.Coordinates.NormalizedSubplanData
import OAI.Geometry.RCD.Transport.SubplanAbsoluteIntegral
import OAI.Geometry.RCD.Harmonic.InteriorQuadraticDefect

namespace OAI

/-! # An absolute path-error bound from the actual Poisson mean estimate -/

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

theorem DistancePoissonMeanData.path_defect_bound (p₀ : X) (k : ℕ)
    (hK : K≤0) (hκ : 0≤κ) (hBJ : 0≤J+B/2) (hr1 : r k≤1)
    (π : Measure C(Time,X)) [IsProbabilityMeasure π] (hgeo : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hopt : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
      (π.map (fun γ => (γ 0,γ 1))))
    {Bπ : ℝ≥0∞} (hBπ : Bπ≠∞) (hcomp : ∀ t : Time, π.map (fun γ => γ t)≤Bπ • hausdorff n X)
    (hs₀ : ∀ᵐ x ∂π.map (fun γ => γ 0), dist x (p k)≤r k/512)
    (hs₁ : ∀ᵐ x ∂π.map (fun γ => γ 1), dist x (p k)≤r k/512)
    (l h t : Time) (hl : 0<(l:ℝ)) (hlh : (l:ℝ)<h) (hh : (h:ℝ)<1)
    (ht : (t:ℝ)∈Icc (l:ℝ) h) :
    let E := (poissonMeanConstant K (hX.centeredActionBound hn p₀) l*((h:ℝ)-l)^2)*
      (r k)^2*Bπ.toReal*Real.sqrt ((hausdorff n X).real (ball (p k) (r k)))*Real.sqrt (W.budget K k)
    (∫ γ, |interiorQuadraticDefect (W.representative k) l h t γ| ∂π)≤2*E := by
  intro E
  obtain ⟨L,A,hU,hUc,_hu,_hA⟩ := W.representative_spec k
  have hfin := finite_second_moment_cost
    (finiteSecondMoment_of_bounded (π.map (fun γ => γ 0)) (p k) hs₀)
    (finiteSecondMoment_of_bounded (π.map (fun γ => γ 1)) (p k) hs₁) hopt.1 hopt.2.1
  have hd := path_cost_integrable π hfin
  have hE : 0≤E := by dsimp only [E,poissonMeanConstant]; positivity
  apply integral_abs_le_of_normalized_submeans π
    (interiorQuadraticDefect_continuous hU.continuous l h t).measurable
    (interiorQuadraticDefect_integrable π hU.continuous hUc hd l h t) hE
  intro σ hσ hσ0
  obtain ⟨hprob,hgeoσ,hoptσ,hcompσ,hsσ₀,hsσ₁⟩ := normalized_subplan_data π hgeo hopt hfin
    (hausdorff n X) hcomp (p k) hs₀ hs₁ σ hσ hσ0
  let := hprob
  have ha : (σ univ)⁻¹≠∞ := ENNReal.inv_ne_top.mpr hσ0
  have hBσ : (σ univ)⁻¹*Bπ≠∞ := ENNReal.mul_ne_top ha hBπ
  have hdσ : Integrable (fun γ : C(Time,X) => dist (γ 0) (γ 1)^2) ((σ univ)⁻¹ • σ) :=
    (hd.mono_measure hσ).smul_measure ha
  rw [integral_interiorQuadraticDefect _ hU.continuous hUc hdσ l h t]
  have he := W.bounded_mean_estimate (hX := hX) (hn := hn) p₀ k hK hκ hBJ hr1 ((σ univ)⁻¹ • σ)
    hgeoσ hoptσ hBσ hcompσ hsσ₀ hsσ₁ l h t hl hlh hh ht
  convert he using 1
  dsimp only [E]
  rw [ENNReal.toReal_mul]
  ring

end RegularPointCoordinates

end

end OAI
