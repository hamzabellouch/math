import OAI.Probability.GammaPassage.AnalyticEndgame
import OAI.Probability.GammaPassage.MeanNormSwap

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set MeasureTheory

/-- The slope wedge used by the manuscript's probabilistic argument. -/
def NoCornerWedge (μ : Plane → ℝ) : Prop :=
  ∀ b : ℝ, |b| ≤ 1 →
    leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
      rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))

/-- Coordinate-swap symmetry and norm homogeneity extend absence of corners
on the slope wedge to differentiability at every nonzero vector. -/
theorem differentiable_away_of_noCornerWedge (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (hswap : ∀ v, μ (swapPlane v)=μ v)
    (hnc : NoCornerWedge μ) : DifferentiableAwayFromOrigin μ := by
  have horizontal (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
      DifferentiableAt ℝ μ v := by
    have hx : v 0 ≠ 0 := by
      intro hx
      have hy : v 1=0 := by simpa [hx] using hdom
      apply hv
      ext i
      fin_cases i <;> simp [hx,hy]
    have hb : |v 1/v 0| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr hx)).mpr hdom
    obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner μ hμ (v 1/v 0) (hnc _ hb)
    have hh := norm_differentiable_smul μ hμ (direction (v 1/v 0)) (v 0) hx hℓ.differentiableAt
    rwa [plane_direction_representation v hx] at hh
  intro v hv
  have hd : DifferentiableAt ℝ μ v := by
    by_cases hh : |v 1| ≤ |v 0|
    · exact horizontal v hv hh
    · have hsv : swapPlane v ≠ 0 := by
        intro hz
        exact hv (swapPlane.injective (by simpa using hz))
      have hdom : |swapPlane v 1| ≤ |swapPlane v 0| := by
        simpa using (le_of_not_ge hh)
      have hs := horizontal (swapPlane v) hsv hdom
      have hc := hs.comp v swapPlane.toContinuousLinearEquiv.differentiableAt
      have he : (fun z => μ (swapPlane z))=μ := funext hswap
      simpa only [Function.comp_def,he] using hc
  exact ⟨fderiv ℝ μ v,hd.hasFDerivAt⟩

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} {τ : Edge → Ω → ℝ} {shape rate : ℝ}

/-- Absence of corners on the slope wedge gives differentiability and regular
boundary charts for the Gamma mean norm. -/
theorem gammaMeanNorm_analytic_of_noCorner
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (hnc : NoCornerWedge (gammaMeanNorm h hs hr)) :
    DifferentiableAwayFromOrigin (gammaMeanNorm h hs hr) ∧
      ∀ v ∈ frontier {z | gammaMeanNorm h hs hr z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | gammaMeanNorm h hs hr z ≤ 1}) v := by
  have hn := gammaMeanNorm_laws h hs hr
  have hd := differentiable_away_of_noCornerWedge _ hn (gammaMeanNorm_swap h hs hr) hnc
  exact ⟨hd, norm_boundary_curve_chart _ hn hd⟩

/-- A time-constant property and absence of corners on the slope wedge identify
the Gamma mean norm as a differentiable limit norm with regular boundary charts. -/
theorem gammaMeanNorm_target_conjunction_of_inputs
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (ht : IsTimeConstant P τ (gammaMeanNorm h hs hr))
    (hnc : NoCornerWedge (gammaMeanNorm h hs hr)) :
    ∃ μ : Plane → ℝ, TimeConstantNorm μ ∧ IsTimeConstant P τ μ ∧
      DifferentiableAwayFromOrigin μ ∧
      ∀ v ∈ frontier {z | μ z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  obtain ⟨hd,hcharts⟩ := gammaMeanNorm_analytic_of_noCorner h hs hr hnc
  exact ⟨gammaMeanNorm h hs hr,gammaMeanNorm_laws h hs hr,ht,hd,hcharts⟩

end GammaFPP.Analytic

end OAI
