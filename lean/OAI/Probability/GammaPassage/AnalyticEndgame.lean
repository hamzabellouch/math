import OAI.Probability.GammaPassage.AnalyticCore

namespace OAI

namespace GammaFPP.Analytic
open PlanarFPP Set Filter
open scoped Topology

/-- No corner in every finite slope of the horizontal coordinate chart. -/
def NoCornerInCoordinates (μ : Plane → ℝ) : Prop :=
  ∀ b : ℝ, leftSlope (fun t : ℝ => μ (direction b + t • transverseUnit)) =
    rightSlope (fun t : ℝ => μ (direction b + t • transverseUnit))

lemma norm_comp_swap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) :
    TimeConstantNorm (fun v => μ (swapPlane v)) := by
  refine ⟨fun v => hμ.nonneg _, ?_, ?_, ?_⟩
  · intro v
    rw [hμ.zero_iff]
    exact ⟨fun hv => swapPlane.injective (by simpa using hv), fun hv => by simp [hv]⟩
  · intro v w
    simpa only [map_add] using hμ.triangle (swapPlane v) (swapPlane w)
  · intro a v
    simpa only [map_smul] using hμ.homogeneous a (swapPlane v)

lemma differentiable_horizontal_of_noCorner (μ : Plane → ℝ)
    (hμ : TimeConstantNorm μ) (hnc : NoCornerInCoordinates μ)
    (v : Plane) (hx : v 0 ≠ 0) : DifferentiableAt ℝ μ v := by
  obtain ⟨ℓ,hℓ⟩ := planar_differentiability_of_no_corner μ hμ (v 1/v 0) (hnc _)
  have hd := norm_differentiable_smul μ hμ (direction (v 1/v 0)) (v 0) hx hℓ.differentiableAt
  rwa [plane_direction_representation v hx] at hd

/-- Absence of corners in both coordinate charts implies differentiability
away from the origin for an arbitrary planar norm. -/
theorem differentiable_away_of_noCorner (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hnc : NoCornerInCoordinates μ)
    (hncs : NoCornerInCoordinates (fun v => μ (swapPlane v))) :
    DifferentiableAwayFromOrigin μ := by
  intro v hv
  have hd : DifferentiableAt ℝ μ v := by
    by_cases hx : v 0 ≠ 0
    · exact differentiable_horizontal_of_noCorner μ hμ hnc v hx
    · have hy : v 1 ≠ 0 := by
        intro hy
        apply hv
        ext i
        fin_cases i <;> simp_all
      have hs := differentiable_horizontal_of_noCorner (fun z => μ (swapPlane z))
        (norm_comp_swap μ hμ) hncs (swapPlane v) (by simpa using hy)
      have hc := hs.comp v swapPlane.toContinuousLinearEquiv.differentiableAt
      simpa only [Function.comp_def, swapPlane_swap] using hc
  exact ⟨fderiv ℝ μ v, hd.hasFDerivAt⟩

lemma norm_profile_contDiff (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) :
    ContDiff ℝ 1 (fun t => μ (direction t)) := by
  have he (t : ℝ) : direction 0+t • transverseUnit=direction t := by
    ext i; fin_cases i <;> simp [direction,transverseUnit,PiLp.add_apply,PiLp.smul_apply]
  have hc := convex_transverse_profile μ (direction 0) transverseUnit
    hμ.triangle (norm_positive_homogeneous μ hμ)
  have hder : Differentiable ℝ (fun t : ℝ => μ (direction 0+t • transverseUnit)) := by
    intro t
    have hne : direction t ≠ 0 := by
      intro hz
      have hh := congrArg xCoord hz
      change (1 : ℝ)=0 at hh
      norm_num at hh
    obtain ⟨ℓ,hℓ⟩ := hd (direction t) hne
    have hh : DifferentiableAt ℝ μ (direction 0+t • transverseUnit) := by
      rw [he]
      exact hℓ.differentiableAt
    have hm : DifferentiableAt ℝ (fun s : ℝ => direction 0+s • transverseUnit) t :=
      (((hasDerivAt_id t).smul_const transverseUnit).const_add (direction 0)).differentiableAt
    exact DifferentiableAt.comp (g := μ) (f := fun s : ℝ => direction 0+s • transverseUnit) t hh hm
  simpa only [he] using convex_contDiff_one _ hc hder

lemma differentiable_away_comp_swap (μ : Plane → ℝ)
    (hd : DifferentiableAwayFromOrigin μ) :
    DifferentiableAwayFromOrigin (fun v => μ (swapPlane v)) := by
  intro v hv
  have hne : swapPlane v ≠ 0 := by
    intro hz
    exact hv (swapPlane.injective (by simpa using hz))
  obtain ⟨ℓ,hℓ⟩ := hd (swapPlane v) hne
  exact ⟨ℓ.comp swapPlane.toContinuousLinearEquiv.toContinuousLinearMap,
    hℓ.comp v swapPlane.toContinuousLinearEquiv.hasFDerivAt⟩

/-- The unit sphere of a differentiable planar norm has regular `C¹` curve
charts with continuous local inverses. -/
theorem norm_sphere_curve_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane) (hv : μ v=1) :
    GammaFPP.HasC1CurveChart {z | μ z=1} v := by
  have horizontal (ν : Plane → ℝ) (hν : TimeConstantNorm ν)
      (hder : DifferentiableAwayFromOrigin ν) (z : Plane) (hz : ν z=1)
      (hx : z 0 ≠ 0) : GammaFPP.HasC1CurveChart {w | ν w=1} z := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact sphere_horizontal_chart ν hν (norm_profile_contDiff ν hν hder) (-1)
        (by norm_num) z hz (by linarith)
    · exact sphere_horizontal_chart ν hν (norm_profile_contDiff ν hν hder) 1
        (by norm_num) z hz (by simpa using hpos)
  by_cases hx : v 0 ≠ 0
  · exact horizontal μ hμ hd v hv hx
  · have hvne : v ≠ 0 := by
      intro he
      have hz := (hμ.zero_iff v).mpr he
      linarith
    have hy : v 1 ≠ 0 := by
      intro hy
      apply hvne
      ext i
      fin_cases i <;> simp_all
    have hs := horizontal (fun z => μ (swapPlane z)) (norm_comp_swap μ hμ)
      (differentiable_away_comp_swap μ hd) (swapPlane v) (by simpa using hv)
      (by simpa using hy)
    have hh := chart_preimage_isometry {z | μ (swapPlane z)=1} v swapPlane hs
    have he : swapPlane ⁻¹' {z | μ (swapPlane z)=1} = {z | μ z=1} := by
      ext z
      simp only [mem_preimage, mem_ofPred_eq, swapPlane_swap]
    rwa [he] at hh

/-- The topological frontier of the norm unit ball has regular `C¹` curve charts. -/
theorem norm_boundary_curve_chart (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hd : DifferentiableAwayFromOrigin μ) (v : Plane)
    (hv : v ∈ frontier {z | μ z ≤ 1}) :
    GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  rw [norm_ball_frontier μ hμ] at hv ⊢
  exact norm_sphere_curve_chart μ hμ hd v hv

/-- A planar norm with no corners in both coordinate charts is differentiable
away from zero and has regular `C¹` charts on its unit-ball frontier. -/
theorem analytic_endgame (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hnc : NoCornerInCoordinates μ)
    (hncs : NoCornerInCoordinates (fun v => μ (swapPlane v))) :
    DifferentiableAwayFromOrigin μ ∧
      ∀ v ∈ frontier {z | μ z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  have hd := differentiable_away_of_noCorner μ hμ hnc hncs
  exact ⟨hd, norm_boundary_curve_chart μ hμ hd⟩

/-- Symmetric norms need only the original horizontal no-corner statement. -/
theorem analytic_endgame_of_swap (μ : Plane → ℝ) (hμ : TimeConstantNorm μ)
    (hswap : ∀ v, μ (swapPlane v)=μ v) (hnc : NoCornerInCoordinates μ) :
    DifferentiableAwayFromOrigin μ ∧
      ∀ v ∈ frontier {z | μ z ≤ 1},
        GammaFPP.HasC1CurveChart (frontier {z | μ z ≤ 1}) v := by
  apply analytic_endgame μ hμ hnc
  simpa only [NoCornerInCoordinates, hswap] using hnc

end GammaFPP.Analytic

end OAI
