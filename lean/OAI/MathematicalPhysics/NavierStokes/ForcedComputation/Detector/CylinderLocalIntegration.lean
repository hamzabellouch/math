import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.CylinderCompactCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Integration of first derivatives in the horizontal directions and
over one vertical period. Only C¹ regularity is needed. -/

noncomputable section
namespace ForcedComputation.VelocityDetector.CylinderLocalCalculus
open ShearFlows Set MeasureTheory Filter
open scoped ContDiff Topology

theorem plane_integral_derivative_zero {g : Plane → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (j : Fin 2) :
    (∫ x, fderiv ℝ g x (PlanarHamiltonian.basis j)) = 0 := by
  have hD : Integrable (fun x => fderiv ℝ g x (PlanarHamiltonian.basis j)) :=
    ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (PlanarHamiltonian.basis j))
  have hI : Integrable g := hg.continuous.integrable_of_hasCompactSupport hc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure Plane)) (f := fun _ : Plane => (1 : ℝ)) (g := g)
    (v := PlanarHamiltonian.basis j) (by simp)
    (by simpa only [one_mul] using hD) (by simpa only [one_mul] using hI)
    (fun _ _ => differentiableAt_const 1)
    (fun x _ => hg.differentiable (by norm_num) x)
  simpa only [one_mul, fderiv_const_apply, zero_apply, zero_mul, integral_zero,
    neg_zero] using h

theorem vertical_integral_derivative_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hp : g 1 = g 0) : (∫ z, deriv g z ∂verticalPeriodMeasure) = 0 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1)
    (fun z _ => (hg.differentiable (by norm_num) z).hasDerivAt)
    ((hg.continuous_deriv (by norm_num)).intervalIntegrable 0 1)
  rw [hp, sub_self] at h
  simpa only [verticalPeriodMeasure, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using h

theorem atHeight_smooth : ContDiff ℝ ∞ (fun y : Plane × ℝ => atHeight y.1 y.2) := by
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> dsimp [atHeight] <;> fun_prop

theorem scalarSpatialD_horizontal_support {g : Space → ℝ} {K : Set Plane}
    (hK : IsClosed K) (hs : ∀ x, horizontal x ∉ K → g x = 0)
    (j : Fin 3) (x : Space) (hx : horizontal x ∉ K) : scalarSpatialD j g x = 0 := by
  have hn : ∀ᶠ y in 𝓝 x, horizontal y ∉ K :=
    (hK.isOpen_compl.preimage (show Continuous horizontal from by
      apply continuous_pi
      intro j
      fin_cases j <;> dsimp [horizontal] <;> fun_prop)).mem_nhds hx
  have he : g =ᶠ[𝓝 x] (fun _ => 0) := hn.mono (fun y hy => hs y hy)
  simp only [scalarSpatialD, he.fderiv_eq, fderiv_const_apply]
  rfl

theorem scalarSpatialD_cylinder_integrable {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → g x = 0)
    (j : Fin 3) :
    Integrable (fun y => scalarSpatialD j g (atHeight y.1 y.2)) cylinderMeasure := by
  apply integrable_horizontal_compact
    (((hg.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      atHeight_smooth.continuous) hK
  intro y hy
  apply scalarSpatialD_horizontal_support hK.isClosed hs
  simpa only [atHeight_horizontal] using hy

theorem integral_horizontal_scalarD_zero {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → g x = 0)
    (j : Fin 2) :
    (∫ y, scalarSpatialD j.castSucc g (atHeight y.1 y.2) ∂cylinderMeasure) = 0 := by
  rw [cylinderMeasure, integral_prod_symm _ (scalarSpatialD_cylinder_integrable hg hK hs _)]
  have hz (z : ℝ) : (∫ x : Plane, scalarSpatialD j.castSucc g (atHeight x z)) = 0 := by
    have hi : ContDiff ℝ 1 (fun x : Plane => atHeight x z) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> dsimp [atHeight] <;> fun_prop
    have hcs : HasCompactSupport (fun x : Plane => g (atHeight x z)) := by
      apply HasCompactSupport.intro hK
      intro x hx
      apply hs
      simpa only [atHeight_horizontal] using hx
    have he (x : Plane) : scalarSpatialD j.castSucc g (atHeight x z) =
        fderiv ℝ (fun X : Plane => g (atHeight X z)) x (PlanarHamiltonian.basis j) := by
      have hd := (hg.differentiable (by norm_num) (atHeight x z)).hasFDerivAt.comp x
        (atHeight_hasFDerivAt x z)
      change HasFDerivAt (fun X : Plane => g (atHeight X z)) _ x at hd
      rw [hd.fderiv]
      simp only [ContinuousLinearMap.comp_apply, planeInclusion_basis, scalarSpatialD]
    simp_rw [he]
    exact plane_integral_derivative_zero (hg.comp hi) hcs j
  simp only [hz, integral_zero]

theorem integral_vertical_scalarD_zero {g : Space → ℝ} (hg : ContDiff ℝ 1 g)
    {K : Set Plane} (hK : IsCompact K) (hs : ∀ x, horizontal x ∉ K → g x = 0)
    (hp : VerticallyPeriodic g) :
    (∫ y, scalarSpatialD 2 g (atHeight y.1 y.2) ∂cylinderMeasure) = 0 := by
  rw [cylinderMeasure, integral_prod _ (scalarSpatialD_cylinder_integrable hg hK hs _)]
  have hz (x : Plane) :
      (∫ z, scalarSpatialD 2 g (atHeight x z) ∂verticalPeriodMeasure) = 0 := by
    have hi : ContDiff ℝ 1 (fun z : ℝ => atHeight x z) := by
      apply contDiff_pi.mpr
      intro i
      fin_cases i <;> dsimp [atHeight] <;> fun_prop
    have he (z : ℝ) : scalarSpatialD 2 g (atHeight x z) =
        deriv (fun Z : ℝ => g (atHeight x Z)) z := by
      have hmap : HasDerivAt (fun Z : ℝ => atHeight x Z) (basis 2) z := by
        apply hasDerivAt_pi.mpr
        intro i
        fin_cases i
        · simpa [atHeight, basis] using hasDerivAt_const z (x 0)
        · simpa [atHeight, basis] using hasDerivAt_const z (x 1)
        · change HasDerivAt (fun z : ℝ => z) 1 z
          exact (hasFDerivAt_id (𝕜 := ℝ) z).hasDerivAt
      exact ((hg.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt z hmap).deriv.symm
    have heq : atHeight x 1 = atHeight x 0 + (1 : ℝ) • basis 2 := by
      ext i
      fin_cases i <;> simp [atHeight, basis]
    have hperiod : g (atHeight x 1) = g (atHeight x 0) := by
      rw [heq]
      simpa only [Int.cast_one] using hp (atHeight x 0) 1
    simp_rw [he]
    exact vertical_integral_derivative_zero (hg.comp hi) hperiod
  simp only [hz, integral_zero]

end ForcedComputation.VelocityDetector.CylinderLocalCalculus

end

end OAI
