import Mathlib.Analysis.Calculus.MeanValue
import OAI.Geometry.NodalSets.Charts.SphereChartDivergenceData
import OAI.Geometry.NodalSets.Elliptic.RealDifferenceQuotientTest

namespace OAI

namespace Yau.Target
open Yau.Geometry Set
open scoped ContDiff
noncomputable section

theorem sphereChartPrincipalDensity_difference_bound (d : SphereEnergyData) (p : Base) :
    ∃ C > 0, ∀ (i j k : Fin 4) (h : ℝ) (x : Yau.Jets.Coord),
      x ∈ realFinCube 4 → x+(Pi.single k h : Yau.Jets.Coord) ∈ realFinCube 4 →
      |Yau.realDifferenceQuotient k h (fun y ↦ sphereChartPrincipalDensity d p y i j) x| ≤ C := by
  let F : Yau.Jets.Coord → Fin 4 → Fin 4 → Yau.Jets.Coord →L[ℝ] ℝ :=
    fun x i j ↦ fderiv ℝ (fun y ↦ sphereChartPrincipalDensity d p y i j) x
  have hF : Continuous F := continuous_pi (fun i ↦ continuous_pi (fun j ↦
    ((sphereChartPrincipalDensity_smooth d p i j).fderiv_right (m := ∞) (by simp)).continuous))
  obtain ⟨C,hC,hb⟩ := ((realFinCube_isCompact 4).image hF).isBounded.exists_pos_norm_le
  refine ⟨C,hC,?_⟩
  intro i j k h x hx hxt
  have hder (y : Yau.Jets.Coord) (hy : y ∈ realFinCube 4) :
      ‖fderiv ℝ (fun y ↦ sphereChartPrincipalDensity d p y i j) y‖ ≤ C :=
    (norm_le_pi_norm (F y i) j).trans ((norm_le_pi_norm (F y) i).trans (hb _ ⟨y,hy,rfl⟩))
  have hconv : Convex ℝ (realFinCube 4) := convex_pi (fun _ _ ↦ convex_Icc _ _)
  have hd := hconv.norm_image_sub_le_of_norm_fderiv_le
    (fun y _ ↦ (sphereChartPrincipalDensity_smooth d p i j).differentiable (by simp) y) hder hx hxt
  simp only [add_sub_cancel_left,Pi.norm_single,Real.norm_eq_abs] at hd
  by_cases hh : h=0
  · subst h
    simp [Yau.realDifferenceQuotient,hC.le]
  · calc
      _ = |h⁻¹| * |sphereChartPrincipalDensity d p (x+(Pi.single k h : Yau.Jets.Coord)) i j-sphereChartPrincipalDensity d p x i j| :=
        abs_mul _ _
      _ ≤ |h⁻¹| * (C*|h|) := mul_le_mul_of_nonneg_left hd (abs_nonneg _)
      _ = C := by rw [abs_inv]; field_simp [abs_ne_zero.mpr hh]

end
end Yau.Target

end OAI
