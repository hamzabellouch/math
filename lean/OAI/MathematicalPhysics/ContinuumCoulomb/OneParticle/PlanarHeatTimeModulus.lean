import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarHeatBoxBounds
import OAI.MathematicalPhysics.ContinuumCoulomb.Reduction.UniformSamplesOn

namespace OAI

/-! A concrete time modulus for the actual planar heat average, obtained
by integrating the pointwise density modulus over the fixed square. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem planarHeatTime_lipschitz (r : PlanarPosition) {η t s : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) :
    |Real.exp (-t) * planarHeatAverage t r - Real.exp (-s) * planarHeatAverage s r| ≤
      4 * planarBoxTimeConstant r η * |t - s| := by
  let f := fun u x y => HeatKernelModulus.density r u (planarPairEquiv.symm (x, y))
  have hsec (u : ℝ) (hu : η ≤ u) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      ContinuousOn (f u x) (Set.Icc (-1 : ℝ) 1) := by
    apply UniformQuadrature.continuousOn_of_abs_sub_le
    intro y hy y' hy'
    exact planarBox_spatial_second r hη hu hx hy hy'
  have houter (u : ℝ) (hu : η ≤ u) :
      ContinuousOn (fun x => ∫ y in (-1 : ℝ)..1, f u x y) (Set.Icc (-1 : ℝ) 1) := by
    apply UniformQuadrature.continuousOn_of_abs_sub_le
    intro x hx x' hx'
    have h := UniformQuadrature.integral_parameter_lipschitz (f u) (by norm_num : (-1 : ℝ) ≤ 1)
      (hsec u hu) (by
        intro z hz z' hz' y hy
        exact planarBox_spatial_first r hη hu hz hz' hy) hx hx'
    convert h using 1
  have hinner (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
      |(∫ y in (-1 : ℝ)..1, f t x y) - ∫ y in (-1 : ℝ)..1, f s x y| ≤
        2 * planarBoxTimeConstant r η * |t - s| := by
    rw [← intervalIntegral.integral_sub
      ((hsec t ht x hx).intervalIntegrable_of_Icc (by norm_num))
      ((hsec s hs x hx).intervalIntegrable_of_Icc (by norm_num))]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun y => f t x y - f s x y) (a := -1) (b := 1)
      (C := planarBoxTimeConstant r η * |t - s|) (by
        intro y hy
        have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := by
          have hy'' : y ∈ Set.Ioc (-1 : ℝ) 1 := by
            simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hy
          exact ⟨hy''.1.le, hy''.2⟩
        simpa only [Real.norm_eq_abs] using planarBox_time r hη ht hs hx hy')
    rw [show (1 : ℝ) - -1 = 2 by norm_num,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.norm_eq_abs] at h
    convert h using 1
    ring
  rw [planarHeatResolvent_box, planarHeatResolvent_box]
  change |(∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f t x y) -
    ∫ x in (-1 : ℝ)..1, ∫ y in (-1 : ℝ)..1, f s x y| ≤ _
  rw [← intervalIntegral.integral_sub
    ((houter t ht).intervalIntegrable_of_Icc (by norm_num))
    ((houter s hs).intervalIntegrable_of_Icc (by norm_num))]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => (∫ y in (-1 : ℝ)..1, f t x y) - ∫ y in (-1 : ℝ)..1, f s x y)
    (a := -1) (b := 1) (C := 2 * planarBoxTimeConstant r η * |t - s|) (by
      intro x hx
      have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
        have hx'' : x ∈ Set.Ioc (-1 : ℝ) 1 := by
          simpa only [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hx
        exact ⟨hx''.1.le, hx''.2⟩
      simpa only [Real.norm_eq_abs] using hinner x hx')
  rw [show (1 : ℝ) - -1 = 2 by norm_num,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), Real.norm_eq_abs] at h
  convert h using 1
  ring

end ContinuumCoulomb

end

end OAI
