import OAI.MeasureTheory.Falconer.Recursion.PointRieszPotential

namespace OAI

/-! # Bounded Riesz potentials give all-center Frostman bounds -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d : ℕ}

theorem ball_mass_le_potential (μ : Measure (Space d)) (x : Space d)
    {u r : ℝ} (hu : 0 < u) (hr : 0 < r) :
    μ (ball x r) ≤ ENNReal.ofReal (r^u) * euclideanRieszPotential μ u x := by
  have hcancel : ENNReal.ofReal (r^u) * (ENNReal.ofReal r)^(-u) = 1 := by
    rw [← ENNReal.ofReal_rpow_of_pos hr,
      ← ENNReal.rpow_add _ _ (ENNReal.ofReal_ne_zero_iff.mpr hr) ENNReal.ofReal_ne_top]
    simp
  have hpoint (y : Space d) (hy : y ∈ ball x r) :
      1 ≤ ENNReal.ofReal (r^u) * (edist x y)^(-u) := by
    have hd : edist x y ≤ ENNReal.ofReal r := by
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      exact (by simpa [mem_ball,dist_comm] using hy : dist x y < r).le
    have hp : (ENNReal.ofReal r)^(-u) ≤ (edist x y)^(-u) := by
      rw [ENNReal.rpow_neg,ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hd hu.le)
    rw [← hcancel]
    exact mul_le_mul_right hp _
  calc
    _ = ∫⁻ _ in ball x r, (1:ℝ≥0∞) ∂μ := by simp
    _ ≤ ∫⁻ y in ball x r, ENNReal.ofReal (r^u) * (edist x y)^(-u) ∂μ :=
      setLIntegral_mono' measurableSet_ball hpoint
    _ ≤ ∫⁻ y, ENNReal.ofReal (r^u) * (edist x y)^(-u) ∂μ :=
      setLIntegral_le_lintegral _ _
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem frostman_of_ae_bounded_potential (η μ : Measure (Space d))
    (hdom : η ≤ μ) {u B : ℝ} (hu : 0 < u)
    (hpotential : ∀ᵐ x ∂η, euclideanRieszPotential μ u x ≤ ENNReal.ofReal B) :
    FrostmanBallBound η u (2^u*B) := by
  intro x r hr
  by_cases hzero : η (ball x r) = 0
  · rw [hzero]
    exact bot_le
  · obtain ⟨y,hy,hpot⟩ := (Measure.exists_mem_of_measure_ne_zero_of_ae hzero (ae_restrict_of_ae hpotential))
    have hsub : ball x r ⊆ ball y (2*r) := by
      intro z hz
      apply mem_ball.mpr
      have hd := dist_triangle z x y
      have hz' := mem_ball.mp hz
      have hy' := mem_ball.mp hy
      rw [dist_comm x y] at hd
      linarith
    calc
      η (ball x r) ≤ η (ball y (2*r)) := measure_mono hsub
      _ ≤ μ (ball y (2*r)) := hdom _
      _ ≤ ENNReal.ofReal ((2*r)^u) * euclideanRieszPotential μ u y :=
        ball_mass_le_potential μ y hu (by positivity)
      _ ≤ ENNReal.ofReal ((2*r)^u) * ENNReal.ofReal B := mul_le_mul_right hpot _
      _ = ENNReal.ofReal ((2^u*B)*r^u) := by
        rw [← ENNReal.ofReal_mul (by positivity),Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le]
        congr 1
        ring

end Falconer

end OAI
