import OAI.MeasureTheory.Falconer.Incidence.AngularTubeCount

namespace OAI

/-! # Tube-count means for a spherical law with a finite-scale ball bound -/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem sphere_ball_bound_extended {d : ℕ} (ν : Measure (Sphere d))
    {δ L s : ℝ} (hmass : ν univ ≤ 1) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s))
    (x : Space d) {r : ℝ} (hr : δ ≤ r) :
    ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s) := by
  by_cases hr₁ : r ≤ 1
  · exact hball x r hr hr₁
  · have hpow : 1 ≤ r^s := Real.one_le_rpow (le_of_not_ge hr₁) hs
    have hprod : 1 ≤ L*r^s := one_le_mul_of_one_le_of_one_le hL hpow
    exact (measure_mono (subset_univ _)).trans (hmass.trans
      (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hprod))

theorem tube_mean_inverse_power {d : ℕ} {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (v : ι → Space d) (ν : Measure (Sphere d))
    {δ W L s : ℝ} (hW : 0 < W) (hL : 1 ≤ L) (hs : 0 ≤ s) (hmass : ν univ ≤ 1)
    (hball : ∀ x : Space d, ∀ r : ℝ, δ ≤ r → r ≤ 1 →
      ν {w : Sphere d | dist (w:Space d) x < r} ≤ ENNReal.ofReal (L*r^s))
    (hv : ∀ i ∈ S.erase a, v i ≠ 0)
    (hscale : ∀ i ∈ S.erase a, δ ≤ 3*W/‖v i‖) :
    (∫⁻ w, (finiteTubeCount S v W w : ℝ≥0∞) ∂ν) ≤
      1+ENNReal.ofReal (2*L*(3*W)^s*(∑ i ∈ S.erase a, (1/‖v i‖)^s)) := by
  classical
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hsum : (∑ i ∈ S.erase a, 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s)) =
      ENNReal.ofReal (2*L*(3*W)^s*(∑ i ∈ S.erase a, (1/‖v i‖)^s)) := by
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i hi
      have he : 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s) =
          ENNReal.ofReal (2*(L*(3*W/‖v i‖)^s)) := by
        rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [he]
      congr 1
      rw [Real.div_rpow (by positivity : 0 ≤ 3*W) (norm_nonneg _),
        one_div,Real.inv_rpow (norm_nonneg _)]
      ring
    · intro i _
      positivity
  rw [finiteTubeCount_mean]
  calc
    _ ≤ ∑ i ∈ insert a (S.erase a), ν (angularTubeEvent (v i) W) :=
      Finset.sum_le_sum_of_subset (by intro i hi; by_cases h : i=a <;> simp [h,hi])
    _ = ν (angularTubeEvent (v a) W)+∑ i ∈ S.erase a, ν (angularTubeEvent (v i) W) :=
      Finset.sum_insert (Finset.notMem_erase a S)
    _ ≤ 1+∑ i ∈ S.erase a, 2*ENNReal.ofReal (L*(3*W/‖v i‖)^s) := by
      apply add_le_add ((measure_mono (subset_univ _)).trans hmass)
      apply Finset.sum_le_sum
      intro i hi
      exact perpendicular_direction_measure ν (hv i hi) hW
        (fun x => sphere_ball_bound_extended ν hmass hL hs hball x (hscale i hi))
    _ = _ := by rw [hsum]

end Falconer

end OAI
