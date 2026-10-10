import OAI.Geometry.RCD.Coordinates.CoordinateHeatInput
import OAI.Geometry.RCD.Heat.AnnularKernelDifference
import OAI.Geometry.RCD.Transport.GeodesicShortSteps

namespace OAI

/-! # Interior Lipschitz control for heat flow of an annular source -/

open Set Metric MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- A source supported away from an interior ball has a uniformly Lipschitz
heat evolution there, all the way down to arbitrarily small positive time. -/
theorem NoncollapsedRCD.annular_heat_difference {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (hg : HasCoordinateHeatBounds (hausdorff n X) ker) :
    ∃ J : ℝ, 0 < J ∧ ∀ (p : X) (R t : ℝ), 0 < R → -1 ≤ K*R^2 →
      0 < t → t ≤ 1 → t ≤ R^2 →
      ∀ q : Lp ℝ 2 (hausdorff n X), Integrable q (hausdorff n X) →
      (∀ᵐ z ∂hausdorff n X, q z ≠ 0 → R ≤ dist z p ∧ dist z p ≤ 2*R) →
      ∀ x y : X, dist x p ≤ R/8 → dist y p ≤ R/8 →
      |kernelHeat (hausdorff n X) hX.quadratic hk t q x-
        kernelHeat (hausdorff n X) hX.quadratic hk t q y| ≤
        (J/(R*(hausdorff n X).real (ball p R))*(∫ z, |q z| ∂hausdorff n X))*dist x y := by
  obtain ⟨J,hJ,hkernel⟩ := hX.annular_kernel_difference hn hk hg
  refine ⟨J,hJ,?_⟩
  intro p R t hR hcurv ht ht1 htR q hqi hqs x y hx hy
  let μ := hausdorff n X
  let V := μ.real (ball p R)
  let F := kernelHeat μ hX.quadratic hk t q
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport p R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hc : 0 ≤ J/(R*V) := by positivity
  have hi (a : X) : Integrable (fun z => ker t a z*q z) μ :=
    (heatKernel_memLp μ hX.quadratic hk ht a).integrable_mul (Lp.memLp q)
  obtain ⟨γ,hxγ,hyγ,hγ⟩ := hX.geodesic x y
  have hdxy : dist x y ≤ R/4 := by
    have hh := dist_triangle x p y
    rw [dist_comm p y] at hh
    linarith
  have hγp (s : Time) : dist (γ s) p ≤ R/2 := by
    have hgs := hγ s 0
    rw [hxγ,hyγ] at hgs
    change dist (γ s) x = |(s:ℝ)-0| *dist x y at hgs
    rw [sub_zero,abs_of_nonneg s.2.1] at hgs
    have hdist : dist (γ s) x ≤ dist x y := by
      rw [hgs]
      exact mul_le_of_le_one_left dist_nonneg s.2.2
    have hh := dist_triangle (γ s) x p
    linarith
  have hshort (s u : Time) (hsu : dist (γ s) (γ u) ≤ Real.sqrt t) :
      |F (γ s)-F (γ u)| ≤
        (J/(R*V)*(∫ z, |q z| ∂μ))*dist (γ s) (γ u) := by
    have hid : Integrable (fun z => (ker t (γ s) z-ker t (γ u) z)*q z) μ := by
      convert (hi (γ s)).sub (hi (γ u)) using 1
      funext z
      exact sub_mul _ _ _
    have hdiff : F (γ s)-F (γ u) =
        ∫ z, (ker t (γ s) z-ker t (γ u) z)*q z ∂μ := by
      dsimp only [F]
      rw [kernelHeat_eq_integral μ hX.quadratic hk ht q (γ s),
        kernelHeat_eq_integral μ hX.quadratic hk ht q (γ u),
        ← integral_sub (hi (γ s)) (hi (γ u))]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => (sub_mul _ _ _).symm
    rw [hdiff]
    calc
      _ ≤ ∫ z, |(ker t (γ s) z-ker t (γ u) z)*q z| ∂μ := abs_integral_le_integral_abs
      _ ≤ ∫ z, (J/(R*V)*dist (γ s) (γ u))*|q z| ∂μ := by
        apply integral_mono_ae hid.abs (hqi.abs.const_mul _)
        filter_upwards [hqs] with z hz
        by_cases hqz : q z = 0
        · simp [hqz]
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right
          (hkernel p R t hR hcurv ht ht1 htR (γ s) (γ u) z (hγp s)
            (hz hqz).1 (hz hqz).2 hsu) (abs_nonneg _)
      _ = _ := by rw [integral_const_mul]; ring
  have hh := hγ.short_step_bound F (Real.sqrt_pos.mpr ht) hshort
  simpa only [hxγ,hyγ,F,V,μ] using hh

end RegularPointCoordinates

end

end OAI
