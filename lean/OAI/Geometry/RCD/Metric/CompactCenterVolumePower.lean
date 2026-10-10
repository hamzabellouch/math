import OAI.Geometry.RCD.Metric.RescaledBallVolume

namespace OAI

/-! # Uniform polynomial normalization volumes for centers in one compact ball -/

open Set Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n)

include hX hn in
theorem compact_center_volume_power (z : X) {R : ℝ} (hR : 1 ≤ R) :
    ∃ V : ℝ, 0 < V ∧ ∀ (y : X), dist y z ≤ R →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 →
        V*(Real.sqrt t)^n ≤ (hausdorff n X).real (ball y (Real.sqrt t)) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num) hR
  let a := |K| *R^2
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg K) (sq_nonneg R)
  let E := (2*Real.exp (4*Real.sqrt a))*R
  have hE : 0 < E := by dsimp only [E]; positivity
  let mass := (hausdorff n X).real (ball z R)
  have hmass : 0 < mass := ENNReal.toReal_pos (hX.fullSupport z R hR0).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  let V := mass/E^n
  refine ⟨V,div_pos hmass (pow_pos hE n),?_⟩
  intro y hy t ht ht1
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs1 : Real.sqrt t ≤ R := by
    nlinarith [Real.sq_sqrt ht.le,Real.sqrt_nonneg t]
  have hcurv : -a ≤ K*R^2 := by
    have hh := mul_le_mul_of_nonneg_right (neg_abs_le K) (sq_nonneg R)
    simpa only [a,neg_mul] using hh
  have hb := hX.rescaled_ball_volume_lower hn ha (div_pos hs hR0)
    ((div_le_one hR0).mpr hs1) z R hR0 hcurv y hy
  have hrad : Real.sqrt t/R*R=Real.sqrt t := by field_simp
  have hcoef : (Real.sqrt t/R)/(2*Real.exp (4*Real.sqrt a))=Real.sqrt t/E := by
    dsimp only [E]
    field_simp
  rw [hrad,hcoef] at hb
  calc
    V*(Real.sqrt t)^n = (Real.sqrt t/E)^n*mass := by
      dsimp only [V]
      rw [div_pow]
      ring
    _ ≤ _ := hb

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
