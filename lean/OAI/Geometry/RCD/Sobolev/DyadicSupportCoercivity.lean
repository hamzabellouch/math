import OAI.Geometry.RCD.Sobolev.CoveredCoercivity
import OAI.Geometry.RCD.Metric.DyadicVolumeLower

namespace OAI

/-! # Support-sensitive coercivity on dyadic scales

A support set small compared with the CD lower volume of a dyadic ball
leaves a large zero set in every covering ball. The resulting coercivity
constant gains the square of that smaller radius.
-/

open Set Metric MeasureTheory
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.dyadic_support_coercivity {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ C D : ℝ, 0 < C ∧ 2 ≤ D ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (w : SobolevSpace (hausdorff n X) hX.quadratic) (A : Set X),
      MeasurableSet A → A ⊆ ball p R →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[
        (hausdorff n X).restrict Aᶜ] 0) →
      ∀ k : ℕ, 2*D^(k+1)*(hausdorff n X).real A ≤
        (hausdorff n X).real (ball p R) →
      (∫ x in ball p R, (SobolevSpace.toLp (hausdorff n X) hX.quadratic w x)^2
        ∂hausdorff n X) ≤ C*(R/2^k)^2 *
          energyForm (hausdorff n X) hX.quadratic w w := by
  obtain ⟨C, hC, hcover⟩ := hX.covered_zero_set_coercivity hn
  obtain ⟨D, hD, hvol⟩ := hX.rescaled_dyadic_volume_lower hn
  refine ⟨C, D, hC, hD, ?_⟩
  intro p R hR hcurv w A hA hsubA hz k hsize
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hpow : 0 < D^(k+1) := pow_pos hDpos _
  have hAfin : μ A ≠ ∞ := (hX.finiteOnBounded A (isBounded_ball.subset hsubA)).ne
  apply hcover p R (R/2^k) hR (by positivity)
    (div_le_self hR.le (one_le_pow₀ (by norm_num))) hcurv w
  intro q hq
  let B := ball q (R/2^k) \ A
  have hqfin : μ (ball q (R/2^k)) ≠ ∞ := (hX.finiteOnBounded _ isBounded_ball).ne
  have hzeroFin : μ (ball q (R/2^k) ∩ {x | u x = 0}) ≠ ∞ :=
    ne_top_of_le_ne_top hqfin (measure_mono inter_subset_left)
  have hsmall : 2*μ.real A ≤ μ.real (ball q (R/2^k)) := by
    have hv := hvol p R hR hcurv q hq k
    change μ.real (ball p R) ≤ D^(k+1)*μ.real (ball q (R/2^k)) at hv
    change 2*D^(k+1)*μ.real A ≤ μ.real (ball p R) at hsize
    nlinarith
  have hinter : μ.real (ball q (R/2^k) ∩ A) ≤ μ.real A :=
    measureReal_mono inter_subset_right hAfin
  have hadd := measureReal_inter_add_sdiff (μ := μ) (s := ball q (R/2^k)) hA hqfin
  have hBhalf : μ.real (ball q (R/2^k)) ≤ 2*μ.real B := by
    dsimp only [B]
    linarith
  have hzglobal : ∀ᵐ x ∂μ, x ∉ A → u x = 0 := (ae_restrict_iff' hA.compl).mp hz
  have hzero : B ≤ᵐ[μ] ball q (R/2^k) ∩ {x | u x = 0} := by
    filter_upwards [hzglobal] with x hx hxB
    exact ⟨hxB.1, hx hxB.2⟩
  have hBzero : μ.real B ≤ μ.real (ball q (R/2^k) ∩ {x | u x = 0}) :=
    ENNReal.toReal_mono hzeroFin (measure_mono_ae hzero)
  exact hBhalf.trans (mul_le_mul_of_nonneg_left hBzero (by norm_num))

end RegularPointCoordinates

end

end OAI
