import OAI.NumberTheory.PiExponent.Analysis.AnalyticDeterminantCollision
import OAI.NumberTheory.PiExponent.Analysis.PeriodAnalytic
import OAI.NumberTheory.PiExponent.Polynomials.SimplexLog

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent

noncomputable def holomorphicError (K : ℕ) (w0 v0 wstar : ℝ) : ℝ :=
  100 * K / w0 + Real.log 2 / v0 + Real.log (200 * K) / wstar

theorem formal_period_collision_bound
    {m : ℕ} {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (group : ι → κ) (transverse : κ → Fin m →₀ ℕ)
    (j ell h : ι → ℕ) (a : ι → Fin m → ℕ) (w : Fin m → ℝ)
    {K : ℕ} {H w0 v0 wstar : ℝ}
    (hK : 0 < K) (hH : 0 < H) (hw0 : 0 < w0) (hws : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) (hj : ∀ r, j r < K)
    (hcol : ∀ c, w0 * h c + ∑ i, w i * a c i ≤ H)
    (hell : ((∑ r, ell r : ℕ) : ℝ) ≤ (Fintype.card ι : ℝ) * H / v0) :
    ‖Matrix.det (fun r c => PowerSeries.coeff (ell r)
      ((MatrixTranslation.periodMonomial (j r) (2 * (Real.pi : ℂ) * Complex.I)
        (h c) (a c)).coeff (transverse (group r))))‖ ≤
      Real.exp (-(Real.log 2 / 4) *
        (∑ A, (Collision.multiplicity Finset.univ group A : ℝ) ^ 2) +
        (Fintype.card ι : ℝ) * H *
          (holomorphicError K w0 v0 wstar + Collision.collisionRemainder (Fintype.card ι) H)) := by
  let R : NNReal := ⟨100 * (K : ℝ), by positivity⟩
  have hR : 0 < R := by change (0 : ℝ) < 100 * K; positivity
  have hR1 : (1 : ℝ) ≤ R := by
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    change (1 : ℝ) ≤ 100 * K
    linarith
  have hb := AnalyticCollision.translated_row_determinant_exp_bound
    group (fun A c => PeriodAnalytic.columnFunction (h c) (a c) (transverse A))
    (fun r => (j r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) ell R hR hH
    (fun A c => PeriodAnalytic.differentiable_columnFunction _ _ _)
    (A := (R : ℝ) / w0 + Real.log (2 * (R : ℝ)) / wstar) (v := v0)
    (fun A c z hz => PeriodAnalytic.norm_columnFunction_le (h c) (a c) (transverse A) w
      hR1 hH.le hw0 hws hw (hcol c)
      (by simpa only [Metric.mem_sphere, dist_zero_right] using hz.le))
    (fun r => AnalyticCollision.period_center_radius_bound hK (hj r)) hell
  have hRv : (R : ℝ) = 100 * K := rfl
  rw [hRv] at hb
  have he : (2 : ℝ) * (100 * K) = 200 * K := by ring
  rw [he] at hb
  simp_rw [PeriodAnalytic.periodMonomial_coeff_eq_rowTest]
  convert! hb using 1
  congr 1
  unfold holomorphicError
  ring

theorem tendsto_collisionRemainder_of_normalized_pow {M : ℝ → ℕ} {d : ℕ} {L : ℝ}
    (hM : Tendsto (fun H : ℝ => (M H : ℝ) / H ^ d) atTop (𝓝 L)) (hL : 0 < L) :
    Tendsto (fun H => Collision.collisionRemainder (M H) H) atTop (𝓝 0) := by
  convert tendsto_log_add_div_of_normalized_pow hM hL
    (Real.log 2 / 4 - Real.log (1 - Collision.collisionRatio)) using 1
  funext H
  unfold Collision.collisionRemainder
  congr 1
  ring

end PiExponent

end OAI
