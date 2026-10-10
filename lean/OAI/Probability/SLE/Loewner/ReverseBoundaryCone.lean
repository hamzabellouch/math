import OAI.Probability.SLE.Loewner.ReverseBoundarySquare

namespace OAI

/-! A reverse trajectory starting at the driver enters a vertical cone.
The squared coordinate removes the singularity at the initial point. -/
noncomputable section
open Set Filter Complex
open scoped Topology

namespace SLEExactGauge

theorem reverse_boundary_cone_of_small_center
    {T L M : ℝ} (hT : 0 ≤ T) (hL : 0 ≤ L) (hsmall : 2*L*M ≤ 1)
    (q : ℝ → ℂ) (u u' : ℝ → ℝ)
    (hc : ContinuousOn q (Icc 0 T)) (huc : ContinuousOn u (Icc 0 T))
    (hq0 : q 0=(u 0 : ℂ))
    (hq : ∀ t ∈ Ioc 0 T, HasDerivWithinAt q
      (-2/(q t-(u t : ℂ))) (Ici t) t)
    (hu : ∀ t ∈ Ioc 0 T, HasDerivWithinAt u (u' t) (Ici t) t)
    (hp : ∀ t ∈ Ioc 0 T, 0 < (q t).im)
    (hb : ∀ t ∈ Ioc 0 T, |u' t| ≤ L)
    (hM : ∀ t ∈ Ioc 0 T, ‖q t-(u t : ℂ)‖ ≤ M) :
    ∀ t ∈ Icc 0 T, ((q t).re-u t)^2 ≤ t ∧ 3*t ≤ (q t).im^2 := by
  have he := reverse_boundary_square_estimate hT q u u' hc huc hq0 hq hu hp hb hM hL
  intro t ht
  let z : ℂ := q t-(u t : ℂ)
  have hnorm : ‖z^2+4*(t : ℂ)‖ ≤ t :=
    (he t ht).trans (by nlinarith [mul_le_mul_of_nonneg_right hsmall ht.1])
  have hre : (z^2+4*(t : ℂ)).re ≤ t := (Complex.re_le_norm _).trans hnorm
  have hz : ‖z^2‖ ≤ 5*t := by
    calc
      ‖z^2‖ = ‖(z^2+4*(t : ℂ))-4*(t : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z^2+4*(t : ℂ)‖+‖4*(t : ℂ)‖ := norm_sub_le _ _
      _ ≤ t+4*t := by
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
        norm_num only [norm_ofNat]
        exact add_le_add hnorm le_rfl
      _ = 5*t := by ring
  have hnormsq : ‖z^2‖ = z.re^2+z.im^2 := by
    rw [norm_pow,← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    ring
  have here : (z^2+4*(t : ℂ)).re=z.re^2-z.im^2+4*t := by
    simp [pow_two,Complex.mul_re]
  rw [hnormsq] at hz
  rw [here] at hre
  have hx : z.re=(q t).re-u t := by simp [z]
  have hy : z.im=(q t).im := by simp [z]
  rw [hx,hy] at hre hz
  constructor <;> nlinarith

end SLEExactGauge

end

end OAI
