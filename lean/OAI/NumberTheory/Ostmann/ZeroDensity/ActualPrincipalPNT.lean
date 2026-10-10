import OAI.NumberTheory.Ostmann.ZeroDensity.PrincipalChebyshevEstimate
import OAI.NumberTheory.Ostmann.ZeroDensity.SmoothPrincipalPNTBridge

namespace OAI

/-! # The principal smooth PNT without a progression hypothesis -/

namespace Ostmann

open Filter Asymptotics

theorem actual_principal_chebyshev_pnt : ∃ c > 0,
    (Chebyshev.psi - id) =O[atTop]
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 2))) := by
  obtain ⟨c, hc, h⟩ := principal_chebyshev_error
  refine ⟨c, hc, IsBigO.of_bound 25 ?_⟩
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hxp : 0 < x := by linarith
  simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.sqrt_eq_rpow,
    abs_of_pos (mul_pos hxp (Real.exp_pos _)), mul_assoc] using hx

theorem actualSmoothPrincipalPNT : PublishedSmoothPrincipalPNT :=
  publishedSmoothPrincipalPNT_of_chebyshev actual_principal_chebyshev_pnt

end Ostmann

end OAI
