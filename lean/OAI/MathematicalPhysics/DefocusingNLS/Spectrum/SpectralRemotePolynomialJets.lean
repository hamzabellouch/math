import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialDerivatives

namespace OAI

/-! Uniform bounds for fixed derivatives of the convergent finite
polynomial approximations to the exterior profile. -/

open Polynomial Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_polynomial_euler_coeff (P : ℂ[X]) (k i : ℕ) :
    ((radialPolynomialEuler^[k]) P).coeff i = (-2*(i : ℂ))^k*P.coeff i := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply',radialPolynomialEuler_coeff,ih,pow_succ]
      ring

theorem spectralRemote_polynomial_euler_degree (P : ℂ[X]) (d k : ℕ) (hP : P.natDegree ≤ d) :
    ((radialPolynomialEuler^[k]) P).natDegree ≤ d := by
  induction k with
  | zero => exact hP
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact radialPolynomialEuler_degree _ d ih

theorem spectralRemote_polynomial_jet_bound (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d k : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (hP : ∀ i, i ≤ d → Tendsto (fun n => (P n).coeff i) atTop (𝓝 (Q.coeff i))) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n in atTop, ∀ t, 0 ≤ t →
      ‖iteratedDeriv k (radialExteriorPolynomialFunction (P n)) t‖ ≤ D := by
  have hu := radialPolynomialFunction_uniform_limit
    (fun n => (radialPolynomialEuler^[k]) (P n)) ((radialPolynomialEuler^[k]) Q) d
    (hdeg.mono (fun n hn => spectralRemote_polynomial_euler_degree (P n) d k hn))
    (spectralRemote_polynomial_euler_degree Q d k hQ)
    (fun i hi => by
      simpa only [spectralRemote_polynomial_euler_coeff] using (hP i hi).const_mul ((-2*(i : ℂ))^k))
  obtain ⟨D,hD,hDb⟩ := radialExteriorPolynomial_deriv_bounded Q k
  refine ⟨D+1,by positivity,?_⟩
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hu) 1 (by norm_num)] with n hn
  intro t ht
  have hh := hn t ht
  rw [← iteratedDeriv_radialExteriorPolynomial,← iteratedDeriv_radialExteriorPolynomial] at hh
  calc
    _ ≤ dist (iteratedDeriv k (radialExteriorPolynomialFunction (P n)) t)
        (iteratedDeriv k (radialExteriorPolynomialFunction Q) t)+
        ‖iteratedDeriv k (radialExteriorPolynomialFunction Q) t‖ := by
      rw [dist_eq_norm]
      simpa only [sub_add_cancel] using norm_add_le
        (iteratedDeriv k (radialExteriorPolynomialFunction (P n)) t-
          iteratedDeriv k (radialExteriorPolynomialFunction Q) t)
        (iteratedDeriv k (radialExteriorPolynomialFunction Q) t)
    _ ≤ 1+D := add_le_add (by simpa only [dist_comm] using hh.le) (hDb t ht)
    _ = D+1 := by ring

end DefocusingNLS

end OAI
