import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralSubunitCoefficients
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPolynomialSubunitLimit

namespace OAI

/-! Fixed coefficients of both linearized odd-power polynomials vanish as
the exponent grows and the background polynomial remains strictly subunit. -/

open Polynomial Filter Topology
namespace DefocusingNLS

theorem spectralPolynomial_circle_bound (P : ℂ[X]) (m : ℕ) (hm : 1 ≤ m)
    (ε ρ : ℝ) (hρ : 0 ≤ ρ)
    (hP : ∀ z : ℂ, ‖z‖=ε → ‖P.eval z‖ ≤ ρ) (z : ℂ) (hz : ‖z‖=ε) :
    ‖(spectralDiagonalPolynomial m P).eval z‖ ≤ (2*(m : ℝ)+1)*ρ^(2*m) ∧
    ‖(spectralCrossPolynomial m P).eval z‖ ≤ (2*(m : ℝ)+1)*ρ^(2*m) := by
  have hc : (Polynomial.mapRingHom (starRingEnd ℂ) P).eval z=star (P.eval (star z)) := by
    simpa using (Polynomial.eval_map_apply (p := P) (starRingEnd ℂ) (star z))
  have hp := hP z hz
  have hs := hP (star z) (by simpa only [norm_star] using hz)
  have hdiag : ‖(spectralDiagonalPolynomial m P).eval z‖ ≤ ((m : ℝ)+1)*ρ^(2*m) := by
    simp only [spectralDiagonalPolynomial,eval_mul,eval_C,eval_pow,hc,
      norm_mul,norm_pow,norm_star,Complex.norm_natCast]
    simp only [Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ((m : ℝ)+1)*ρ^m*ρ^m := by gcongr
      _ = _ := by rw [mul_assoc,← pow_add]; congr 2; omega
  have hcross : ‖(spectralCrossPolynomial m P).eval z‖ ≤ (m : ℝ)*ρ^(2*m) := by
    simp only [spectralCrossPolynomial,eval_mul,eval_C,eval_pow,hc,
      norm_mul,norm_pow,norm_star,Complex.norm_natCast]
    calc
      _ ≤ (m : ℝ)*ρ^(m+1)*ρ^(m-1) := by gcongr
      _ = _ := by rw [mul_assoc,← pow_add]; congr 2; omega
  constructor
  · exact hdiag.trans (mul_le_mul_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m] : (m : ℝ)+1 ≤ 2*(m : ℝ)+1)
      (pow_nonneg hρ _))
  · exact hcross.trans (mul_le_mul_of_nonneg_right (by nlinarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m] : (m : ℝ) ≤ 2*(m : ℝ)+1)
      (pow_nonneg hρ _))

theorem spectralPolynomial_coefficient_limit (P : ℕ → ℂ[X]) (Q : ℂ[X]) (d k : ℕ)
    (hdeg : ∀ᶠ n in atTop, (P n).natDegree ≤ d)
    (hP : ∀ j, j ≤ d → Tendsto (fun n => (P n).coeff j) atTop (𝓝 (Q.coeff j)))
    (hzero : ‖Q.coeff 0‖ < 1) :
    Tendsto (fun n => (spectralDiagonalPolynomial n (P n)).coeff k) atTop (𝓝 0) ∧
    Tendsto (fun n => (spectralCrossPolynomial n (P n)).coeff k) atTop (𝓝 0) := by
  obtain ⟨ε,ρ,hε,_hε1,hρ,hρ1,hcircle⟩ :=
    radialPolynomial_eventually_subunit_circle P Q d hdeg hP hzero
  have hlim : Tendsto (fun n : ℕ => ((2*(n : ℝ)+1)*ρ^(2*n))/ε^k) atTop (𝓝 0) := by
    simpa only [zero_div] using (spectralSubunitCoefficient_decay ρ hρ hρ1).div_const (ε^k)
  have hbound : ∀ᶠ n in atTop,
      ‖(spectralDiagonalPolynomial n (P n)).coeff k‖ ≤ ((2*(n : ℝ)+1)*ρ^(2*n))/ε^k ∧
      ‖(spectralCrossPolynomial n (P n)).coeff k‖ ≤ ((2*(n : ℝ)+1)*ρ^(2*n))/ε^k := by
    filter_upwards [hcircle,eventually_ge_atTop 1] with n hn hmn
    have hB : 0 ≤ (2*(n : ℝ)+1)*ρ^(2*n) := by positivity
    have hb := fun z hz => spectralPolynomial_circle_bound (P n) n hmn ε ρ hρ
      (fun w hw => hn w hw.le) z hz
    exact ⟨(le_div_iff₀ (pow_pos hε k)).mpr
      (radialPolynomial_coefficient_scaled_bound _ ε _ hε.le hB (fun z hz => (hb z hz).1) k),
      (le_div_iff₀ (pow_pos hε k)).mpr
      (radialPolynomial_coefficient_scaled_bound _ ε _ hε.le hB (fun z hz => (hb z hz).2) k)⟩
  exact ⟨squeeze_zero_norm' (hbound.mono (fun _ h => h.1)) hlim,
    squeeze_zero_norm' (hbound.mono (fun _ h => h.2)) hlim⟩

end DefocusingNLS

end OAI
