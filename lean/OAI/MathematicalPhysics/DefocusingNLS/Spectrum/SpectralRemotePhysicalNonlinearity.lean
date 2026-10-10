import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRemotePhysicalCoefficientScale

namespace OAI

/-! Uniform physical odd-power coefficient symbols. The radial decay order
is independent of the growing nonlinearity power. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralRemote_physical_nonlinear_symbols
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (nu : ℕ → ℂ)
    (hscale : ∀ n, 2*(m n : ℝ)*(nu n).re = -2)
    (B : ℝ) (hB : 0 ≤ B) (hnu : ∀ᶠ n in atTop, |(nu n).im| ≤ B)
    (q : ℕ → ℝ → ℂ) (hq : HasUniformLogJetBound L 0 q)
    (rho : ℝ) (hrho : 0 ≤ rho) (hrho1 : rho < 1)
    (hb : ∀ᶠ n in atTop, ∀ t ∈ Ioi (L n), ‖q n t‖ ≤ rho) :
    HasUniformLogJetBound L (-2) (fun n t =>
      spectralDiagonalCoefficient (m n) (Complex.exp (nu n*(t : ℂ))*q n t)) ∧
    HasUniformLogJetBound L (-2) (fun n t =>
      spectralCrossCoefficient (m n) (Complex.exp (nu n*(t : ℂ))*q n t)) := by
  obtain ⟨hd,hc⟩ := spectralRemote_nonlinear_circular_symbols hL m hm q hq rho hrho hrho1 hb
  have he : HasUniformLogJetBound L (-2) (fun (_ : ℕ) t => Complex.exp ((-2 : ℂ)*(t : ℂ))) :=
    spectralRemote_complex_exponential_symbol (fun _ => -2) 2 (-2) (by norm_num)
      (Eventually.of_forall (fun _ => by norm_num)) (fun _ => by norm_num)
  let beta := fun n => (-2 : ℂ)+2*Complex.I*((nu n).im : ℂ)
  have hbeta : ∀ᶠ n in atTop, ‖beta n‖ ≤ 2+2*B := by
    filter_upwards [hnu] with n hn
    calc
      _ ≤ ‖(-2 : ℂ)‖+‖2*Complex.I*((nu n).im : ℂ)‖ := norm_add_le _ _
      _ = 2+2*|(nu n).im| := by norm_num [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      _ ≤ _ := by linarith
  have heb := spectralRemote_complex_exponential_symbol (L := L) beta (2+2*B) (-2)
    (by positivity) hbeta (fun n => by simp [beta,Complex.mul_re,Complex.mul_im])
  have hmp : ∀ᶠ n in atTop, 1 ≤ m n := hm.eventually (eventually_ge_atTop 1)
  constructor
  · have hprod : HasUniformLogJetBound L (-2) (fun n t =>
        Complex.exp ((-2 : ℂ)*(t : ℂ))*spectralDiagonalCoefficient (m n) (q n t)) := by
      simpa only [add_zero] using he.mul hd
    apply hprod.eventually_congr
    filter_upwards [hmp] with n hn
    intro t ht
    exact (spectralRemote_physical_coefficient_factors (m n) hn (nu n) (q n t) t (hscale n)).1.symm
  · have hprod : HasUniformLogJetBound L (-2) (fun n t =>
        Complex.exp (beta n*(t : ℂ))*spectralCrossCoefficient (m n) (q n t)) := by
      simpa only [add_zero] using heb.mul hc
    apply hprod.eventually_congr
    filter_upwards [hmp] with n hn
    intro t ht
    exact (spectralRemote_physical_coefficient_factors (m n) hn (nu n) (q n t) t (hscale n)).2.symm

end DefocusingNLS

end OAI
