import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralLiouvilleInverseEnergy
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace OAI

/-! Bounded transformed Cauchy data give bounded physical boundary energy. -/

open Filter Topology
namespace DefocusingNLS

theorem spectralPhysicalLiouvillePair_eventual_energy_bound
    (B M : ℝ) (hB : 0 < B) (_hM : 0 ≤ M)
    (omega : ℕ → ℝ) (hw : Tendsto omega atTop atTop) (f g : ℕ → ℝ → ℂ)
    (hp : Tendsto (fun n => (Real.sqrt (omega n) : ℂ)*
      (spectralPhysicalLiouvillePair (f n) (g n) B).1.1) atTop (𝓝 0))
    (hdp : Tendsto (fun n => (spectralPhysicalLiouvillePair (f n) (g n) B).1.2) atTop (𝓝 0))
    (hm : ∀ᶠ n in atTop,
      ‖(spectralPhysicalLiouvillePair (f n) (g n) B).2.2‖^2+
        omega n*‖(spectralPhysicalLiouvillePair (f n) (g n) B).2.1‖^2 ≤ M) :
    ∀ᶠ n in atTop, spectralPhysicalShellDensity (f n) (g n) B ≤
      (3+2*(11/(2*B)+B/4)^2)*(2+M) := by
  have hp' : Tendsto (fun n => ‖(Real.sqrt (omega n) : ℂ)*
      (spectralPhysicalLiouvillePair (f n) (g n) B).1.1‖^2) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0)] using hp.norm.pow 2
  have hdp' : Tendsto (fun n => ‖(spectralPhysicalLiouvillePair (f n) (g n) B).1.2‖^2)
      atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by decide : 2 ≠ 0)] using hdp.norm.pow 2
  filter_upwards [hm,hw.eventually (eventually_ge_atTop 1),
    hp'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1)),
    hdp'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1))] with n hmn hwn hpn hdn
  have hw0 : 0 ≤ omega n := by linarith
  rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hw0] at hpn
  have hvalp : ‖(spectralPhysicalLiouvillePair (f n) (g n) B).1.1‖^2 ≤ 1 := by
    nlinarith [sq_nonneg ‖(spectralPhysicalLiouvillePair (f n) (g n) B).1.1‖]
  have hvalm : ‖(spectralPhysicalLiouvillePair (f n) (g n) B).2.1‖^2+
      ‖(spectralPhysicalLiouvillePair (f n) (g n) B).2.2‖^2 ≤ M := by
    nlinarith [sq_nonneg ‖(spectralPhysicalLiouvillePair (f n) (g n) B).2.1‖]
  exact (spectralPhysicalLiouvillePair_inverse_energy B hB (f n) (g n)).trans
    (mul_le_mul_of_nonneg_left (by linarith) (by positivity))

end DefocusingNLS

end OAI
