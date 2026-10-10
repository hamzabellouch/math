import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.GaussianFrequency

namespace OAI

/-! The frequency evaluated by the literal programs satisfies exactly the
oscillator/slab relation and lies in the uniform spectral-gap regime. -/

noncomputable section
namespace ContinuumCoulomb

theorem manufactured_scale_positive {rho : ℕ} (hrho : 0 < rho)
    {N : ℝ} (hN : 2 ≤ N) (k : ℕ) : 0 < (8/(rho:ℝ))*(N^k)^30 := by
  have hr : (0:ℝ) < rho := by exact_mod_cast hrho
  have hNp : 0 < N := by linarith
  positivity

theorem manufactured_mesh_positive {N : ℝ} (hN : 2 ≤ N) (k : ℕ) :
    0 < 1/(N^k)^10 := by
  have hNp : 0 < N := by linarith
  positivity

theorem manufactured_frequency_relation (rho : ℕ) :
    (GaussianFrequency.frequency rho)^2 = 4*Real.pi*(rho:ℝ) := by
  unfold GaussianFrequency.frequency
  exact Real.sq_sqrt (by positivity)

theorem manufactured_frequency_ge_one {rho : ℕ} (hrho : 0 < rho) :
    1 ≤ GaussianFrequency.frequency rho := by
  have hr : (1:ℝ) ≤ rho := by exact_mod_cast Nat.succ_le_iff.mpr hrho
  have hp : (1:ℝ) ≤ 4*Real.pi := by linarith [Real.pi_gt_three]
  unfold GaussianFrequency.frequency
  apply Real.le_sqrt_of_sq_le
  simpa only [one_mul,one_pow] using mul_le_mul hp hr (by norm_num : (0:ℝ) ≤ 1) (by positivity : 0 ≤ 4*Real.pi)

theorem manufactured_frequency_positive {rho : ℕ} (hrho : 0 < rho) :
    0 < GaussianFrequency.frequency rho := lt_of_lt_of_le zero_lt_one (manufactured_frequency_ge_one hrho)

end ContinuumCoulomb

end

end OAI
