import OAI.MathematicalPhysics.ContinuumCoulomb.Nuclei.RoundingPolynomialBudget

namespace OAI

/-! Fixed exponent choices absorb all three physical simulation errors
inside the margin retained by the positive-spin source program. -/

noncomputable section
namespace ContinuumCoulomb

theorem physical_promise_error_budget {N M scale : ℝ}
    (hN : 2 ≤ N) (hM : 1 ≤ M) (hMN : M ≤ N) (hscale : 1 ≤ scale)
    (s B p g q : ℕ) (hp : 60*B+s+14 ≤ p) (hg : s+14 ≤ g)
    (hq : 60*B+s+14 ≤ q) :
    scale*(N^p)⁻¹ + scale*(N^g)⁻¹*((N^(30*B))⁻¹)^2 + 1/(N^q+1) ≤
      scale*((N^(30*B))⁻¹)^2*(1/(2048*M^s)) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hM0 : 0 < M := by linarith
  have hscale0 : 0 ≤ scale := by linarith
  have hi {a b : ℕ} (hab : b ≤ a) : (N^a)⁻¹ ≤ (N^b)⁻¹ := by
    exact inv_anti₀ (pow_pos hN0 b) (pow_le_pow_right₀ hN1 hab)
  have hid : (N^(60*B+s+14))⁻¹ = ((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    rw [show 60*B+s+14=(30*B)*2+(s+14) by omega,pow_add,pow_mul,mul_inv_rev,inv_pow]
    ring
  have hcont : scale*(N^p)⁻¹ ≤ scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left (hi hp) hscale0
    simpa only [hid,mul_assoc] using hh
  have hfinite : scale*(N^g)⁻¹*((N^(30*B))⁻¹)^2 ≤
      scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hh := mul_le_mul_of_nonneg_left (hi hg)
      (mul_nonneg hscale0 (sq_nonneg ((N^(30*B))⁻¹)))
    simpa only [mul_assoc,mul_comm,mul_left_comm] using hh
  have hnum : 1/(N^q+1) ≤ scale*((N^(30*B))⁻¹)^2*(N^(s+14))⁻¹ := by
    have hfirst : 1/(N^q+1) ≤ (N^q)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hN0 q)
        (show N^q ≤ N^q+1 by linarith)
    have hsecond := (hi hq).trans (le_mul_of_one_le_left (by positivity) hscale)
    exact hfirst.trans (by simpa only [hid,mul_assoc] using hsecond)
  have htail : 3*(N^(s+14))⁻¹ ≤ 1/(2048*M^s) := by
    have hpow : (6144:ℝ) ≤ N^14 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hN 14
      norm_num at hh
      linarith
    have hproduct : 3*(2048*M^s) ≤ N^(s+14) := by
      rw [pow_add]
      calc
        _ = M^s*6144 := by ring
        _ ≤ N^s*N^14 := mul_le_mul (pow_le_pow_left₀ hM0.le hMN s) hpow
          (by norm_num) (pow_nonneg hN0.le s)
    exact (div_le_div_iff₀ (pow_pos hN0 (s+14)) (by positivity : 0 < 2048*M^s)).mpr
      (by simpa only [one_mul] using hproduct)
  have ht := mul_le_mul_of_nonneg_left htail
    (mul_nonneg hscale0 (sq_nonneg ((N^(30*B))⁻¹)))
  nlinarith only [hcont,hfinite,hnum,ht]

end ContinuumCoulomb

end

end OAI
