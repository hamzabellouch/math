import OAI.Combinatorics.EditApproximation.Binary.IntegerPreprocessing

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 theorem fixed_height_power_subpolynomial (k : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (inputHeight N : ℝ) ^ k ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (k : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((k : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1; ext N; ring
  filter_upwards [subexponential_height_to_input _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) k (Nat.two_pow_pos _)] at hN

end EditApproximation

end OAI
