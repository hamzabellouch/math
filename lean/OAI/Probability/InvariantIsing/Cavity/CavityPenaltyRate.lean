import OAI.Probability.InvariantIsing.Cavity.CavityAmplitudePenalty
import OAI.Probability.InvariantIsing.Arrays.TensorMinimumPressure

namespace OAI

/-! The extension penalty is negligible in each fixed-size cavity step. -/

noncomputable section
open Filter
open scoped Topology

namespace InvariantIsing

lemma cavity_extension_penalty_tendsto (n : ℕ) :
    Tendsto (fun N : ℕ => (N+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^N) atTop (𝓝 0) := by
  have hlin : Tendsto (fun N : ℕ => (N : ℝ)*(1/2:ℝ)^N) atTop (𝓝 0) := by
    simpa only [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 (r := (1/2:ℝ)) (by norm_num)).tendsto_atTop_zero
  have hgeom : Tendsto (fun N : ℕ => (1/2:ℝ)^N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hh := (hlin.add (hgeom.const_mul (n : ℝ))).const_mul (1/4:ℝ)
  simp only [mul_zero, add_zero] at hh
  convert hh using 1
  funext N
  ring

lemma cavity_total_minimum_penalty_tendsto (N : ℕ → ℕ) (hN : Tendsto N atTop atTop)
    (n : ℕ) (p : ℕ → ℝ) (hp : Tendsto p atTop (𝓝 0)) :
    Tendsto (fun r => (n : ℝ)*p r+(N r+n : ℝ)*(1/4:ℝ)*(1/2:ℝ)^(N r)) atTop (𝓝 0) := by
  simpa only [mul_zero, add_zero, Function.comp_def] using
    (hp.const_mul (n : ℝ)).add ((cavity_extension_penalty_tendsto n).comp hN)

end InvariantIsing

end

end OAI
