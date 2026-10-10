import Mathlib

namespace OAI

noncomputable section
open Set Filter Function Metric
open scoped Topology
open Set Filter Function Metric
open scoped Topology ContDiff InnerProductSpace
namespace YauCounterexamples

theorem radial_trace_absorption (L b K S δ f e T : ℝ)
    (hb : 0 ≤ b) (hK : 0 ≤ K) (_hS : 0 ≤ S)
    (hf : f^2 ≤ S*b) (hsmall : 9216*K*S*δ^2 ≤ 1)
    (htrace : L^2/16*b-288*K*δ^2*L^2*f^2-8*K*e^2 ≤ T) :
    L^2/32*b-8*K*e^2 ≤ T := by
  have h1 := mul_le_mul_of_nonneg_left hf
    (show 0 ≤ 288*K*δ^2*L^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ L^2*b/32 by positivity)
  nlinarith only [h1,h2,htrace]
end YauCounterexamples

open Filter Set
open scoped Topology

end

end OAI
