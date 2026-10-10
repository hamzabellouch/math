import Mathlib
import OAI.Combinatorics.UniformKServer.FiniteLawTheorem
import OAI.Combinatorics.UniformKServer.FiniteFlowMinimax

namespace OAI

noncomputable section

/-! A single finite-horizon strongly lazy flow, now independent of the law. Its
additive endpoint is uniform over horizons and all words. -/
namespace UniformKServer.OfflineLaw
open Finset FiniteProbability PartitionTree FiniteFlowSpace RealFlow TreeRounding
open scoped Classical
variable {n k : ℕ} [NeZero k]
local instance configEqHP : DecidableEq (Configuration n k) := fun a b=>Classical.propDecidable (a=b)

theorem horizon_policy (d : RationalMetric n) (s : Configuration n k) (hk : 2≤k) :
    ∃ B : ℝ,∀ N : ℕ,∃ F : Data (Fin n) (Configuration n k) (Fin k),
      Valid F serve PublicInput.allowed s N ∧
      ∀w : List (Fin n),w.length≤N →
        flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] w≤
          absoluteRate*(Real.log (k+1))^2*offlineCost d s w+B := by
  obtain ⟨B,hB⟩ := finite_law d s hk
  refine ⟨B,?_⟩
  intro N
  let q : Word (Fin n) N→ℝ := fun v=>absoluteRate*(Real.log (k+1))^2*offlineCost d s (letters v)+B
  have hL (P : Law (Word (Fin n) N)) : ∃F : Data (Fin n) (Configuration n k) (Fin k),
      Valid F serve PublicInput.allowed s N ∧
      P.expect (fun v=>flowCost F (fun c r j=>(d.distance (c j) r : ℝ)) [] (letters v))≤P.expect q := by
    obtain ⟨F,hF,hc⟩ := hB (Word (Fin n) N) N letters P letters_bound
    refine ⟨F,hF,?_⟩
    simpa only [q,Law.expect_add,Law.expect_mul,Law.expect_const] using hc
  obtain ⟨F,hF,hcost⟩ := eliminate serve PublicInput.allowed s
    (fun c r j=>(d.distance (c j) r : ℝ)) q hL
  refine ⟨F,hF,?_⟩
  intro w hw
  simpa only [q,letters_code] using hcost (code w hw)

end UniformKServer.OfflineLaw

end

end OAI
