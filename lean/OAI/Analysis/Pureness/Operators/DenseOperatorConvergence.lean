import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.MetricSpace.Equicontinuity

namespace OAI
noncomputable section
namespace CuntzPureness
open Filter Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def boundedOperatorConvergenceSubmodule (F : ℕ → E →L[ℂ] E) : Submodule ℂ E where
  carrier := {x | Tendsto (fun n => F n x) atTop (nhds x)}
  zero_mem' := by simpa only [Set.mem_ofPred_eq, map_zero] using tendsto_const_nhds (x := (0 : E))
  add_mem' := by
    intro x y hx hy
    simpa only [Set.mem_ofPred_eq, map_add] using hx.add hy
  smul_mem' := by
    intro c x hx
    simpa only [Set.mem_ofPred_eq, map_smul] using hx.const_smul c

lemma boundedOperatorConvergenceSubmodule_closed (F : ℕ → E →L[ℂ] E)
    (C : ℝ) (hC : ∀ n x, ‖F n x‖ ≤ C * ‖x‖) :
    IsClosed (boundedOperatorConvergenceSubmodule F : Set E) := by
  have he : Equicontinuous (fun n x => F n x) :=
    Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => C * r)
      (by
        have hb : Continuous (fun r : ℝ => C * r) := continuous_const.mul continuous_id
        simpa only [mul_zero] using hb.tendsto 0)
      (fun n x => F n x) (fun x y n => by
        simpa only [dist_eq_norm, ← map_sub] using hC n (x-y))
  exact he.isClosed_setOfPred_tendsto continuous_id

theorem boundedOperators_tendsto_of_dense_span {ι : Type*} (v : ι → E)
    (hd : Dense (Submodule.span ℂ (Set.range v) : Set E))
    (F : ℕ → E →L[ℂ] E) (C : ℝ) (hC : ∀ n x, ‖F n x‖ ≤ C * ‖x‖)
    (hv : ∀ i, Tendsto (fun n => F n (v i)) atTop (nhds (v i))) (x : E) :
    Tendsto (fun n => F n x) atTop (nhds x) := by
  have hs : Submodule.span ℂ (Set.range v) ≤ boundedOperatorConvergenceSubmodule F :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hv i)
  exact closure_minimal hs (boundedOperatorConvergenceSubmodule_closed F C hC) (hd x)
end CuntzPureness

end

end OAI
