import Mathlib

namespace OAI

section
section
noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff NNReal

namespace WeakMTWTransport

lemma exists_convex_norm_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {p q : E} {N : ℝ} (hp : p∈S) (hq : q∈S)
    (hpN : ‖p‖^2≤N) (hqN : N≤‖q‖^2) :
    ∃ w∈convexHull ℝ S, ‖w‖^2=N := by
  let f : ℝ → E := fun t => (1-t) • p+t • q
  have hc : Continuous (fun t => ‖f t‖^2) := by dsimp [f]; fun_prop
  have h0 : ‖f 0‖^2≤N := by simpa [f] using hpN
  have h1 : N≤‖f 1‖^2 := by simpa [f] using hqN
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ)≤1) hc.continuousOn ⟨h0,h1⟩
  refine ⟨f t,?_,he⟩
  exact (convex_convexHull ℝ S) (subset_convexHull ℝ S hp) (subset_convexHull ℝ S hq)
    (by linarith only [ht.2]) ht.1 (by ring)

end WeakMTWTransport
end
end
end

end OAI
