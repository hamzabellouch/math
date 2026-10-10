import Mathlib

namespace OAI

section

noncomputable section
open Set Filter
open scoped Topology

namespace WeakMTWTransport
section DualCompact
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local instance dualCompactGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance dualCompactSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
lemma exists_dual_limit [FiniteDimensional ℝ E]
    {gj:ℕ → E →L[ℝ] ℝ} {C:ℝ}
    (hb:∀ᶠ j in atTop,‖gj j‖≤C) :
    ∃g:E →L[ℝ] ℝ,∃σ:ℕ → ℕ,StrictMono σ ∧ Tendsto (gj ∘ σ) atTop (𝓝 g) := by
  let : FiniteDimensional ℝ (E →L[ℝ] ℝ) := ContinuousLinearMap.finiteDimensional
  obtain ⟨N,hN⟩:=eventually_atTop.mp hb
  have H : IsCompact (Metric.closedBall (0:E →L[ℝ] ℝ) C) := isCompact_closedBall _ _
  obtain ⟨g,hg,σ,hσ,hlim⟩:=H.tendsto_subseq (x := fun j => gj (j+N)) (fun j=>by
    simpa only [Metric.mem_closedBall,dist_zero_right] using hN (j+N) (Nat.le_add_left _ _))
  exact ⟨g,fun j=>σ j+N,fun i j hij=>Nat.add_lt_add_right (hσ hij) N,hlim⟩
end DualCompact
end WeakMTWTransport

end
end

end OAI
