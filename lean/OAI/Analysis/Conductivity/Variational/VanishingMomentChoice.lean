import Mathlib
import OAI.Analysis.Conductivity.Variational.SynchronizedChartWaves

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Matrix Filter Topology

lemma exists_vanishing_moment_selection {P : Type*} [TopologicalSpace P]
    {p : P} {m : P → Coord3} (hm : Tendsto m (𝓝 p) (𝓝 0))
    {C : ℝ} {R : P → Coord3 → Prop}
    (he : ∀ᶠ q in 𝓝 p,∃ c : Coord3,‖c‖≤C*‖m q‖ ∧ R q c) :
    ∃ c : P → Coord3,Tendsto c (𝓝 p) (𝓝 0) ∧ ∀ᶠ q in 𝓝 p,R q (c q) := by
  classical
  have hx (q : P) : ∃ c : Coord3,
      (∃ d : Coord3,‖d‖≤C*‖m q‖ ∧ R q d) → ‖c‖≤C*‖m q‖ ∧ R q c := by
    by_cases h : ∃ d : Coord3,‖d‖≤C*‖m q‖ ∧ R q d
    · obtain ⟨c,hc⟩ := h
      exact ⟨c,fun _ => hc⟩
    · exact ⟨0,fun h' => (h h').elim⟩
  choose c hc using hx
  have hb : ∀ᶠ q in 𝓝 p,‖c q‖≤C*‖m q‖ ∧ R q (c q) := he.mono (fun q hq => hc q hq)
  refine ⟨c,?_,hb.mono (fun _ h => h.2)⟩
  apply squeeze_zero_norm' (hb.mono (fun _ h => h.1))
  simpa only [norm_zero,mul_zero] using hm.norm.const_mul C

end ScalarConductivity

end
end

end OAI
