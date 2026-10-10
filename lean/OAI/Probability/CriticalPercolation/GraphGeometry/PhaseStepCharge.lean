import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.GraphGeometry.WiredEvent
import OAI.Probability.CriticalPercolation.GraphGeometry.ProbIsolateThree

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.BondGraph
open scoped Classical
open FiniteProduct

variable {V E : Type*} [Fintype V] [Fintype E] (G : BondGraph V E)

lemma phase_step_charge (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (hn : ∀ e b, 0 ≤ w e b) (e : E) (a s t v b : V)
    (has : a ≠ s) (hat : a ≠ t) (hst : s ≠ t)
    {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (he0 : w e False = 1-p) (he1 : w e True = p)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    (1-p)*delta w (G.wiredEvent a s t) e *
      prob w (fun ω => G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω) ≤
    potential w (G.isolateThree a s t) (G.joinedPair a s t) -
      ((1-p)*potential (pin w e False) (G.isolateThree a s t) (G.joinedPair a s t) +
      p*potential (pin w e True) (G.isolateThree a s t) (G.joinedPair a s t)) := by
  have h0 : w e False ≠ 0 := by rw [he0]; exact (sub_pos.mpr hp.2).ne'
  have h1 : w e True ≠ 0 := by rw [he1]; exact hp.1.ne'
  rw [potential_split w hn e _ _ (fun _ h => h.1) hp.1 hp.2 he0 he1,
    G.phase_delta_rewire w hw e h0 h1 a s t v b he hv,
    G.phase_pair_mass w hw e h0 h1 a s t v b he hv,he1,
    G.phase_avoid_rewire w hw e h0 h1 a s t v b he hv,
    G.phase_target_rewire w hw e h0 h1 a s t v b he hv]
  have hh := G.wired_pair_charge (pin w e False) (pin_normalized w hw e False)
    (pin_nonneg w hn e False) a s t b has hat hst hp
  dsimp only at hh
  convert hh using 1
  ring

end CriticalPercolation.BondGraph

end
end

end OAI
