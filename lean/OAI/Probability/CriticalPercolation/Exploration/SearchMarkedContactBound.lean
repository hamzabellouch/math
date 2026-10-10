import Mathlib
import OAI.Probability.CriticalPercolation.Exploration.ClosedPivotWeight

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators
open scoped Classical

namespace CriticalPercolation.LazyDFS
open scoped Classical
open FiniteProduct SearchTree

variable {V E : Type*} [Fintype E] [Fintype V] [DecidableEq V] [DecidableEq E]

theorem search_marked_contact_bound (G : BondGraph V E) (B : Set V)
    (order : List (Dart V E)) (horder : GoodDarts G order) (ho : Exhaustive G order)
    (a : V) {p : ℝ} (hp : p ∈ Set.Ioo 0 1) (w : E → Prop → ℝ)
    (h0 : ∀ e, w e False = 1-p) (h1 : ∀ e, w e True = p) :
    let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
    let T := search G order a B
    expect w (fun ω => ∑ e, T.closedPivotWeight p F w ω e *
      (1 + T.prefixScore p F w (Function.update ω e True) e)) ≤ 4 := by
  let F := fun ω : Set E => ∃ b ∈ B, (G.openGraph ω).Reachable a b
  let T := search G order a B
  have hv : T.Valid ∅ := compile_valid G order B _ _ _
  have hF : ∀ s t, s ⊆ t → F s → F t := by
    rintro s t hst ⟨b,hb,hab⟩
    exact ⟨b,hb,hab.mono (G.openGraph_mono hst)⟩
  have hm := search_target_pivotal_moments G B order horder ho a hp w h0 h1
  have hb := marked_prefix_bound T ∅ hv hp F hF w (homogeneous_normalized w p h0 h1)
    (fun e b => (homogeneous_positive w hp h0 h1 e b).le)
    (fun e _ => ⟨h0 e,h1 e⟩) h0 h1
  exact hb.trans (by linarith [hm.1,hm.2])

end CriticalPercolation.LazyDFS

end
end

end OAI
