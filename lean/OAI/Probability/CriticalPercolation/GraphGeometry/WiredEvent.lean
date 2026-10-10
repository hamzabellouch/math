import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.IsolateThree
import OAI.Probability.CriticalPercolation.ProductMeasure.Delta
import OAI.Probability.CriticalPercolation.GraphGeometry.ReachableReplaceTail
import OAI.Probability.CriticalPercolation.ProductMeasure.ProbRequiresBit

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

variable {V E : Type*} (G : BondGraph V E)

def wiredEvent (a s t : V) (ω : Set E) : Prop :=
  ((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t

lemma wiredEvent_mono (a s t : V) :
    ∀ (ω ω' : Set E), ω ⊆ ω' → G.wiredEvent a s t ω → G.wiredEvent a s t ω' := by
  intro ω ω' h hF
  exact hF.mono (sup_le_sup_right (G.openGraph_mono h) _)

lemma earlier_pivot_iff (a s t : V) (ω : Set E) :
    (G.wiredEvent a s t ω ∧ ¬(G.openGraph ω).Reachable a t) ↔ G.joinedPair a s t ω := by
  dsimp [wiredEvent,joinedPair,isolateThree]
  constructor
  · rintro ⟨hf,hat⟩
    have hst : (G.openGraph ω).Reachable s t := by
      rcases (Wiring.reachable_sup_edge (G.openGraph ω) a s a t).mp hf with h | ⟨_,h⟩ | ⟨_,h⟩
      · exact (hat h).elim
      · exact h
      · exact (hat h).elim
    exact ⟨⟨fun has => hat (has.trans hst),hat⟩,hst⟩
  · rintro ⟨⟨_,hat⟩,hst⟩
    exact ⟨(Wiring.reachable_sup_edge (G.openGraph ω) a s a t).mpr
      (Or.inr (Or.inl ⟨.refl _,hst⟩)),hat⟩

lemma reachable_force_rewire (e : E) (s v b x y : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) :
    (G.openGraph (Function.update ω e True)).Reachable x y ↔
      ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable x y := by
  rw [G.openGraph_force_true ω e v b he]
  exact Wiring.reachable_replace_tail _ s v b x y hv

lemma wired_force_rewire (e : E) (a s t v b : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) :
    G.wiredEvent a s t (Function.update ω e True) ↔
      ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t := by
  dsimp only [wiredEvent]
  rw [G.openGraph_force_true ω e v b he,sup_right_comm]
  exact Wiring.reachable_replace_tail _ s v b a t (hv.mono le_sup_left)

lemma phase_pair_force (e : E) (a s t v b : V) (ω : Set E)
    (he : G.ends e = s(v,b)) (hv : (G.openGraph ω).Reachable s v) (hclosed : ¬ω e) :
    (G.joinedPair a s t (Function.update ω e True) ∧
      openPivot (G.wiredEvent a s t) e (Function.update ω e True)) ↔
    (((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
      ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  erw [← G.earlier_pivot_iff,openPivot_force_true,G.wired_force_rewire e a s t v b ω he hv,
    G.reachable_force_rewire e s v b a t ω he hv]
  have hu : Function.update ω e False = ω := by
    have hb : ω e = False := propext (iff_false_intro hclosed)
    rw [← hb]
    exact Function.update_eq_self _ _
  rw [hu]
  dsimp only [wiredEvent]
  tauto

variable [Fintype E]

lemma phase_delta_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    delta w (G.wiredEvent a s t) e =
      prob (pin w e False) (fun ω =>
        ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t) := by
  rw [delta_eq_pivotal w hw e he0 he1 _ (G.wiredEvent_mono a s t)]
  apply prob_congr_support
  intro ω hω
  rw [G.wired_force_rewire e a s t v b ω he (hv ω hω)]
  rfl

lemma phase_pair_mass (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob w (fun ω => G.joinedPair a s t ω ∧ openPivot (G.wiredEvent a s t) e ω) =
      w e True * prob (pin w e False) (fun ω =>
        ((G.openGraph ω) ⊔ SimpleGraph.edge a s ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge a s).Reachable a t ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  rw [prob_requires_bit w e True _ (fun ω h => propext (iff_true_intro h.2.1)),
    prob_pin_transport w hw e False True he0 he1]
  congr 1
  apply prob_congr_support
  intro ω hω
  have hb := density_pin_support w e False ω hω
  exact G.phase_pair_force e a s t v b ω he (hv ω hω) (by simp only [hb,not_false_eq_true])

lemma phase_avoid_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob (pin w e True) (G.isolateThree a s t) =
      prob (pin w e False) (fun ω =>
        ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t) := by
  rw [prob_pin_transport w hw e False True he0 he1]
  apply prob_congr_support
  intro ω hω
  dsimp only [isolateThree]
  rw [G.reachable_force_rewire e s v b a s ω he (hv ω hω),
    G.reachable_force_rewire e s v b a t ω he (hv ω hω)]

lemma phase_target_rewire (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (e : E) (he0 : w e False ≠ 0) (he1 : w e True ≠ 0) (a s t v b : V)
    (he : G.ends e = s(v,b))
    (hv : ∀ ω, density (pin w e False) ω ≠ 0 → (G.openGraph ω).Reachable s v) :
    prob (pin w e True) (G.joinedPair a s t) =
      prob (pin w e False) (fun ω =>
        ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a s ∧
          ¬((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable a t ∧
          ((G.openGraph ω) ⊔ SimpleGraph.edge s b).Reachable s t) := by
  rw [prob_pin_transport w hw e False True he0 he1]
  apply prob_congr_support
  intro ω hω
  dsimp only [joinedPair,isolateThree]
  rw [G.reachable_force_rewire e s v b a s ω he (hv ω hω),
    G.reachable_force_rewire e s v b a t ω he (hv ω hω),
    G.reachable_force_rewire e s v b s t ω he (hv ω hω)]
  tauto

end CriticalPercolation.BondGraph

end
end

end OAI
