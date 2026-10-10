import Mathlib
import OAI.Probability.CriticalPercolation.GraphGeometry.EraseBond
import OAI.Probability.CriticalPercolation.GraphGeometry.WiredEvent

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

def connects (a t : V) (ω : Set E) : Prop := (G.openGraph ω).Reachable a t

lemma connects_mono (a t : V) : ∀ (ω ω' : Set E), ω ⊆ ω' → G.connects a t ω → G.connects a t ω' :=
  fun _ _ h => fun hr => hr.mono (G.openGraph_mono h)

lemma eraseBond_force (f : E) (a : V) (ω : Set E) (b : Prop) :
    (G.eraseBond f a).openGraph (Function.update ω f b) = (G.eraseBond f a).openGraph ω := by
  erw [G.eraseBond_openGraph,G.eraseBond_openGraph]
  congr 1
  ext e
  change (e ≠ f ∧ Function.update ω f b e) ↔ (e ≠ f ∧ e ∈ ω)
  by_cases h : e = f
  · subst e; simp
  · erw [Function.update_of_ne h]
    rfl

lemma connects_eq_wired_deleted (f : E) (a v z t : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z))
    (hv : ((G.eraseBond f a).openGraph ω).Reachable a v) :
    G.connects a t ω ↔ (G.eraseBond f a).wiredEvent a z t ω := by
  dsimp only [connects,wiredEvent]
  rw [G.openGraph_eq_eraseBond_sup f a v z ω hf he]
  exact Wiring.reachable_replace_tail _ a v z a t hv

lemma pivot_eq_deleted_joined (f : E) (a v z t : V) (ω : Set E)
    (hf : f ∈ ω) (he : G.ends f = s(v,z))
    (hv : ((G.eraseBond f a).openGraph ω).Reachable a v) :
    openPivot (G.connects a t) f ω ↔ (G.eraseBond f a).joinedPair a z t ω := by
  unfold openPivot
  rw [G.connects_eq_wired_deleted f a v z t ω hf he hv]
  have hclose : G.connects a t (Function.update ω f False) ↔
      ((G.eraseBond f a).openGraph ω).Reachable a t := by
    dsimp only [connects]
    erw [← G.eraseBond_openGraph_force_false]
  erw [hclose]
  exact (and_iff_right hf).trans ((G.eraseBond f a).earlier_pivot_iff a z t ω)

variable [Fintype E]

lemma deleted_joined_pin_eq (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (f : E) (h0 : w f False ≠ 0) (h1 : w f True ≠ 0) (a z t : V) :
    prob (pin w f True) ((G.eraseBond f a).joinedPair a z t) =
      prob (pin w f False) ((G.eraseBond f a).joinedPair a z t) := by
  rw [prob_pin_transport w hw f False True h0 h1]
  apply prob_congr
  intro ω
  dsimp [joinedPair,isolateThree]
  erw [G.eraseBond_force]

lemma delta_eq_deleted_joined (w : E → Prop → ℝ) (hw : ∀ e, ∑ b, w e b = 1)
    (f : E) (h0 : w f False ≠ 0) (h1 : w f True ≠ 0) (a v z t : V)
    (he : G.ends f = s(v,z))
    (hv : ∀ ω, density (pin w f False) ω ≠ 0 → ((G.eraseBond f a).openGraph ω).Reachable a v) :
    delta w (G.connects a t) f = prob (pin w f True) ((G.eraseBond f a).joinedPair a z t) := by
  rw [G.deleted_joined_pin_eq w hw f h0 h1 a z t,
    delta_eq_pivotal w hw f h0 h1 _ (G.connects_mono a t)]
  apply prob_congr_support
  intro ω hω
  have hf0 := density_pin_support w f False ω hω
  have hf1 : Function.update ω f True f := by
    erw [Function.update_self]
    trivial
  have hv' : ((G.eraseBond f a).openGraph (Function.update ω f True)).Reachable a v := by
    erw [G.eraseBond_force]
    exact hv ω hω
  have hopen := G.connects_eq_wired_deleted f a v z t (Function.update ω f True) hf1 he hv'
  have hgraph : G.openGraph ω = (G.eraseBond f a).openGraph ω := by
    erw [G.eraseBond_openGraph_force_false]
    have hu : Function.update ω f False = ω := by
      erw [← hf0,Function.update_eq_self]
    erw [hu]
  erw [hopen]
  dsimp only [wiredEvent,connects]
  erw [G.eraseBond_force,hgraph]
  exact (G.eraseBond f a).earlier_pivot_iff a z t ω

end CriticalPercolation.BondGraph

namespace CriticalPercolation.Wiring
variable {V : Type*}

lemma pivot_component_avoids (H : SimpleGraph V) (A B : Set V) (w a z : V)
    (ha : a ∈ A) (hA : ∀ u ∈ A, H.Reachable w u)
    (hopen : ∃ t ∈ B, (H ⊔ SimpleGraph.edge a z).Reachable w t)
    (hclosed : ¬∃ t ∈ B, H.Reachable w t) :
    (∃ t ∈ B, H.Reachable z t) ∧ ∀ u ∈ A, ¬H.Reachable z u := by
  obtain ⟨t,ht,hwt⟩ := hopen
  have hzt : H.Reachable z t := by
    rcases (reachable_sup_edge H a z w t).mp hwt with h | ⟨_,h⟩ | ⟨_,h⟩
    · exact (hclosed ⟨t,ht,h⟩).elim
    · exact h
    · exact (hclosed ⟨t,ht,(hA a ha).trans h⟩).elim
  refine ⟨⟨t,ht,hzt⟩,?_⟩
  intro u hu hzu
  exact hclosed ⟨t,ht,(hA u hu).trans (hzu.symm.trans hzt)⟩
end CriticalPercolation.Wiring

end
end

end OAI
