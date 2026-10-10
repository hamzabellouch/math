import OAI.NumberTheory.Ostmann.Tree.CycleSelection
import OAI.NumberTheory.Ostmann.Tree.Diagram

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators

def labelProducts {E V U : Type*} [Fintype E] [DecidableEq V] [CommGroup U]
    (label : E → V) : (E → U) →* (V → U) where
  toFun M v := ∏ e with label e=v, M e
  map_one' := by funext v; simp
  map_mul' M N := by funext v; simp [Finset.prod_mul_distrib]

theorem labelProducts_surjective {E V U : Type*} [Fintype E] [DecidableEq V] [CommGroup U]
    (label : E → V) (hl : Function.Surjective label) :
    Function.Surjective (labelProducts (U:=U) label) := by
  classical
  let s : V → E := fun v => Classical.choose (hl v)
  have hs : ∀v,label (s v)=v := fun v => Classical.choose_spec (hl v)
  intro t
  let M : E → U := fun e => if e=s (label e) then t (label e) else 1
  refine ⟨M,?_⟩
  funext v
  change (∏ e with label e=v, M e)=t v
  rw [Finset.prod_eq_single (s v)]
  · simp [M,hs]
  · intro e he hne
    have hv := (Finset.mem_filter.mp he).2
    simp [M,hv,hne]
  · intro hn
    exact False.elim (hn (by simp [hs]))

theorem BalancedSelection.labelProducts_act {E V W U : Type*} [Fintype E]
    [DecidableEq E] [DecidableEq V] [DecidableEq W] [CommGroup U]
    {left : E → V} {right : E → W} (c : BalancedSelection left right)
    (z : U) (M : E → U) : labelProducts left (c.act z M)=labelProducts left M := by
  funext v
  exact c.left_product z M v

def BalancedSelection.actEquiv {E V W U : Type*}
    [DecidableEq E] [DecidableEq V] [DecidableEq W] [CommGroup U]
    {left : E → V} {right : E → W} (c : BalancedSelection left right)
    (z : U) : (E → U) ≃ (E → U) where
  toFun := c.act z
  invFun := c.act z⁻¹
  left_inv M := by rw [← c.act_mul,inv_mul_cancel,c.act_one]
  right_inv M := by rw [← c.act_mul,mul_inv_cancel,c.act_one]

end
end Ostmann.Tree

end OAI
