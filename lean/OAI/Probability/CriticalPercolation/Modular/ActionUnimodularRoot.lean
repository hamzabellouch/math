import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.GraphGeometry.GraphActionCoordinates
import OAI.Probability.CriticalPercolation.Modular.ActionMassTransport
import OAI.Probability.CriticalPercolation.Modular.Unimodularity

namespace OAI

section
noncomputable section
open Set
open scoped Classical BigOperators

namespace CriticalPercolation.BondGraph
variable {V E Λ : Type*} [Group Λ] [MulAction Λ V] [MulAction Λ E]
    (G : BondGraph V E)

def unimodularRoot_of_action (ha : G.PreservesEnds (Λ := Λ))
    (S : Set V) (hS : S.Finite) (hcover : ∀ x, ∃ u∈S, x∈MulAction.orbit Λ u)
    (o : V) (w : V → ℝ) (hp : ∀ x, 0<w x)
    (hw : ∀ (φ : Λ) x, w (φ • x) = w x)
    (hfin : ∀ x y, (ActionOrbitTransport.stabilizerOrbit Λ V x y).Finite)
    (hbal : ∀ x y, w x * (ActionOrbitTransport.suborbitCard Λ V x y : ℝ) =
      w y * (ActionOrbitTransport.suborbitCard Λ V y x : ℝ)) : G.UnimodularRoot := by
  let R := ActionOrbitTransport.representatives Λ V S hS hcover
  let Z := ∑ x∈R.roots, w x
  have hZ : 0<Z := by
    obtain ⟨u,hu,_,_⟩ := R.cover o
    exact Finset.sum_pos' (fun x _ => (hp x).le) ⟨u,hu,hp u⟩
  let W := fun x => w x / Z
  have hW : ∀ (φ : Λ) x, W (φ • x) = W x := by
    intro φ x
    simp only [W,hw]
  have hB (x y : V) : W x * (ActionOrbitTransport.suborbitCard Λ V x y : ℝ) =
      W y * (ActionOrbitTransport.suborbitCard Λ V y x : ℝ) := by
    simp only [W,div_mul_eq_mul_div,hbal]
  refine ⟨R.roots,W,?_,?_,?_,?_⟩
  · intro x _
    exact div_pos (hp x) hZ
  · change (∑ x∈R.roots,w x/Z)=1
    rw [←Finset.sum_div,div_self (ne_of_gt hZ)]
  · intro v
    obtain ⟨u,hu,φ,hφ⟩ := R.cover v
    exact ⟨u,hu,G.smulAut ha φ,hφ⟩
  · intro F hF hr hc
    exact ActionOrbitTransport.Representatives.massTransport Λ V R hfin W hW hB F
      (fun φ x y => hF (G.smulAut ha φ) x y) hr hc

end CriticalPercolation.BondGraph
end
end

end OAI
