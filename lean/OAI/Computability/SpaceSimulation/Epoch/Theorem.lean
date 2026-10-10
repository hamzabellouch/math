import OAI.Computability.SpaceSimulation.Evaluation.Evaluate
import OAI.Computability.SpaceSimulation.Epoch.Uniform
import OAI.Computability.SpaceSimulation.Epoch.Agrees
import OAI.Computability.SpaceSimulation.Epoch.Meter

namespace OAI

namespace Fifths.Tour

def visits (D : Tour) := D.E * D.b

theorem finalDigit (D : Tour) (g : D.FiniteWords) :
    Radix.get D.m (D.valueOf D.target) D.b = (D.story D.visits).ctrl := by
  unfold target
  rw [D.at_history (by unfold E; omega) le_rfl]
  have e := D.log_agrees g ((D.E-1)*D.b) D.b D.b le_rfl
  simpa [visits,E,add_mul,b] using e

attribute [local irreducible] Fifths.Bin.pair Fifths.Modulus.chosen

/-- Epoch application. No simulation-specific assumptions beyond
bounded words, uniform interface, and appropriate amount of space. -/
theorem follows {I X : Type} {D : I → Tour} {x : I → List X} {S cp}
    (q : Runnable D x S cp) (g : ∀ i, (D i).FiniteWords)
    (h : Scaled S (fun i => (D i).E * (D i).per)) :
    Comp x S cp (fun i => ((D i).story (D i).visits).ctrl) := by
  let C := fun i => (D i).circuit
  have b : Comp x S cp (fun i => (D i).target.val) :=
    q.makeV (r := id) (Comp.refl q.kOf.source) q.kOf.plus1.minus1 (q.nOf.add q.kOf)
  have l := Circuit.evaluate (q.ready g) (fun i => (D i).certified (g i))
    (fun i => (D i).coins) (fun i => (D i).covers) (fun i => (D i).target)
    b (h.of_le (fun i => (D i).coins_total _))
  have y := Comp.digit q.mOf l q.bOf (q.powersFit id (fun i => Nat.le_succ (D i).b))
  exact y.congr (fun i => (D i).finalDigit (g i))

end Fifths.Tour

end OAI
