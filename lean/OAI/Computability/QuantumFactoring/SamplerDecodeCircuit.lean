import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalOrderNetworks

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace BooleanNetwork

def leftNet (u v : ℕ) : BooleanNetwork (u+v) u := select (Fin.castAdd v)
def rightNet (u v : ℕ) : BooleanNetwork (u+v) v := select (Fin.natAdd u)
lemma leftNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (leftNet u v).eval (Fin.append x y)=x := by
  funext i
  exact Fin.append_left x y i
lemma rightNet_eval {u v : ℕ} (x : Basis u) (y : Basis v) :
    (rightNet u v).eval (Fin.append x y)=y := by
  funext i
  exact Fin.append_right x y i
lemma equalOn_basis {k w : ℕ} (a b : BooleanNetwork k w) (x : Basis k) :
    (equalOn a b).eval x 0=true ↔ a.eval x=b.eval x := by
  rw [equalOn_value]
  constructor
  · intro h
    exact (bitsEquiv w).injective (BitVec.eq_of_toNat_eq h)
  · intro h; rw [h]

end BooleanNetwork
namespace OrderTrial

def sampleYNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) b :=
  select (fun i => (((Fin.natAdd (u+u) (Triangular.dataWire i)).castAdd u).castAdd (OrderSample.scratch u b)))
def sampleUNet (u b : ℕ) : BooleanNetwork (OrderSample.width u b) u :=
  select (fun i => ((Fin.natAdd (OrderSample.inputWidth u b) i).castAdd (OrderSample.scratch u b)))
lemma sampleYNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleYNet u b).eval x=sampleY x := rfl
lemma sampleUNet_eval {u b : ℕ} (x : Basis (OrderSample.width u b)) :
    (sampleUNet u b).eval x=sampleU x := rfl

def triangularSelectedNet {k b : ℕ} (y : BooleanNetwork k b) : BooleanNetwork k (Triangular.width b) :=
  packNet (Triangular.work b) (y.pair (Completion.zeros k b)) (Completion.zeros k (b+b))
lemma triangularSelectedNet_eval {k b : ℕ} (y : BooleanNetwork k b) (x : Basis k) :
    (triangularSelectedNet y).eval x=Triangular.encode b (y.eval x,0) := by
  have h := (basisResidue b).symm_apply_eq.mpr (basisResidue_zero b).symm
  rw [triangularSelectedNet,packNet_eval,eval_pair,Completion.zeros_eval,Completion.zeros_eval]
  simp only [Triangular.encode,h]

/-- Full selection compares retained read-only inputs and every sampler scratch
bit, not only the apparent phase and modular residue fields. -/
def samplerSelectedNet {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) : BooleanNetwork k 1 :=
  equalOn z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))
lemma samplerSelectedNet_eval {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) (x : Basis k) :
    (samplerSelectedNet a m z).eval x 0=true ↔ SampleSelected (a.eval x) (m.eval x) (z.eval x) := by
  rw [samplerSelectedNet,equalOn_basis,packNet_eval,eval_pair,eval_pair,
    triangularSelectedNet_eval]
  simp only [eval_comp,sampleYNet_eval,sampleUNet_eval,SampleSelected,OrderSample.word,OrderSample.inputWord]
lemma samplerSelectedNet_count {k u b : ℕ} (a m : BooleanNetwork k u)
    (z : BooleanNetwork k (OrderSample.width u b)) :
    (samplerSelectedNet a m z).net.count ≤
      3*z.net.count+a.net.count+m.net.count+3*b+Triangular.work b+
        OrderSample.scratch u b+98*OrderSample.width u b+21 := by
  have h := equalOn_count z (packNet (OrderSample.scratch u b)
    ((a.pair m).pair (triangularSelectedNet (z.comp (sampleYNet u b))))
    (z.comp (sampleUNet u b)))
  simp only [packNet_count,count_pair,triangularSelectedNet,Completion.zeros_count,
    count_comp,sampleYNet,sampleUNet,count_select] at h
  dsimp only [samplerSelectedNet,triangularSelectedNet,sampleYNet,sampleUNet]
  omega

end OrderTrial
end ExactQuantumFactoring


end

end OAI
