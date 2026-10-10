import Mathlib
import OAI.Computability.QuantumFactoring.RationalEmission
import OAI.Computability.QuantumFactoring.TreePreparationEmission

namespace OAI



section
namespace ExactQuantumFactoring.PhysicalTreeEmission
open BitStackProgram BitStackProgram.Emits NetworkEmission NetworkEmission.NetEmits
variable {α : Type} {ea : α→List Bool} {n : α→ℕ}
def unitEquiv : Fin 1 ≃ Unit where
  toFun := fun _=>()
  invFun := fun _=>0
  left_inv i:=by exact Subsingleton.elim ..
  right_inv i:=by exact Subsingleton.elim ..
lemma quarterD (hn : Emits ea unaryCode n) : Emits ea unaryCode (fun x=>Quarter.D (n x)):=
  coinBits (hn.unaryMul hn) (const _ _ 1) (hn.unaryPow 11)
lemma keepGeneric {k d : α→ℕ} {coin : ∀x,BooleanNetwork (k x) (d x)} {p : α→ℚ}
    (hk : Emits ea unaryCode k) (hd : Emits ea unaryCode d) (hp : Emits ea ratCode p)
    (hc : NetEmits ea coin) :
    NetEmits ea (fun x=>retentionNet (d x) (.const (p x)) (.var ()) (fun _:Unit=>coin x)):=
by
  apply retention (v:=Unit) unitEquiv (fs:=fun x (_:Unit)=>coin x)
    (p:=fun x=>RatExpr.const (p x)) (coin:=fun _=>NatExpr.var ()) hk hd hd
  · exact NetworkEmission.Emits.rConst hp
  · exact const _ _ (NatExpr.var ())
  · intro i;exact hc
lemma quarterKeep {p : α→ℚ} (hn : Emits ea unaryCode n) (hp : Emits ea ratCode p) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (p x)):=by
  exact keepGeneric (quarterWidth hn) (quarterD hn) hp (quarterCoin hn)
lemma quarterOrdKeep (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (Quarter.retention (n x))):=
  quarterKeep hn (quarterRetention hn)
lemma quarterGuessKeep (hn : Emits ea unaryCode n) :
    NetEmits ea (fun x=>PhysicalTree.quarterKeep (n x) (Quarter.guessRetention (n x))):=
  quarterKeep hn (quarterGuessRetention hn)
end ExactQuantumFactoring.PhysicalTreeEmission

end



end OAI
