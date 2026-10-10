import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionAt
import OAI.Computability.QuantumFactoring.NetworkAtArithmetic

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma varsFin {ι : Type*} [Fintype ι] {v : ∀x,ι→BooleanNetwork (a x) (b x)}
    (h : ∀i,NetworkAt len (fun x=>v x i)) :
    ∃p : Polynomial ℕ,∀x i,(v x i).net.count≤p.eval (len x) := by
  classical
  change ∀i,∃p : Polynomial ℕ,∀x,(v x i).net.count≤p.eval (len x) at h
  choose p hp using h
  refine ⟨∑i,p i,fun x i=>?_⟩
  rw [Polynomial.eval_finsetSum]
  exact (hp i x).trans (Finset.single_le_sum (f:=fun j=>(p j).eval (len x)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i))
end NetworkAt
namespace OrderTrial
variable {α : Type*} {len a w steps : α→ℕ}
lemma checkedConvergent_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hi : PolyAt len steps) :
    NetworkAt len (fun x=>checkedConvergent (steps x) (Q x) (B x) (k x)) := by
  let cv := fun x=>(k x |>.pair (Q x)).comp (convergentNet (w x) (steps x))
  have hcv : NetworkAt len cv := (hk.pair hQ).comp (NetworkAt.convergentNet hw hi)
  have hd : NetworkAt len (fun x=>(cv x).comp (rootGuess (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hj : NetworkAt len (fun x=>(cv x).comp (rootModulus (w x))) :=
    hcv.comp (NetworkAt.select _)
  have hv : ∃p : Polynomial ℕ,∀x i,
      (![Q x,B x,k x,(cv x).comp (rootGuess (w x)),(cv x).comp (rootModulus (w x))] i).net.count
        ≤p.eval (len x) := by
    apply NetworkAt.varsFin
    intro i; fin_cases i
    · exact hQ
    · exact hB
    · exact hk
    · exact hd
    · exact hj
  have he : NatExprAt len (fun _ : α=>binCheckExpr) := PolyAt.const len binCheckExpr.weight
  have hp := he.isOne hw hv
  have hz := NetworkAt.wordConstant (a:=a) (fun x=>BitVec.ofNat (w x) 0) hw
  exact (hp.wordMux hd hz hw).pair (hp.wordMux hj hz hw)

lemma recoveryNet_count_of_bound {n w K c : ℕ} (Q B k : BooleanNetwork n w)
    (hc : ∀i,i<K → (checkedConvergent i Q B k).net.count≤c) :
    (recoveryNet Q B k K).net.count≤2*w+K*(c+120*w+31) := by
  induction K with
  | zero => simp only [recoveryNet,count_pair,wordConstant_count,zero_mul,add_zero];omega
  | succ K ih =>
    have hh := ih (fun i hi=>hc i (by omega))
    have hi := hc K (by omega)
    have hp := pairChoice_count w
    simp only [recoveryNet,count_pair,count_comp]
    nlinarith

lemma recoveryNet_poly {Q B k : ∀x,BooleanNetwork (a x) (w x)}
    (hQ : NetworkAt len Q) (hB : NetworkAt len B) (hk : NetworkAt len k)
    (hw : PolyAt len w) (hsteps : PolyAt len steps) :
    NetworkAt len (fun x=>recoveryNet (Q x) (B x) (k x) (steps x)) := by
  let index : Type _ := Σx:α,Fin (steps x)
  let param : index→α := Sigma.fst
  have hi : PolyAt (fun z:index=>len z.1) (fun z=>z.2.val) :=
    (hsteps.pull param).of_le fun z=>z.2.isLt.le
  have hh:=checkedConvergent_poly (hQ.pull param) (hB.pull param) (hk.pull param)
    (hw.pull param) hi
  obtain ⟨p,hp⟩:=hh
  have hpoly : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le (bound:=fun x=>2*w x+steps x*(p.eval (len x)+120*w x+31))
  · exact ((PolyAt.const len 2).mul hw).add
      (hsteps.mul ((hpoly.add ((PolyAt.const len 120).mul hw)).add (PolyAt.const len 31)))
  · intro x
    exact recoveryNet_count_of_bound (Q x) (B x) (k x) (fun i hi=>hp ⟨x,⟨i,hi⟩⟩)
end OrderTrial
end ExactQuantumFactoring

end



end OAI
