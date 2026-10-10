import Mathlib
import OAI.Computability.QuantumFactoring.RetainedTreeFilter
import OAI.Computability.QuantumFactoring.RetainedSplitPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace SplitMachine
lemma previousNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.previousNet s).net.count=0 := by
  simp only [previousNet,count_comp,count_select,Nat.add_zero]
lemma lastSplitNet_count {n c : ℕ} (M : SplitMachine n c) (s : ℕ) :
    (M.lastSplitNet s).net.count=0 := by
  simp only [lastSplitNet,count_comp,count_select,Nat.add_zero]
end SplitMachine
namespace NodeMachine
lemma nodePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (FixedSplit.width n),v.net.count≤B→
      (M.retainedSplitFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) ((PhysicalNode.machine n (2*n)).width s))
    (hv : v.net.count≤B) : (M.nodePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [nodePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp ((PhysicalNode.machine n (2*n)).previousNet s)) (by
      simpa only [count_comp,SplitMachine.previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp ((PhysicalNode.machine n (2*n)).lastSplitNet s)) (by
      simpa only [count_comp,SplitMachine.lastSplitNet_count,Nat.add_zero] using hv)
    simp only [nodePrefixFilter,count_band]
    nlinarith
lemma nodePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((PhysicalNode.machine (len x) (2*len x)).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).nodePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (FixedSplit.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedSplitFilter_at (ht.pull fst) (hq.pull fst) hv (fun xi:ix=>hpos xi.1)
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact nodePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
lemma retainedNodeFilter_at {α : Type*} {len c T : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).retainedNodeFilter (hpos x) (T x) (raw x)) :=
  nodePrefixFilter_at hpos ht ((PolyAt.const len 2).mul (PolyAt.self len)) hq hr
lemma treePrefixFilter_count {n c : ℕ} (M : NodeMachine n c) (hn : 0<n) (T B C : ℕ)
    (h : ∀v : BooleanNetwork (M.width T) (NodeKernel.width n),v.net.count≤B→
      (M.retainedNodeFilter hn T v).net.count≤C)
    (s : ℕ) (v : BooleanNetwork (M.width T) (M.width s))
    (hv : v.net.count≤B) : (M.treePrefixFilter hn T s v).net.count≤ s*(C+1)+1 := by
  induction s with
  | zero=>simp only [treePrefixFilter,count_constant,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ s ih=>
    have hi:=ih (v.comp (M.previousNet s)) (by
      simpa only [count_comp,previousNet_count,Nat.add_zero] using hv)
    have hh:=h (v.comp (M.lastNodeNet s)) (by
      simpa only [count_comp,lastNodeNet_count,Nat.add_zero] using hv)
    simp only [treePrefixFilter,count_band]
    nlinarith
lemma treePrefixFilter_at {α : Type*} {len c T s : α→ℕ} {M : ∀x,NodeMachine (len x) (c x)}
    (hpos : ∀x,0<len x) (ht : PolyAt len T) (hs : PolyAt len s)
    (hq : NetworkAt len (fun x=>(M x).query))
    {raw : ∀x,BooleanNetwork ((M x).width (T x)) ((M x).width (s x))}
    (hr : NetworkAt len raw) :
    NetworkAt len (fun x=>(M x).treePrefixFilter (hpos x) (T x) (s x) (raw x)) := by
  let ix:=Σx,{v : BooleanNetwork ((M x).width (T x)) (NodeKernel.width (len x)) // v.net.count≤(raw x).net.count}
  let fst : ix→α:=Sigma.fst
  have hv : NetworkAt (fun xi:ix=>len xi.1) (fun xi=>xi.2.val):=
    NetworkAt.of_le (hr.pull fst) (fun xi=>xi.2.property)
  obtain ⟨p,hp⟩:=retainedNodeFilter_at (fun xi:ix=>hpos xi.1) (ht.pull fst) (hq.pull fst) hv
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply NetworkAt.of_le ((hs.mul (hc.add (PolyAt.const len 1))).add (PolyAt.const len 1))
  intro x
  exact treePrefixFilter_count (M x) (hpos x) (T x) (raw x).net.count (p.eval (len x))
    (fun v hh=>hp ⟨x,v,hh⟩) (s x) (raw x) le_rfl
end NodeMachine
end ExactQuantumFactoring

end



end OAI
