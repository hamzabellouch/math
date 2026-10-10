import Mathlib
import OAI.Computability.QuantumFactoring.RetainedTable
import OAI.Computability.QuantumFactoring.RetainedFavorableCount
import OAI.Computability.QuantumFactoring.RetainedCanonical
import OAI.Computability.QuantumFactoring.RetainedComponentOrder
import OAI.Computability.QuantumFactoring.RetainedTotient
import OAI.Computability.QuantumFactoring.NetworkAt
import OAI.Computability.QuantumFactoring.RetainedNetworkPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace NetworkAt
variable {α : Type*} {len a b : α→ℕ}
lemma all_map {δ : α→Type*} (ls : ∀x,List (δ x)) (f : ∀x,δ x→BooleanNetwork (a x) 1)
    (hl : PolyAt len (fun x=>(ls x).length))
    (hf : NetworkAt (fun xi : Σx,{i // i∈ls x}=>len xi.1) (fun xi=>f xi.1 xi.2.val)) :
    NetworkAt len (fun x=>BooleanNetwork.all ((ls x).map (f x))) := by
  obtain ⟨p,hp⟩:=hf
  apply all (by simpa only [List.length_map] using hl)
  refine ⟨p,?_⟩
  intro x g hg
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hg
  exact hp ⟨x,⟨i,hi⟩⟩
lemma any_ofFn {k : α→ℕ} {f : ∀x,Fin (k x)→BooleanNetwork (a x) 1} (hk : PolyAt len k)
    (hf : NetworkAt (fun xi : Σx,Fin (k x)=>len xi.1) (fun xi=>f xi.1 xi.2)) :
    NetworkAt len (fun x=>BooleanNetwork.any (List.ofFn (f x))) := by
  obtain ⟨p,hp⟩:=hf
  have hc : PolyAt len (fun x=>p.eval (len x)):=⟨p,fun _=>le_rfl⟩
  apply of_le ((hk.mul (hc.add (PolyAt.const len 4))).add (PolyAt.const len 1))
  intro x
  have h:=any_count (List.ofFn (f x)) (c:=p.eval (len x)) (by
    intro g hg;obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hg;exact hp ⟨x,i⟩)
  simpa only [List.length_ofFn] using h
lemma primeComponent {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.primeComponent (f x) (g x)) :=
  of_le (RetainedPolynomial.primeComponentBound_at hb (PolyAt.add hf hg))
    (fun x=>primeComponent_count _ _ (by omega) (by omega))
lemma dividesOn {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.dividesOn (f x) (g x)) := by
  have hh : PolyAt len (fun x=>(f x).net.count+(g x).net.count+216*b x*b x+154*b x+27) :=
    ((((PolyAt.add hf hg).add (((PolyAt.const len 216).mul hb).mul hb)).add
      ((PolyAt.const len 154).mul hb)).add (PolyAt.const len 27))
  exact of_le hh fun x=>dividesOn_count _ _
lemma sameTwoVal {f g : ∀x,BooleanNetwork (a x) (b x)}
    (hb : PolyAt len b) (hf : NetworkAt len f) (hg : NetworkAt len g) :
    NetworkAt len (fun x=>BitArithmetic.sameTwoVal (f x) (g x)) := by
  have hi : PolyAt len (fun x=>2*(f x).net.count+2*(g x).net.count+864*b x*b x+616*b x+118) :=
    (((((PolyAt.const len 2).mul hf).add ((PolyAt.const len 2).mul hg)).add
      (((PolyAt.const len 864).mul hb).mul hb)).add ((PolyAt.const len 616).mul hb)).add (PolyAt.const len 118)
  exact of_le ((hb.mul hi).add (PolyAt.const len 1)) fun x=>sameTwoVal_count _ _
end NetworkAt
namespace NodeMachine
variable {α : Type*} {len n c t : α→ℕ} {M : ∀x,NodeMachine (n x) (c x)}
variable (hn : PolyAt len n) (ht : PolyAt len t)
  (hq : NetworkAt len (fun x=>(M x).query))
include hn ht hq
lemma retainedOrder_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedOrder (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableOrderBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedOrder_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedTotient_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedTotient (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  apply NetworkAt.of_le (RetainedPolynomial.tableTotientBound_at hn (ht.mul hn) hB)
  intro x
  exact (M x).retainedTotient_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedFavorableCount_at {m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedFavorableCount (t x) (m x)) := by
  have hB:=(PolyAt.add hm hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableFavorableCountBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedFavorableCount_count _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedCanonical_at {a m : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) :
    NetworkAt len (fun x=>(M x).retainedCanonical (t x) (a x) (m x)) := by
  have hB:=((PolyAt.add ha hm).add hq).add (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (RetainedPolynomial.tableCanonicalBound_at hn (ht.mul hn) hC)
  intro x
  exact (M x).retainedCanonical_count _ _ _ (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega) (by dsimp only;omega)
lemma retainedComponentOrder_at {a m p : ∀x,BooleanNetwork ((M x).width (t x)) (n x)}
    (ha : NetworkAt len a) (hm : NetworkAt len m) (hp : NetworkAt len p) :
    NetworkAt len (fun x=>(M x).retainedComponentOrder (t x) (a x) (m x) (p x)) :=
  retainedOrder_at hn ht hq ha (NetworkAt.primeComponent hn hm hp)
omit hq in
lemma tableNets_length_at : PolyAt len (fun x=>(tableNets ((M x).fieldRows (t x))).length) := by
  simpa only [fieldRows_table_length] using ht.mul hn
omit ht in
lemma tableNets_at : NetworkAt (fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>len xi.1)
    (fun xi=>xi.2.val) := by
  let pull:=fun xi : Σx,{p // p∈tableNets ((M x).fieldRows (t x))}=>xi.1
  have hB:=PolyAt.add hq (RetainedPolynomial.resultBound_at hn)
  have hC:=((PolyAt.const len 3).mul hB).add ((PolyAt.const len 220).mul hn) |>.add (PolyAt.const len 50)
  apply NetworkAt.of_le (hC.pull pull)
  rintro ⟨x,p,hp⟩
  apply tableNets_counts _ (c:=(M x).query.net.count+PhysicalNode.resultBound (n x)) _ _ hp
  intro r hr
  have hh:=(M x).fieldRows_counts (t x) r hr
  exact ⟨hh.1.trans (by omega),fun p hp=>(hh.2 p hp).trans (by omega)⟩
end NodeMachine
end ExactQuantumFactoring

end



end OAI
