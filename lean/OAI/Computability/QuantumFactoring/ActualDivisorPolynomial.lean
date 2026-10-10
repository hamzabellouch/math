import Mathlib
import OAI.Computability.QuantumFactoring.PhysicalSplitDecoder
import OAI.Computability.QuantumFactoring.OrderDecoderPolynomial
import OAI.Computability.QuantumFactoring.SplitDecoderPolynomial

namespace OAI



section

namespace ExactQuantumFactoring
open BooleanNetwork BitArithmetic
namespace FixedSplit
lemma actualBaseNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualBaseNet xi.2) := by
  simpa only [NetworkAt,actualBaseNet,count_comp,launchWires,count_select,Nat.zero_add,
    baseNet_count] using PolyAt.ofPoly PreparationPolynomial.listOutput (fun xi:Σn,Fin (n^5)=>xi.1)
lemma modulusNet_poly : NetworkAt id modulusNet :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderRawNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderRawNet xi.2) :=
  (NetworkAt.select _).comp (NetworkAt.select _)
lemma actualOrderNet_poly : NetworkAt (fun xi:Σn,Fin (n^5)=>xi.1) (fun xi=>actualOrderNet xi.2) :=
  OrderSlots.outputOn_poly actualBaseNet_poly (modulusNet_poly.pull Sigma.fst) actualOrderRawNet_poly
lemma liftedModulus_poly : NetworkAt id liftedModulus :=
  modulusNet_poly.comp (NetworkAt.resizeWord (PolyAt.self id) ((PolyAt.self id).add (PolyAt.const id 1)))
lemma roots_poly : NetworkAt id (fun n=>rootsOn n (liftedModulus n)) :=
  liftedModulus_poly.rootsOn (PolyAt.self id)
lemma ordersBits_poly : NetworkAt id (fun n=>ordersBits (liftedModulus n) (actualPairs n)) := by
  let len : (Σn,Fin (n^5))→ℕ:=Sigma.fst
  have hn:=PolyAt.self len
  have hw:=hn.add (PolyAt.const len 1)
  have hm:=liftedModulus_poly.pull (Sigma.fst (β:=fun n=>Fin (n^5)))
  have he:=PolyAt.ofPoly PreparationPolynomial.transitionWidth len
  obtain ⟨p,hp⟩:=((actualBaseNet_poly.comp (NetworkAt.resizeWord hn hw)).candidateBits hm
    actualOrderNet_poly hw he)
  apply NetworkAt.firstProperNet liftedModulus_poly
    ((PolyAt.self id).add (PolyAt.const id 1))
    (by simpa only [actualPairs,List.length_map,List.length_ofFn,id_eq] using (PolyAt.self (id : ℕ→ℕ)).pow 5)
  refine ⟨p,?_⟩
  intro n d hd
  obtain ⟨ar,har,rfl⟩:=List.mem_map.mp hd
  obtain ⟨i,rfl⟩:=List.mem_ofFn.mp har
  exact hp ⟨n,i⟩
lemma divisorNet_poly : NetworkPoly divisorNet := by
  have hn:=PolyAt.self (id : ℕ→ℕ)
  have hw:=hn.add (PolyAt.const id 1)
  exact (liftedModulus_poly.evenOn hw).wordMux (NetworkAt.wordConstant _ hw)
    ((liftedModulus_poly.properOn roots_poly hw).wordMux roots_poly ordersBits_poly hw) hw
end FixedSplit
end ExactQuantumFactoring

end



end OAI
