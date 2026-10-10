import Mathlib
import OAI.Combinatorics.Chromatic.Walls.TriangularLevelQueues

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open Classical
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I] [DecidableEq I]
variable (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M) (coord : M →+ (I → ℤ))
variable (hcoord : ∀d,coord (C d)=d) (pc : I)

omit [Fintype I] in
include hcoord in
lemma simpleRoot_injective : Function.Injective (simpleRoot C) := by
  intro i j h
  have H:=congrArg coord h
  change coord (C (Pi.single i 1))=coord (C (Pi.single j 1)) at H
  rw [hcoord,hcoord] at H
  by_contra hn
  have HH:=congrFun H i
  simp [hn] at HH

def rootMutation (p r : M) : M :=
  if r=p then -p else ForwardChain.positiveMutate Ω p r

include hcoord in
lemma mutatedRoot_inventory (i : I) :
    simpleRoot (mutatedRoots Ω C pc) i=rootMutation Ω (simpleRoot C pc) (simpleRoot C i) := by
  by_cases hi : i=pc
  · subst i
    rw [mutatedRoot_p]
    simp [rootMutation]
  · have hn : simpleRoot C i≠simpleRoot C pc :=
      fun hh=>hi (simpleRoot_injective C coord hcoord hh)
    rw [mutatedRoot_off Ω C pc i hi]
    simp only [rootMutation,hn,ite_false,ForwardChain.positiveMutate,mutationPairing,max_comm]

include hcoord in
lemma mutatedRoot_list (is : List I) :
    is.map (simpleRoot (mutatedRoots Ω C pc))=
      (is.map (simpleRoot C)).map (rootMutation Ω (simpleRoot C pc)) := by
  rw [List.map_map]
  exact List.map_congr_left fun i _=>mutatedRoot_inventory Ω C coord hcoord pc i

lemma rootMutation_map_off (p : M) (l : List M) (hp : p∉l) :
    l.map (rootMutation Ω p)=l.map (ForwardChain.positiveMutate Ω p) := by
  apply List.map_congr_left
  intro r hr
  have hn:r≠p:=by intro h; subst r; exact hp hr
  simp [rootMutation,hn]

lemma rootMutation_rotation_perm (p a b c : M) (bs : List M) (hp : p=b-a)
    (ha : Ω p a=1) (hb : Ω p b=1) (hc : Ω p c= -1)
    (hs : ∀x∈bs,Ω p x=0) (hnd : (ForwardChain.gaps a (b::bs) c).Nodup) :
    ((ForwardChain.gaps a (b::bs) c).map (rootMutation Ω p)).Perm
      (ForwardChain.gaps a (bs++[c+p]) c) := by
  change ((b-a)::ForwardChain.gaps b bs c).Nodup at hnd
  have hnot : p∉ForwardChain.gaps b bs c := by rw [hp]; exact (List.nodup_cons.mp hnd).1
  simp only [ForwardChain.gaps,List.map_cons,←hp,rootMutation]
  rw [rootMutation_map_off Ω p _ hnot]
  exact ForwardChain.gaps_rotation_perm Ω p a b c bs hp ha hb hc hs

lemma rootMutation_gaps_fixed (p a c : M) (bs : List M)
    (ha : Ω p a≤0) (hc : 0≤Ω p c) (hb : ∀b∈bs,Ω p b=0)
    (hp : p∉ForwardChain.gaps a bs c) :
    (ForwardChain.gaps a bs c).map (rootMutation Ω p)=ForwardChain.gaps a bs c := by
  rw [rootMutation_map_off Ω p _ hp]
  exact ForwardChain.gaps_mutate_fixed Ω p a c bs ha hc hb
end
end ElementaryPositivity.QuantumTorus

end

end OAI
