import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionBasic

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission
open BitStackProgram BitStackProgram.Procedure

def Node.Bound (B : ℕ) : Node→Prop
  | .constant _=>True
  | .copy i=>i≤B
  | .neg i=>i≤B
  | .conj i j=>i≤B ∧ j≤B
lemma Node.Bound.mono {A B : ℕ} {o : Node} (h : o.Bound A) (hab : A≤B) : o.Bound B:=by
  cases o <;> simp only [Node.Bound] at * <;> omega
lemma Node.Bound.map {A B : ℕ} {o : Node} (h : o.Bound A) (f : ℕ→ℕ)
    (hf : ∀i,i≤A→f i≤B) : (o.map f).Bound B:=by
  cases o with
  | constant=>trivial
  | copy i=>exact hf i h
  | neg i=>exact hf i h
  | conj i j=>exact ⟨hf i h.1,hf j h.2⟩
def Data.width (a : Data) : ℕ:=a.inputs+a.nodes.length
def Data.mass (a : Data) : ℕ:=a.width+a.outputs.length
def Data.Valid (a : Data) : Prop := (∀o∈a.nodes,o.Bound a.width) ∧ (∀i∈a.outputs,i≤a.width)
lemma eraseNode_bound {n : ℕ} (o : BoolNode n) : (eraseNode o).Bound n:=by
  cases o <;> simp only [eraseNode,Node.Bound] <;> omega
lemma eraseNet_nodes_bound {n k : ℕ} (p : BoolNet n k) : ∀o∈eraseNet p,o.Bound k:=by
  induction p with
  | input=>intro o ho;cases ho
  | @add k p op ih=>
    intro o ho
    simp only [eraseNet,List.mem_append,List.mem_singleton] at ho
    rcases ho with ho|rfl
    · exact (ih _ ho).mono (by omega)
    · exact (eraseNode_bound op).mono (by omega)
lemma erase_valid {n m : ℕ} (a : BooleanNetwork n m) : (erase a).Valid:=by
  have hw : (erase a).width=a.width:=by
    change n+(eraseNet a.net).length=a.width
    rw [eraseNet_length];exact a.net.width_eq.symm
  constructor
  · rw [hw];exact eraseNet_nodes_bound a.net
  · intro i hi
    change i∈List.ofFn (fun j=>(a.output j).val) at hi
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hi
    rw [hw];exact Nat.le_of_lt (a.output j).isLt
lemma valid_select (n : ℕ) (xs : List ℕ) (h : ∀i∈xs,i≤n) : (select n xs).Valid:=
by
  constructor
  · intro o ho;cases ho
  · exact h
lemma valid_node (n : ℕ) (o : Node) (h : o.Bound n) : (node n o).Valid:=by
  constructor
  · intro p hp
    have he : p=o:=by simpa only [node,List.mem_singleton] using hp
    subst p
    exact h.mono (by simp [Data.width,node])
  · intro i hi
    have he : i=n:=by simpa only [node,List.mem_singleton] using hi
    subst i;simp [Data.width,node]
lemma pairIndex_bound (n wa wb i : ℕ) (hn : n≤wa) (hi : i≤n+wb) :
    pairIndex n wa i≤wa+wb:=by unfold pairIndex;split <;> omega
lemma pair_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.inputs=b.inputs) : (pair a b).Valid:=by
  have hw : (pair a b).width=a.width+b.nodes.length:=by simp [Data.width,pair,Nat.add_assoc]
  have hf : ∀i,i≤b.width→pairIndex a.inputs a.width i≤(pair a b).width:=by
    intro i hi
    rw [hw]
    apply pairIndex_bound
    · exact Nat.le_add_right _ _
    · simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [pair,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [pair,List.mem_append,List.mem_map] at hi
    rcases hi with hi|⟨j,hj,rfl⟩
    · exact (ha.2 _ hi).trans (by rw [hw];omega)
    · exact hf _ (hb.2 _ hj)
lemma headD_drop_bound {xs : List ℕ} {B : ℕ} (h : ∀j∈xs,j≤B) (i : ℕ) :
    (xs.drop i).headD 0≤B:=by
  cases hh : (xs.drop i).head? with
  | none=>simp [List.headD_eq_head?_getD,hh]
  | some j=>
    rw [List.headD_eq_head?_getD,hh,Option.getD_some]
    exact h _ (List.mem_of_mem_drop (List.mem_of_head? hh))
lemma attachRawIndex_bound {xs : List ℕ} {wa wb : ℕ} (h : ∀j∈xs,j≤wa)
    (i : ℕ) (hi : i≤xs.length+wb) : attachRawIndex wa xs i≤wa+wb:=by
  unfold attachRawIndex
  split
  · exact (headD_drop_bound h i).trans (by omega)
  · omega
lemma comp_valid {a b : Data} (ha : a.Valid) (hb : b.Valid) (he : a.outputs.length=b.inputs) :
    (comp a b).Valid:=by
  have hw : (comp a b).width=a.width+b.nodes.length:=by simp [Data.width,comp,Nat.add_assoc]
  have hf : ∀i,i≤b.width→attachRawIndex a.width a.outputs i≤(comp a b).width:=by
    intro i hi
    rw [hw]
    apply attachRawIndex_bound ha.2
    simpa only [Data.width,←he] using hi
  constructor
  · intro o ho
    simp only [comp,List.mem_append,List.mem_map] at ho
    rcases ho with ho|⟨p,hp,rfl⟩
    · exact (ha.1 _ ho).mono (by rw [hw];omega)
    · exact (hb.1 _ hp).map _ hf
  · intro i hi
    simp only [comp,List.mem_map] at hi
    obtain ⟨j,hj,rfl⟩:=hi
    exact hf _ (hb.2 _ hj)
lemma pair_mass (a b : Data) : (pair a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,pair,List.length_append,List.length_map];omega
lemma comp_mass (a b : Data) : (comp a b).mass≤a.mass+b.mass:=by
  simp only [Data.mass,Data.width,comp,List.length_append,List.length_map];omega
lemma nat_bits_length_bound (n : ℕ) : n.bits.length≤n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self
lemma listCode_length_bound {α : Type} (ea : α→List Bool) (xs : List α) (B : ℕ)
    (h : ∀a∈xs,(ea a).length≤B) : (listCode ea xs).length≤xs.length*(2*B+2)+1:=by
  induction xs with
  | nil=>simp [listCode]
  | cons a xs ih=>
    have ha:=h a (by simp)
    have hh:=ih (by intro b hb;exact h b (by simp [hb]))
    simp only [listCode_length_cons,List.length_cons]
    nlinarith
lemma nodeCode_bound {o : Node} {B : ℕ} (h : o.Bound B) : (nodeCode o).length≤8*B+30:=by
  have h0 : (Nat.bits 0).length=0:=rfl
  have h1 : (Nat.bits 1).length=1:=rfl
  have h2 : (Nat.bits 2).length=2:=rfl
  have h3 : (Nat.bits 3).length=2:=rfl
  cases o <;> simp only [Node.Bound] at h
  · simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h1]
    omega
  · rename_i i
    have hi:=(nat_bits_length_bound i).trans h
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h0,h2]
    omega
  · rename_i i j
    have hi:=(nat_bits_length_bound i).trans h.1
    have hj:=(nat_bits_length_bound j).trans h.2
    simp only [nodeCode,nodePayload,nodeView,prodCode,pairBits_length,boolCode,List.length_singleton,h3]
    omega
lemma dataCode_bound {a : Data} {B : ℕ} (ha : a.Valid) (hm : a.mass≤B) :
    (dataCode a).length≤100*(B+1)^2:=by
  have hn : a.inputs≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hw : a.width≤B:=by dsimp [Data.mass] at hm;omega
  have hnl : a.nodes.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hol : a.outputs.length≤B:=by dsimp [Data.mass,Data.width] at hm;omega
  have hb:=(nat_bits_length_bound a.inputs).trans hn
  have hns:=listCode_length_bound nodeCode a.nodes (8*B+30) (fun o ho=>nodeCode_bound ((ha.1 _ ho).mono hw))
  have hos:=listCode_length_bound Nat.bits a.outputs B (fun i hi=>(nat_bits_length_bound i).trans ((ha.2 _ hi).trans hw))
  simp only [dataCode,dataPayload,dataView,prodCode,pairBits_length]
  have h1:=Nat.mul_le_mul_right (2*(8*B+30)+2) hnl
  have h2:=Nat.mul_le_mul_right (2*B+2) hol
  nlinarith
end ExactQuantumFactoring.NetworkEmission

end



end OAI
