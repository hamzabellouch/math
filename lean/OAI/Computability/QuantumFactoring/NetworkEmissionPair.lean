import Mathlib
import OAI.Computability.QuantumFactoring.NetworkEmissionModel
import OAI.Computability.QuantumFactoring.BooleanAlgebra

namespace OAI



section

namespace ExactQuantumFactoring.NetworkEmission

def pairIndex (n width i : ℕ) : ℕ:=if i<n then i else width+(i-n)
lemma pairIndex_eq {n k : ℕ} (h : n ≤ k) :
    pairIndex n k=attachIndex (fun i : Fin n=>i.castLE h) := by
  funext i
  unfold pairIndex attachIndex
  split_ifs <;> rfl

def pair (a b : Data) : Data:=
  let f:=pairIndex a.inputs (a.inputs+a.nodes.length)
  ⟨a.inputs,a.nodes++b.nodes.map (Node.map f),a.outputs++b.outputs.map f⟩
lemma erase_pair {n m l : ℕ} (a : BooleanNetwork n m) (b : BooleanNetwork n l) :
    erase (a.pair b)=pair (erase a) (erase b) := by
  have hw : n+(eraseNet a.net).length=a.width := by rw [eraseNet_length];exact a.net.width_eq.symm
  let ρ : Fin n→Fin a.width:=fun i=>i.castLE a.net.input_le
  simp only [erase,BooleanNetwork.pair,pair,hw,pairIndex_eq a.net.input_le,attach_erase]
  congr 1
  have he : (fun i=>(Fin.append (fun j=>(a.output j).castLE (a.net.attach_le ρ b.net))
      ((a.net.attach ρ b.net).2.2 ∘ b.output) i).val)=
      Fin.append (fun j=>(a.output j).val)
        (fun j=>((a.net.attach ρ b.net).2.2 (b.output j)).val) := by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp
  rw [he,List.ofFn_fin_append,List.map_ofFn]
  congr 2
  funext i
  exact attach_output a.net ρ b.net (b.output i)

/-- A finite output permutation/quotation involves no Boolean node. -/
def rewire (a : Data) (outputs : List ℕ) : Data:=⟨a.inputs,a.nodes,outputs⟩
lemma erase_rewire {n m l : ℕ} (a : BooleanNetwork n m) (f : Fin l→Fin m) :
    erase (a.rewire f)=rewire (erase a) (List.ofFn (fun i=>(a.output (f i)).val)) := rfl
end ExactQuantumFactoring.NetworkEmission

end


end OAI
