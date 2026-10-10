import Mathlib
import OAI.Combinatorics.KMedianRecovery.Sampling.SeedTensor

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
def count : List ℕ→ℕ→ℕ
  | [],b=>b
  | n::ns,b=>n*count ns b
lemma count_eq (ds : List ℕ) (b : ℕ) : count ds b=(ds++[b]).prod := by
  induction ds with
  | nil=>simp [count]
  | cons n ns ih=>simp only [count,List.cons_append,List.prod_cons,ih]
def tensorEquiv : (ds : List ℕ)→(b : ℕ)→(Fin (count ds b)→Bool)≃Tensor ds b
  | [],_=>Equiv.refl _
  | n::ns,b=> ((Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.curry (Fin n) (Fin (count ns b)) Bool)).trans
      (Equiv.arrowCongr (Equiv.refl (Fin n)) (tensorEquiv ns b))
lemma tensorEquiv_cons (n : ℕ) (ns : List ℕ) (b : ℕ) (s : Fin (count (n::ns) b)→Bool) (i : Fin n) :
    tensorEquiv (n::ns) b s i=tensorEquiv ns b (fun j=>s (finProdFinEquiv (i,j))) := rfl
lemma raw_tensorEquiv (ds : List ℕ) (b : ℕ) (s : Fin (count ds b)→Bool) :
    raw (tensorEquiv ds b s)=List.ofFn s := by
  induction ds with
  | nil=>rfl
  | cons n ns ih=>
    change Fin (n*count ns b)→Bool at s
    change (List.ofFn (fun i:Fin n=>raw (tensorEquiv ns b (fun j=>s (finProdFinEquiv (i,j)))))).flatten =
      List.ofFn (s:Fin (n*count ns b)→Bool)
    simp only [ih]
    conv_rhs => rw [List.ofFn_mul]
    congr 2
    funext i
    congr 1
    funext j
    congr 1
    apply Fin.ext
    change j.val+count ns b*i.val=i.val*count ns b+j.val
    ring
lemma nest_flat (ds : List ℕ) (b : ℕ) (s : Fin (count ds b)→Bool) :
    nest ds.length (pairBits (shape (ds++[b]),List.ofFn s))=parsed (tensorEquiv ds b s) := by
  rw [←raw_tensorEquiv ds b s]
  exact nest_tensor _
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
