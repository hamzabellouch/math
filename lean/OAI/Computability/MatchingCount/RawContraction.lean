import OAI.Computability.MatchingCount.RawFlowCompiler

namespace OAI

section

namespace BinaryMatching.Raw
open Finset

def outside (n : ℕ) (A : Cut) : Option ℕ := (List.range n).find? (fun i => !mem A i)
def contractMap (A : Cut) (r i : ℕ) : ℕ := if mem A i then i else r
def contract (n : ℕ) (c : Matrix ℕ) (A : Cut) (r : ℕ) : Matrix ℕ :=
  matrix n (fun i j => if i=j then 0 else
    (tab n (fun u => (tab n (fun v =>
      if contractMap A r u=i ∧ contractMap A r v=j then get c u v else 0)).sum)).sum)
def lift (n : ℕ) (A : Cut) (r : ℕ) (S : Cut) : Cut :=
  tab n (fun i => mem S (contractMap A r i))
def cheaper (n : ℕ) (c : Matrix ℕ) (S T : Cut) : Cut :=
  if cutCapacity n c S≤cutCapacity n c T then S else T

lemma outside_rep {n : ℕ} (A : Finset (Fin n)) :
    outside n (cutRep A)=(OddMincut.outside A).map Fin.val := by
  unfold outside OddMincut.outside
  rw [range_eq_fin,List.find?_map]
  congr 1
  congr 1
  funext i
  simp only [Function.comp_apply,mem_rep,decide_not]

lemma contractMap_rep {n : ℕ} (A : Finset (Fin n)) (r i : Fin n) :
    contractMap (cutRep A) r.val i.val=(OddCutParity.contractMap A r i).val := by
  simp only [contractMap,mem_rep,decide_eq_true_eq,OddCutParity.contractMap]
  split_ifs <;> rfl

lemma contract_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (A : Finset (Fin n)) (r : Fin n) :
    contract n (matrixRep c) (cutRep A) r.val=
      matrixRep (CutAlgebra.push c (OddCutParity.contractMap A r)) := by
  apply matrix_eq_rep
  intro i j
  simp only [Fin.ext_iff,contractMap_rep,sum_tab,get_rep,CutAlgebra.push]

lemma lift_rep {n : ℕ} (A S : Finset (Fin n)) (r : Fin n) :
    lift n (cutRep A) r.val (cutRep S)=cutRep (CutAlgebra.lift (OddCutParity.contractMap A r) S) := by
  apply tab_eq_rep
  intro i
  simp only [contractMap_rep,mem_rep,CutAlgebra.mem_lift]

lemma cheaper_rep {n : ℕ} (c : Fin n → Fin n → ℕ) (S T : Finset (Fin n)) :
    cheaper n (matrixRep c) (cutRep S) (cutRep T)=cutRep (OddMincut.cheaper c S T) := by
  simp only [cheaper,cutCapacity_rep,OddMincut.cheaper]
  split_ifs <;> rfl
end BinaryMatching.Raw
end

end OAI
