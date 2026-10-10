import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem.TreePath
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ K : ℕ}
variable {w : NumericalLine D h ℓ}

lemma all_forward (P : TreePath w K) {E : Finset (Fin ℓ)}
    (hPE : ∀ i,P.edge i ∈ E)
    (hroot : P.vertex 0 ∉ E.image (fun e => w.line.offset e.succ)) :
    ∀ i,P.forward i=true := by
  intro i
  induction hiv : i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_contra hf
    have hf' : P.forward i=false := Bool.eq_false_of_not_eq_true hf
    have he := P.endpoints i
    simp only [hf',Bool.false_eq_true,ite_false] at he
    by_cases hn : i.val=0
    · have hi : i.castSucc=(0:Fin (P.length+1)) := Fin.ext hn
      exact hroot (mem_image.mpr ⟨P.edge i,hPE i,he.1.symm.trans (congrArg P.vertex hi)⟩)
    · let j : Fin P.length := ⟨i.val-1,by omega⟩
      have hj : P.forward j=true := ih j.val (by dsimp [j]; omega) j rfl
      have hej := P.endpoints j
      simp only [hj,ite_true] at hej
      have hji : j.succ=i.castSucc := Fin.ext (by dsimp [j]; omega)
      have hsame : P.edge j=P.edge i := tree_destination_injective w.line (P.tree j) (P.tree i)
        (hej.2.symm.trans ((congrArg P.vertex hji).trans he.1))
      have hv : P.vertex j.castSucc=P.vertex i.succ := hej.1.trans (hsame ▸ he.2.symm)
      have hh := congrArg Fin.val (P.distinct hv)
      dsimp [j] at hh
      omega

lemma edges_before_endpoint (P : TreePath w K) (hf : ∀ i,P.forward i=true)
    (e : Fin ℓ) (he : P.vertex (Fin.last P.length)=w.line.offset e.castSucc) :
    ∀ i,P.edge i<e := by
  intro i
  have hconn (k : Fin P.length) := P.endpoints k
  simp only [hf,ite_true] at hconn
  
  induction n : P.length-1-i.val using Nat.strong_induction_on generalizing i with
  | h n ih =>
    by_cases hi : i.val+1=P.length
    · have hil : i.succ=Fin.last P.length := Fin.ext hi
      exact incoming_earlier w.line (P.tree i) ((hconn i).2.symm.trans ((congrArg P.vertex hil).trans he))
    · let j : Fin P.length := ⟨i.val+1,by omega⟩
      have hj : P.edge j<e := ih (P.length-1-j.val) (by dsimp [j]; omega) j rfl
      have hij : i.succ=j.castSucc := Fin.ext rfl
      exact (incoming_earlier w.line (P.tree i)
        ((hconn i).2.symm.trans ((congrArg P.vertex hij).trans (hconn j).1))).trans hj

end
end OrdinaryCorrelations.GraphKernel.PrimeSystem.TreePath

end

end OAI
