import OAI.NumberTheory.OrdinaryCorrelations.HighTrace.UncutTreeEdges

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology

namespace OrdinaryCorrelations.GraphKernel.PrimeSystem
open OrdinaryCorrelations.SignedTrace OrdinaryCorrelations.NumericalSubtrees Finset Classical
noncomputable section
variable {S : PrimeSystem} {B τ C₀ : ℝ} {D : S.DivisorFamily B τ C₀} {h ℓ L : ℕ}
namespace TreePath
variable {w : NumericalLine D h ℓ}

def subpath (P : TreePath w L) (a b : Fin (P.length+1)) (hab : a<b) : TreePath w L where
  length := b.val-a.val
  length_pos := by omega
  length_le := by have := P.length_le; omega
  vertex := fun i => P.vertex ⟨a.val+i.val,by omega⟩
  distinct := by
    intro i j he
    have hv := congrArg Fin.val (P.distinct he)
    apply Fin.ext
    dsimp at hv
    omega
  vertex_mem := fun i => P.vertex_mem ⟨a.val+i.val,by omega⟩
  edge := fun i => P.edge ⟨a.val+i.val,by omega⟩
  tree := fun i => P.tree ⟨a.val+i.val,by omega⟩
  forward := fun i => P.forward ⟨a.val+i.val,by omega⟩
  endpoints := by
    intro i
    let k : Fin P.length := ⟨a.val+i.val,by omega⟩
    have hx : k.castSucc=(⟨a.val+i.castSucc.val,by omega⟩ : Fin (P.length+1)) := by
      apply Fin.ext
      rfl
    have hy : k.succ=(⟨a.val+i.succ.val,by omega⟩ : Fin (P.length+1)) := by
      apply Fin.ext
      dsimp [k]
      omega
    have he := P.endpoints k
    rw [hx,hy] at he
    exact he

@[simp] lemma subpath_start (P : TreePath w L) (a b : Fin (P.length+1)) (hab : a<b) :
    (P.subpath a b hab).vertex 0=P.vertex a := by
  change P.vertex ⟨a.val+0,_⟩=P.vertex a
  congr 1

@[simp] lemma subpath_finish (P : TreePath w L) (a b : Fin (P.length+1)) (hab : a<b) :
    (P.subpath a b hab).vertex (Fin.last (P.subpath a b hab).length)=P.vertex b := by
  change P.vertex ⟨a.val+(b.val-a.val),_⟩=P.vertex b
  congr 1
  apply Fin.ext
  dsimp
  omega

end TreePath
end
end OrdinaryCorrelations.GraphKernel.PrimeSystem

end

end OAI
