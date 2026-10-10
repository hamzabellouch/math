import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumBufferedExtent
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPorts

namespace OAI

/-! Finite coordinate arrays for every assembled simple route. -/

noncomputable section
namespace ContinuumCoulomb
open scoped Classical
namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def bufferedNode (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : Fin ((M.bufferedPath hd e).val.length+1)) : ℕ × ℕ :=
  (M.bufferedPath hd e).val.getVert i.val

theorem bufferedNode_injective (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    Function.Injective (M.bufferedNode hd e) := by
  intro i j h
  apply Fin.ext
  exact (M.bufferedPath hd e).property.getVert_injOn
    (show i.val ≤ (M.bufferedPath hd e).val.length by omega)
    (show j.val ≤ (M.bufferedPath hd e).val.length by omega) h

@[simp] theorem bufferedNode_zero (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.bufferedNode hd e 0 = M.placedVertex (M.left e) :=
  SimpleGraph.Walk.getVert_zero _

@[simp] theorem bufferedNode_last (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term) :
    M.bufferedNode hd e (Fin.last (M.bufferedPath hd e).val.length) = M.placedVertex (M.right e) :=
  SimpleGraph.Walk.getVert_length _

theorem bufferedNode_step (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : Fin (M.bufferedPath hd e).val.length) :
    qmaSquareGrid.Adj (M.bufferedNode hd e i.castSucc) (M.bufferedNode hd e i.succ) :=
  qmaGridPath_getVert_step (M.bufferedPath hd e) i

theorem bufferedNode_bounds (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : Fin ((M.bufferedPath hd e).val.length+1)) :
    (M.bufferedNode hd e i).1 < M.bufferedWidth ∧ (M.bufferedNode hd e i).2 < M.bufferedHeight :=
  M.bufferedPath_bounds hd e ((M.bufferedPath hd e).val.getVert_mem_support i.val)

def bufferedGridNode (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : Fin ((M.bufferedPath hd e).val.length+1)) : Fin M.bufferedWidth × Fin M.bufferedHeight :=
  (⟨(M.bufferedNode hd e i).1,(M.bufferedNode_bounds hd e i).1⟩,
   ⟨(M.bufferedNode hd e i).2,(M.bufferedNode_bounds hd e i).2⟩)

theorem bufferedNode_mem (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3) (e : M.Term)
    (i : Fin ((M.bufferedPath hd e).val.length+1)) : M.bufferedNode hd e i ∈ M.routedVertices hd := by
  apply Finset.mem_union.mpr
  right
  apply Finset.mem_biUnion.mpr
  refine ⟨e,Finset.mem_univ _,?_⟩
  exact List.mem_toFinset.mpr ((M.bufferedPath hd e).val.getVert_mem_support i.val)

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
