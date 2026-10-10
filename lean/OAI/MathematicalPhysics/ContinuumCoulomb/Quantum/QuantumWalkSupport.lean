import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumWalkErasure

namespace OAI

/-! The actual buffered walk is a finite list of explicit arm and Manhattan
points. Loop erasure therefore computes the path used by the port geometry. -/

noncomputable section
namespace ContinuumCoulomb

 theorem qmaGridWalk_support_list (p : ℕ → ℕ × ℕ) (L : ℕ)
    (hstep : ∀ k < L, qmaSquareGrid.Adj (p k) (p (k+1))) :
    (qmaGridWalk p L hstep).support = (List.range (L+1)).map p := by
  induction L generalizing p with
  | zero => simp [qmaGridWalk]
  | succ L ih =>
    simp only [qmaGridWalk,SimpleGraph.Walk.support_cons,ih,List.range_succ_eq_map,
      List.map_cons,List.map_map,Function.comp_def]

namespace QMASpatialExchangeModel
variable {A B : ℕ} (M : QMASpatialExchangeModel A B)

def endpointArmList (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) : List (ℕ × ℕ) :=
  (List.range (M.endpointArmLength hd v e+1)).map (M.endpointArmPoint hd v e)

def spacedList (e : M.Term) : List (ℕ × ℕ) :=
  let p := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.left e))
  let q := qmaLanePoint (M.spacedColor e) (M.routeVertex (M.right e))
  (List.range (qmaManhattanLength p q+1)).map (qmaManhattanPoint p q)

def bufferedList (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) : List (ℕ × ℕ) :=
  M.endpointArmList hd (M.left e) ⟨e,Or.inl rfl⟩ ++ (M.spacedList e).tail ++
    (M.endpointArmList hd (M.right e) ⟨e,Or.inr rfl⟩).reverse.tail

@[simp] theorem endpointArmWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (v : Fin M.n) (e : M.Incident v) :
    (M.endpointArmWalk hd v e).support = M.endpointArmList hd v e := by
  simp only [endpointArmWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,
    endpointArmList]

@[simp] theorem spacedWalk_support_eq (e : M.Term) :
    (M.spacedWalk e).support = M.spacedList e := by
  simp only [spacedWalk,SimpleGraph.Walk.support_copy,qmaGridWalk_support_list,spacedList]

 theorem bufferedWalk_support_eq (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) : (M.bufferedWalk hd e).support = M.bufferedList hd e := by
  simp only [bufferedWalk,SimpleGraph.Walk.support_append,SimpleGraph.Walk.support_reverse,
    endpointArmWalk_support_eq,spacedWalk_support_eq,bufferedList]

 theorem bufferedPath_support_list (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) :
    (M.bufferedPath hd e).val.support = QuantumWalkErasure.erase (M.bufferedList hd e) := by
  rw [M.bufferedPath_support_explicit,M.bufferedWalk_support_eq]

 theorem coarseRoute_list (hd : ∀ v, qmaGraphDegree M.left M.right v ≤ 3)
    (e : M.Term) (i : ℕ) :
    M.coarseRoute hd e i =
      (QuantumWalkErasure.erase (M.bufferedList hd e)).getD i (M.placedVertex (M.right e)) := by
  rw [coarseRoute,SimpleGraph.Walk.getVert_eq_getD_support,M.bufferedPath_support_list]

end QMASpatialExchangeModel
end ContinuumCoulomb

end

end OAI
