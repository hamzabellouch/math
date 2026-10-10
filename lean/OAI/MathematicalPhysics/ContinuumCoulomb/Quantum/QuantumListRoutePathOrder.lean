import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteNextWork

namespace OAI

/-! The output path array has exactly the output bond array's tag order. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule QuantumRouteCode

def pathPiece (r : Routed) : Fin 3 → List Pair :=
  ![[lookup r.2 1,lookup r.2 2],[lookup r.2 0,lookup r.2 1],(r.2.drop 2).reverse]

theorem pathBlock_ofFn (r : Routed) : pathBlock r=List.ofFn (pathPiece r) := by
  simp [pathBlock,pathPiece,List.ofFn_succ,List.ofFn_zero]

def tagPath (x : Input) : Tags (x.1,x.2.1) → List Pair
  | .inl i => (decoratedEntry x (indexEquiv false x.2.1.2.2 i).val).2
  | .inr (i,k) => pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 i).val) k

private theorem ofFn_triples {m : ℕ} (f : Fin m × Fin 3 → List Pair) :
    List.ofFn (fun k : Fin (m*3) => f (finProdFinEquiv.symm k)) =
      (List.ofFn fun i : Fin m => List.ofFn fun k : Fin 3 => f (i,k)).flatten := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg (fun g : Fin m → List (List Pair) => List.ofFn g)
  funext i
  apply congrArg (fun g : Fin 3 → List Pair => List.ofFn g)
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

theorem paths_flat (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (flatTagEquiv (x.1,x.2.1) i)) := by
  rw [List.ofFn_add]
  change _ = (List.ofFn (fun i : Fin (partition false x.2.1.2.2).length =>
    tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.castAdd ((partition true x.2.1.2.2).length*3) i))))++
    List.ofFn (fun i : Fin ((partition true x.2.1.2.2).length*3) =>
      tagPath x (flatTagEquiv (x.1,x.2.1) (Fin.natAdd (partition false x.2.1.2.2).length i)))
  simp only [flatTagEquiv,Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd,Equiv.sumCongr_apply,Equiv.refl_apply,
    Sum.map_inl,Sum.map_inr,tagPath]
  have h3 := ofFn_triples (fun p : Fin (partition true x.2.1.2.2).length × Fin 3 =>
    pathPiece (decoratedEntry x (indexEquiv true x.2.1.2.2 p.1).val) p.2)
  rw [h3]
  change (selectedRoutes false x).map Prod.snd++((selectedRoutes true x).map pathBlock).flatten = _
  rw [map_selectedRoutes,map_selectedRoutes]
  simp_rw [pathBlock_ofFn]

theorem paths_tagged (x : Input) : paths x=List.ofFn
    (fun i => tagPath x (tagEquiv (x.1,x.2.1) i)) := by
  rw [paths_flat]
  apply List.ext_getElem
  · simp only [List.length_ofFn,value_length]
  · intro i hi hj
    simp only [List.getElem_ofFn,tagEquiv,Equiv.trans_apply,finCongr_apply]
    apply congrArg (tagPath x)
    apply congrArg (flatTagEquiv (x.1,x.2.1))
    exact Fin.ext rfl

end ContinuumCoulomb.QuantumListRouteProgram

end

end OAI
