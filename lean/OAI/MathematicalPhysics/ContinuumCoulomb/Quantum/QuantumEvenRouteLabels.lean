import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenListPieces
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumEvenTapeOrder

namespace OAI

/-! Explicit vertex and edge labels for the even subdivision of a planar route family. -/

noncomputable section
namespace ContinuumCoulomb.QuantumEvenRouteLabels
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPlanarRouteData G)
    {m : ℕ} (labels : G.Edge ≃ Fin m)

def selectedEquiv (G : QMARationalExchangeGraph) :
    Fin (Finset.univ : Finset G.Edge).card ≃ G.Edge where
  toFun := QMAEvenRouteData.selected
  invFun e := (Finset.univ : Finset G.Edge).equivFin ⟨e,Finset.mem_univ e⟩
  left_inv i := by
    change (Finset.univ : Finset G.Edge).equivFin
      ⟨((Finset.univ : Finset G.Edge).equivFin.symm i).val,_⟩=i
    exact (Finset.univ : Finset G.Edge).equivFin.apply_symm_apply i
  right_inv e := by
    change ((Finset.univ : Finset G.Edge).equivFin.symm
      ((Finset.univ : Finset G.Edge).equivFin ⟨e,Finset.mem_univ e⟩)).val=e
    rw [Equiv.symm_apply_apply]

def activeIndex : Fin m ≃ Fin (Finset.univ : Finset G.Edge).card :=
  labels.symm.trans (selectedEquiv G).symm

theorem selected_index (i : Fin m) :
    QMAEvenRouteData.selected (activeIndex labels i)=labels.symm i := by
  exact (selectedEquiv G).apply_symm_apply (labels.symm i)

def vertex : Fin (G.n+m*2) ≃ Fin (G.n+(Finset.univ : Finset G.Edge).card*2) :=
  ((vertexEquiv G.n m).symm.trans
    (Equiv.sumCongr (Equiv.refl _) (Equiv.prodCongr (activeIndex labels) (Equiv.refl _)))).trans
      (vertexEquiv _ _)

@[simp] theorem vertex_old (v : Fin G.n) : vertex labels (old G.n m v)=old _ _ v := by
  simp only [vertex,old,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
    Sum.map_inl,Equiv.refl_apply]

@[simp] theorem vertex_fresh (i : Fin m) (a : Fin 2) :
    vertex labels (fresh G.n m i a)=fresh _ _ (activeIndex labels i) a := by
  simp only [vertex,fresh,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.sumCongr_apply,
    Sum.map_inr,Equiv.prodCongr_apply]
  rfl

def edge (t : Fin m × Fin 3) : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) :=
  if h : t.2=0 then .inr (.inl (activeIndex labels t.1))
  else .inr (.inr (activeIndex labels t.1,⟨t.2.val-1,by omega⟩))

def unedge : QMAPartialPathsEdge (Finset.univ : Finset G.Edge) → Fin m × Fin 3
  | .inl e => (e.property (Finset.mem_univ _)).elim
  | .inr (.inl i) => ((activeIndex labels).symm i,0)
  | .inr (.inr (i,a)) => ((activeIndex labels).symm i,a.succ)

def edgeEquiv : (Fin m × Fin 3) ≃ QMAPartialPathsEdge (Finset.univ : Finset G.Edge) where
  toFun := edge labels
  invFun := unedge labels
  left_inv := by
    rintro ⟨i,k⟩
    fin_cases k
    all_goals
      change ((activeIndex labels).symm (activeIndex labels i),_)=(i,_)
      rw [Equiv.symm_apply_apply]
      rfl
  right_inv := by
    rintro (e | (i | ⟨i,a⟩))
    · exact (e.property (Finset.mem_univ _)).elim
    · change Sum.inr (Sum.inl (activeIndex labels ((activeIndex labels).symm i)))=Sum.inr (Sum.inl i)
      rw [Equiv.apply_symm_apply]
    · fin_cases a
      all_goals
        change Sum.inr (Sum.inr (activeIndex labels ((activeIndex labels).symm i),_))=Sum.inr (Sum.inr (i,_))
        rw [Equiv.apply_symm_apply]
        rfl

def work (t : Fin m × Fin 3) : ℕ := if t.2=2 then 4*P.length (labels.symm t.1)-1 else 0

theorem work_eq (t : Fin m × Fin 3) :
    P.toEven.nextWork (edge labels t)=work P labels t := by
  rcases t with ⟨i,k⟩
  fin_cases k
  · rfl
  · rfl
  · change 4*P.length (QMAEvenRouteData.selected (activeIndex labels i))-1=
      4*P.length (labels.symm i)-1
    rw [selected_index labels i]

def originalPath (i : Fin m) : List Pair :=
  (List.range (P.length (labels.symm i)+1)).map (P.point (labels.symm i))

theorem fresh_eq (i : Fin m) : QuantumEvenListPieces.fresh (originalPath P labels i)=
    [P.toEven.freshPosition (activeIndex labels i) 0,
     P.toEven.freshPosition (activeIndex labels i) 1] := by
  rw [originalPath,QuantumEvenListPieces.fresh_range _ _ (P.length_pos _)]
  simp only [QMAEvenRouteData.freshPosition,ite_true,show (1:Fin 2)≠0 from by decide,ite_false,
    selected_index labels i,QMAPlanarRouteData.toEven,QMAPlanarRouteData.leaf,QMAPlanarRouteData.direction]

theorem paths_eq (i : Fin m) : QuantumEvenListPieces.paths (originalPath P labels i)=
    List.ofFn (fun k : Fin 3 => (List.range (2*work P labels (i,k)+2)).map
      (P.toEven.nextPoint (edge labels (i,k)))) := by
  rw [originalPath,QuantumEvenListPieces.paths_range _ _ (P.length_pos _)]
  have he : 2*(4*P.length (labels.symm i)-1)+2=8*P.length (labels.symm i) :=
    P.even_length _
  have h0 : (List.range (2*work P labels (i,0)+2)).map
      (P.toEven.nextPoint (edge labels (i,0)))=
        [qmaInflatedPoint (P.point (labels.symm i)) 1,
          qmaRouteLeaf (P.point (labels.symm i) 0)
            (qmaGridNeighborIndex (P.point (labels.symm i) 0) (P.point (labels.symm i) 1))] := by
    change (List.range 2).map (fun k => if k=0 then
      qmaInflatedPoint (P.point (QMAEvenRouteData.selected (activeIndex labels i))) 1 else
      qmaRouteLeaf (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 0)
        (qmaGridNeighborIndex (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 0)
          (P.point (QMAEvenRouteData.selected (activeIndex labels i)) 1)))=_
    rw [selected_index labels i]
    rfl
  have h1 : (List.range (2*work P labels (i,1)+2)).map
      (P.toEven.nextPoint (edge labels (i,1)))=
        [qmaInflatedPoint (P.point (labels.symm i)) 0,qmaInflatedPoint (P.point (labels.symm i)) 1] := by
    change (List.range 2).map (qmaInflatedPoint
      (P.point (QMAEvenRouteData.selected (activeIndex labels i))))=_
    rw [selected_index labels i]
    rfl
  have h2 : (List.range (2*work P labels (i,2)+2)).map
      (P.toEven.nextPoint (edge labels (i,2)))=
        (List.range (8*P.length (labels.symm i))).map
          (fun k => qmaInflatedPoint (P.point (labels.symm i)) (8*P.length (labels.symm i)-k)) := by
    change (List.range (2*(4*P.length (labels.symm i)-1)+2)).map
      (fun k => qmaInflatedPoint (P.point (QMAEvenRouteData.selected (activeIndex labels i)))
        (2*(4*P.length (QMAEvenRouteData.selected (activeIndex labels i))-1)+2-k))=_
    rw [selected_index labels i,he]
  change _=[_,_,_]
  exact congrArg₂ List.cons h0.symm
    (congrArg₂ List.cons h1.symm (congrArg₂ List.cons h2.symm rfl))

theorem positions_eq :
    (List.ofFn (fun v => qmaLeafCenter (P.position v)))++
      ((List.ofFn (originalPath P labels)).map QuantumEvenListPieces.fresh).flatten=
        List.ofFn (fun v => P.toEven.nextPosition (vertex labels v)) := by
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext v
    change qmaLeafCenter (P.position v)=P.toEven.nextPosition (vertex labels (old G.n m v))
    rw [vertex_old,QMAEvenRouteData.nextPosition_old]
    rfl
  · rw [List.map_ofFn,List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    dsimp only [Function.comp_apply]
    rw [fresh_eq]
    have hf (a : Fin 2) : P.toEven.nextPosition (vertex labels
        ((⟨i.val*2+a.val,by omega⟩ : Fin (m*2)).natAdd G.n))=
          P.toEven.freshPosition (activeIndex labels i) a := by
      have he : ((⟨i.val*2+a.val,by omega⟩ : Fin (m*2)).natAdd G.n)=fresh G.n m i a := by
        apply Fin.ext
        change G.n+(i.val*2+a.val)=G.n+(a.val+2*i.val)
        omega
      rw [he,vertex_fresh,QMAEvenRouteData.nextPosition_fresh]
    simp only [hf,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one]

theorem allPaths_eq :
    ((List.ofFn (originalPath P labels)).map QuantumEvenListPieces.paths).flatten=
      List.ofFn (fun k : Fin (m*3) =>
        (List.range (2*work P labels (finProdFinEquiv.symm k)+2)).map
          (P.toEven.nextPoint (edge labels (finProdFinEquiv.symm k)))) := by
  rw [List.map_ofFn,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  dsimp only [Function.comp_apply]
  rw [paths_eq]
  apply congrArg List.ofFn
  funext k
  have he : (⟨i.val*3+k.val,by omega⟩ : Fin (m*3))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    change i.val*3+k.val=k.val+3*i.val
    omega
  rw [he,Equiv.symm_apply_apply]

end ContinuumCoulomb.QuantumEvenRouteLabels

end

end OAI
