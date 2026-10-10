import OAI.Combinatorics.ContingencyTables.Rooted.RootedPenaltyEvaluateProgram

namespace OAI

/-! # Computed catalog coordinates for the oracle grid

The executable free-cell order need not agree with `Fintype.equivFin`.
Explicit reindexing identifies the grid exponent evaluated from the
catalog-ordered list.
-/

namespace ContingencyTables.RootedCatalogGrid

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open RootedCompletion
open scoped Classical

noncomputable section
variable {m n : ℕ}

abbrev freeCount (A : Instance (Fin m) (Fin n)) :=
  (RootedForestCatalog.catalog (RootedForestCatalog.data A,false)).length

def coordinateEquiv (A : Instance (Fin m) (Fin n)) :
    Fin (freeCount A) ≃ Fin (CompanionOracleDensity.dimension A) :=
  (RootedForestCatalog.freeEquiv A).trans (CompanionOracleDensity.index A).symm

def gridEquiv (A : Instance (Fin m) (Fin n)) (K : ℕ) :
    Grid (I := Fin (freeCount A)) K ≃
      Grid (I := Fin (CompanionOracleDensity.dimension A)) K where
  toFun v i := v ((coordinateEquiv A).symm i)
  invFun v i := v (coordinateEquiv A i)
  left_inv v := by funext i; simp only [Equiv.symm_apply_apply]
  right_inv v := by funext i; simp only [Equiv.apply_symm_apply]

lemma gridEquiv_apply (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    gridEquiv A K v (coordinateEquiv A i)=v i := by
  change v ((coordinateEquiv A).symm (coordinateEquiv A i))=v i
  rw [Equiv.symm_apply_apply]

lemma gridEquiv_free (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) (f : FreeCell A.small A.T) :
    gridEquiv A K v ((CompanionOracleDensity.index A).symm f)=
      v ((RootedForestCatalog.freeEquiv A).symm f) := by
  change v ((coordinateEquiv A).symm ((CompanionOracleDensity.index A).symm f))=_
  simp only [coordinateEquiv,Equiv.symm_trans_apply,Equiv.symm_symm,
    Equiv.apply_symm_apply]

lemma gridEdge_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) (i : Fin (freeCount A)) :
    IsGridEdge (gridEquiv A K v,gridEquiv A K w,coordinateEquiv A i) ↔
      IsGridEdge (v,w,i) := by
  constructor
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : coordinateEquiv A j≠coordinateEquiv A i :=
        fun h => hj ((coordinateEquiv A).injective h)
      simpa only [gridEquiv_apply] using hrest (coordinateEquiv A j) hji
  · rintro ⟨hstep,hrest⟩
    refine ⟨?_,?_⟩
    · simpa only [corner,gridEquiv_apply] using hstep
    · intro j hj
      have hji : (coordinateEquiv A).symm j≠i := by
        intro h
        exact hj ((Equiv.apply_symm_apply (coordinateEquiv A) j).symm.trans
          (congrArg (coordinateEquiv A) h))
      exact hrest ((coordinateEquiv A).symm j) hji

theorem neighbor_iff (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v w : Grid (I := Fin (freeCount A)) K) :
    Neighbor (gridEquiv A K v) (gridEquiv A K w) ↔ Neighbor v w := by
  constructor
  · rintro ⟨i,side,hi⟩
    refine ⟨(coordinateEquiv A).symm i,side,?_⟩
    cases side with
    | false =>
      change IsGridEdge (gridEquiv A K w,gridEquiv A K v,i) at hi
      apply (gridEdge_iff A K w v ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
    | true =>
      change IsGridEdge (gridEquiv A K v,gridEquiv A K w,i) at hi
      apply (gridEdge_iff A K v w ((coordinateEquiv A).symm i)).mp
      simpa only [Equiv.apply_symm_apply] using hi
  · rintro ⟨i,side,hi⟩
    refine ⟨coordinateEquiv A i,side,?_⟩
    cases side with
    | false => exact (gridEdge_iff A K w v i).mpr hi
    | true => exact (gridEdge_iff A K v w i).mpr hi

def naturalValues (A : Instance (Fin m) (Fin n)) {K : ℕ}
    (v : Grid (I := Fin (freeCount A)) K) : FreeCell A.small A.T → ℕ :=
  fun f => (v ((RootedForestCatalog.freeEquiv A).symm f)).val.toNat

theorem naturalBin_grid (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) :
    CompanionOracleDensity.naturalBin A (gridEquiv A K v)=naturalValues A v := by
  funext f
  unfold CompanionOracleDensity.naturalBin naturalValues
  rw [gridEquiv_free]

theorem naturalValues_list (A : Instance (Fin m) (Fin n)) (K : ℕ)
    (v : Grid (I := Fin (freeCount A)) K) :
    List.ofFn (fun i => naturalValues A v (RootedForestCatalog.freeEquiv A i))=
      List.ofFn (fun i => (v i).val.toNat) := by
  apply congrArg List.ofFn
  funext i
  simp only [naturalValues,Equiv.symm_apply_apply]

theorem evaluatorInput_grid (A : Instance (Fin m) (Fin n)) (C a K : ℕ)
    (x q : Fin m → Fin n → ℕ) (v : Grid (I := Fin (freeCount A)) K) :
    RootedPenaltyEvaluateProgram.data A C a x q (naturalValues A v)=
      (((A.d,A.W),(C,a)),(RootedDemandProgram.data A x q,
        List.ofFn (fun i => (v i).val.toNat))) := by
  unfold RootedPenaltyEvaluateProgram.data
  rw [naturalValues_list]

/-- Catalog-order evaluation is exactly the grid
exponent after reindexing. The runtime code never uses this equivalence. -/
theorem evaluate_grid (A : Instance (Fin m) (Fin n)) (C a K : ℕ) (hC : 0 < C)
    (z : View A → ℕ) (v : Grid (I := Fin (freeCount A)) K) :
    RootedPenaltyEvaluateProgram.evaluate
      (((A.d,A.W),(C,a)),
        (RootedDemandProgram.data A (ForestCountIdentification.smallX A.small z)
          (fun i j => A.b i j-ForestCountIdentification.smallY A.small z i j),
          List.ofFn (fun i => (v i).val.toNat)))=
      RootedOracleDensity.gridExponent A (rowColumn A.T) C a z (gridEquiv A K v) := by
  rw [←evaluatorInput_grid]
  rw [RootedPenaltyEvaluateProgram.evaluate,RootedPenaltyEvaluateProgram.exponentInput_data]
  have h := RootedOracleDensity.exponentCode_grid A (rowColumn A.T) C a hC z
    (RootedForestCatalog.treeEquiv A) (RootedForestCatalog.freeEquiv A) (gridEquiv A K v)
  rw [naturalBin_grid] at h
  exact h

end
end ContingencyTables.RootedCatalogGrid

end OAI
