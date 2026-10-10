import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPositionProgram

namespace OAI

/-! Reordering the port vertices or crossing cells reorders the output
positions by a finite equivalence, preserving their injectivity. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open MediatorGraph QuantumRouteCode
open scoped Classical

variable {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) {n r : ℕ}
    (σ : Fin n ≃ Fin (P.finishedGraph N D).n)
    (τ : Fin r ≃ Fin P.crossingCells.card)

def extend : Fin (n+r*2) ≃ Fin ((P.finishedGraph N D).n+P.crossingCells.card*2) :=
  ((vertexEquiv n r).symm.trans (Equiv.sumCongr σ
    (Equiv.prodCongr τ (Equiv.refl (Fin 2))))).trans (vertexEquiv _ _)

theorem extend_old (v : Fin n) : extend P N D σ τ (old n r v)=old _ _ (σ v) := by
  simp [extend,old]

theorem extend_fresh (i : Fin r) (a : Fin 2) :
    extend P N D σ τ (MediatorGraph.fresh n r i a)=MediatorGraph.fresh _ _ (τ i) a := by
  simp [extend,MediatorGraph.fresh]

theorem reordered_cells_mem (p : Pair) :
    p ∈ List.ofFn (fun i => (P.crossingCell (τ i)).val) ↔ P.IsCrossing p := by
  rw [List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩
    exact P.mem_crossingCells.mp (P.crossingCell (τ i)).property
  · intro hp
    let c : P.Crossing := ⟨p,P.mem_crossingCells.mpr hp⟩
    refine ⟨τ.symm (P.crossingCells.equivFin c),?_⟩
    simp only [Equiv.apply_symm_apply,QMAPortRouteData.crossingCell,
      Equiv.symm_apply_apply]
    rfl

theorem positions_reordered :
    positions (List.ofFn (fun i => (P.crossingCell (τ i)).val),
      List.ofFn (fun v => P.finishedPosition N D (σ v))) =
      List.ofFn (fun v => P.crossingPosition N D (extend P N D σ τ v)) := by
  rw [positions,moved_ofFn (reordered_cells_mem P τ)]
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext v
    change qmaCrossingMove P.IsCrossing (P.finishedPosition N D (σ v))=
      P.crossingPosition N D (extend P N D σ τ (old n r v))
    rw [extend_old,P.crossingPosition_old]
    rfl
  · rw [fresh,List.map_ofFn,List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have hf (a : Fin 2) :
        P.crossingPosition N D (extend P N D σ τ
          ((⟨i.val*2+a.val,by omega⟩ : Fin (r*2)).natAdd n)) =
          qmaGadgetAncilla (P.crossingCell (τ i)).val a := by
      have he : ((⟨i.val*2+a.val,by omega⟩ : Fin (r*2)).natAdd n)=MediatorGraph.fresh n r i a := by
        apply Fin.ext
        change n+(i.val*2+a.val)=n+(a.val+2*i.val)
        omega
      rw [he,extend_fresh,P.crossingPosition_fresh]
      rfl
    simp only [hf,List.ofFn_succ,List.ofFn_zero,Fin.succ_zero_eq_one]
    rfl

theorem output_injective : Function.Injective
    (fun v => P.crossingPosition N D (extend P N D σ τ v)) :=
  (P.crossingPosition_injective N D).comp (extend P N D σ τ).injective

end ContinuumCoulomb.QuantumCrossingPositionProgram

end

end OAI
