import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleScale
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteNextPoint

namespace OAI

/-! Exact coefficients and scalar offset of the literal scheduled subdivision.
The edge labels agree with the geometry relabeling. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListSchedule
open scoped BigOperators Classical

private theorem selected_bond (x : Input) (i : Fin (partition true x.2.2.2).length) :
    blockBondInput (indexed (i.val,x)) =
      (QuantumListPathStep.parameters (stepInput x),i.val,((partition true x.2.2.2).get i).2) := by
  have h : (indexed (i.val,x)).2.2=(partition true x.2.2.2).get i := by
    change ((partition true x.2.2.2).drop i.val).headD zeroEntry = _
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
    rfl
  change (QuantumListPathStep.parameters (stepInput x),i.val,(indexed (i.val,x)).2.2.2) = _
  rw [h]

theorem next_weight_tag (N : ℚ) (s : State) (hs : Valid s) (t : Tags (N,s)) :
    (graph (value (N,s)) (value_valid (N,s) hs)).weight ((tagEquiv (N,s)).symm t) =
      ((schedule s hs).next N).graph.weight (tagEdge (N,s) hs t) := by
  change ((value (N,s)).2.2.get ((tagEquiv (N,s)).symm t)).2.2.2 = _
  rw [tagEquiv_get,Equiv.apply_symm_apply]
  rcases t with i | ⟨i,k⟩
  · exact (congrArg (fun e : Entry => e.2.2.2) (retained_source s hs i)).symm
  · change QuantumListPathProgram.coefficient (blockBondInput (indexed (i.val,(N,s)))) k.castSucc = _
    unfold QuantumListPathProgram.coefficient
    rw [selected_bond]
    simp only [QuantumListPathStep.parameters,stepInput]
    change QuantumPathCode.coefficients (false,
      (QuantumListPathStep.parameters (stepInput (N,s))).2.2,
      ((partition true s.2.2).get i).2.2.2) k.castSucc = _
    rw [scale_eq N s hs]
    have he := congrArg (fun e : Entry => e.2.2.2) (active_source s hs i)
    rw [← he]
    fin_cases k <;> rfl

theorem next_weight (N : ℚ) (s : State) (hs : Valid s)
    (i : Fin (value (N,s)).2.2.length) :
    (graph (value (N,s)) (value_valid (N,s) hs)).weight i =
      ((schedule s hs).next N).graph.weight (nextEdge (N,s) hs i) := by
  have h := next_weight_tag N s hs (tagEquiv (N,s) i)
  have hi : (tagEquiv (N,s)).symm (tagEquiv (N,s) i)=i := Equiv.symm_apply_apply _ _
  have he := nextEdge_tag (N,s) hs (tagEquiv (N,s) i)
  exact (congrArg (graph (value (N,s)) (value_valid (N,s) hs)).weight hi).symm.trans
    (h.trans (congrArg ((schedule s hs).next N).graph.weight
      ((congrArg (nextEdge (N,s) hs) hi).symm.trans he).symm))

theorem next_constant (N : ℚ) (s : State) (hs : Valid s) :
    (graph (value (N,s)) (value_valid (N,s) hs)).constant =
      ((schedule s hs).next N).graph.constant := by
  let R := (graph s hs).pathScale (schedule s hs).active N
  have hsum := (partition_sum true s.2.2
    (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2)).trans
      (active_sum s hs (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2))
  change s.2.1+QuantumListPathProgram.familyOffset
      (QuantumListPathStep.parameters (stepInput (N,s)),erase (partition true s.2.2)) = _
  unfold QuantumListPathProgram.familyOffset QuantumListPathProgram.offset
    QuantumListPathProgram.coefficient
  simp only [erase,List.map_map,Function.comp_def]
  change s.2.1+((partition true s.2.2).map (fun e =>
      (3/4:ℚ)+3*e.2.2.2^2+3*(QuantumListPathStep.parameters (stepInput (N,s))).2.2^2)).sum = _
  rw [scale_eq N s hs]
  change s.2.1+((partition true s.2.2).map (fun e => (3/4:ℚ)+3*e.2.2.2^2+3*R^2)).sum = _
  rw [hsum,Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change s.2.1+((∑ i : Fin (schedule s hs).active.card,
      ((3/4:ℚ)+3*(s.2.2.get (qmaSelectedIndex (schedule s hs).active i)).2.2.2^2))+
        (schedule s hs).active.card*(3*R^2)) = _
  change _ = (s.2.1+∑ i : Fin (schedule s hs).active.card,
      ((3/4:ℚ)+3*(s.2.2.get (qmaSelectedIndex (schedule s hs).active i)).2.2.2^2))+
        3*(schedule s hs).active.card*R^2
  ring

end ContinuumCoulomb.QuantumListSchedule

end

end OAI
