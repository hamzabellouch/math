import OAI.NumberTheory.Ostmann.Construction.InitialCoordinatesTemplateCells

namespace OAI

noncomputable section
namespace Ostmann.Construction.InitialCoordinatesTemplate

def sourceBlock (offset n : ℕ) (r : SlotRole) : List SourceSlot :=
  List.ofFn fun i : Fin n => ⟨r,offset+i.val⟩

theorem sourceBlock_mapIdx (offset n : ℕ) (r : SlotRole) :
    (List.replicate n r).mapIdx (fun i q => (⟨q,offset+i⟩ : SourceSlot)) = sourceBlock offset n r := by
  rw [List.mapIdx_eq_ofFn]
  simp only [List.length_replicate, List.get_eq_getElem, List.getElem_replicate]
  rfl

theorem initial_eq_mapIdx (m k : ℕ) :
    Template.initial m k = (Template.initialRoles m k).mapIdx (fun i q => (⟨q,i⟩ : SourceSlot)) := by
  rw [List.mapIdx_eq_ofFn]
  rfl

theorem initial_zero (m : ℕ) :
    Template.initial m 0 = sourceBlock 0 m .bulk ++ sourceBlock m 6 .top := by
  rw [initial_eq_mapIdx]
  simp only [Template.initialRoles, List.range_zero, List.flatMap_nil, List.append_nil,
    List.mapIdx_append, List.length_replicate]
  rw [show (fun i q => (⟨q,i⟩ : SourceSlot)) = (fun i q => ⟨q,0+i⟩) by funext i q; simp]
  rw [sourceBlock_mapIdx]
  simpa only [zero_add, Nat.add_comm] using congrArg (fun z => sourceBlock 0 m .bulk ++ z)
    (sourceBlock_mapIdx m 6 .top)

theorem initial_succ (m k : ℕ) :
    Template.initial m (k+1) = Template.initial m k ++ sourceBlock (m+6+4*k) 4 (.compensation (k+1)) := by
  rw [initial_eq_mapIdx, initial_eq_mapIdx]
  have hr : Template.initialRoles m (k+1) =
      Template.initialRoles m k ++ List.replicate 4 (.compensation (k+1)) := by
    simp only [Template.initialRoles, List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.append_assoc]
  rw [hr,List.mapIdx_append,initialRoles_length]
  congr 1
  simpa only [Nat.add_comm] using sourceBlock_mapIdx (m+6+4*k) 4 (.compensation (k+1))

end Ostmann.Construction.InitialCoordinatesTemplate

end

end OAI
