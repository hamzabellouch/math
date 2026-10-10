import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListRouteProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListScheduleGraph

namespace OAI

/-! The route-array filter selects exactly the same source indices as the
literal work-list filter, preserving their order. -/

namespace ContinuumCoulomb.QuantumListRouteProgram
open QuantumListSchedule

private theorem headD_drop {α : Type} (xs : List α) (d : α) (i : Fin xs.length) :
    (xs.drop i.val).headD d=xs.get i := by
  rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem i.isLt]
  rfl

def decoratedEntry (x : Input) (i : Fin x.2.1.2.2.length) : Routed :=
  (x.2.1.2.2.get i,(x.2.2.2.drop i.val).headD [])

theorem decorated_eq (x : Input) : decorated x=List.ofFn (decoratedEntry x) := by
  have h := (List.ofFn_getElem_eq_map (List.range x.2.1.2.2.length)
    (fun i => indexed (i,x))).symm
  simp only [List.length_range,List.getElem_range] at h
  rw [decorated,h]
  apply congrArg List.ofFn
  funext i
  exact congrArg (fun e => (e,(x.2.2.2.drop i.val).headD []))
    (headD_drop x.2.1.2.2 zeroEntry i)

theorem selectedRoutes_eq (b : Bool) (x : Input) :
    selectedRoutes b x=(QuantumListSchedule.indices b x.2.1.2.2).map (decoratedEntry x) := by
  rw [selectedRoutes,decorated_eq,List.ofFn_eq_map,List.filter_map]
  rfl

theorem selectedRoutes_length (b : Bool) (x : Input) :
    (selectedRoutes b x).length=(partition b x.2.1.2.2).length := by
  rw [selectedRoutes_eq,List.length_map,indices_length]

theorem selectedRoutes_get (b : Bool) (x : Input) (i : Fin (partition b x.2.1.2.2).length) :
    (selectedRoutes b x).get (Fin.cast (selectedRoutes_length b x).symm i) =
      decoratedEntry x (indexEquiv b x.2.1.2.2 i).val := by
  change _ = decoratedEntry x ((indices b x.2.1.2.2).get
    (Fin.cast (indices_length b x.2.1.2.2).symm i))
  have hl : i.val<(selectedRoutes b x).length := by
    rw [selectedRoutes_length]
    exact i.isLt
  have hr : i.val<(indices b x.2.1.2.2).length := by
    rw [indices_length]
    exact i.isLt
  have h := congrArg (fun rs : List Routed => rs[i.val]?) (selectedRoutes_eq b x)
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hl,List.getElem?_eq_getElem hr,
    Option.map_some,Option.some.injEq,List.get_eq_getElem,Fin.val_cast] using h

theorem selectedRoutes_entries (b : Bool) (x : Input) :
    (selectedRoutes b x).map Prod.fst=partition b x.2.1.2.2 := by
  rw [selectedRoutes_eq,List.map_map]
  exact indices_map b x.2.1.2.2

end ContinuumCoulomb.QuantumListRouteProgram

end OAI
