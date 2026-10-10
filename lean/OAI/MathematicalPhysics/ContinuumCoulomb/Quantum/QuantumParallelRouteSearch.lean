import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteRouteSearch

namespace OAI

/-! The predicate mask and the path list have the same 140-entry order.
Searching the mask therefore returns the path of the actual first permitted
catalog route, without encoding proof-carrying route objects. -/

noncomputable section
namespace ContinuumCoulomb.QuantumFiniteRouteSearch
open ExactQuantumFactoring.BitStackProgram

private theorem mapped_drop_findIdx {α β : Type} (xs : List α) (p : α → Bool)
    (f : α → β) (default : β) :
    ((xs.map f).drop (xs.findIdx p)).headD default = (xs.find? p).elim default f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    by_cases h : p a
    · simp [List.findIdx_cons,h]
    · simpa [List.findIdx_cons,List.find?_cons,h,Nat.add_comm] using ih

def selectParallelValue {β : Type} (default : β) (x : List β × List Bool) : β :=
  (x.1.drop (firstTrue 140 x.2)).headD default

theorem selectParallelValue_eq {α β : Type} (default : β) (xs : List α)
    (p : α → Bool) (f : α → β) (hlen : xs.length = 140) {a : α}
    (hfind : xs.find? p = some a) :
    selectParallelValue default (xs.map f,xs.map p) = f a := by
  have hi : firstTrue 140 (xs.map p) = xs.findIdx p := by
    rw [firstTrue_eq_findIdx (by simpa using hlen),List.findIdx_map]
    rfl
  rw [selectParallelValue,hi,mapped_drop_findIdx,hfind]
  rfl

noncomputable def selectParallelProgram {β : Type} (eb : β → List Bool) (default : β) :
    Procedure (prodCode (listCode eb) (listCode Procedure.boolCode)) eb
      (selectParallelValue default) :=
  (Procedure.listGet eb default).comp
    (((indexProgram 140).comp (Procedure.second _ _)).pair (Procedure.first _ _))

end ContinuumCoulomb.QuantumFiniteRouteSearch

end

end OAI
