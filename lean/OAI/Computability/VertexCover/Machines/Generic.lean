import Mathlib
import OAI.Computability.VertexCover.Machines.Serialization
import OAI.Computability.VertexCover.Machines.TableBase
import OAI.Computability.VertexCover.Machines.FixedOps

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
                                   
section

namespace VertexCover.Machine
open UniqueGames.Foundations.PCP

noncomputable def Poly.rawBooleans : Poly (listBits boolBits) id (id : List Bool → List Bool) := by
  let bit : Poly boolBits id (fun b => [b]) :=
    (Poly.identity boolBits).encodeCongr id (fun _ => rfl) (fun _ => rfl)
  exact ((Poly.listMap boolBits id false [] bit).comp Poly.rawFlatten).congr (fun xs => by induction xs with
    | nil => rfl
    | cons b bs ih => simpa only [Function.comp_apply,id_eq,List.map_cons,List.flatten_cons,List.singleton_append] using congrArg (List.cons b) ih)

noncomputable def Poly.vectorOfFn {α : Type} (ea : α → List Bool) (n : ℕ)
    (f : α → Fin n → Bool) (cf : ∀ i, Poly ea boolBits (fun a => f a i)) :
    Poly ea (fun v : Vector Bool n => v.toList) (fun a => Vector.ofFn (f a)) := by
  let c := (Poly.fixedList ea boolBits f cf (List.ofFn id)).comp Poly.rawBooleans
  exact c.encodeCongr id (fun _ => rfl) (fun a => by
    simp only [Function.comp_apply,id_eq,List.map_ofFn,Function.comp_def]
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂; simp)

namespace GenericMachine
open GenericGraphTables
abbrev Row (q : ℕ) := (ℕ × ℕ) × RelationTable q
abbrev Data (q : ℕ) := ℕ × List (Row q)
def relationCode {q : ℕ} (r : RelationTable q) : List Bool := r.toList
def rowCode {q : ℕ} : Row q → List Bool := prodBits (prodBits natBits natBits) relationCode
def dataCode {q : ℕ} : Data q → List Bool := prodBits natBits (listBits rowCode)
def rowData {q n m : ℕ} (r : DartRow q n m) : Row q := ((r.tail.val,r.reverseIndex.val),r.relation)
def erase {q : ℕ} (T : Table q) : Data q := (T.vertices,T.rows.toList.map rowData)
def code {q : ℕ} (T : Table q) : List Bool := dataCode (erase T)
def relationDefault (q : ℕ) : RelationTable q := Vector.replicate (q*q) false
def rowDefault (q : ℕ) : Row q := ((0,0),relationDefault q)

noncomputable def verticesPoly {q : ℕ} : Poly (code (q := q)) natBits Table.vertices :=
  (Poly.fst natBits (listBits rowCode)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)
noncomputable def rowsPoly {q : ℕ} : Poly (code (q := q)) (listBits rowCode) (fun T => T.rows.toList.map rowData) :=
  (Poly.snd natBits (listBits rowCode)).encodeCongr erase (fun _ => rfl) (fun _ => rfl)
noncomputable def dartsPoly {q : ℕ} : Poly (code (q := q)) natBits Table.darts :=
  ((rowsPoly (q := q)).comp (Poly.listLength rowCode (rowDefault q))).congr (fun T => by simp)
noncomputable def lookupPoly {q : ℕ} : Poly (prodBits (code (q := q)) natBits) rowCode
    (fun p : Table q × ℕ => (erase p.1).2.getD p.2 (rowDefault q)) := by
  let rows := (Poly.fst code natBits).comp (rowsPoly (q := q))
  let idx := Poly.snd (code (q := q)) natBits
  exact ((idx.pair rows).comp (Poly.listGetD rowCode (rowDefault q))).congr (fun _ => by
    simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop,List.getD_eq_getElem?_getD]
    rfl)
 theorem lookup_valid {q : ℕ} (T : Table q) (i : Fin T.darts) :
    (erase T).2.getD i.val (rowDefault q) = rowData T.rows[i] := by
  simp only [erase,List.getD_eq_getElem?_getD,List.getElem?_map]
  rw [List.getElem?_eq_getElem (by simp)]
  rfl

 theorem materialize_source {α : Type} {q : ℕ} (Q : α → Table q) (r : α × ℕ → Row q)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) (a : α) :
    ((Q a).vertices,(List.range (Q a).darts).map (fun i => r (a,i))) = erase (Q a) := by
  apply Prod.ext
  · rfl
  apply List.ext_getElem
  · simp [erase]
  · intro i h₁ h₂
    simp only [erase,List.getElem_map,List.getElem_range,Vector.getElem_toList]
    exact hr a ⟨i,by simpa using h₁⟩
noncomputable def materializePoly {α : Type} (ea : α → List Bool) (a₀ : α) {q : ℕ}
    (Q : α → Table q) {r : α × ℕ → Row q}
    (cn : Poly ea natBits (fun a => (Q a).vertices))
    (cm : Poly ea natBits (fun a => (Q a).darts))
    (cr : Poly (prodBits ea natBits) rowCode r)
    (hr : ∀ a (i : Fin (Q a).darts), r (a,i.val) = rowData (Q a).rows[i]) :
    Poly ea code Q := by
  let rows := Poly.tabulate ea rowCode a₀ (rowDefault q) cm cr
  exact (cn.pair rows).encodeCongr id (fun _ => rfl) (fun a => by
    exact congrArg dataCode (materialize_source Q r hr a))
end GenericMachine

end VertexCover.Machine
end


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
