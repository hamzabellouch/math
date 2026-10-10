import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumOrderedXZTerm
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRawExchange

namespace OAI

/-! Raw scalar/field/pair instructions read directly from the ordered
site-label list. Only two entries are inspected at the final X/Z stage. -/

namespace ContinuumCoulomb.QuantumOrderedRawPacking

abbrev Letter := ℕ × ℕ
abbrev Input := List Letter × ℚ

def scalar (j : ℚ) : QuantumRawExchange.Raw :=
  ((false,false),((0,0),((false,false),j)))

def field (u : Letter) (j : ℚ) : QuantumRawExchange.Raw :=
  if u.2 = 0 then scalar j else
    ((false,true),((u.1,0),((decide (u.2=1),false),j)))

def pair (u v : Letter) (j : ℚ) : QuantumRawExchange.Raw :=
  ((true,false),((u.1,v.1),((decide (u.2=1),decide (v.2=1)),j)))

def value (x : Input) : QuantumRawExchange.Raw :=
  match x.1 with
  | [] => scalar x.2
  | [u] => field u x.2
  | u :: v :: _ => if u.1=v.1 then field u x.2 else
      if u.2=0 then field v x.2 else
      if v.2=0 then field u x.2 else pair u v x.2

theorem axis_zero (a : Fin 4) :
    decide (QuantumOrderedXZTerm.axis a = 0) = decide (a.val = 1) := by
  fin_cases a <;> rfl

theorem field_pack {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) (j : ℚ) :
    field (i.val,(w i).val) j = QuantumRawExchange.pack (QuantumOrderedXZTerm.field w i) j := by
  by_cases hi : w i = 0
  · simp [field,scalar,QuantumOrderedXZTerm.field,hi,QuantumRawExchange.pack]
  · have hv : (w i).val ≠ 0 := fun h => hi (Fin.ext h)
    simp only [field,hv,ite_false,QuantumOrderedXZTerm.field,hi,QuantumRawExchange.pack,
      axis_zero]

theorem value_pack {n : ℕ} (xs : List (Fin n)) (w : Fin n → Fin 4) (j : ℚ) :
    value (xs.map (fun i => (i.val,(w i).val)),j) =
      QuantumRawExchange.pack (QuantumOrderedXZTerm.ofSites xs w) j := by
  cases xs with
  | nil => rfl
  | cons i xs =>
    cases xs with
    | nil => exact field_pack w i j
    | cons k xs =>
      by_cases hik : i=k
      · subst k
        simp only [List.map_cons,value,ite_true,QuantumOrderedXZTerm.ofSites,dite_true]
        exact field_pack w i j
      · have hv : i.val ≠ k.val := fun h => hik (Fin.ext h)
        have hi : (w i).val=0 ↔ w i=0 := Fin.val_eq_zero_iff
        have hk : (w k).val=0 ↔ w k=0 := Fin.val_eq_zero_iff
        simp only [List.map_cons,value,hv,ite_false,QuantumOrderedXZTerm.ofSites,
          dite_eq_right hik,hi,hk]
        split_ifs with hi hk
        · exact field_pack w k j
        · exact field_pack w i j
        · simp only [pair,QuantumRawExchange.pack,axis_zero]

end ContinuumCoulomb.QuantumOrderedRawPacking

end OAI
