import Mathlib
import OAI.Computability.QuantumFactoring.BitStackWords

namespace OAI



section

namespace ExactQuantumFactoring.BitStackProgram.Procedure
variable {β : Type}

/-- A truth table on one Boolean has two literal finite output words. This
performs no run-time computation in its Boolean branch labels. -/
noncomputable def ofBool (eb : β→List Bool) (f : Bool→β) :
    Procedure boolCode eb f := by
  let p:=constant (fun _ : Unit=>[]) eb (f false)
  let q:=constant (fun _ : Unit=>[]) eb (f true)
  exact ((chooseBit p q).precompose (fun b=>(b,()))).congrFun
    (by intro b;cases b <;> rfl)

noncomputable def ofBool₂ (eb : β→List Bool) (f : Bool→Bool→β) :
    Procedure (prodCode boolCode boolCode) eb (fun x=>f x.1 x.2) :=
  (choose (ofBool eb (f false)) (ofBool eb (f true))).congrFun
    (by rintro ⟨b,c⟩;cases b <;> rfl)

noncomputable def ofBool₃ (eb : β→List Bool) (f : Bool→Bool→Bool→β) :
    Procedure (prodCode boolCode (prodCode boolCode boolCode)) eb
      (fun x=>f x.1 x.2.1 x.2.2) :=
  (choose (ofBool₂ eb (f false)) (ofBool₂ eb (f true))).congrFun
    (by rintro ⟨b,c,d⟩;cases b <;> rfl)

noncomputable def boolNot : Procedure boolCode boolCode not := ofBool boolCode not
noncomputable def boolAnd : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 && x.2) := ofBool₂ boolCode and
noncomputable def boolOr : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>x.1 || x.2) := ofBool₂ boolCode or
noncomputable def boolXor : Procedure (prodCode boolCode boolCode) boolCode
    (fun x=>xor x.1 x.2) := ofBool₂ boolCode xor

noncomputable def cons : Procedure (prodCode boolCode (id : List Bool→List Bool)) id
    (fun x=>x.1::x.2) := by
  let pp : Procedure (id : List Bool→List Bool) id (fun xs=>false::xs):=
    (prepend id [false]).result (by intro xs;rfl)
  let qq : Procedure (id : List Bool→List Bool) id (fun xs=>true::xs):=
    (prepend id [true]).result (by intro xs;rfl)
  exact (choose pp qq).congrFun (by rintro ⟨b,xs⟩;cases b <;> rfl)
end ExactQuantumFactoring.BitStackProgram.Procedure

end



end OAI
