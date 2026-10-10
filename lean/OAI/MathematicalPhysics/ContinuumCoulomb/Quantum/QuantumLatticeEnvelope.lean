import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumLatticeCoefficient

namespace OAI

/-! A literal polynomial program computes the final coefficient envelope;
the exponent in the source promise is uniform over all inputs. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCoefficientPrograms
open ExactQuantumFactoring.BitStackProgram

private noncomputable def addP {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x+g x) := Procedure.unaryAdd.comp (p.pair q)
private noncomputable def mulP {α : Type} {ea : α → List Bool} {f g : α → ℕ}
    (p : Procedure ea unaryCode f) (q : Procedure ea unaryCode g) :
    Procedure ea unaryCode (fun x => f x*g x) := Procedure.unaryMul.comp (p.pair q)

noncomputable def iteratedOfProgram {α : Type} {ea : α → List Bool} {m L T : α → ℕ}
    (pm : Procedure ea unaryCode m) (pl : Procedure ea unaryCode L)
    (pt : Procedure ea unaryCode T) (k : ℕ) :
    Procedure ea unaryCode (fun x => iterated (m x) (L x) (T x) k) := by
  induction k with
  | zero => exact pl
  | succ k ih =>
    exact pathCoefficientProgram (mulP (Procedure.constant ea unaryCode (3^k)) pm) ih pt

abbrev LatticeInput := ℕ × (ℕ × (ℕ × ℕ))
def latticeInputCode : LatticeInput → List Bool :=
  prodCode unaryCode (prodCode unaryCode (prodCode unaryCode unaryCode))

noncomputable opaque latticeM : Procedure latticeInputCode unaryCode (fun x => x.1) := Procedure.first _ _
noncomputable opaque latticeTail : Procedure latticeInputCode (prodCode unaryCode (prodCode unaryCode unaryCode))
    (fun x => x.2) := Procedure.second _ _
noncomputable opaque latticeR : Procedure latticeInputCode unaryCode (fun x => x.2.1) :=
  (Procedure.first _ _).comp latticeTail
noncomputable opaque latticeLT : Procedure latticeInputCode (prodCode unaryCode unaryCode)
    (fun x => x.2.2) := (Procedure.second _ _).comp latticeTail
noncomputable opaque latticeL : Procedure latticeInputCode unaryCode (fun x => x.2.2.1) :=
  (Procedure.first _ _).comp latticeLT
noncomputable opaque latticeT : Procedure latticeInputCode unaryCode (fun x => x.2.2.2) :=
  (Procedure.second _ _).comp latticeLT

noncomputable opaque latticeBoundProgram (D : ℕ) :
    Procedure latticeInputCode unaryCode (fun x => latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let c := Procedure.constant latticeInputCode unaryCode
  let m₁ := mulP (c (3^D)) latticeM
  let L₁ := iteratedOfProgram latticeM latticeL latticeT D
  let m₂ := addP m₁ (mulP (c 9) latticeR)
  let L₂ := crossingCoefficientProgram m₁ latticeR (mulP (addP m₁ (c 1)) L₁) latticeT
  let L₃ := mulP (addP m₂ (c 1)) L₂
  let L₄ := iteratedOfProgram (mulP (c 3) m₂) (pathCoefficientProgram m₂ L₃ latticeT) latticeT 80
  exact (mulP (addP (mulP (c (3^81)) m₂) (c 1)) L₄).congrFun (by intro x; rfl)

theorem latticeBound_power (D : ℕ) : ∃ a : ℕ, ∀ x : LatticeInput,
    latticeBound D x.1 x.2.1 x.2.2.1 x.2.2.2 ≤ ((latticeInputCode x).length+2)^a :=
  unaryProcedure_power_bound (latticeBoundProgram D)

end ContinuumCoulomb.QuantumCoefficientPrograms

end

end OAI
