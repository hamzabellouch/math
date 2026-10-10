import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListPathProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRoutingProgram

namespace OAI

/-! The nine ordinary exchange interactions in a crossing gadget, serialized
in a fixed order. Every endpoint and rational coefficient is computed literally. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingListBlock
open ExactQuantumFactoring.BitStackProgram MediatorListProgram

abbrev Sites := (ℕ × ℕ) × (ℕ × ℕ)
def sitesCode : Sites → List Bool :=
  prodCode (prodCode Nat.bits Nat.bits) (prodCode Nat.bits Nat.bits)
def site (s : Sites) : Fin 4 → ℕ := ![s.1.1,s.1.2,s.2.1,s.2.2]
abbrev Crossing := (ℚ × ℚ) × Sites
def crossingCode : Crossing → List Bool := prodCode (prodCode ratCode ratCode) sitesCode
abbrev Parameters := ℕ × ℚ
def parametersCode : Parameters → List Bool := prodCode unaryCode ratCode
abbrev Input := Parameters × (ℕ × Crossing)
def inputCode : Input → List Bool := prodCode parametersCode (prodCode unaryCode crossingCode)

def base (x : Input) : ℕ := x.1.1+2*x.2.1

def left (x : Input) : Fin 9 → ℕ :=
  ![site x.2.2.2 0,site x.2.2.2 0,site x.2.2.2 1,site x.2.2.2 2,
    base x,site x.2.2.2 0,site x.2.2.2 1,site x.2.2.2 2,site x.2.2.2 3]
def right (x : Input) : Fin 9 → ℕ :=
  ![site x.2.2.2 1,site x.2.2.2 3,site x.2.2.2 2,site x.2.2.2 3,
    base x+1,base x,base x,base x+1,base x+1]
def coefficient (x : Input) : Fin 9 → ℚ :=
  let c := QuantumRoutingCode.coefficients (x.1.2,x.2.2.1)
  ![c 5,c 6,c 7,c 8,x.1.2^2,c 1,c 2,c 3,c 4]
def bond (x : Input) (k : Fin 9) : Bond := (left x k,right x k,coefficient x k)
def block (x : Input) : List Bond := List.ofFn (bond x)

noncomputable opaque crossingProgram : Procedure inputCode crossingCode (fun x => x.2.2) :=
  (Procedure.second unaryCode crossingCode).comp (Procedure.second parametersCode _)
noncomputable opaque sitesProgram : Procedure inputCode sitesCode (fun x => x.2.2.2) :=
  (Procedure.second (prodCode ratCode ratCode) sitesCode).comp crossingProgram
noncomputable opaque siteProgram (k : Fin 4) : Procedure inputCode Nat.bits (fun x => site x.2.2.2 k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits Nat.bits).comp
      ((Procedure.first (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.second Nat.bits Nat.bits).comp
      ((Procedure.first (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => ?_) k
  · exact (Procedure.first Nat.bits Nat.bits).comp
      ((Procedure.second (prodCode Nat.bits Nat.bits) _).comp sitesProgram)
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact (Procedure.second Nat.bits Nat.bits).comp
      ((Procedure.second (prodCode Nat.bits Nat.bits) _).comp sitesProgram)

noncomputable opaque radiusProgram : Procedure inputCode ratCode (fun x => x.1.2) :=
  (Procedure.second unaryCode ratCode).comp (Procedure.first parametersCode _)
noncomputable opaque baseProgram : Procedure inputCode Nat.bits base := by
  let n := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode ratCode).comp (Procedure.first parametersCode (prodCode unaryCode crossingCode)))
  let i := Procedure.unaryToBits.comp
    ((Procedure.first unaryCode crossingCode).comp (Procedure.second parametersCode (prodCode unaryCode crossingCode)))
  exact Procedure.binaryAdd.comp (n.pair
    (Procedure.binaryMul.comp ((Procedure.constant inputCode Nat.bits 2).pair i)))
noncomputable opaque nextProgram : Procedure inputCode Nat.bits (fun x => base x+1) :=
  Procedure.binaryAdd.comp (baseProgram.pair (Procedure.constant inputCode Nat.bits 1))
noncomputable opaque leftProgram (k : Fin 9) : Procedure inputCode Nat.bits (fun x => left x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 0
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact siteProgram 3

noncomputable opaque rightProgram (k : Fin 9) : Procedure inputCode Nat.bits (fun x => right x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 3
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact siteProgram 3
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact baseProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact nextProgram
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact nextProgram

noncomputable opaque coefficientsProgram (k : Fin 10) :
    Procedure inputCode ratCode (fun x => QuantumRoutingCode.coefficients (x.1.2,x.2.2.1) k) :=
  (QuantumRoutingCode.coefficientProgram k).comp
    (radiusProgram.pair ((Procedure.first (prodCode ratCode ratCode) sitesCode).comp crossingProgram))
noncomputable opaque coefficientProgram (k : Fin 9) :
    Procedure inputCode ratCode (fun x => coefficient x k) := by
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 5
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 6
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 7
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 8
  refine Fin.cases ?_ (fun k => ?_) k
  · exact QuantumRoutingCode.squareProgram radiusProgram
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 1
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 2
  refine Fin.cases ?_ (fun k => ?_) k
  · exact coefficientsProgram 3
  refine Fin.cases ?_ (fun k => Fin.elim0 k) k
  exact coefficientsProgram 4

noncomputable opaque bondProgram (k : Fin 9) : Procedure inputCode bondCode (fun x => bond x k) :=
  (leftProgram k).pair ((rightProgram k).pair (coefficientProgram k))
noncomputable opaque blockProgram : Procedure inputCode (listCode bondCode) block :=
  QuantumRawExchange.fixedListProgram inputCode bondCode 9 (fun k x => bond x k) bondProgram

theorem block_length (x : Input) : (block x).length=9 := List.length_ofFn

theorem block_bounded (x : Input) (r : ℕ) (hi : x.2.1 < r)
    (hs : ∀ a, site x.2.2.2 a < x.1.1) :
    SourceBondLists.bounded (x.1.1+2*r) (block x) := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  fin_cases k <;> simp [bond,left,right,base,site] at * <;> omega

theorem block_noLoops (x : Input) (hs : ∀ a, site x.2.2.2 a < x.1.1)
    (hinj : Function.Injective (site x.2.2.2)) :
    ∀ e ∈ block x, e.1 ≠ e.2.1 := by
  intro e he
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp he
  have h0 := hs 0
  have h1 := hs 1
  have h2 := hs 2
  have h3 := hs 3
  have h01 := hinj.ne (by decide : (0 : Fin 4) ≠ 1)
  have h03 := hinj.ne (by decide : (0 : Fin 4) ≠ 3)
  have h12 := hinj.ne (by decide : (1 : Fin 4) ≠ 2)
  have h23 := hinj.ne (by decide : (2 : Fin 4) ≠ 3)
  fin_cases k <;> simp [bond,left,right,base,site] at * <;> omega

end ContinuumCoulomb.QuantumCrossingListBlock

end

end OAI
