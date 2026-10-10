import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumForkListPoints

namespace OAI

/-! A complete literal rational fork round, including all four background
bonds, the scalar offset and the remaining active ports. -/

noncomputable section
namespace ContinuumCoulomb.QuantumForkList
open ExactQuantumFactoring.BitStackProgram

abbrev BondInput := ℕ × (ℕ × (ℚ × Pair))
def bondInputCode : BondInput → List Bool :=
  prodCode Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
def bond (x : BondInput) (k : Fin 4) : MediatorListProgram.Bond :=
  ![(x.2.2.2.1.1,x.2.2.2.2.1,2*x.2.2.2.1.2*x.2.2.2.2.2),
    (x.1+2*x.2.1,x.1+2*x.2.1+1,x.2.2.1^2),
    (x.2.2.2.1.1,x.1+2*x.2.1+1,2*x.2.2.1*x.2.2.2.1.2),
    (x.2.2.2.2.1,x.1+2*x.2.1+1,2*x.2.2.1*x.2.2.2.2.2)] k

noncomputable def bondProgram (k : Fin 4) :
    Procedure bondInputCode MediatorListProgram.bondCode (fun x => bond x k) := by
  let n := Procedure.first Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
  let tail := Procedure.second Nat.bits (prodCode Nat.bits (prodCode ratCode pairCode))
  let i := (Procedure.first Nat.bits (prodCode ratCode pairCode)).comp tail
  let rest := (Procedure.second Nat.bits (prodCode ratCode pairCode)).comp tail
  let r := (Procedure.first ratCode pairCode).comp rest
  let p := (Procedure.second ratCode pairCode).comp rest
  let a := (Procedure.first Nat.bits ratCode).comp ((Procedure.first portCode portCode).comp p)
  let b := (Procedure.first Nat.bits ratCode).comp ((Procedure.second portCode portCode).comp p)
  let j := leftWeight.comp p
  let q := rightWeight.comp p
  let two := Procedure.constant bondInputCode ratCode 2
  let twiceI := Procedure.binaryMul.comp ((Procedure.constant bondInputCode Nat.bits 2).pair i)
  let first := Procedure.binaryAdd.comp (n.pair twiceI)
  let second := Procedure.successor.comp first
  refine Fin.cases ?_ (fun k => ?_) k
  · exact a.pair (b.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair j)).pair q)))
  · refine Fin.cases ?_ (fun k => ?_) k
    · exact first.pair (second.pair (QuantumRoutingCode.squareProgram r))
    · refine Fin.cases ?_ (fun k => ?_) k
      · exact a.pair (second.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair r)).pair j)))
      · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
        exact b.pair (second.pair (Procedure.ratMul.comp ((Procedure.ratMul.comp (two.pair r)).pair q)))

noncomputable def pairBondsProgram : Procedure bondInputCode (listCode MediatorListProgram.bondCode)
    (fun x => pairBonds x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (QuantumRawExchange.fixedListProgram bondInputCode MediatorListProgram.bondCode 4
    (fun k x => bond x k) bondProgram).congrFun (by
      intro x
      simp [bond,pairBonds,List.ofFn_succ])

noncomputable def addedBondInputProgram :
    Procedure (prodCode unaryCode scaleCode) bondInputCode
      (fun x => (x.2.2.1,x.1,x.2.1,
        (((catalog x.2.2.2.2.2).drop x.1).headD (0,((0,0),(0,0)))).2)) := by
  let i := Procedure.unaryToBits.comp (Procedure.first unaryCode scaleCode)
  let env := Procedure.second unaryCode scaleCode
  let r := (Procedure.first ratCode stateCode).comp env
  let s := (Procedure.second ratCode stateCode).comp env
  let n := Procedure.unaryToBits.comp (countProgram.comp s)
  let ps := catalogProgram.comp (groupsProgram.comp s)
  let selected := (Procedure.second Nat.bits pairCode).comp
    ((Procedure.listGet taggedCode (0,((0,0),(0,0)))).comp (i.pair ps))
  exact n.pair (i.pair (r.pair selected))

noncomputable def addedBondsProgram : Procedure scaleCode (listCode MediatorListProgram.bondCode)
    (fun x => addedBonds x.2 x.1) := by
  let s := Procedure.second ratCode stateCode
  let count := pairCountProgram.comp (groupsProgram.comp s)
  let block := pairBondsProgram.comp addedBondInputProgram
  let tab := Procedure.tabulate (f := fun (x : ScaleInput) i => pairBonds x.2.1 i x.1
    (((catalog x.2.2.2.2).drop i).headD (0,((0,0),(0,0)))).2) [] block
  exact ((QuantumRawExchange.flattenProgram MediatorListProgram.bondCode (0,0,0)).comp
    (tab.comp (count.pair (Procedure.identity scaleCode)))).congrFun (by
      intro x
      simp only [Function.comp_apply,addedBonds,catalog_length]
      rfl)

noncomputable def nextProgram : Procedure scaleCode stateCode (fun x => next x.1 x.2) := by
  let s := Procedure.second ratCode stateCode
  let n := countProgram.comp s
  let gs := groupsProgram.comp s
  let count := pairCountProgram.comp gs
  let r := scaleProgram
  let nextCount := Procedure.unaryAdd.comp (n.pair (Procedure.unaryAdd.comp (count.pair count)))
  let nextBonds := (Procedure.listAppend MediatorListProgram.bondCode (0,0,0)).comp
    ((bondsProgram.comp s).pair (addedBondsProgram.comp (r.pair s)))
  let pairs := (Procedure.listMap (0,((0,0),(0,0))) ((0,0),(0,0))
    (Procedure.second Nat.bits pairCode)).comp (catalogProgram.comp gs)
  let offsets := RationalSumProgram.sumProgram.comp
    ((Procedure.listMap ((0,0),(0,0)) 0 pairOffsetProgram).comp pairs)
  let countRat := Procedure.natToRat.comp (Procedure.unaryToBits.comp count)
  let singlets := Procedure.ratMul.comp
    ((Procedure.ratMul.comp ((Procedure.constant scaleCode ratCode 3).pair countRat)).pair
      (QuantumRoutingCode.squareProgram r))
  let nextScalar := Procedure.ratAdd.comp
    ((Procedure.ratAdd.comp ((scalarProgram.comp s).pair offsets)).pair singlets)
  let nextGroups := nextGroupsProgram.comp ((Procedure.unaryToBits.comp n).pair (r.pair gs))
  exact (nextCount.pair (nextBonds.pair (nextScalar.pair nextGroups))).congrFun (by
    intro x
    dsimp only [Function.comp_apply,next]
    rw [two_mul]
    rfl)

noncomputable def iterateProgram : (D : ℕ) →
    Procedure scaleCode stateCode (fun x => iterate x.1 D x.2)
  | 0 => Procedure.second ratCode stateCode
  | D+1 => (nextProgram.comp
      ((Procedure.first ratCode stateCode).pair (iterateProgram D))).congrFun (by
        intro x
        rfl)

end ContinuumCoulomb.QuantumForkList

end

end OAI
