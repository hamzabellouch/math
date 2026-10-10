import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCellPathProgram
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumFiniteMembership
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumCrossingPlacement
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumPortChainProgram

namespace OAI

/-! Literal physical coordinates after crossing removal. Only ports in the
computed crossing cells move; the two fresh spins use fixed local coordinates. -/

noncomputable section
namespace ContinuumCoulomb.QuantumCrossingPositionProgram
open ExactQuantumFactoring.BitStackProgram QuantumRouteCode
open scoped Classical

abbrev Input := List Pair × Pair
def inputCode : Input → List Bool := prodCode (listCode pairCode) pairCode
def cell (z : Pair) : Pair := (z.1/32,z.2/32)
def move (x : Input) : Pair := qmaCrossingMove (fun p => p ∈ x.1) x.2

noncomputable opaque cellProgram : Procedure pairCode pairCode cell := by
  let c := Procedure.constant pairCode Nat.bits 32
  exact (Procedure.binaryDiv.comp ((Procedure.first Nat.bits Nat.bits).pair c)).pair
    (Procedure.binaryDiv.comp ((Procedure.second Nat.bits Nat.bits).pair c))

noncomputable opaque innerProgram (a : Fin 4) : Procedure pairCode pairCode
    (fun p => qmaInnerPort p a) := by
  refine ((QuantumCellPathProgram.translateProgram).comp
    ((Procedure.identity pairCode).pair
      (Procedure.constant pairCode pairCode (qmaInnerPort (0,0) a)))).congrFun ?_
  intro p
  fin_cases a <;> simp [qmaCellTranslate,qmaInnerPort]

noncomputable opaque ancillaProgram (a : Fin 2) : Procedure pairCode pairCode
    (fun p => qmaGadgetAncilla p a) := by
  refine ((QuantumCellPathProgram.translateProgram).comp
    ((Procedure.identity pairCode).pair
      (Procedure.constant pairCode pairCode (qmaGadgetAncilla (0,0) a)))).congrFun ?_
  intro p
  fin_cases a <;> simp [qmaCellTranslate,qmaGadgetAncilla]

noncomputable opaque chosenInnerProgram : Procedure pairCode pairCode
    (fun z => qmaInnerPort (cell z) (qmaPortIndex z)) := by
  let c := Procedure.constant pairCode Nat.bits 32
  let rx := Procedure.binaryMod.comp ((Procedure.first Nat.bits Nat.bits).pair c)
  let ry := Procedure.binaryMod.comp ((Procedure.second Nat.bits Nat.bits).pair c)
  let eq (p : Procedure pairCode Nat.bits (fun z => z.1%32)) (n : ℕ) :=
    Procedure.binaryEq.comp (p.pair (Procedure.constant pairCode Nat.bits n))
  let x23 := eq rx 23
  let y23 := Procedure.binaryEq.comp (ry.pair (Procedure.constant pairCode Nat.bits 23))
  let x9 := eq rx 9
  exact (Procedure.conditional x23 ((innerProgram 0).comp cellProgram)
    (Procedure.conditional y23 ((innerProgram 1).comp cellProgram)
      (Procedure.conditional x9 ((innerProgram 2).comp cellProgram)
        ((innerProgram 3).comp cellProgram)))).congrFun (by
      intro z
      simp only [Function.comp_apply,qmaPortIndex,decide_eq_true_eq]
      split_ifs <;> rfl)

noncomputable opaque moveProgram : Procedure inputCode pairCode move := by
  let cs := Procedure.first (listCode pairCode) pairCode
  let z := Procedure.second (listCode pairCode) pairCode
  let p := cellProgram.comp z
  let memp := QuantumFiniteMembership.pairMemberProgram.comp (p.pair cs)
  let center := QuantumPortChainProgram.centerProgram.comp p
  let isCenter := QuantumFiniteMembership.pairEqProgram.comp (z.pair center)
  exact (Procedure.conditional
    (Procedure.boolAnd.comp (memp.pair (Procedure.boolNot.comp isCenter)))
    (chosenInnerProgram.comp z) z).congrFun (by
      intro x
      simp only [Function.comp_apply,move,qmaCrossingMove,cell,Bool.and_eq_true,decide_eq_true_eq,
        Bool.not_eq_true_eq_eq_false,decide_eq_false_iff_not])

def moved (x : List Pair × List Pair) : List Pair := x.2.map (fun z => move (x.1,z))
def fresh (cs : List Pair) : List Pair :=
  (cs.map (fun p => [qmaGadgetAncilla p 0,qmaGadgetAncilla p 1])).flatten
def positions (x : List Pair × List Pair) : List Pair := moved x++fresh x.1

noncomputable opaque movedProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode) moved :=
  Procedure.listMapWith (f := fun cs z => move (cs,z)) (0,0) (0,0) moveProgram

noncomputable opaque freshProgram : Procedure (listCode pairCode) (listCode pairCode) fresh := by
  let pair := (Procedure.listCons pairCode).comp ((ancillaProgram 0).pair
    ((Procedure.listCons pairCode).comp ((ancillaProgram 1).pair
      (Procedure.constant pairCode (listCode pairCode) []))))
  exact (QuantumRawExchange.flattenProgram pairCode (0,0)).comp
    (Procedure.listMap (0,0) [] pair)

noncomputable opaque positionsProgram :
    Procedure (prodCode (listCode pairCode) (listCode pairCode)) (listCode pairCode) positions :=
  (Procedure.listAppend pairCode (0,0)).comp (movedProgram.pair
    (freshProgram.comp (Procedure.first (listCode pairCode) (listCode pairCode))))

theorem move_eq {cs : List Pair} {cross : Pair → Prop} [DecidablePred cross]
    (hc : ∀ p, p ∈ cs ↔ cross p) (z : Pair) :
    move (cs,z)=qmaCrossingMove cross z := by
  simp only [move,qmaCrossingMove,hc]

theorem moved_ofFn {cs : List Pair} {cross : Pair → Prop} [DecidablePred cross]
    (hc : ∀ p, p ∈ cs ↔ cross p) {n : ℕ} (pos : Fin n → Pair) :
    moved (cs,List.ofFn pos)=List.ofFn (fun v => qmaCrossingMove cross (pos v)) := by
  simp only [moved,List.map_ofFn,Function.comp_def,move_eq hc]

theorem fresh_length (cs : List Pair) : (fresh cs).length=2*cs.length := by
  simp only [fresh,List.length_flatten,List.map_map,Function.comp_def,List.length_cons,
    List.length_nil,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.mul_comm]
  norm_cast

theorem positions_length (x : List Pair × List Pair) :
    (positions x).length=x.2.length+2*x.1.length := by
  simp only [positions,List.length_append,moved,List.length_map,fresh_length]

theorem moved_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) (cs : List Pair) (hc : ∀ p, p ∈ cs ↔ P.IsCrossing p) :
    moved (cs,List.ofFn (P.finishedPosition N D))=List.ofFn (P.movedPosition N D) :=
  moved_ofFn hc (P.finishedPosition N D)

theorem fresh_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G) :
    fresh (List.ofFn (fun i => (P.crossingCell i).val))=
      (List.ofFn fun i => [P.freshCrossingPosition i 0,P.freshCrossingPosition i 1]).flatten := by
  simp only [fresh,List.map_ofFn,Function.comp_def,QMAPortRouteData.freshCrossingPosition]

theorem crossingPosition_list {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) :
    List.ofFn (P.crossingPosition N D) = List.ofFn (P.movedPosition N D)++
      (List.ofFn fun i => [P.freshCrossingPosition i 0,P.freshCrossingPosition i 1]).flatten := by
  rw [List.ofFn_add]
  apply congrArg₂ (· ++ ·)
  · apply congrArg List.ofFn
    funext v
    exact P.crossingPosition_old N D v
  · rw [List.ofFn_mul]
    apply congrArg List.flatten
    apply congrArg List.ofFn
    funext i
    have hf (a : Fin 2) :
        P.crossingPosition N D
          ((⟨i.val*2+a.val,by omega⟩ : Fin (P.crossingCells.card*2)).natAdd
            (P.finishedGraph N D).n) = P.freshCrossingPosition i a := by
      have he :
          ((⟨i.val*2+a.val,by omega⟩ : Fin (P.crossingCells.card*2)).natAdd
            (P.finishedGraph N D).n) = MediatorGraph.fresh _ _ i a := by
        apply Fin.ext
        change (P.finishedGraph N D).n+(i.val*2+a.val) =
          (P.finishedGraph N D).n+(a.val+2*i.val)
        omega
      rw [he,P.crossingPosition_fresh]
    simpa only [List.ofFn_succ,List.ofFn_zero,List.cons_append,List.nil_append,
      Fin.succ_zero_eq_one] using
      congrArg List.ofFn (funext hf)

theorem positions_actual {G : QMARationalExchangeGraph} (P : QMAPortRouteData G)
    (N : ℚ) (D : ℕ) (cs : List Pair)
    (hcs : cs=List.ofFn (fun i => (P.crossingCell i).val))
    (hc : ∀ p, p ∈ cs ↔ P.IsCrossing p) :
    positions (cs,List.ofFn (P.finishedPosition N D))=List.ofFn (P.crossingPosition N D) := by
  rw [positions,moved_actual P N D cs hc,hcs,fresh_actual,crossingPosition_list]

end ContinuumCoulomb.QuantumCrossingPositionProgram

end

end OAI
