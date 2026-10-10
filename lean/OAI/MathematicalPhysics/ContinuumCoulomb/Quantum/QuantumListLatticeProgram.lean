import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListLattice
import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumListMergeProgram

namespace OAI

/-! Literal source serialization from the computed coordinate and bond tapes. -/

noncomputable section
namespace ContinuumCoulomb.QuantumListLattice
open ExactQuantumFactoring.BitStackProgram MediatorListProgram QuantumRouteCode

abbrev Input := List Pair × (List Bond × (ℚ × (ℚ × ℚ)))
def inputCode : Input → List Bool := prodCode (listCode pairCode)
  (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)

def packet (x : Input) : QuantumLatticeSerialization.Input :=
  (x.1.map qmaGridCoordinate,QuantumListMerge.value x.1.length x.2.1,x.2.2)
def value (x : Input) : BinaryHeisenberg := QuantumLatticeSerialization.value (packet x)

noncomputable def coordinateProgram : Procedure pairCode QuantumLatticeSerialization.coordinateCode
    qmaGridCoordinate :=
  (Procedure.natToInt.comp (Procedure.first Nat.bits Nat.bits)).pair
    (Procedure.natToInt.comp (Procedure.second Nat.bits Nat.bits))

noncomputable def packetProgram : Procedure inputCode QuantumLatticeSerialization.inputCode packet := by
  let ps := Procedure.first (listCode pairCode)
    (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)
  let tail := Procedure.second (listCode pairCode)
    (prodCode (listCode bondCode) QuantumLatticeSerialization.thresholdCode)
  let xs := (Procedure.first (listCode bondCode) QuantumLatticeSerialization.thresholdCode).comp tail
  let t := (Procedure.second (listCode bondCode) QuantumLatticeSerialization.thresholdCode).comp tail
  let n := (ExactQuantumFactoring.NativeAIG.Emission.listUnaryLength pairCode (0,0)).comp ps
  let bonds := QuantumListMerge.valueProgram.comp (n.pair xs)
  let points := (Procedure.listMap (0,0) (0,0) coordinateProgram).comp ps
  exact points.pair (bonds.pair t)

noncomputable def program : Procedure inputCode binaryHeisenbergCodec.encode value :=
  QuantumLatticeSerialization.program.comp packetProgram

theorem value_source (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) :
    value (ps,xs,a,b,c)=(source ps xs hp hn hb hl ha a b c hab).binary := by
  have hp' : List.ofFn (fun i : Fin ps.length => qmaGridCoordinate (ps.get i)) =
      ps.map qmaGridCoordinate := by
    simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map ps qmaGridCoordinate
  have he' : List.ofFn (fun i : Fin (QuantumListMerge.value ps.length xs).length =>
      QuantumLatticeSerialization.edge ((QuantumListMerge.value ps.length xs).get i)) =
      (QuantumListMerge.value ps.length xs).map QuantumLatticeSerialization.edge := by
    simpa only [List.get_eq_getElem] using
      List.ofFn_getElem_eq_map (QuantumListMerge.value ps.length xs) QuantumLatticeSerialization.edge
  change BinaryHeisenberg.mk _ _ _ _ = BinaryHeisenberg.mk _ _ _ _
  exact congrArg₂ (fun p e => BinaryHeisenberg.mk p e
    (BinaryRational.ofRat (a-c)) (BinaryRational.ofRat (b-c))) hp'.symm he'.symm

theorem value_valid (ps : List Pair) (xs : List Bond) (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) : (value (ps,xs,a,b,c)).Valid := by
  rw [value_source ps xs hp hn hb hl ha a b c hab]
  exact (source ps xs hp hn hb hl ha a b c hab).binary_valid

theorem value_mem_yes (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) {k : ℕ}
    (hpoly : (value (ps,xs,a,b,c)).PolynomialPromise k)
    (he : sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1) ≤ (a:ℝ)) :
    value (ps,xs,a,b,c) ∈ (sourceHeisenbergPromise k).yes := by
  rw [value_source ps xs hp hn hb hl ha a b c hab] at hpoly ⊢
  exact SquareLatticeHeisenberg.binary_mem_yes _ hpoly
    (source_yes ps xs hp hn hb hl ha a b c hab he)

theorem value_mem_no (ps : List Pair) (xs : List Bond)
    (hp : 0 < ps.length) (hn : ps.Nodup)
    (hb : SourceBondLists.bounded ps.length xs)
    (hl : ∀ e ∈ xs, e.1≠e.2.1) (ha : Adjacent ps xs hb)
    (a b c : ℚ) (hab : a < b) {k : ℕ}
    (hpoly : (value (ps,xs,a,b,c)).PolynomialPromise k)
    (he : (b:ℝ) ≤ sourceMatrixBottom ps.length
      (SourceBondLists.matrix ps.length xs+(c:ℂ) • 1)) :
    value (ps,xs,a,b,c) ∈ (sourceHeisenbergPromise k).no := by
  rw [value_source ps xs hp hn hb hl ha a b c hab] at hpoly ⊢
  exact SquareLatticeHeisenberg.binary_mem_no _ hpoly
    (source_no ps xs hp hn hb hl ha a b c hab he)

end ContinuumCoulomb.QuantumListLattice

end

end OAI
