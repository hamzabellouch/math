import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.TreeDPCount
import OAI.Combinatorics.MatchingCount.Machines.TreeSlotWeight
import OAI.Combinatorics.MatchingCount.Machines.TreePostRealization
import OAI.Combinatorics.MatchingCount.Machines.TreeSlotIndex

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
abbrev TierData := (ℕ×List Bool)×(List Bool×List Fraction)

def slotCount (x : TierData) : ℕ := (x.1.2.length+1)*x.2.1.length
def slotCountRealizer : Realizer slotCount := (composition
  (pair (composition (composition first.snd listLength) successor)
    (composition second.fst listLength)) multiply).congr (fun _=>rfl)
lemma polynomial_slotCount : PolynomialTime slotCountRealizer := by
  unfold slotCountRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_successor
  tree_cost
lemma slotCount_bound (x : TierData) : slotCount x≤((X+1)*X : Polynomial ℕ).eval (weight x) := by
  have ht := (list_length_le_weight x.1.2).trans ((weight_snd x.1).trans (weight_fst x))
  have hq := (list_length_le_weight x.2.1).trans ((weight_fst x.2).trans (weight_snd x))
  simpa [slotCount] using Nat.mul_le_mul (Nat.add_le_add_right ht 1) hq

def slots (x : TierData) : List ℕ := List.range (slotCount x)
def slotsRealizer : Realizer slots := composition slotCountRealizer range
lemma polynomial_slots : PolynomialTime slotsRealizer :=
  polynomial_boundedRange polynomial_slotCount ((X+1)*X) slotCount_bound

def weightRow (x : TierData×ℕ) : List Fraction :=
  x.1.2.2.map (fun w=>slotWeight ((x.1.1,x.2/x.1.2.1.length),w))
def weightRowRealizer : Realizer weightRow := (composition
  (pair (pair first.fst (composition (pair second (composition first.snd.fst listLength)) quotient)) first.snd.snd)
  (mapWith slotWeightRealizer)).congr (fun _=>rfl)
lemma polynomial_weightRow : PolynomialTime weightRowRealizer := by
  unfold weightRowRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_slotWeight
  have := polynomial_quotient
  tree_cost

def weightRows (x : TierData) : List (List Fraction) := (slots x).map (fun i=>weightRow (x,i))
def weightRowsRealizer : Realizer weightRows := composition (pair identity slotsRealizer) (mapWith weightRowRealizer)
lemma polynomial_weightRows : PolynomialTime weightRowsRealizer := by
  unfold weightRowsRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slots)
    (polynomial_mapWith polynomial_weightRow)

lemma index_enum {I : Type} [Fintype I] [LinearOrder I]
    (i : Fin (Fintype.card I)) : index (UnitRefresh.orderedEnum I i)=i.val := by simp [index]
lemma range_slot_indices (T q : ℕ) : List.range ((T+1)*q)=
    List.ofFn (fun i : Fin (Fintype.card (Slot T q))=>index (UnitRefresh.orderedEnum (Slot T q) i)) := by
  simp only [index_enum]
  rw [show Fintype.card (Slot T q)=(T+1)*q from slot_card T q]
  simpa using (ExecutableDP.map_range_ofFn (fun n=>n) ((T+1)*q))

lemma weightRows_source {V L : Type} [Fintype V] [LinearOrder V] [Fintype L] [LinearOrder L]
    {bags : V→Finset L} (w : Transport.BagEdge bags→ℚ) (hw : ∀ e,0≤w e)
    (ft fq : List Bool) :
    weightRows ((Fintype.card V,ft),(fq,List.ofFn (fun e=>TreeFraction.repr (w (UnitRefresh.orderedEnum _ e)))))=
      List.ofFn (fun i : Fin (Fintype.card (Slot ft.length fq.length))=>
        List.ofFn (fun e=>TreeFraction.repr
          (Transport.rationalSlotWeight w (UnitRefresh.orderedEnum _ i) (UnitRefresh.orderedEnum _ e)))) := by
  have hrow (slot : Slot ft.length fq.length) :
      weightRow (((Fintype.card V,ft),(fq,List.ofFn
        (fun edge=>TreeFraction.repr (w (UnitRefresh.orderedEnum _ edge))))),index slot)=
        List.ofFn (fun edge=>TreeFraction.repr
          (Transport.rationalSlotWeight w slot (UnitRefresh.orderedEnum _ edge))) := by
    unfold weightRow
    dsimp only
    rw [slot_index_div,List.map_ofFn]
    exact congrArg List.ofFn (funext (fun edge=>slotWeight_source ft w hw slot
      (UnitRefresh.orderedEnum (Transport.BagEdge bags) edge)))
  rw [weightRows,slots,slotCount,range_slot_indices,List.map_ofFn]
  exact congrArg List.ofFn (funext (fun slot=>hrow
    (UnitRefresh.orderedEnum (Slot ft.length fq.length) slot)))

theorem weightRows_post : ∃ p : Polynomial ℕ,∀ x : TierData,∀ t : ℕ,
    p.eval (TreePost.packed x).length≤t → ∀ coins : Fin t→Bool,
      (run (TreePost.machine weightRowsRealizer.program) (TreePost.packed x) coins).state=none ∧
      (run (TreePost.machine weightRowsRealizer.program) (TreePost.packed x) coins).tape.right₀=
        Turing.ListBlank.mk (TreePost.packed (weightRows x)) :=
  TreePost.polynomial_compiles weightRowsRealizer polynomial_weightRows
end MatchingFPRAS.NumericLadder

end OAI
