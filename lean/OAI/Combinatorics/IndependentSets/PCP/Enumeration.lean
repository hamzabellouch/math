import Mathlib
import OAI.Combinatorics.IndependentSets.PCP.AlphabetGraph

namespace OAI

namespace IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

open IndependentSetsGames.Foundations.Hastad
open scoped BigOperators

def bitValue (bit : Bool) : Nat := if bit then 1 else 0

def boolEquiv : Bool ≃ Fin 2 := finTwoEquiv.symm

@[simp] theorem boolEquiv_val (bit : Bool) : (boolEquiv bit).val = bitValue bit := by
  cases bit <;> rfl

def productEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A × B ≃ Fin (a * b) :=
  (Equiv.prodCongr left right).trans finProdFinEquiv

@[simp] theorem productEquiv_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) (y : B) :
    (productEquiv left right (x, y)).val = (left x).val * b + (right y).val := by
  change (right y).val + b * (left x).val = _
  simp [Nat.mul_comm, Nat.add_comm]

def sumEquiv {A B : Type*} {a b : Nat} (left : A ≃ Fin a) (right : B ≃ Fin b) :
    A ⊕ B ≃ Fin (a + b) :=
  (Equiv.sumCongr left right).trans finSumFinEquiv

@[simp] theorem sumEquiv_inl_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (x : A) :
    (sumEquiv left right (.inl x)).val = (left x).val := rfl

@[simp] theorem sumEquiv_inr_val {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) (y : B) :
    (sumEquiv left right (.inr y)).val = a + (right y).val := rfl

def tapeCount (q : Nat) : Nat := 2 ^ q
def pairTapeCount (q : Nat) : Nat := 2 ^ (q * q)
def fiveTapeCount (q : Nat) : Nat := pairTapeCount q ^ 5
def localCount (q : Nat) : Nat := 4 * (2 * tapeCount q) * fiveTapeCount q
def eventCount (m q : Nat) : Nat := m * localCount q
def addressCount (n m q : Nat) : Nat := n * tapeCount q + m * pairTapeCount q
def vertexCount (n m q : Nat) : Nat := eventCount m q + addressCount n m q
def dartCount (m q : Nat) : Nat := eventCount m q * 12

def cubeEquiv (q : Nat) : Cube (Fin q) ≃ Fin (tapeCount q) :=
  (Equiv.arrowCongr (Equiv.refl (Fin q)) boolEquiv).trans finFunctionFinEquiv

def cubeRank {q : Nat} (tape : Cube (Fin q)) : Fin (tapeCount q) := cubeEquiv q tape
def cubeUnrank {q : Nat} (index : Fin (tapeCount q)) : Cube (Fin q) :=
  (cubeEquiv q).symm index

@[simp] theorem cubeUnrank_cubeRank {q : Nat} (tape : Cube (Fin q)) :
    cubeUnrank (cubeRank tape) = tape := (cubeEquiv q).symm_apply_apply tape

@[simp] theorem cubeRank_cubeUnrank {q : Nat} (index : Fin (tapeCount q)) :
    cubeRank (cubeUnrank index) = index := (cubeEquiv q).apply_symm_apply index

theorem cubeUnrank_digit {q : Nat} (index : Fin (tapeCount q)) (i : Fin q) :
    bitValue (cubeUnrank index i) = index.val / 2 ^ i.val % 2 := by
  have digit : boolEquiv (cubeUnrank index i) =
      (⟨index.val / 2 ^ i.val % 2, Nat.mod_lt _ (by decide)⟩ : Fin 2) := by
    change boolEquiv (boolEquiv.symm _) = _
    exact boolEquiv.apply_symm_apply _
  simpa only [boolEquiv_val] using congrArg Fin.val digit

theorem cubeEquiv_val (q : Nat) (tape : Cube (Fin q)) :
    (cubeEquiv q tape).val = ∑ i : Fin q, bitValue (tape i) * 2 ^ i.val := by
  change (finFunctionFinEquiv (fun i => boolEquiv (tape i))).val = _
  rw [finFunctionFinEquiv_apply]
  simp only [boolEquiv_val]

def pairIndex (q : Nat) : Fin q × Fin q ≃ Fin (q * q) := finProdFinEquiv

theorem pairIndex_val (q : Nat) (i j : Fin q) :
    (pairIndex q (i, j)).val = i.val * q + j.val := by
  change j.val + q * i.val = _
  simp [Nat.mul_comm, Nat.add_comm]

def pairCubeEquiv (q : Nat) : Cube (Fin q × Fin q) ≃ Fin (pairTapeCount q) :=
  (Equiv.arrowCongr (pairIndex q) (Equiv.refl Bool)).trans (cubeEquiv (q * q))

def pairCubeRank {q : Nat} (tape : Cube (Fin q × Fin q)) : Fin (pairTapeCount q) :=
  pairCubeEquiv q tape

def pairCubeUnrank {q : Nat} (index : Fin (pairTapeCount q)) : Cube (Fin q × Fin q) :=
  (pairCubeEquiv q).symm index

@[simp] theorem pairCubeUnrank_pairCubeRank {q : Nat} (tape : Cube (Fin q × Fin q)) :
    pairCubeUnrank (pairCubeRank tape) = tape := (pairCubeEquiv q).symm_apply_apply tape

@[simp] theorem pairCubeRank_pairCubeUnrank {q : Nat} (index : Fin (pairTapeCount q)) :
    pairCubeRank (pairCubeUnrank index) = index := (pairCubeEquiv q).apply_symm_apply index

theorem pairCubeEquiv_val (q : Nat) (tape : Cube (Fin q × Fin q)) :
    (pairCubeEquiv q tape).val =
      ∑ i : Fin (q * q), bitValue (tape ((pairIndex q).symm i)) * 2 ^ i.val :=
  cubeEquiv_val (q * q) _

def inputCoordinateEquiv (q : Nat) :
    AlphabetReduction.InputCoordinate (Fin q) ≃ Fin (2 * tapeCount q) :=
  productEquiv boolEquiv (cubeEquiv q)

def fivePairTapesEquiv (q : Nat) :
    (Cube (Fin q × Fin q) × Cube (Fin q × Fin q) × Cube (Fin q × Fin q) ×
      Cube (Fin q × Fin q) × Cube (Fin q × Fin q)) ≃ Fin (fiveTapeCount q) :=
  (productEquiv (pairCubeEquiv q)
    (productEquiv (pairCubeEquiv q)
      (productEquiv (pairCubeEquiv q)
        (productEquiv (pairCubeEquiv q) (pairCubeEquiv q))))).trans
    (finCongr (by simp [fiveTapeCount, pow_succ, Nat.mul_assoc]))

def localEventEquiv (q : Nat) : AlphabetGraph.LocalEvent (Fin q) ≃ Fin (localCount q) :=
  (productEquiv (Equiv.refl (Fin 4))
    (productEquiv (inputCoordinateEquiv q) (fivePairTapesEquiv q))).trans
    (finCongr (by simp [localCount, Nat.mul_assoc]))

def eventEquiv (m q : Nat) :
    AlphabetGraph.Event (Fin m) (Fin q) ≃ Fin (eventCount m q) :=
  productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)

def addressEquiv (n m q : Nat) :
    AlphabetGraph.Address (Fin n) (Fin m) (Fin q) ≃ Fin (addressCount n m q) :=
  sumEquiv (productEquiv (Equiv.refl (Fin n)) (cubeEquiv q))
    (productEquiv (Equiv.refl (Fin m)) (pairCubeEquiv q))

def vertexEquiv (n m q : Nat) :
    QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) ≃ Fin (vertexCount n m q) :=
  sumEquiv (eventEquiv m q) (addressEquiv n m q)

def dartEquiv (m q : Nat) :
    QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6 ≃ Fin (dartCount m q) :=
  (productEquiv (productEquiv (eventEquiv m q) (Equiv.refl (Fin 6))) boolEquiv).trans
    (finCongr (by simp [dartCount, Nat.mul_assoc]))

def labelEquiv : QueryIncidence.Label 6 ≃ Fin 64 := cubeEquiv 6

theorem labelEquiv_val (label : QueryIncidence.Label 6) :
    (labelEquiv label).val = ∑ i : Fin 6, bitValue (label i) * 2 ^ i.val :=
  cubeEquiv_val 6 label

@[simp] theorem inputCoordinateEquiv_val (q : Nat) (side : Bool) (tape : Cube (Fin q)) :
    (inputCoordinateEquiv q (side, tape)).val =
      bitValue side * tapeCount q + (cubeEquiv q tape).val := by
  simp [inputCoordinateEquiv]

theorem fivePairTapesEquiv_val (q : Nat) (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) :
    (fivePairTapesEquiv q (f, g, r₀, r₁, r₂)).val =
      (pairCubeEquiv q f).val * pairTapeCount q ^ 4 +
        (pairCubeEquiv q g).val * pairTapeCount q ^ 3 +
        (pairCubeEquiv q r₀).val * pairTapeCount q ^ 2 +
        (pairCubeEquiv q r₁).val * pairTapeCount q + (pairCubeEquiv q r₂).val := by
  simp [fivePairTapesEquiv, productEquiv_val, pow_succ, Nat.mul_assoc, Nat.add_assoc]

theorem localEventEquiv_val (q : Nat) (kind : Fin 4)
    (coordinate : AlphabetReduction.InputCoordinate (Fin q))
    (f g r₀ r₁ r₂ : Cube (Fin q × Fin q)) :
    (localEventEquiv q (kind, coordinate, f, g, r₀, r₁, r₂)).val =
      kind.val * (2 * tapeCount q * fiveTapeCount q) +
        (inputCoordinateEquiv q coordinate).val * fiveTapeCount q +
        (fivePairTapesEquiv q (f, g, r₀, r₁, r₂)).val := by
  simp [localEventEquiv, productEquiv_val, Nat.add_assoc]

@[simp] theorem eventEquiv_val (m q : Nat) (edge : Fin m)
    (sample : AlphabetGraph.LocalEvent (Fin q)) :
    (eventEquiv m q (edge, sample)).val = edge.val * localCount q +
      (localEventEquiv q sample).val := by
  change (localEventEquiv q sample).val + localCount q * edge.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inl_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (addressEquiv n m q (.inl (vertex, tape))).val =
      vertex.val * tapeCount q + (cubeEquiv q tape).val := by
  change (cubeEquiv q tape).val + tapeCount q * vertex.val = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem addressEquiv_inr_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (addressEquiv n m q (.inr (edge, tape))).val =
      n * tapeCount q + (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val) := by
  change n * tapeCount q + ((pairCubeEquiv q tape).val + pairTapeCount q * edge.val) = _
  simp [Nat.mul_comm, Nat.add_comm]

@[simp] theorem vertexEquiv_event_val (n m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) :
    (vertexEquiv n m q (.inl event)).val = (eventEquiv m q event).val := rfl

@[simp] theorem vertexEquiv_vertexAddress_val (n m q : Nat) (vertex : Fin n)
    (tape : Cube (Fin q)) :
    (vertexEquiv n m q (.inr (.inl (vertex, tape)))).val =
      eventCount m q + (vertex.val * tapeCount q + (cubeEquiv q tape).val) := by
  change eventCount m q + (addressEquiv n m q (.inl (vertex, tape))).val = _
  rw [addressEquiv_inl_val]

@[simp] theorem vertexEquiv_edgeAddress_val (n m q : Nat) (edge : Fin m)
    (tape : Cube (Fin q × Fin q)) :
    (vertexEquiv n m q (.inr (.inr (edge, tape)))).val =
      eventCount m q + (n * tapeCount q +
        (edge.val * pairTapeCount q + (pairCubeEquiv q tape).val)) := by
  change eventCount m q + (addressEquiv n m q (.inr (edge, tape))).val = _
  rw [addressEquiv_inr_val]

@[simp] theorem dartEquiv_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q ((event, slot), orientation)).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue orientation := by
  change (boolEquiv orientation).val + 2 * (slot.val + 6 * (eventEquiv m q event).val) = _
  rw [boolEquiv_val]
  omega

theorem dartEquiv_reverse_val (m q : Nat)
    (event : AlphabetGraph.Event (Fin m) (Fin q)) (slot : Fin 6) (orientation : Bool) :
    (dartEquiv m q (QueryIncidence.reverse ((event, slot), orientation))).val =
      (eventEquiv m q event).val * 12 + slot.val * 2 + bitValue (!orientation) :=
  dartEquiv_val m q event slot (!orientation)

def ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) : List A :=
  List.ofFn order.symm

@[simp] theorem ordered_length {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).length = count := by simp [ordered]

theorem mem_ordered {A : Type*} {count : Nat} (order : A ≃ Fin count) (x : A) :
    x ∈ ordered order := by
  simp only [ordered, List.mem_ofFn]
  exact ⟨order x, order.symm_apply_apply x⟩

theorem ordered_nodup {A : Type*} {count : Nat} (order : A ≃ Fin count) :
    (ordered order).Nodup := by
  rw [ordered, List.nodup_ofFn]
  exact order.symm.injective

@[simp] theorem ordered_refl (n : Nat) : ordered (Equiv.refl (Fin n)) = List.finRange n := rfl

@[simp] theorem ordered_bool : ordered boolEquiv = [false, true] := rfl

theorem ordered_trans_finCongr {A : Type*} {a b : Nat}
    (order : A ≃ Fin a) (sameCount : a = b) :
    ordered (order.trans (finCongr sameCount)) = ordered order := by
  cases sameCount
  rfl

theorem ordered_product {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (productEquiv left right) =
      (ordered left).flatMap (fun x => (ordered right).map (fun y => (x, y))) := by
  have atIndex (i : Fin a) (j : Fin b) (h : i.val * b + j.val < a * b) :
      (productEquiv left right).symm ⟨i.val * b + j.val, h⟩ =
        (left.symm i, right.symm j) := by
    have same : (⟨i.val * b + j.val, h⟩ : Fin (a * b)) = finProdFinEquiv (i, j) := by
      apply Fin.ext
      simp [finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
    rw [same]
    simp [productEquiv]
  unfold ordered
  rw [List.ofFn_mul]
  simp only [atIndex, List.flatMap_def, List.map_ofFn, Function.comp_def]

theorem ordered_sum {A B : Type*} {a b : Nat}
    (left : A ≃ Fin a) (right : B ≃ Fin b) :
    ordered (sumEquiv left right) =
      (ordered left).map Sum.inl ++ (ordered right).map Sum.inr := by
  have atLeft (i : Fin a) :
      (sumEquiv left right).symm (i.castLE (Nat.le_add_right a b)) =
        Sum.inl (left.symm i) := by
    change (Equiv.sumCongr left right).symm
      (finSumFinEquiv.symm (Fin.castAdd b i)) = _
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have atRight (j : Fin b) :
      (sumEquiv left right).symm (j.natAdd a) = Sum.inr (right.symm j) := by
    change (Equiv.sumCongr left right).symm (finSumFinEquiv.symm (j.natAdd a)) = _
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  unfold ordered
  rw [List.ofFn_add]
  simp only [atLeft, atRight, List.map_ofFn, Function.comp_def]

def localEvents (q : Nat) : List (AlphabetGraph.LocalEvent (Fin q)) :=
  ordered (localEventEquiv q)

@[simp] theorem localEvents_length (q : Nat) : (localEvents q).length = localCount q :=
  ordered_length _

theorem ordered_event (m q : Nat) :
    ordered (eventEquiv m q) =
      (List.finRange m).flatMap (fun edge => (localEvents q).map (fun event => (edge, event))) := by
  change ordered (productEquiv (Equiv.refl (Fin m)) (localEventEquiv q)) = _
  rw [ordered_product, ordered_refl]
  rfl

theorem ordered_dart (m q : Nat) :
    ordered (dartEquiv m q) =
      (List.finRange m).flatMap (fun edge =>
        (localEvents q).flatMap (fun event =>
          (List.finRange 6).flatMap (fun slot =>
            [(((edge, event), slot), false), (((edge, event), slot), true)]))) := by
  unfold dartEquiv dartCount
  rw [ordered_trans_finCongr, ordered_product, ordered_product, ordered_event]
  simp only [ordered_refl, ordered_bool, List.flatMap_assoc, List.flatMap_map,
    List.map_cons, List.map_nil]

@[simp] theorem card_cube (q : Nat) : Fintype.card (Cube (Fin q)) = tapeCount q := by
  simpa using Fintype.card_congr (cubeEquiv q)

@[simp] theorem card_pairCube (q : Nat) :
    Fintype.card (Cube (Fin q × Fin q)) = pairTapeCount q := by
  simpa using Fintype.card_congr (pairCubeEquiv q)

@[simp] theorem card_localEvent (q : Nat) :
    Fintype.card (AlphabetGraph.LocalEvent (Fin q)) = localCount q := by
  simpa using Fintype.card_congr (localEventEquiv q)

@[simp] theorem card_event (m q : Nat) :
    Fintype.card (AlphabetGraph.Event (Fin m) (Fin q)) = eventCount m q := by
  simpa using Fintype.card_congr (eventEquiv m q)

@[simp] theorem card_address (n m q : Nat) :
    Fintype.card (AlphabetGraph.Address (Fin n) (Fin m) (Fin q)) = addressCount n m q := by
  simpa using Fintype.card_congr (addressEquiv n m q)

@[simp] theorem card_vertex (n m q : Nat) :
    Fintype.card (QueryIncidence.Vertex (AlphabetGraph.Event (Fin m) (Fin q))
      (AlphabetGraph.Address (Fin n) (Fin m) (Fin q))) = vertexCount n m q := by
  simpa using Fintype.card_congr (vertexEquiv n m q)

@[simp] theorem card_dart (m q : Nat) :
    Fintype.card (QueryIncidence.Dart (AlphabetGraph.Event (Fin m) (Fin q)) 6) =
      dartCount m q := by
  simpa using Fintype.card_congr (dartEquiv m q)

@[simp] theorem localCount_formula (q : Nat) :
    localCount q = 4 * (2 * 2 ^ q) * (2 ^ (q * q)) ^ 5 := rfl

end IndependentSetsGames.Foundations.PCP.AlphabetTable.Enumeration

end OAI
