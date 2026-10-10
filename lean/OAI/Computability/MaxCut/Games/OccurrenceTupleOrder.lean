import Mathlib
import OAI.Computability.MaxCut.Encoding.GameEncodingSize
import OAI.Computability.MaxCut.Machines.MachineTupleOdometer
import OAI.Computability.MaxCut.Games.AddressGame

namespace OAI

/-! Exact coordinate-order bridge from the checked tuple odometer to the
outer reduction's occurrence enumeration. The odometer changes coordinate zero
fastest; `ActualEnumeration.functions` changes it slowest. Reading saved digit
`j.rev` as query coordinate `j` matches the complete ordered list. No primitive
machine or assumed whole-loop runtime is introduced here. -/

namespace MaxCutGames.Reduction.OccurrenceTupleOrder

open Turing
open MaxCutGames.Foundations.Complexity
open MachineTupleOdometer

variable {α : Type*}

/-- Read the physical saved digit positions in reverse coordinate order. -/
def readCoordinates {m k : Nat} (digits : Fin k → Fin m) : Fin k → Fin m :=
  digits ∘ Fin.rev

@[simp] theorem readCoordinates_apply {m k : Nat} (digits : Fin k → Fin m) (j : Fin k) :
    readCoordinates digits j = digits j.rev := rfl

@[simp] theorem readCoordinates_involutive {m k : Nat} (digits : Fin k → Fin m) :
    readCoordinates (readCoordinates digits) = digits := by
  funext j
  simp only [readCoordinates_apply, Fin.rev_rev]

def coordinateEquiv (m k : Nat) : (Fin k → Fin m) ≃ (Fin k → Fin m) where
  toFun := readCoordinates
  invFun := readCoordinates
  left_inv := readCoordinates_involutive
  right_inv := readCoordinates_involutive

theorem readCoordinates_snoc {m k : Nat} (tail : Fin k → Fin m) (d : Fin m) :
    readCoordinates (Fin.snoc tail d) = Fin.cons d (readCoordinates tail) :=
  Fin.snoc_comp_rev d tail

/-- Exact equality of occurrence lists after reading saved digits in reverse
coordinate order. This includes dimension zero and radix zero. -/
theorem tupleOrder_readCoordinates (m k : Nat) :
    (MachineTupleOdometer.tupleOrder m k).map readCoordinates =
      ActualEnumeration.functions (List.finRange m) k := by
  induction k with
  | zero =>
    rw [MachineTupleOdometer.tupleOrder_dimension_zero]
    change [readCoordinates (fun i : Fin 0 => Fin.elim0 i)] = [Fin.elim0]
    congr 1
  | succ k ih =>
    have each (d : Fin m) :
        ((MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d)).map
          readCoordinates =
        (ActualEnumeration.functions (List.finRange m) k).map (Fin.cons d) := by
      calc
        _ = ((MachineTupleOdometer.tupleOrder m k).map readCoordinates).map (Fin.cons d) := by
          simp only [List.map_map, Function.comp_def, readCoordinates_snoc]
        _ = _ := by rw [ih]
    rw [MachineTupleOdometer.tupleOrder_snoc]
    change ((List.finRange m).flatMap (fun d =>
      (MachineTupleOdometer.tupleOrder m k).map (fun tail => Fin.snoc tail d))).map
      readCoordinates = _
    simp only [List.map_flatMap, each]
    simp only [ActualEnumeration.functions, Explicit.pairs, List.map_flatMap,
      List.map_map, Function.comp_def]

theorem functions_readCoordinates (m k : Nat) :
    (ActualEnumeration.functions (List.finRange m) k).map readCoordinates =
      MachineTupleOdometer.tupleOrder m k := by
  have h := congrArg (List.map readCoordinates) (tupleOrder_readCoordinates m k)
  simpa only [List.map_map, Function.comp_def, readCoordinates_involutive,
    List.map_id_fun', id_eq] using h.symm

/-- An arbitrary exact emitted list, including serialized edge bytes, inherits
the order identity. There is no permutation or counting-only replacement. -/
theorem functions_flatMap (m k : Nat) (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      (MachineTupleOdometer.tupleOrder m k).flatMap
        (fun digits => emit (readCoordinates digits)) := by
  rw [← tupleOrder_readCoordinates]
  exact List.flatMap_map readCoordinates emit _

variable {K Λ σ : Type} [DecidableEq K]
  {m k : Nat} {current remaining : Nat → K} {bodyLabel : Λ}
  {checkLabel resetLabel : Nat → Λ}
  {program : Λ → TM2.Stmt (MachineTupleOdometer.Alphabet (K := K)) Λ (σ × Option Bool)}
  {exitLabel : Λ} {start finish : MachineTupleOdometer.Configuration K Λ σ}

/-- Apply the coordinate readout to an existing actual odometer schedule.
Its visit-order theorem already follows from the real nested-cycle constructors. -/
theorem actualSchedule_order
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish) :
    tree.order.map readCoordinates = ActualEnumeration.functions (List.finRange m) k := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder, tupleOrder_readCoordinates]

theorem actualSchedule_flatMap
    (tree : MachineTupleOdometer.NestedCycle m current remaining bodyLabel
      checkLabel resetLabel program k exitLabel start finish)
    (emit : (Fin k → Fin m) → List α) :
    (ActualEnumeration.functions (List.finRange m) k).flatMap emit =
      tree.order.flatMap (fun digits => emit (readCoordinates digits)) := by
  rw [MachineTupleOdometer.NestedCycle.order_eq_tupleOrder]
  exact functions_flatMap m k emit

end MaxCutGames.Reduction.OccurrenceTupleOrder

namespace MaxCutGames.Integration.AddressTupleBudget

open Reduction Foundations.Complexity
open AddressTupleBody

variable {k s d noiseCount : Nat}

def radixBound (s d L : Nat) : Nat := L + (2^s + 2^d + 4)

def magnitude (k s d L : Nat) : Nat :=
  (L+1) + radixBound s d L + (radixBound s d L)^(1+9*k) +
    (1+9*k)*(radixBound s d L+1) + 1

noncomputable def magnitudePolynomial (k s d : Nat) : Polynomial Nat :=
  (Polynomial.X+1) + (Polynomial.X+Polynomial.C (2^s+2^d+4)) +
    (Polynomial.X+Polynomial.C (2^s+2^d+4))^(1+9*k) +
    Polynomial.C (1+9*k)*(Polynomial.X+Polynomial.C (2^s+2^d+4)+1) + 1

@[simp] theorem magnitudePolynomial_eval (k s d L : Nat) :
    (magnitudePolynomial k s d).eval L = magnitude k s d L := by
  simp only [magnitudePolynomial, magnitude, radixBound, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]

theorem source_counts_le (F : SourceEncoding.Input) :
    F.«variables»+F.equations.length ≤ (SourceEncoding.inputBits F).length := by
  rw [SourceEncoding.inputBits_length]
  omega

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.«variables» F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.«variables» F.equations.length s d)^(1+9*k) ≤ _
  unfold magnitude
  omega

theorem field_length_le_magnitude (k s d L : Nat) : L+1 ≤ magnitude k s d L := by
  unfold magnitude
  omega

theorem canonicalValues_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    AddressTupleLoaded.canonicalValues F tuple j slot ≤
      (SourceEncoding.inputBits F).length := by
  rw [canonicalValues_eq_actual]
  unfold CanonicalBodyTemplate.sourceFields CanonicalBodyTemplate.recordFields
  split_ifs with h
  · have hname := (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).isLt
    have hvars := SourceEncoding.inputBits_length_ge_variables F
    change _ < F.«variables» at hname
    change (ActualGame.names (source F) (tuple j) ⟨slot.val,h⟩).val ≤
      (SourceEncoding.inputBits F).length
    exact (Nat.le_of_lt hname).trans hvars
  · have hocc := (tuple j).isLt
    have hcount := SourceEncoding.inputBits_length_ge_equations F
    omega

theorem loaded_fields_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (i : Fin (4*k)) :
    ((loaded F tuple base) (MachineAddressEdge.addressSlots
      (Slots k s d noiseCount) (.field i))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have fields := AddressTupleLoaded.loaded_savedFields F tuple base ready.saved ready.fields
  have atField := congrFun fields i
  change loaded F tuple base (MachineAddressEdge.addressSlots
    (Slots k s d noiseCount) (.field i)) = _ at atField
  rw [atField]
  simp only [CanonicalBodyMachine.savedFields, encodeWord_length]
  exact (Nat.add_le_add_right (canonicalValues_le F tuple _ _) 1).trans
    (field_length_le_magnitude k s d _)

/-- These are the actual canonical words, not arbitrary interpreted templates. -/
theorem queryWords_lt_radix (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (w : Nat) (hw : w ∈ AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) :
    w < CanonicalAddress.base F.«variables» F.equations.length s d := by
  rw [canonicalValues_eq_actual, rhs_eq_actual] at hw
  erw [AddressOutcomeSpecs.bitVector_rhsBits] at hw
  erw [AddressByteSemantics.queryWords_actual (source F) (tuple,X)] at hw
  exact CanonicalAddress.bodyWords_lt_base _ w hw

theorem queryWords_encoded_length_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d) :
    (encodeWords (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))).length ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hwords := encodeWords_length_le
    (AddressByteSemantics.queryWords (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple)))
    (radixBound s d (SourceEncoding.inputBits F).length)
    (fun w hw => (Nat.le_of_lt (queryWords_lt_radix F tuple X w hw)).trans (radix_le F s d))
  rw [AddressByteSemantics.queryWords_length] at hwords
  unfold magnitude
  omega

theorem queryWords_digits_le_magnitude (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (X : ActualGame.Map k s d)
    (i : Nat) (hi : i < 1+9*k) :
    MachineTemplateAddress.digits (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))) i ≤
        magnitude k s d (SourceEncoding.inputBits F).length := by
  have hi' : i < (AddressByteSemantics.queryWords
      (AddressTupleLoaded.canonicalValues F tuple) X
      (AddressOutcomeSpecs.bitVector (rhs F tuple))).length := by
    simpa only [AddressByteSemantics.queryWords_length] using hi
  simp only [MachineTemplateAddress.digits, List.getElem?_eq_getElem hi', Option.getD_some]
  exact (Nat.le_of_lt (queryWords_lt_radix F tuple X _ (List.getElem_mem hi'))).trans
    (radix_le_magnitude F k s d)

theorem selected_values_bound (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d) :
    ∀ row ∈ MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple),
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (encodeWords (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right).length ≤
          magnitude k s d (SourceEncoding.inputBits F).length ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).left i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) ∧
      (∀ i, i < 1+9*k → MachineTemplateAddress.digits (AddressOutcomeSpecs.values
        (AddressTupleLoaded.canonicalValues F tuple) row).right i ≤
          magnitude k s d (SourceEncoding.inputBits F).length) := by
  rw [AddressOutcomeSpecs.selected_rows]
  intro row member
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp member
  simp only [AddressOutcomeSpecs.values_row_left, AddressOutcomeSpecs.values_row_right]
  exact ⟨queryWords_encoded_length_le_magnitude F tuple p.1,
    queryWords_encoded_length_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p),
    queryWords_digits_le_magnitude F tuple p.1,
    queryWords_digits_le_magnitude F tuple (AddressOutcomeSpecs.rightMap T p)⟩

/-- Both canonical templates have exactly the same fixed token count. -/
noncomputable def rowPolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  Polynomial.C (2^((2*k+1)*(s+d+1))*T.vectors.length) *
    MachineAddressEdge.timePolynomial (1+9*k) (1+9*k) (1+9*k) + 1

private theorem eval_sum_constant_inline_AddressTupleBudget {α : Type} (items : List α) (p : Polynomial Nat) (M : Nat) :
    ((items.map (fun _ => p)).sum).eval M = items.length*p.eval M := by
  induction items with
  | nil => simp
  | cons item items ih =>
    simp only [List.map_cons, List.sum_cons, Polynomial.eval_add, List.length_cons,
      Nat.add_mul, Nat.one_mul, ih]
    omega

theorem selected_polynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d)
    (b : Fin k → Bool) (M : Nat) :
    (MachineOutcomeRows.timePolynomial
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) b)).eval M =
        (rowPolynomial k T).eval M := by
  simp only [MachineOutcomeRows.timePolynomial, AddressOutcomeSpecs.selected_rows,
    List.map_map, Function.comp_def, AddressOutcomeSpecs.row_left_length,
    AddressOutcomeSpecs.row_right_length, Polynomial.eval_add, Polynomial.eval_one,
    eval_sum_constant_inline_AddressTupleBudget, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
      (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
      (loaded F tuple base)).sum+1 ≤
        (rowPolynomial k T).eval (magnitude k s d (SourceEncoding.inputBits F).length) := by
  have h := MachineOutcomeRows.phaseCost_le_timePolynomial (Slots k s d noiseCount)
    (MachineOutcomeRows.selected (AddressOutcomeSpecs.rows k T) (rhs F tuple))
    (loaded F tuple base) _ _
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple))
    (magnitude k s d (SourceEncoding.inputBits F).length)
    (AddressTupleLoaded.loaded_clean F tuple base clean)
    (loaded_fields_le_magnitude F tuple base ready)
    (radix_le_magnitude F k s d) (capacity_le_magnitude F k s d)
    (selected_values_bound F tuple T)
  simpa only [selected_polynomial_eval] using h

theorem physicalField_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (j : Fin k) (slot : Fin 4) :
    ((SourceEncoding.equationWords F.equations[(tuple j).val])[slot.val]'(by simp)) ≤
      (SourceEncoding.inputBits F).length := by
  have hv := SourceEncoding.inputBits_length_ge_variables F
  have hl := SourceEncoding.inputBits_length F
  have h₁ := F.equations[(tuple j).val].first.isLt
  have h₂ := F.equations[(tuple j).val].second.isLt
  have h₃ := F.equations[(tuple j).val].third.isLt
  fin_cases slot <;>
    simp only [SourceEncoding.equationWords, List.getElem_cons_zero,
      List.getElem_cons_succ] <;> (try split_ifs) <;> omega

private theorem lengthSum_le_of_mem_inline_AddressTupleBudget {K : Type} [DecidableEq K]
    (chosen : List K) (base : K → List Bool) (M : Nat)
    (bounded : ∀ tape ∈ chosen, (base tape).length ≤ M) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length*M := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons tape chosen ih =>
    have first := bounded tape (by simp)
    have rest := ih (fun t ht => bounded t (List.mem_cons_of_mem tape ht))
    simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
      List.length_cons, Nat.add_mul, Nat.one_mul] at *
    omega

/-- Cleanup sees only the four loaded fields per position; output is not scanned. -/
theorem cleanup_budget_le (rows : Rows k) (B C : Nat)
    (values : MachineOutcomeRows.Spec (4*k) (1+9*k) → MachineOutcomeRows.Values (1+9*k))
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base) :
    AddressTupleCleanup.budget k s d noiseCount (emitted rows B C values F tuple base) ≤
      4*k*((SourceEncoding.inputBits F).length+2) := by
  have h := lengthSum_le_of_mem_inline_AddressTupleBudget (AddressTupleCleanup.loadedFields k s d noiseCount)
    (emitted rows B C values F tuple base) ((SourceEncoding.inputBits F).length+1) (by
      intro tape member
      obtain ⟨j, slot, rfl⟩ :=
        (AddressTupleCleanup.mem_loadedFields k s d noiseCount tape).mp member
      rw [emitted, MachineAddressEdge.appended_other]
      · rw [loaded, AddressTupleLoaded.loaded_field F tuple base ready.fields, encodeWord_length]
        exact Nat.add_le_add_right (physicalField_le F tuple j slot) 1
      · rw [AddressMachineSpace.addressSlots_output]
        simp [AddressMachineSpace.headerTape])
  rw [AddressTupleCleanup.loadedFields_length] at h
  change MachineDrainMany.lengthSum _ _ + 4*k ≤ _
  calc
    _ ≤ 4*k*((SourceEncoding.inputBits F).length+1)+4*k := Nat.add_le_add_right h _
    _ = 4*k*((SourceEncoding.inputBits F).length+2) := by ring

/-- Fixed program dimensions determine this explicit polynomial in input bits. -/
noncomputable def timePolynomial (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) :
    Polynomial Nat :=
  (Polynomial.C k*(Polynomial.C 10*Polynomial.X+Polynomial.C 20)+1)+1+
    (rowPolynomial k T).comp (magnitudePolynomial k s d)+
    Polynomial.C (4*k)*(Polynomial.X+Polynomial.C 2)+1

theorem timePolynomial_eval (k : Nat) {s d : Nat} (T : NoiseTables.Table s d) (L : Nat) :
    (timePolynomial k T).eval L =
      (k*(10*L+20)+1)+1+(rowPolynomial k T).eval (magnitude k s d L)+4*k*(L+2)+1 := by
  simp only [timePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one, Polynomial.eval_comp, magnitudePolynomial_eval]

/-- Uniform bound for the actual tuple body, with all canonical values instantiated. -/
theorem budget_le_timePolynomial (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    AddressTupleBody.budget (AddressOutcomeSpecs.rows k T)
      (CanonicalAddress.base F.«variables» F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.«variables» F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end MaxCutGames.Integration.AddressTupleBudget

namespace MaxCutGames.Integration.AddressTuplePolynomial

open Turing Reduction Foundations.Complexity
open AddressTupleBody AddressMachineSpace

variable {k s d noiseCount : Nat} {Λ : Type}

noncomputable def run_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    StateTransition.EvalsToInTime (TM2.step P)
      ⟨some (labels (main (AddressOutcomeSpecs.rows k T))), (((oldRhs, ()), ()), none), base⟩
      (some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
        base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩)
      ((AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length) := by
  have actual := AddressTupleBody.run_actual T labels exit P atLabels F tuple base
    ready clean oldRhs hB hC
  exact {
    steps := actual.steps
    evals_in_steps := actual.evals_in_steps
    steps_le_m := actual.steps_le_m.trans
      (AddressTupleBudget.budget_le_timePolynomial F tuple T base ready clean)
  }

/-- The explicit iterated transition trace and its uniform bound, for callers
that compose traces directly instead of runtime-witness structures. -/
theorem trace_actual (T : NoiseTables.Table s d)
    (labels : AddressTupleBody.Label k s d noiseCount (AddressOutcomeSpecs.rows k T) → Λ)
    (exit : Option Λ)
    (P : Λ → TM2.Stmt (fun _ : AddressTupleBody.Arena k s d noiseCount => Bool) Λ (BodyState k))
    (atLabels : ∀ l, P (labels l) = instruction (AddressOutcomeSpecs.rows k T) labels exit l)
    (F : SourceEncoding.Input) (tuple : Fin k → Fin F.equations.length)
    (base : AddressTupleBody.Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base)
    (oldRhs : Fin k → Bool)
    (hB : base (headerTape k s d noiseCount .baseValue) =
      encodeWord (CanonicalAddress.base F.«variables» F.equations.length s d))
    (hC : base (headerTape k s d noiseCount .capacity) =
      encodeWord (AddressGame.bodyCapacity (source F) k s d)) :
    ∃ steps ≤ (AddressTupleBudget.timePolynomial k T).eval (SourceEncoding.inputBits F).length,
      (MachineComposition.advance (TM2.step P))^[steps]
        (some ⟨some (labels (main (AddressOutcomeSpecs.rows k T))),
          (((oldRhs, ()), ()), none), base⟩) =
        some ⟨exit, initialState k, MachineAddressEdge.appended (Slots k s d noiseCount)
          base (AddressOutcomeSpecs.tupleBits (source F) k T tuple)⟩ := by
  have actual := run_actual T labels exit P atLabels F tuple base ready clean oldRhs hB hC
  exact ⟨actual.steps, actual.steps_le_m, actual.evals_in_steps⟩

end MaxCutGames.Integration.AddressTuplePolynomial

/-!
# Polynomial encoded length of the actual output

The encoder uses a unary, delimited forward-permutation
format. The instance is the actual list-based reduction, including canonical
body deduplication and every repeated edge occurrence. The polynomial's
coefficients depend only on the fixed gadget table and tuple dimensions.

These are output-length theorems. They do not assert a machine running-time
certificate for canonicalization, enumeration, or serialization.
-/

namespace MaxCutGames.Reduction.OutputSize

open ActualSource
open MaxCutGames.Integration
open MaxCutGames.Foundations

variable {n s d : Nat}

theorem explicitBodies_length_le (S : Source) (k s d : Nat) :
    (ActualGame.explicitBodies S k s d).length ≤
      S.occurrences ^ k * 2 ^ ((s + d) * (2 * k + 1)) := by
  let := ActualGame.orbitBodyDecidableEq S k s d
  exact (Encoding.imageVertices_length_le
    (ActualEnumeration.queries S.occurrences k s d)
    (ActualOrbit.body (ActualGame.canonical S k s d))).trans_eq
      (ActualEnumeration.length_queries S.occurrences k s d)

def vertexCoefficient (k s d : Nat) : Nat :=
  2 * CloneGap.distinctTriples.length ^ k * 2 ^ ((s + d) * (2 * k + 1))

def edgeCoefficient (k : Nat) (T : NoiseTables.Table s d) : Nat :=
  CloneGap.distinctTriples.length ^ k *
    2 ^ ((2 * k + 1) * (s + d + 1)) * T.vectors.length

private theorem collect_vertex_coefficient_inline_OutputSize (m D k b : Nat) :
    2 * ((m * D) ^ k * b) = (2 * D ^ k * b) * m ^ k := by
  rw [Nat.mul_pow]
  ac_rfl

private theorem collect_edge_coefficient_inline_OutputSize (m D k b p : Nat) :
    (m * D) ^ k * b * p = (D ^ k * b * p) * m ^ k := by
  rw [Nat.mul_pow]
  ac_rfl

theorem output_vertices_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (UniformReduction.output es hne k T).vertices ≤
      vertexCoefficient k s d * es.length ^ k := by
  rw [UniformReduction.output_vertex_count]
  have h := Nat.mul_le_mul_left 2
    (explicitBodies_length_le (UniformReduction.source es hne) k s d)
  calc
    _ ≤ 2 * ((UniformReduction.source es hne).occurrences ^ k *
        2 ^ ((s + d) * (2 * k + 1))) := h
    _ = 2 * ((es.length * CloneGap.distinctTriples.length) ^ k *
        2 ^ ((s + d) * (2 * k + 1))) := by rw [UniformReduction.source_occurrences]
    _ = _ := collect_vertex_coefficient_inline_OutputSize _ _ _ _

theorem output_constraints_eq (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (UniformReduction.output es hne k T).constraints.length =
      edgeCoefficient k T * es.length ^ k := by
  rw [UniformReduction.output_constraint_count]
  exact collect_edge_coefficient_inline_OutputSize _ _ _ _ _

def sizeBound (vertexCoeff edgeCoeff alphabet tupleLength inputLength : Nat) : Nat :=
  vertexCoeff * inputLength ^ tupleLength + alphabet +
    edgeCoeff * inputLength ^ tupleLength + 3 +
      edgeCoeff * inputLength ^ tupleLength *
        (2 * (vertexCoeff * inputLength ^ tupleLength) + alphabet * (alphabet + 1))

theorem sizeBound_mono (vertexCoeff edgeCoeff alphabet tupleLength : Nat)
    {a b : Nat} (hab : a ≤ b) :
    sizeBound vertexCoeff edgeCoeff alphabet tupleLength a ≤
      sizeBound vertexCoeff edgeCoeff alphabet tupleLength b := by
  have hp := Nat.pow_le_pow_left hab tupleLength
  have hv := Nat.mul_le_mul_left vertexCoeff hp
  have he := Nat.mul_le_mul_left edgeCoeff hp
  unfold sizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hv alphabet) he) 3)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

theorem output_bits_length_le (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (UniformReduction.output es hne k T)).length ≤
      sizeBound (vertexCoefficient k s d) (edgeCoefficient k T) (2 ^ s) k es.length := by
  have h := GameEncodingSize.gameBits_length_le (UniformReduction.output es hne k T)
  have hv := output_vertices_le es hne k T
  rw [output_constraints_eq] at h
  apply h.trans
  unfold sizeBound
  exact Nat.add_le_add
    (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right hv _) _) 3)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

/-- An explicit polynomial for the actual serialized game. -/
noncomputable def outputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C (vertexCoefficient k s d) * Polynomial.X ^ k
  let E := Polynomial.C (edgeCoefficient k T) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem outputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (m : Nat) :
    (outputPolynomial k T).eval m =
      sizeBound (vertexCoefficient k s d) (edgeCoefficient k T) (2 ^ s) k m := by
  simp [outputPolynomial, sizeBound]

theorem output_bits_polynomial_in_occurrences
    (es : List (CloneGap.Equation (Fin n))) (hne : es ≠ [])
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (UniformReduction.output es hne k T)).length ≤
      (outputPolynomial k T).eval es.length := by
  rw [outputPolynomial_eval]
  exact output_bits_length_le es hne k T

theorem output_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (UniformReduction.output input.equations input.nonempty k T)).length ≤
        (outputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [outputPolynomial_eval]
  exact (output_bits_length_le input.equations input.nonempty k T).trans
    (sizeBound_mono _ _ _ _ (SourceEncoding.inputBits_length_ge_equations input))

/-- Fixed reduction parameters give one polynomial for every encoded input. -/
theorem fixed_parameters_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits
        (UniformReduction.output input.equations input.nonempty k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨outputPolynomial k T, fun input => output_bits_polynomial_in_input input k T⟩

end MaxCutGames.Reduction.OutputSize

namespace MaxCutGames.Reduction.AddressOutputSize

open ActualSource
open MaxCutGames.Integration
open MaxCutGames.Foundations

variable {s d : Nat}

def vertexBound (k s d inputLength : Nat) : Nat :=
  2 * ((48 + CloneGap.distinctTriples.length) * inputLength +
    2 ^ s + 2 ^ d + 4) ^ (1 + 9 * k)

def edgeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  OutputSize.edgeCoefficient k T * inputLength ^ k

def bitsBound (vertices edges alphabet : Nat) : Nat :=
  vertices + alphabet + edges + 3 +
    edges * (2 * vertices + alphabet * (alphabet + 1))

theorem bitsBound_mono {vertices vertices' edges edges' alphabet : Nat}
    (hv : vertices ≤ vertices') (he : edges ≤ edges') :
    bitsBound vertices edges alphabet ≤ bitsBound vertices' edges' alphabet := by
  unfold bitsBound
  exact Nat.add_le_add
    (Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_right hv alphabet) he) 3)
    (Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hv) _))

def sizeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  bitsBound (vertexBound k s d inputLength) (edgeBound k T inputLength) (2 ^ s)

theorem table_constraints_eq (S : Source) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput S k T).constraints.length =
      Explicit.edgeCount S.occurrences k (s + d) T.vectors.length := by
  unfold AddressGame.tableOutput
  erw [AddressGame.outputInstance_length]
  simp only [TableReduction.tableEnumeration]
  erw [List.length_finRange]

private theorem scaled_sum_le_inline_AddressOutputSize {n m N : Nat} (a b : Nat) (hn : n ≤ N) (hm : m ≤ N) :
    n * a + m * b ≤ (a + b) * N := by
  calc
    _ ≤ N * a + N * b :=
      Nat.add_le_add (Nat.mul_le_mul_right a hn) (Nat.mul_le_mul_right b hm)
    _ = _ := by rw [Nat.add_mul]; ac_rfl

theorem output_constraints_eq {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (UniformReduction.source es hne) k T).constraints.length =
      edgeBound k T es.length := by
  rw [table_constraints_eq, UniformReduction.source_occurrences]
  unfold Explicit.edgeCount edgeBound OutputSize.edgeCoefficient
  rw [Nat.mul_pow]
  ring

theorem output_vertices_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T).vertices ≤
        vertexBound k s d (SourceEncoding.inputBits input).length := by
  have hn := SourceEncoding.inputBits_length_ge_variables input
  have hm := SourceEncoding.inputBits_length_ge_equations input
  have hsum := scaled_sum_le_inline_AddressOutputSize 48 CloneGap.distinctTriples.length hn hm
  change 2 * (CanonicalAddress.base
    (UniformReduction.source input.equations input.nonempty).«variables»
    (UniformReduction.source input.equations input.nonempty).occurrences s d) ^
      (1 + 9 * k) ≤ _
  rw [CanonicalAddress.base_eq, UniformReduction.source_variables,
    UniformReduction.source_occurrences]
  unfold vertexBound
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _) _

theorem output_constraints_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T).constraints.length ≤
        edgeBound k T (SourceEncoding.inputBits input).length := by
  rw [output_constraints_eq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (SourceEncoding.inputBits_length_ge_equations input) k)

theorem output_bits_length_le (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T)).length ≤
        sizeBound k T (SourceEncoding.inputBits input).length := by
  exact (GameEncodingSize.gameBits_length_le _).trans
    (bitsBound_mono (output_vertices_le_input input k T)
      (output_constraints_le_input input k T))

/-- One fixed polynomial includes every declared address and every edge table. -/
noncomputable def outputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C 2 *
    (Polynomial.C (48 + CloneGap.distinctTriples.length) * Polynomial.X +
      Polynomial.C (2 ^ s) + Polynomial.C (2 ^ d) + Polynomial.C 4) ^ (1 + 9 * k)
  let E := Polynomial.C (OutputSize.edgeCoefficient k T) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem outputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) :
    (outputPolynomial k T).eval inputLength = sizeBound k T inputLength := by
  simp only [outputPolynomial, sizeBound, bitsBound, vertexBound, edgeBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

theorem output_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits (AddressGame.tableOutput
      (UniformReduction.source input.equations input.nonempty) k T)).length ≤
        (outputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [outputPolynomial_eval]
  exact output_bits_length_le input k T

theorem fixed_parameters_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits (AddressGame.tableOutput
        (UniformReduction.source input.equations input.nonempty) k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨outputPolynomial k T, fun input => output_bits_polynomial_in_input input k T⟩

def directVertexBound (k s d inputLength : Nat) : Nat :=
  2 * (inputLength + 2 ^ s + 2 ^ d + 4) ^ (1 + 9 * k)

def directEdgeCoefficient (k s d noiseCount : Nat) : Nat :=
  2 ^ ((2 * k + 1) * (s + d + 1)) * noiseCount

def directSizeBound (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) : Nat :=
  bitsBound (directVertexBound k s d inputLength)
    (directEdgeCoefficient k s d T.vectors.length * inputLength ^ k) (2 ^ s)

theorem direct_vertices_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).vertices ≤
      directVertexBound k s d (SourceEncoding.inputBits input).length := by
  have hsum : input.«variables» + input.equations.length ≤
      (SourceEncoding.inputBits input).length := by
    rw [SourceEncoding.inputBits_length]
    omega
  change 2 * (CanonicalAddress.base input.«variables» input.equations.length s d) ^
    (1 + 9 * k) ≤ _
  rw [CanonicalAddress.base_eq]
  unfold directVertexBound
  apply Nat.mul_le_mul_left 2
  apply Nat.pow_le_pow_left
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hsum _) _) _

theorem direct_constraints_eq (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).constraints.length =
      directEdgeCoefficient k s d T.vectors.length * input.equations.length ^ k := by
  rw [table_constraints_eq]
  unfold Explicit.edgeCount directEdgeCoefficient Source.ofList
  ac_rfl

theorem direct_constraints_le_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T).constraints.length ≤
      directEdgeCoefficient k s d T.vectors.length * (SourceEncoding.inputBits input).length ^ k := by
  rw [direct_constraints_eq]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (SourceEncoding.inputBits_length_ge_equations input) k)

theorem direct_bits_length_le (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
        directSizeBound k T (SourceEncoding.inputBits input).length :=
  (GameEncodingSize.gameBits_length_le _).trans
    (bitsBound_mono (direct_vertices_le_input input k T)
      (direct_constraints_le_input input k T))

noncomputable def directOutputPolynomial (k : Nat) (T : NoiseTables.Table s d) : Polynomial Nat :=
  let V := Polynomial.C 2 * (Polynomial.X + Polynomial.C (2 ^ s) +
    Polynomial.C (2 ^ d) + Polynomial.C 4) ^ (1 + 9 * k)
  let E := Polynomial.C (directEdgeCoefficient k s d T.vectors.length) * Polynomial.X ^ k
  V + Polynomial.C (2 ^ s) + E + Polynomial.C 3 +
    E * (Polynomial.C 2 * V + Polynomial.C ((2 ^ s) * (2 ^ s + 1)))

theorem directOutputPolynomial_eval (k : Nat) (T : NoiseTables.Table s d) (inputLength : Nat) :
    (directOutputPolynomial k T).eval inputLength = directSizeBound k T inputLength := by
  simp only [directOutputPolynomial, directSizeBound, bitsBound, directVertexBound,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_C, Polynomial.eval_X]

theorem direct_bits_polynomial_in_input (input : SourceEncoding.Input)
    (k : Nat) (T : NoiseTables.Table s d) :
    (Complexity.gameBits
      (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
        (directOutputPolynomial k T).eval (SourceEncoding.inputBits input).length := by
  rw [directOutputPolynomial_eval]
  exact direct_bits_length_le input k T

theorem fixed_parameters_direct_output_size (k : Nat) (T : NoiseTables.Table s d) :
    ∃ p : Polynomial Nat, ∀ input : SourceEncoding.Input,
      (Complexity.gameBits
        (AddressGame.tableOutput (Source.ofList input.equations input.nonempty) k T)).length ≤
          p.eval (SourceEncoding.inputBits input).length :=
  ⟨directOutputPolynomial k T, fun input => direct_bits_polynomial_in_input input k T⟩

end MaxCutGames.Reduction.AddressOutputSize

end OAI
