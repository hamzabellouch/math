import OAI.Computability.UniqueGames.Machines.MachineCompositionLemmas
import OAI.Computability.UniqueGames.Reduction.AddressTupleBody

namespace OAI


namespace UniqueGamesTheorem.Integration.AddressTupleBudget

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
    F.variables+F.equations.length ≤ (SourceEncoding.inputBits F).length := by
  rw [SourceEncoding.inputBits_length]
  omega

theorem radix_le (F : SourceEncoding.Input) (s d : Nat) :
    CanonicalAddress.base F.variables F.equations.length s d ≤
      radixBound s d (SourceEncoding.inputBits F).length := by
  have h := source_counts_le F
  simp only [CanonicalAddress.base_eq, radixBound]
  omega

theorem radix_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    CanonicalAddress.base F.variables F.equations.length s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := radix_le F s d
  unfold magnitude
  omega

theorem capacity_le_magnitude (F : SourceEncoding.Input) (k s d : Nat) :
    AddressGame.bodyCapacity (source F) k s d ≤
      magnitude k s d (SourceEncoding.inputBits F).length := by
  have h := Nat.pow_le_pow_left (radix_le F s d) (1+9*k)
  change (CanonicalAddress.base F.variables F.equations.length s d)^(1+9*k) ≤ _
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
    change _ < F.variables at hname
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
    w < CanonicalAddress.base F.variables F.equations.length s d := by
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

private theorem eval_sum_constant {α : Type} (items : List α) (p : Polynomial Nat) (M : Nat) :
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
    eval_sum_constant, FixedOutcomes.tableParams_length, rowPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]

theorem rows_budget_le (F : SourceEncoding.Input)
    (tuple : Fin k → Fin F.equations.length) (T : NoiseTables.Table s d)
    (base : Arena k s d noiseCount → List Bool) (ready : Ready F tuple base)
    (clean : MachineAddressEdge.Clean (Slots k s d noiseCount) base) :
    (MachineOutcomeRows.rowCosts (Slots k s d noiseCount)
      (CanonicalAddress.base F.variables F.equations.length s d)
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

private theorem lengthSum_le_of_mem {K : Type} [DecidableEq K]
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
  have h := lengthSum_le_of_mem (AddressTupleCleanup.loadedFields k s d noiseCount)
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
      (CanonicalAddress.base F.variables F.equations.length s d)
      (AddressGame.bodyCapacity (source F) k s d)
      (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ≤
        (timePolynomial k T).eval (SourceEncoding.inputBits F).length := by
  have rowsBound := rows_budget_le F tuple T base ready clean
  have cleanupBound := cleanup_budget_le (AddressOutcomeSpecs.rows k T)
    (CanonicalAddress.base F.variables F.equations.length s d)
    (AddressGame.bodyCapacity (source F) k s d)
    (AddressOutcomeSpecs.values (AddressTupleLoaded.canonicalValues F tuple)) F tuple base ready
  rw [AddressTupleBody.budget, timePolynomial_eval]
  omega

end UniqueGamesTheorem.Integration.AddressTupleBudget

end OAI
