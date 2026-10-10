import Mathlib
import OAI.Computability.DirectedFeedback.Machines.PoweringRuntimeBudget
import OAI.Computability.DirectedFeedback.Machines.FinalCNFTime

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section

section

namespace DFVSGames.Reduction.FiniteSource

open CloneGap

variable {α β : Type} {n : Nat}

abbrev Name (s : ActualSource.Source) := Fin s.«variables» × Fin 48

def clonedSource (s : ActualSource.Source) := cloneList s.sourceList

abbrev Occurrence (s : ActualSource.Source) := Fin (clonedSource s).length

def occurrences (s : ActualSource.Source) : List (Occurrence s) :=
  List.finRange (clonedSource s).length

def rawEquation (s : ActualSource.Source) (i : Occurrence s) : Equation (Fin s.«variables» × Nat) :=
  (clonedSource s)[i.val]

def finiteName (s : ActualSource.Source) (v : Fin s.«variables» × Nat) : Name s :=
  (v.1, ⟨v.2 % 48, Nat.mod_lt _ (by decide)⟩)

def mapEquation (f : α → β) (e : Equation α) : Equation β :=
  ⟨f e.first, f e.second, f e.third, e.rhs⟩

def equation (s : ActualSource.Source) (i : Occurrence s) : Equation (Name s) :=
  mapEquation (finiteName s) (rawEquation s i)

theorem satisfied_map (f : α → β) (e : Equation α) (g : β → Bool) :
    satisfied (mapEquation f e) g = satisfied e (g ∘ f) := rfl

theorem mem_cart {xs : List α} {ys : List β} {z : α × β} :
    z ∈ cart xs ys ↔ z.1 ∈ xs ∧ z.2 ∈ ys := by
  simp only [cart, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    cases h
    exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨z.1, hx, z.2, hy, rfl⟩

theorem distinctTriple_bounds {t : Nat × Nat × Nat} (h : t ∈ distinctTriples) :
    t.1 < 48 ∧ t.2.1 < 48 ∧ t.2.2 < 48 := by
  have h := (List.mem_filter.mp h).1
  change t ∈ cart indices (cart indices indices) at h
  rw [mem_cart, mem_cart] at h
  simpa [indices] using h

theorem distinctTriples_nonempty : 0 < distinctTriples.length := by
  have hm : (0, 1, 2) ∈ distinctTriples := by
    simp [distinctTriples, triples, mem_cart, indices, collision]
  exact List.length_pos_iff_exists_mem.mpr ⟨_, hm⟩

theorem cloned_member_properties {source : List (Equation (Fin n))}
    {e : Equation (Fin n × Nat)} (h : e ∈ cloneList source) :
    (e.first.2 < 48 ∧ e.second.2 < 48 ∧ e.third.2 < 48) ∧
    (e.first ≠ e.second ∧ e.first ≠ e.third ∧ e.second ≠ e.third) := by
  obtain ⟨old, _, h⟩ := List.mem_flatMap.mp h
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp h
  have hb := distinctTriple_bounds ht
  have hc : collision t = false := by
    simpa using (List.mem_filter.mp ht).2
  exact ⟨hb, clone_names_distinct old t hc⟩

theorem raw_properties (s : ActualSource.Source) (i : Occurrence s) :
    ((rawEquation s i).first.2 < 48 ∧ (rawEquation s i).second.2 < 48 ∧
      (rawEquation s i).third.2 < 48) ∧
    ((rawEquation s i).first ≠ (rawEquation s i).second ∧
      (rawEquation s i).first ≠ (rawEquation s i).third ∧
      (rawEquation s i).second ≠ (rawEquation s i).third) := by
  apply cloned_member_properties
  exact List.getElem_mem i.isLt

theorem finiteName_injective_on (s : ActualSource.Source)
    {u v : Fin s.«variables» × Nat} (hu : u.2 < 48) (hv : v.2 < 48)
    (h : finiteName s u = finiteName s v) : u = v := by
  have he := congrArg (fun z : Name s => (z.1, z.2.val)) h
  simpa [finiteName, Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hv] using he

theorem names_distinct (s : ActualSource.Source) (i : Occurrence s) :
    (equation s i).first ≠ (equation s i).second ∧
    (equation s i).first ≠ (equation s i).third ∧
    (equation s i).second ≠ (equation s i).third := by
  obtain ⟨⟨h₁, h₂, h₃⟩, ⟨h₁₂, h₁₃, h₂₃⟩⟩ := raw_properties s i
  exact ⟨fun h => h₁₂ (finiteName_injective_on s h₁ h₂ h),
    fun h => h₁₃ (finiteName_injective_on s h₁ h₃ h),
    fun h => h₂₃ (finiteName_injective_on s h₂ h₃ h)⟩

theorem raw_map_occurrences (s : ActualSource.Source) :
    (occurrences s).map (rawEquation s) = clonedSource s := by
  simp [occurrences, List.finRange, List.map_ofFn, rawEquation, Function.comp_def]

theorem occurrences_length (s : ActualSource.Source) :
    (occurrences s).length = (clonedSource s).length := by
  simp [occurrences]

theorem clonedSource_nonempty (s : ActualSource.Source) : 0 < (clonedSource s).length := by
  rw [clonedSource, length_cloneList]
  have hs : 0 < s.sourceList.length := by
    simpa [ActualSource.Source.sourceList] using s.nonempty
  exact Nat.mul_pos hs distinctTriples_nonempty

instance (s : ActualSource.Source) : Nonempty (Occurrence s) :=
  ⟨⟨0, clonedSource_nonempty s⟩⟩

theorem indexed_failure_count (s : ActualSource.Source) (g : Name s → Bool) :
    (occurrences s).countP (fun i => !satisfied (equation s i) g) =
      (clonedSource s).countP (fun e => !satisfied e (g ∘ finiteName s)) := by
  have h := congrArg (fun es => es.countP
    (fun e => !satisfied e (g ∘ finiteName s))) (raw_map_occurrences s)
  simpa only [List.countP_map, Function.comp_def, equation, satisfied_map] using h

theorem indexed_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * (occurrences s).countP (fun i => !satisfied (equation s i) g) := by
  rw [occurrences_length, indexed_failure_count]
  exact clone_gap s.sourceList source_gap (g ∘ finiteName s)

theorem indexed_completeness_count (s : ActualSource.Source) (A : Fin s.«variables» → Bool) :
    (occurrences s).countP (fun i => satisfied (equation s i) (fun z => A z.1)) =
      s.sourceList.countP (fun e => satisfied e A) * distinctTriples.length := by
  have h := congrArg (fun es => es.countP
    (fun e => satisfied e (fun z => A z.1))) (raw_map_occurrences s)
  simp only [List.countP_map, Function.comp_def] at h
  change (occurrences s).countP
    (fun i => satisfied (rawEquation s i) (fun z => A z.1)) = _
  rw [h]
  exact clone_completeness_count s.sourceList A

def incidenceEquation (s : ActualSource.Source) (i : Occurrence s) :
    Incidence.Equation (Name s) := SourceIncidence.toIncidence (equation s i)

theorem incidence_question_predicate (s : ActualSource.Source) (i : Occurrence s)
    (alice : Incidence.Triple) (bob : Bool) (slot : Incidence.Slot) :
    Incidence.questionPredicate (incidenceEquation s i)
      (Incidence.nameAt (incidenceEquation s i) slot) alice bob ↔
      Incidence.parity alice = (incidenceEquation s i).rhs ∧
        Incidence.bitAt alice slot = bob := by
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := names_distinct s i
  exact Incidence.question_predicate_at_slot _ h₁₂ h₁₃ h₂₃ alice bob slot

theorem incidence_failure_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) :
    (occurrences s).length ≤
      64 * Incidence.failureCount (incidenceEquation s) g (occurrences s) := by
  unfold incidenceEquation
  rw [SourceIncidence.failureCount_eq]
  exact indexed_gap s source_gap g

theorem incidence_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (g : Name s → Bool) (alice : Occurrence s → Incidence.Triple) :
    64 * Incidence.acceptedCount (incidenceEquation s) g alice (occurrences s) ≤
      191 * (occurrences s).length :=
  Incidence.soundness_191_over_192 _ g alice _ (incidence_failure_gap s source_gap g)

def nameEquiv (s : ActualSource.Source) : Name s ≃ Fin (s.«variables» * 48) :=
  finProdFinEquiv

def cloned (s : ActualSource.Source) : ActualSource.Source where
  «variables» := s.«variables» * 48
  occurrences := (clonedSource s).length
  nonempty := clonedSource_nonempty s
  equation i := mapEquation (nameEquiv s) (equation s i)

theorem cloned_length (s : ActualSource.Source) :
    (cloned s).occurrences = s.occurrences * distinctTriples.length := by
  change (cloneList s.sourceList).length = _
  rw [length_cloneList, ActualSource.Source.sourceList_length]

theorem cloned_distinct (s : ActualSource.Source) : (cloned s).DistinctNames := by
  intro i
  obtain ⟨h₁₂, h₁₃, h₂₃⟩ := names_distinct s i
  exact ⟨fun h => h₁₂ ((nameEquiv s).injective h),
    fun h => h₁₃ ((nameEquiv s).injective h),
    fun h => h₂₃ ((nameEquiv s).injective h)⟩

theorem count_ofFn (f : Fin n → α) (p : α → Bool) :
    (List.ofFn f).countP p = (List.finRange n).countP (fun i => p (f i)) := by
  have he : (List.finRange n).map f = List.ofFn f := by
    simp [List.finRange, List.map_ofFn, Function.comp_def]
  have h := congrArg (fun es => es.countP p) he
  simpa only [List.countP_map, Function.comp_def] using h.symm

theorem cloned_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !satisfied e A))
    (A : Fin (cloned s).«variables» → Bool) :
    (cloned s).sourceList.length ≤
      64 * (cloned s).sourceList.countP (fun e => !satisfied e A) := by
  change Fin (s.«variables» * 48) → Bool at A
  have h := indexed_gap s source_gap (A ∘ nameEquiv s)
  rw [occurrences_length] at h
  change (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).length ≤
    64 * (List.ofFn (fun i => mapEquation (nameEquiv s) (equation s i))).countP
      (fun e => !satisfied e A)
  rw [List.length_ofFn, count_ofFn]
  exact h

theorem cloned_completeness_count (s : ActualSource.Source) (A : Fin s.«variables» → Bool) :
    (cloned s).sourceList.countP
      (fun e => satisfied e (fun z => A ((nameEquiv s).symm z).1)) =
      s.sourceList.countP (fun e => satisfied e A) * distinctTriples.length := by
  have h := indexed_completeness_count s A
  simpa only [ActualSource.Source.sourceList, count_ofFn, cloned, satisfied_map,
    Function.comp_def, Equiv.symm_apply_apply, occurrences] using h

end DFVSGames.Reduction.FiniteSource
end

section

namespace DFVSGames.Reduction.IncidenceProbability

open Incidence
open scoped BigOperators

variable {Variable Index I Coin : Type*}

theorem sum_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    (∑ i, if p i then (1 : ℚ) else 0) = ((List.ofFn p).countP id : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.countP_cons, ih]
    cases p 0 <;> simp [add_comm]

theorem expect_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    Finset.univ.expect (fun i : Fin n => if p i then (1 : ℚ) else 0) =
      ((List.ofFn p).countP id : ℚ) / n := by
  rw [Fintype.expect_eq_sum_div_card, sum_bool_indicator_eq_count_ofFn]
  simp

def slotOfFin (i : Fin 3) : Slot :=
  if i = 0 then .first else if i = 1 then .second else .third

def slotPredicate (e : Equation Variable) (alice : Triple) (g : Variable → Bool)
    (slot : Fin 3) : Prop :=
  parity alice = e.rhs ∧
    bitAt alice (slotOfFin slot) = g (nameAt e (slotOfFin slot))

instance (e : Equation Variable) (alice : Triple) (g : Variable → Bool) (slot : Fin 3) :
    Decidable (slotPredicate e alice g slot) := inferInstanceAs (Decidable (_ ∧ _))

def slotAcceptance (e : Equation Variable) (alice : Triple) (g : Variable → Bool)
    (slot : Fin 3) : ℚ := if slotPredicate e alice g slot then 1 else 0

theorem slot_predicate_is_question_predicate (e : Equation Variable)
    (h12 : e.first ≠ e.second) (h13 : e.first ≠ e.third)
    (h23 : e.second ≠ e.third) (alice : Triple) (g : Variable → Bool) (slot : Fin 3) :
    slotPredicate e alice g slot ↔
      questionPredicate e (nameAt e (slotOfFin slot)) alice
        (g (nameAt e (slotOfFin slot))) := by
  exact (question_predicate_at_slot e h12 h13 h23 alice _ (slotOfFin slot)).symm

theorem sum_slot_acceptance (e : Equation Variable) (alice : Triple)
    (g : Variable → Bool) :
    ∑ slot : Fin 3, slotAcceptance e alice g slot =
      (acceptedSlots alice (bobTriple g e) e.rhs : ℚ) := by
  rw [Fin.sum_univ_three]
  by_cases valid : parity alice = e.rhs
  · simp only [slotAcceptance, slotPredicate, valid, true_and, slotOfFin,
      show (1 : Fin 3) ≠ 0 from by decide,
      show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
      ↓reduceIte, nameAt, bitAt, acceptedSlots, matchingSlots, bobTriple,
      Nat.cast_add]
    split_ifs <;> simp_all
  · simp [slotAcceptance, slotPredicate, valid, acceptedSlots]

theorem expect_slot_acceptance (e : Equation Variable) (alice : Triple)
    (g : Variable → Bool) :
    Finset.univ.expect (slotAcceptance e alice g) =
      (acceptedSlots alice (bobTriple g e) e.rhs : ℚ) / 3 := by
  rw [Fintype.expect_eq_sum_div_card, sum_slot_acceptance]
  simp

variable [Fintype Index]

def acceptanceProbability (equations : Index → Equation Variable)
    (alice : Index → Triple) (g : Variable → Bool) : ℚ :=
  Finset.univ.expect (fun q : Index × Fin 3 =>
    slotAcceptance (equations q.1) (alice q.1) g q.2)

def failureProbability (equations : Index → Equation Variable) (g : Variable → Bool) : ℚ :=
  Finset.univ.expect (fun i : Index =>
    (failedEquation (bobTriple g (equations i)) (equations i).rhs : ℚ))

theorem acceptance_probability_eq_expected_count (equations : Index → Equation Variable)
    (alice : Index → Triple) (g : Variable → Bool) :
    acceptanceProbability equations alice g =
      Finset.univ.expect (fun i : Index =>
        (acceptedSlots (alice i) (bobTriple g (equations i)) (equations i).rhs : ℚ) / 3) := by
  unfold acceptanceProbability
  rw [← Finset.univ_product_univ, Finset.expect_product]
  exact Finset.expect_congr rfl (fun i _ => expect_slot_acceptance (equations i) (alice i) g)

theorem acceptance_probability_nonnegative (equations : Index → Equation Variable)
    (alice : Index → Triple) (g : Variable → Bool) :
    0 ≤ acceptanceProbability equations alice g := by
  apply Finset.expect_nonneg
  intro q _
  unfold slotAcceptance
  split <;> norm_num

theorem acceptance_probability_le_one [Nonempty Index]
    (equations : Index → Equation Variable) (alice : Index → Triple) (g : Variable → Bool) :
    acceptanceProbability equations alice g ≤ 1 := by
  apply Finset.expect_le Finset.univ_nonempty
  intro q _
  unfold slotAcceptance
  split <;> norm_num

theorem acceptance_plus_failure_third_le_one [Nonempty Index]
    (equations : Index → Equation Variable) (alice : Index → Triple) (g : Variable → Bool) :
    acceptanceProbability equations alice g + failureProbability equations g / 3 ≤ 1 := by
  rw [acceptance_probability_eq_expected_count]
  unfold failureProbability
  rw [Finset.expect_div, ← Finset.expect_add_distrib]
  apply Finset.expect_le Finset.univ_nonempty
  intro i _
  have h : (acceptedSlots (alice i) (bobTriple g (equations i)) (equations i).rhs : ℚ) +
      (failedEquation (bobTriple g (equations i)) (equations i).rhs : ℚ) ≤ 3 := by
    exact_mod_cast local_count_bound (alice i) (bobTriple g (equations i)) (equations i).rhs
  linarith

theorem deterministic_soundness [Nonempty Index]
    (equations : Index → Equation Variable) (alice : Index → Triple) (g : Variable → Bool)
    (gap : (1 : ℚ) / 64 ≤ failureProbability equations g) :
    acceptanceProbability equations alice g ≤ (191 : ℚ) / 192 := by
  have h := acceptance_plus_failure_third_le_one equations alice g
  linarith

theorem failureCount_eq_countP (equations : I → Equation Variable)
    (g : Variable → Bool) (xs : List I) :
    failureCount equations g xs = xs.countP (fun i =>
      decide (parity (bobTriple g (equations i)) ≠ (equations i).rhs)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [failureCount, List.countP_cons, ih]
    by_cases h : parity (bobTriple g (equations i)) = (equations i).rhs
    · simp [failedEquation, h]
    · simp [failedEquation, h, Nat.add_comm]

theorem failure_count_finRange_eq_count_ofFn {n : Nat}
    (equations : Fin n → Equation Variable) (g : Variable → Bool) :
    failureCount equations g (List.finRange n) =
      (List.ofFn (fun i => decide
        (parity (bobTriple g (equations i)) ≠ (equations i).rhs))).countP id := by
  rw [failureCount_eq_countP]
  have h := List.countP_map (l := List.finRange n)
    (f := fun i => decide (parity (bobTriple g (equations i)) ≠ (equations i).rhs))
    (p := id)
  simpa only [List.finRange, List.map_ofFn, Function.comp_def, id_eq] using h.symm

theorem failure_probability_eq_count_finRange {n : Nat}
    (equations : Fin n → Equation Variable) (g : Variable → Bool) :
    failureProbability equations g =
      (failureCount equations g (List.finRange n) : ℚ) / n := by
  rw [failure_count_finRange_eq_count_ofFn]
  rw [← expect_bool_indicator_eq_count_ofFn]
  apply Finset.expect_congr rfl
  intro i _
  by_cases h : parity (bobTriple g (equations i)) = (equations i).rhs
  · simp [failedEquation, h]
  · simp [failedEquation, h]

theorem failure_gap_of_count_gap {n : Nat} (nonempty : 0 < n)
    (equations : Fin n → Equation Variable) (g : Variable → Bool)
    (gap : n ≤ 64 * failureCount equations g (List.finRange n)) :
    (1 : ℚ) / 64 ≤ failureProbability equations g := by
  rw [failure_probability_eq_count_finRange]
  have hn : (0 : ℚ) < n := by exact_mod_cast nonempty
  rw [le_div_iff₀ hn]
  have hg : (n : ℚ) ≤ 64 * (failureCount equations g (List.finRange n) : ℚ) := by
    exact_mod_cast gap
  linarith

theorem soundness_from_count_gap {n : Nat} (nonempty : 0 < n)
    (equations : Fin n → Equation Variable) (alice : Fin n → Triple) (g : Variable → Bool)
    (gap : n ≤ 64 * failureCount equations g (List.finRange n)) :
    acceptanceProbability equations alice g ≤ (191 : ℚ) / 192 := by
  have : Nonempty (Fin n) := ⟨⟨0, nonempty⟩⟩
  exact deterministic_soundness equations alice g
    (failure_gap_of_count_gap nonempty equations g gap)

def randomizedAcceptance [Fintype Coin] (equations : Index → Equation Variable)
    (weight : Coin → ℚ) (alice : Coin → Index → Triple)
    (bob : Coin → Variable → Bool) : ℚ :=
  ∑ c, weight c * acceptanceProbability equations (alice c) (bob c)

theorem randomized_soundness [Nonempty Index] [Fintype Coin]
    (equations : Index → Equation Variable)
    (gap : ∀ g : Variable → Bool, (1 : ℚ) / 64 ≤ failureProbability equations g)
    (weight : Coin → ℚ) (weight_nonnegative : ∀ c, 0 ≤ weight c)
    (weight_sum : ∑ c, weight c = 1)
    (alice : Coin → Index → Triple) (bob : Coin → Variable → Bool) :
    randomizedAcceptance equations weight alice bob ≤ (191 : ℚ) / 192 := by
  calc
    randomizedAcceptance equations weight alice bob ≤
        ∑ c, weight c * ((191 : ℚ) / 192) := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (deterministic_soundness equations (alice c) (bob c) (gap (bob c)))
        (weight_nonnegative c)
    _ = (191 : ℚ) / 192 := by rw [← Finset.sum_mul, weight_sum, one_mul]

instance tripleFintype : Fintype Triple :=
  Fintype.ofEquiv (Bool × Bool × Bool)
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2⟩
      invFun := fun t => (t.first, t.second, t.third)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

instance tripleInhabited : Inhabited Triple := ⟨⟨false, false, false⟩⟩

noncomputable def deterministicValue [Fintype Variable]
    (equations : Index → Equation Variable) : ℚ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty
    (fun s : (Index → Triple) × (Variable → Bool) =>
      acceptanceProbability equations s.1 s.2)

theorem acceptance_le_value [Fintype Variable]
    (equations : Index → Equation Variable) (alice : Index → Triple) (g : Variable → Bool) :
    acceptanceProbability equations alice g ≤ deterministicValue equations := by
  classical
  exact Finset.le_sup'
    (fun s : (Index → Triple) × (Variable → Bool) =>
      acceptanceProbability equations s.1 s.2) (Finset.mem_univ (alice, g))

theorem value_attained [Fintype Variable] (equations : Index → Equation Variable) :
    ∃ (alice : Index → Triple) (g : Variable → Bool),
      acceptanceProbability equations alice g = deterministicValue equations := by
  classical
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun s : (Index → Triple) × (Variable → Bool) =>
      acceptanceProbability equations s.1 s.2)
  exact ⟨s.1, s.2, hs.symm⟩

theorem value_soundness [Nonempty Index] [Fintype Variable]
    (equations : Index → Equation Variable)
    (gap : ∀ g : Variable → Bool, (1 : ℚ) / 64 ≤ failureProbability equations g) :
    deterministicValue equations ≤ (191 : ℚ) / 192 := by
  classical
  apply Finset.sup'_le
  intro s _
  exact deterministic_soundness equations s.1 s.2 (gap s.2)

theorem randomized_acceptance_le_value [Fintype Variable] [Fintype Coin]
    (equations : Index → Equation Variable)
    (weight : Coin → ℚ) (weight_nonnegative : ∀ c, 0 ≤ weight c)
    (weight_sum : ∑ c, weight c = 1)
    (alice : Coin → Index → Triple) (bob : Coin → Variable → Bool) :
    randomizedAcceptance equations weight alice bob ≤ deterministicValue equations := by
  calc
    randomizedAcceptance equations weight alice bob ≤
        ∑ c, weight c * deterministicValue equations := by
      apply Finset.sum_le_sum
      intro c _
      exact mul_le_mul_of_nonneg_left
        (acceptance_le_value equations (alice c) (bob c)) (weight_nonnegative c)
    _ = deterministicValue equations := by rw [← Finset.sum_mul, weight_sum, one_mul]

theorem randomized_value_attained [Fintype Variable] [Fintype Coin]
    (equations : Index → Equation Variable) (weight : Coin → ℚ)
    (weight_sum : ∑ c, weight c = 1) :
    ∃ (alice : Coin → Index → Triple) (bob : Coin → Variable → Bool),
      randomizedAcceptance equations weight alice bob = deterministicValue equations := by
  obtain ⟨alice, bob, h⟩ := value_attained equations
  refine ⟨fun _ => alice, fun _ => bob, ?_⟩
  simp only [randomizedAcceptance, h, ← Finset.sum_mul, weight_sum, one_mul]

theorem cloned_failure_probability_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A))
    (g : FiniteSource.Name s → Bool) :
    (1 : ℚ) / 64 ≤ failureProbability (FiniteSource.incidenceEquation s) g := by
  apply failure_gap_of_count_gap (FiniteSource.clonedSource_nonempty s)
  simpa only [FiniteSource.occurrences, List.length_finRange] using
    FiniteSource.incidence_failure_gap s source_gap g

theorem cloned_value_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A)) :
    deterministicValue (FiniteSource.incidenceEquation s) ≤ (191 : ℚ) / 192 := by
  exact value_soundness _ (cloned_failure_probability_gap s source_gap)

theorem cloned_randomized_soundness [Fintype Coin] (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A))
    (weight : Coin → ℚ) (weight_nonnegative : ∀ c, 0 ≤ weight c)
    (weight_sum : ∑ c, weight c = 1)
    (alice : Coin → FiniteSource.Occurrence s → Triple)
    (bob : Coin → FiniteSource.Name s → Bool) :
    randomizedAcceptance (FiniteSource.incidenceEquation s) weight alice bob ≤
      (191 : ℚ) / 192 := by
  exact randomized_soundness _ (cloned_failure_probability_gap s source_gap)
    weight weight_nonnegative weight_sum alice bob

namespace FoundationBridge

variable {Variable Index I : Type} [Fintype Index]

open DFVSGames.Foundations.Games
open DFVSGames.Soundness.IncidenceExtraction (Incidence)

noncomputable def uniformDistribution (Ω : Type*) [Fintype Ω] [Nonempty Ω] :
    FiniteDistribution Ω where
  weight _ := (Fintype.card Ω : ℝ)⁻¹
  nonnegative _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  normalized := by
    have h : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [h]

theorem uniform_probability_eq_rat_expect {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (event : Ω → Bool) :
    (uniformDistribution Ω).probability event =
      ((Finset.univ.expect (fun x => if event x then (1 : ℚ) else 0) : ℚ) : ℝ) := by
  unfold FiniteDistribution.probability uniformDistribution
  rw [Fintype.expect_eq_sum_div_card]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  cases event x <;> simp

def functionalTriple (a : Fin 3 → Bool) : Triple := ⟨a 0, a 1, a 2⟩

theorem functionalTriple_bitAt (a : Fin 3 → Bool) (i : Fin 3) :
    bitAt (functionalTriple a) (slotOfFin i) = a i := by
  fin_cases i <;> simp [functionalTriple, slotOfFin, bitAt]

def extractionIncidence (equations : I → Equation Variable) :
    DFVSGames.Soundness.IncidenceExtraction.Incidence I Variable where
  name o i := nameAt (equations o) (slotOfFin i)
  rhs o := (equations o).rhs

def DistinctNames (equations : I → Equation Variable) : Prop :=
  ∀ o, (equations o).first ≠ (equations o).second ∧
    (equations o).first ≠ (equations o).third ∧
    (equations o).second ≠ (equations o).third

theorem extraction_names_injective (equations : I → Equation Variable)
    (distinct : DistinctNames equations) :
    ∀ o i j, (extractionIncidence equations).name o i =
      (extractionIncidence equations).name o j → i = j := by
  intro o i j
  obtain ⟨h12, h13, h23⟩ := distinct o
  have h21 := Ne.symm h12
  have h31 := Ne.symm h13
  have h32 := Ne.symm h23
  fin_cases i <;> fin_cases j <;>
    simp_all [extractionIncidence, slotOfFin, nameAt]

noncomputable def foundationGame [Nonempty Index] [Fintype Variable]
    (equations : Index → Equation Variable) : Game Index Variable (Fin 3 → Bool) Bool := by
  classical
  exact
    { questions := (uniformDistribution (Index × Fin 3)).pushforward
        (fun q => (q.1, (extractionIncidence equations).name q.1 q.2))
      accepts := fun o name a b => decide
        ((extractionIncidence equations).namedAccepts o name a b) }

theorem foundation_success_eq_rat_acceptance [Nonempty Index] [Fintype Variable]
    (equations : Index → Equation Variable) (distinct : DistinctNames equations)
    (alice : Index → Fin 3 → Bool) (bob : Variable → Bool) :
    (foundationGame equations).success (alice, bob) =
      (acceptanceProbability equations (fun o => functionalTriple (alice o)) bob : ℝ) := by
  classical
  have hRat : Finset.univ.expect (fun q : Index × Fin 3 =>
      if (extractionIncidence equations).namedAccepts q.1
        ((extractionIncidence equations).name q.1 q.2) (alice q.1)
          (bob ((extractionIncidence equations).name q.1 q.2)) then (1 : ℚ) else 0) =
      acceptanceProbability equations (fun o => functionalTriple (alice o)) bob := by
    apply Finset.expect_congr rfl
    intro q _
    have heq : (extractionIncidence equations).namedAccepts q.1
        ((extractionIncidence equations).name q.1 q.2) (alice q.1)
          (bob ((extractionIncidence equations).name q.1 q.2)) ↔
        slotPredicate (equations q.1) (functionalTriple (alice q.1)) bob q.2 := by
      rw [DFVSGames.Soundness.IncidenceExtraction.Incidence.namedAccepts_iff_accepts _
        (extraction_names_injective equations distinct)]
      simp only [DFVSGames.Soundness.IncidenceExtraction.Incidence.accepts,
        slotPredicate, functionalTriple_bitAt]
      rfl
    by_cases h : slotPredicate (equations q.1) (functionalTriple (alice q.1)) bob q.2
    · simp only [slotAcceptance, ite_eq_left h, ite_eq_left (heq.mpr h)]
    · have hn := fun hn => h (heq.mp hn)
      simp only [slotAcceptance, ite_eq_right h, ite_eq_right hn]
  unfold Game.success foundationGame
  rw [FiniteDistribution.probability_pushforward, uniform_probability_eq_rat_expect]
  simpa only [Game.wins, decide_eq_true_eq] using congrArg (fun x : ℚ => (x : ℝ)) hRat

theorem foundation_value_soundness [Nonempty Index] [Fintype Variable]
    (equations : Index → Equation Variable) (distinct : DistinctNames equations)
    (gap : ∀ g : Variable → Bool, (1 : ℚ) / 64 ≤ failureProbability equations g) :
    (foundationGame equations).value ≤ (191 : ℝ) / 192 := by
  apply (Game.value_le_iff _ _).2
  intro strategy
  rw [foundation_success_eq_rat_acceptance equations distinct]
  have h := (Rat.cast_le (K := ℝ)).mpr (deterministic_soundness equations
    (fun o => functionalTriple (strategy.1 o)) strategy.2 (gap strategy.2))
  norm_num at h ⊢
  exact h

theorem foundation_value_le_one_sub_gap_third [Nonempty Index] [Fintype Variable]
    (equations : Index → Equation Variable) (distinct : DistinctNames equations)
    (epsilon : ℝ)
    (gap : ∀ g : Variable → Bool, epsilon ≤ (failureProbability equations g : ℝ)) :
    (foundationGame equations).value ≤ 1 - epsilon / 3 := by
  apply (Game.value_le_iff _ _).2
  intro strategy
  rw [foundation_success_eq_rat_acceptance equations distinct]
  have h := (Rat.cast_le (K := ℝ)).mpr
    (acceptance_plus_failure_third_le_one equations
      (fun o => functionalTriple (strategy.1 o)) strategy.2)
  push_cast at h
  linarith [gap strategy.2]

def sourceEquation (s : ActualSource.Source) : Fin s.occurrences → Equation (Fin s.«variables») :=
  fun i => SourceIncidence.toIncidence (s.equation i)

noncomputable def sourceGame (s : ActualSource.Source) :
    Game (Fin s.occurrences) (Fin s.«variables») (Fin 3 → Bool) Bool :=
  foundationGame (sourceEquation s)

theorem source_failure_probability (s : ActualSource.Source) (g : Fin s.«variables» → Bool) :
    failureProbability (sourceEquation s) g = s.failure g := by
  unfold failureProbability ActualSource.Source.failure
  apply Finset.expect_congr rfl
  intro i _
  simp only [sourceEquation, SourceIncidence.failedEquation_eq, ActualSource.Source.satisfied]
  by_cases h : CloneGap.satisfied (s.equation i) g = true <;> simp [h]

theorem source_value_le_one_sub_gap_third (s : ActualSource.Source)
    (distinct : s.DistinctNames) (epsilon : ℝ)
    (gap : ∀ g : Fin s.«variables» → Bool, epsilon ≤ (s.failure g : ℝ)) :
    (sourceGame s).value ≤ 1 - epsilon / 3 := by
  apply foundation_value_le_one_sub_gap_third (sourceEquation s) distinct epsilon
  intro g
  rw [source_failure_probability]
  exact gap g

theorem cloned_foundation_value_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.«variables» → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A)) :
    (foundationGame (FiniteSource.incidenceEquation s)).value ≤ (191 : ℝ) / 192 := by
  apply foundation_value_soundness _ _ (cloned_failure_probability_gap s source_gap)
  intro o
  exact FiniteSource.names_distinct s o

end FoundationBridge

end DFVSGames.Reduction.IncidenceProbability
end

section

namespace DFVSGames.Reduction.SourceProbability

open ActualSource

theorem Source_failure_eq_count (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A =
      (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) / S.occurrences := by
  have hp := IncidenceProbability.expect_bool_indicator_eq_count_ofFn
    (fun i : Fin S.occurrences => !S.satisfied A i)
  have he : Finset.univ.expect
      (fun i : Fin S.occurrences => if !S.satisfied A i then (1 : ℚ) else 0) =
      S.failure A := by
    unfold Source.failure
    congr 1
    funext i
    cases S.satisfied A i <;> rfl
  rw [he] at hp
  rw [hp]
  congr 2
  have hmap : List.ofFn (fun i : Fin S.occurrences => !S.satisfied A i) =
      S.sourceList.map (fun e => !CloneGap.satisfied e A) := by
    simp only [Source.sourceList, List.map_ofFn, Source.satisfied, Function.comp_def]
  rw [hmap, List.countP_map]
  rfl

theorem ofList_failure {n : Nat} (es : List (CloneGap.Equation (Fin n)))
    (hne : es ≠ []) (A : Fin n → Bool) :
    (Source.ofList es hne).failure A =
      (es.countP (fun e => !CloneGap.satisfied e A) : ℚ) / es.length := by
  have h := Source_failure_eq_count (Source.ofList es hne) A
  simpa [Source.sourceList, Source.ofList] using h

theorem count_complement {α : Type*} (es : List α) (p : α → Bool) :
    es.countP (fun e => !p e) + es.countP p = es.length := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases hp : p e <;> simp [hp] at * <;> omega

theorem failure_add_satisfaction (S : Source) (A : Fin S.«variables» → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [Source_failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

theorem quarter_gap_iff (S : Source) (A : Fin S.«variables» → Bool) :
    (1 / 4 : ℚ) ≤ S.failure A ↔
      S.sourceList.length ≤ 4 * S.sourceList.countP (fun e => !CloneGap.satisfied e A) := by
  rw [Source_failure_eq_count]
  have hn : (0 : ℚ) < S.occurrences := by exact_mod_cast S.nonempty
  rw [le_div_iff₀ hn]
  constructor
  · intro h
    have h' : (S.occurrences : ℚ) ≤ 4 *
        (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by linarith
    rw [S.sourceList_length]
    exact_mod_cast h'
  · intro h
    rw [S.sourceList_length] at h
    have h' : (S.occurrences : ℚ) ≤ 4 *
        (S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) := by exact_mod_cast h
    linarith

end DFVSGames.Reduction.SourceProbability
end

section

namespace DFVSGames.Outer.HastadSource

open DFVSGames.Foundations Target Complexity PCP
open DFVSGames.Reduction ActualSource
open MachineFiniteAlphabet

def success (input : SourceEncoding.Input) (bits : Fin input.«variables» → Bool) : ℚ :=
  (input.equations.countP (fun e => CloneGap.satisfied e bits) : ℚ) /
    input.equations.length

def asSource (input : SourceEncoding.Input) : Source :=
  Source.ofList input.equations input.nonempty

theorem failure_add_success (input : SourceEncoding.Input)
    (bits : Fin input.«variables» → Bool) :
    (asSource input).failure bits + success input bits = 1 := by
  have h := SourceProbability.failure_add_satisfaction (asSource input) bits
  rw [show (asSource input).sourceList = input.equations from
    Source.sourceList_ofList input.equations input.nonempty] at h
  exact h

def gapInput (H : RoundTables.BaseTable) (F : Formula) :
    Hastad.SourceGeneratorContract.NonemptyFormula :=
  ⟨TableIteration.gapMap H F, TableIteration.gapMap_nonempty H F⟩

def sourceMap (ξ : ℚ) (hξ : 0 < ξ) :=
  Hastad.SourceGeneratorContract.errorMap PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

def output (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) : SourceEncoding.Input :=
  sourceMap ξ hξ (gapInput H F)

theorem complete (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ)
    (F : Formula) (hF : F.Satisfiable) :
    ∃ bits, 1 - ξ ≤ success (output H ξ hξ F) bits := by
  exact Hastad.SourceGap.forError_complete PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableIteration.gapMap_completeness H F hF)

theorem sound (H : RoundTables.BaseTable)
    (certificate : SpectralReturn.SpectralCertificate (ExpanderTables.graph H) (1 / 100 : ℝ))
    (ξ : ℚ) (hξ : 0 < ξ) (F : Formula) (hF : ¬ F.Satisfiable)
    (bits : Fin (output H ξ hξ F).«variables» → Bool) :
    success (output H ξ hξ F) bits ≤ (1 + ξ) / 2 := by
  exact Hastad.SourceGap.forError_sound PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ
    (TableIteration.gapMap H F) (TableGapReduction.gapMap_clauseGap H certificate F hF) bits

noncomputable def roundMachine (H : RoundTables.BaseTable) :=
  RoundComputation.tablePolynomialTime H (PreprocessingRuntime.tablePolynomialTime H)

theorem roundMachine_finite (H : RoundTables.BaseTable) :
    FiniteAlphabet (roundMachine H).tm :=
  RoundComputation.tablePolynomialTime_finite_alphabet H
    (PreprocessingRuntime.tablePolynomialTime H) (PreprocessingRuntime.finiteAlphabet H)

noncomputable def gapMachine (H : RoundTables.BaseTable) :
    Turing.TM2ComputableInPolyTime formulaBits Hastad.SourceGeneratorContract.inputEncoding
      (gapInput H) where
  toTM2ComputableAux :=
    (MachineTableIteration.gapMapCertificate H (roundMachine H)).toTM2ComputableAux
  time := (MachineTableIteration.gapMapCertificate H (roundMachine H)).time
  outputsFun F := (MachineTableIteration.gapMapCertificate H (roundMachine H)).outputsFun F

noncomputable def sourceMachine (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime Hastad.SourceGeneratorContract.inputEncoding
      SourceEncoding.inputBits (sourceMap ξ hξ) :=
  Hastad.SourceGenerator.forErrorComputableInPolyTime PCPIteration.finalClauseGap ξ
    PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ

noncomputable def computation (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits (output H ξ hξ) :=
  MachineSequential.composeBits (f := gapInput H) (g := sourceMap ξ hξ)
    (gapMachine H) (sourceMachine ξ hξ)

theorem finiteAlphabet (H : RoundTables.BaseTable) (ξ : ℚ) (hξ : 0 < ξ) :
    FiniteAlphabet (computation H ξ hξ).tm :=
  MachineFiniteAlphabet.composeBits (gapMachine H) (sourceMachine ξ hξ)
    (TableIterationFiniteAlphabet.gapMap H (roundMachine H) (roundMachine_finite H))
    (Hastad.SourceGenerator.forError_finite_work_alphabets PCPIteration.finalClauseGap ξ
      PCPIteration.finalClauseGap_positive TableGapReduction.finalClauseGap_le_one hξ)

structure Reduction (ξ : ℚ) where
  reduce : Formula → SourceEncoding.Input
  completeness : ∀ F, F.Satisfiable → ∃ bits, 1 - ξ ≤ success (reduce F) bits
  soundness : ∀ F, ¬ F.Satisfiable → ∀ bits, success (reduce F) bits ≤ (1 + ξ) / 2
  computation : Turing.TM2ComputableInPolyTime formulaBits SourceEncoding.inputBits reduce
  finiteAlphabet : FiniteAlphabet computation.tm

theorem exists_reduction (ξ : ℚ) (hξ : 0 < ξ) : Nonempty (Reduction ξ) := by
  obtain ⟨H, certificate⟩ := ExpanderTables.exists_base_table
  exact ⟨⟨output H ξ hξ, complete H ξ hξ, sound H certificate ξ hξ,
    computation H ξ hξ, finiteAlphabet H ξ hξ⟩⟩

end DFVSGames.Outer.HastadSource

end

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
