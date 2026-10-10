import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Reduction.ActualSourceLemmas
import OAI.Computability.UniqueGames.Reduction.SourceIncidenceLemmas
import OAI.Computability.UniqueGames.Reduction.WeightedSource
import OAI.Computability.UniqueGames.Soundness.ExpectationComparisonLemmas

namespace OAI

section

/-! Actual finite incidence-game probabilities for Proposition 4.3.
The referee samples an occurrence and one of three slots independently and
uniformly. Alice sees its occurrence; Bob sees only its variable name.
-/

namespace UniqueGamesTheorem.Reduction.IncidenceProbability

open Incidence
open scoped BigOperators

variable {Variable Index Coin Occurrence : Type*}

theorem sum_bool_indicator_eq_count_ofFn {n : Nat} (p : Fin n → Bool) :
    (∑ i, if p i then (1 : ℚ) else 0) = ((List.ofFn p).countP id : ℚ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, List.ofFn_succ, List.countP_cons, ih]
    cases p 0 <;> simp [add_comm]

/-- Uniform Boolean-event probability is the indexed list's exact occurrence count. -/
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

theorem failureCount_eq_countP (equations : Occurrence → Equation Variable)
    (g : Variable → Bool) (xs : List Occurrence) :
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

/-- A finite randomized strategy, with the common coin including both private coins. -/
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

/-- The actual game value is the maximum over all deterministic local strategies. -/
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

/-- Constant choices of an optimal strategy attain the value under any normalized coin law. -/
theorem randomized_value_attained [Fintype Variable] [Fintype Coin]
    (equations : Index → Equation Variable) (weight : Coin → ℚ)
    (weight_sum : ∑ c, weight c = 1) :
    ∃ (alice : Coin → Index → Triple) (bob : Coin → Variable → Bool),
      randomizedAcceptance equations weight alice bob = deterministicValue equations := by
  obtain ⟨alice, bob, h⟩ := value_attained equations
  refine ⟨fun _ => alice, fun _ => bob, ?_⟩
  simp only [randomizedAcceptance, h, ← Finset.sum_mul, weight_sum, one_mul]

theorem cloned_failure_probability_gap (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A))
    (g : FiniteSource.Name s → Bool) :
    (1 : ℚ) / 64 ≤ failureProbability (FiniteSource.incidenceEquation s) g := by
  apply failure_gap_of_count_gap (FiniteSource.clonedSource_nonempty s)
  simpa only [FiniteSource.occurrences, List.length_finRange] using
    FiniteSource.incidence_failure_gap s source_gap g

/-- Actual finite incidence-game value after the concrete 48-clone construction. -/
theorem cloned_value_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A)) :
    deterministicValue (FiniteSource.incidenceEquation s) ≤ (191 : ℚ) / 192 := by
  exact value_soundness _ (cloned_failure_probability_gap s source_gap)

theorem cloned_randomized_soundness [Fintype Coin] (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
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

variable {Variable Index Occurrence : Type} [Fintype Index]

open UniqueGamesTheorem.Foundations.Games
open UniqueGamesTheorem.Soundness.IncidenceExtraction (Incidence)

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

def extractionIncidence (equations : Occurrence → Equation Variable) :
    UniqueGamesTheorem.Soundness.IncidenceExtraction.Incidence Occurrence Variable where
  name o i := nameAt (equations o) (slotOfFin i)
  rhs o := (equations o).rhs

def DistinctNames (equations : Occurrence → Equation Variable) : Prop :=
  ∀ o, (equations o).first ≠ (equations o).second ∧
    (equations o).first ≠ (equations o).third ∧
    (equations o).second ≠ (equations o).third

theorem extraction_names_injective (equations : Occurrence → Equation Variable)
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
      rw [UniqueGamesTheorem.Soundness.IncidenceExtraction.Incidence.namedAccepts_iff_accepts _
        (extraction_names_injective equations distinct)]
      simp only [UniqueGamesTheorem.Soundness.IncidenceExtraction.Incidence.accepts,
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

def sourceEquation (s : ActualSource.Source) : Fin s.occurrences → Equation (Fin s.variables) :=
  fun i => SourceIncidence.toIncidence (s.equation i)

noncomputable def sourceGame (s : ActualSource.Source) :
    Game (Fin s.occurrences) (Fin s.variables) (Fin 3 → Bool) Bool :=
  foundationGame (sourceEquation s)

theorem source_failure_probability (s : ActualSource.Source) (g : Fin s.variables → Bool) :
    failureProbability (sourceEquation s) g = s.failure g := by
  unfold failureProbability ActualSource.Source.failure
  apply Finset.expect_congr rfl
  intro i _
  simp only [sourceEquation, SourceIncidence.failedEquation_eq, ActualSource.Source.satisfied]
  by_cases h : CloneGap.satisfied (s.equation i) g = true <;> simp [h]

theorem source_value_le_one_sub_gap_third (s : ActualSource.Source)
    (distinct : s.DistinctNames) (epsilon : ℝ)
    (gap : ∀ g : Fin s.variables → Bool, epsilon ≤ (s.failure g : ℝ)) :
    (sourceGame s).value ≤ 1 - epsilon / 3 := by
  apply foundation_value_le_one_sub_gap_third (sourceEquation s) distinct epsilon
  intro g
  rw [source_failure_probability]
  exact gap g

theorem cloned_foundation_value_soundness (s : ActualSource.Source)
    (source_gap : ∀ A : Fin s.variables → Bool,
      s.sourceList.length ≤ 4 * s.sourceList.countP (fun e => !CloneGap.satisfied e A)) :
    (foundationGame (FiniteSource.incidenceEquation s)).value ≤ (191 : ℝ) / 192 := by
  apply foundation_value_soundness _ _ (cloned_failure_probability_gap s source_gap)
  intro o
  exact FiniteSource.names_distinct s o

end FoundationBridge

end UniqueGamesTheorem.Reduction.IncidenceProbability

end

section

namespace UniqueGamesTheorem.Reduction.SourceProbability

open ActualSource

theorem Source_failure_eq_count (S : Source) (A : Fin S.variables → Bool) :
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

theorem failure_add_satisfaction (S : Source) (A : Fin S.variables → Bool) :
    S.failure A +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences = 1 := by
  rw [Source_failure_eq_count, ← add_div]
  have h := count_complement S.sourceList (fun e => CloneGap.satisfied e A)
  have hc : ((S.sourceList.countP (fun e => !CloneGap.satisfied e A) : ℚ) +
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ)) = S.occurrences := by
    exact_mod_cast (h.trans S.sourceList_length)
  rw [hc, div_self]
  exact_mod_cast Nat.ne_of_gt S.nonempty

theorem quarter_gap_iff (S : Source) (A : Fin S.variables → Bool) :
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

end UniqueGamesTheorem.Reduction.SourceProbability

end

section

namespace UniqueGamesTheorem.Reduction.Preprocessing

open ActualSource WeightedSource

def rounded {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source :=
  Source.ofList (W.roundedEquations (W.roundingDenominator γ))
    (W.roundedEquations_for_nonempty γ hγ)

theorem rounded_failure_add_value {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ)
    (A : Fin n → Bool) :
    (rounded W γ hγ).failure A + W.roundedValue (W.roundingDenominator γ)
      (fun e => CloneGap.satisfied e A) = 1 := by
  have h := SourceProbability.failure_add_satisfaction (rounded W γ hγ) A
  simpa [rounded, Source.sourceList, Source.ofList,
    RationalSource.roundedEquations_length, RationalSource.roundedValue,
    List.countP_eq_length_filter] using h

theorem rounded_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (rounded W γ hγ).variables → Bool, (rounded W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := hsource
  refine ⟨A, ?_⟩
  have ht := W.completeness_transport γ ξ hγ hξ (fun e => CloneGap.satisfied e A) hA
  have he := rounded_failure_add_value W γ hγ A
  linarith

theorem rounded_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (rounded W γ hγ).variables → Bool,
      (1 / 4 : ℚ) ≤ (rounded W γ hγ).failure A := by
  intro A
  have ht := W.soundness_transport γ ξ hγ hγsmall hξ
    (fun e => CloneGap.satisfied e A) (hsource A)
  have he := rounded_failure_add_value W γ hγ A
  linarith

def uniformSource {n : Nat} (W : RationalSource (CloneGap.Equation (Fin n)))
    (γ : ℚ) (hγ : 0 < γ) : Source := FiniteSource.cloned (rounded W γ hγ)

theorem cloned_failure_eq (S : Source) (A : Fin S.variables → Bool) :
    (FiniteSource.cloned S).failure
      (fun z => A ((FiniteSource.nameEquiv S).symm z).1) = S.failure A := by
  have hc := SourceProbability.failure_add_satisfaction (FiniteSource.cloned S)
    (fun z => A ((FiniteSource.nameEquiv S).symm z).1)
  have hs := SourceProbability.failure_add_satisfaction S A
  erw [FiniteSource.cloned_completeness_count S A, FiniteSource.cloned_length S] at hc
  simp only [Nat.cast_mul] at hc
  have hn : (S.occurrences : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt S.nonempty
  have hd : (CloneGap.distinctTriples.length : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt FiniteSource.distinctTriples_nonempty
  have hratio :
      ((S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) *
        (CloneGap.distinctTriples.length : ℚ)) /
        ((S.occurrences : ℚ) * (CloneGap.distinctTriples.length : ℚ)) =
      (S.sourceList.countP (fun e => CloneGap.satisfied e A) : ℚ) / S.occurrences := by
    field_simp [hn, hd]
  rw [hratio] at hc
  linarith

theorem uniformSource_complete {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hξ : ξ ≤ γ / 4)
    (hsource : ∃ A : Fin n → Bool,
      1 - ξ ≤ W.weightedValue (fun e => CloneGap.satisfied e A)) :
    ∃ A : Fin (uniformSource W γ hγ).variables → Bool,
      (uniformSource W γ hγ).failure A ≤ γ := by
  obtain ⟨A, hA⟩ := rounded_complete W γ ξ hγ hξ hsource
  refine ⟨fun z => A ((FiniteSource.nameEquiv (rounded W γ hγ)).symm z).1, ?_⟩
  change (FiniteSource.cloned (rounded W γ hγ)).failure _ ≤ γ
  exact (cloned_failure_eq (rounded W γ hγ) A).trans_le hA

theorem uniformSource_distinct {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ : ℚ) (hγ : 0 < γ) :
    (uniformSource W γ hγ).DistinctNames := FiniteSource.cloned_distinct _

theorem uniformSource_sound {n : Nat}
    (W : RationalSource (CloneGap.Equation (Fin n))) (γ ξ : ℚ)
    (hγ : 0 < γ) (hγsmall : γ ≤ 1 / 8) (hξ : ξ ≤ 1 / 16)
    (hsource : ∀ A : Fin n → Bool,
      W.weightedValue (fun e => CloneGap.satisfied e A) ≤ (1 + ξ) / 2) :
    ∀ A : Fin (uniformSource W γ hγ).variables → Bool,
      (1 / 64 : ℚ) ≤ (uniformSource W γ hγ).failure A := by
  intro A
  have hr := rounded_sound W γ ξ hγ hγsmall hξ hsource
  have hgap : ∀ B : Fin (rounded W γ hγ).variables → Bool,
      (rounded W γ hγ).sourceList.length ≤
      4 * (rounded W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e B) := by
    intro B
    exact (SourceProbability.quarter_gap_iff _ B).mp (hr B)
  have hc := FiniteSource.cloned_gap (rounded W γ hγ) hgap A
  change (uniformSource W γ hγ).sourceList.length ≤
    64 * (uniformSource W γ hγ).sourceList.countP (fun e => !CloneGap.satisfied e A) at hc
  rw [SourceProbability.Source_failure_eq_count]
  have hn : (0 : ℚ) < (uniformSource W γ hγ).occurrences := by
    exact_mod_cast (uniformSource W γ hγ).nonempty
  apply (le_div_iff₀ hn).mpr
  rw [Source.sourceList_length] at hc
  have hc' : ((uniformSource W γ hγ).occurrences : ℚ) ≤
      64 * ((uniformSource W γ hγ).sourceList.countP
        (fun e => !CloneGap.satisfied e A) : ℚ) := by exact_mod_cast hc
  linarith

end UniqueGamesTheorem.Reduction.Preprocessing

end

end OAI
