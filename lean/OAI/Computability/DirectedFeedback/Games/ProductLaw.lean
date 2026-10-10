import Mathlib
import OAI.Computability.DirectedFeedback.Probability.RepeatedGameBounds

namespace OAI

namespace DFVSGames.Clean.ProductLaw

open scoped BigOperators
open Foundations.Games
open Soundness.ConditionalIncidences

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P Q S : Type} [Fintype P] [DecidableEq P] [Fintype Q] [Fintype S]

def splitCoordinates (K : Finset P) :
    (P → Q) ≃ (PositionInside K → Q) × (PositionOutside K → Q) :=
  Equiv.piEquivPiSubtypeProd (fun i => i ∈ K) (fun _ => Q)

theorem table_split (μ : P → FiniteDistribution Q) (K : Finset P) :
    (FiniteDistribution.table μ).transport (splitCoordinates K) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).product
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)) := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro pieces
  change (∏ i, (μ i).weight ((splitCoordinates K).symm pieces i)) =
    (∏ i : PositionInside K, (μ i.val).weight (pieces.1 i)) *
      ∏ i : PositionOutside K, (μ i.val).weight (pieces.2 i)
  have h := Fintype.prod_subtype_mul_prod_subtype (fun i : P => i ∈ K)
    (fun i => (μ i).weight ((splitCoordinates K).symm pieces i))
  have hi : Subtype.fintype (fun i : P => i ∈ K) =
      Finset.Subtype.fintype K := Subsingleton.elim _ _
  rw [hi] at h
  calc
    _ = (∏ i : PositionInside K,
        (μ i.val).weight ((splitCoordinates K).symm pieces i.val)) *
        ∏ i : PositionOutside K,
          (μ i.val).weight ((splitCoordinates K).symm pieces i.val) := h.symm
    _ = _ := by
      congr 1 <;> apply Finset.prod_congr rfl <;> intro i _ <;>
        simp [splitCoordinates, Equiv.piEquivPiSubtypeProd, i.property]

theorem probability_product_and (μ : FiniteDistribution Q) (ν : FiniteDistribution S)
    (event : Q → Bool) (given : S → Bool) :
    (μ.product ν).probability (fun x => event x.1 && given x.2) =
      μ.probability event * ν.probability given := by
  classical
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    Fintype.sum_prod_type]
  calc
    _ = ∑ q, ∑ s, (if event q then μ.weight q else 0) *
        (if given s then ν.weight s else 0) := by
      apply Finset.sum_congr rfl
      intro q _
      apply Finset.sum_congr rfl
      intro s _
      cases event q <;> cases given s <;> simp
    _ = _ := by rw [Finset.sum_mul_sum]

theorem probability_product_right (μ : FiniteDistribution Q)
    (ν : FiniteDistribution S) (given : S → Bool) :
    (μ.product ν).probability (fun x => given x.2) = ν.probability given := by
  simpa using probability_product_and μ ν (fun _ => true) given

theorem table_inside_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (event : (PositionInside K → Q) → Bool)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability
        (fun x => event (fun i => x i.val) && given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  rw [← probability_product_and, ← table_split]
  exact (FiniteDistribution.probability_transport (FiniteDistribution.table μ)
    (splitCoordinates K) (fun pieces => event pieces.1 && given pieces.2)).symm

theorem table_outside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool) :
    (FiniteDistribution.table μ).probability (fun x => given (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given := by
  simpa using table_inside_outside μ K (fun _ => true) given

theorem conditioned_inside (μ : P → FiniteDistribution Q) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (FiniteDistribution.table μ).probability
      (fun x => given (fun i => x i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((FiniteDistribution.table μ).condition
      (fun x => given (fun i => x i.val)) positive).probability
        (fun x => event (fun i => x i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  rw [FiniteDistribution.probability_condition]
  simp_rw [Bool.and_comm (given _)]
  rw [table_inside_outside, table_outside]
  have hne : (FiniteDistribution.table
      (fun i : PositionOutside K => μ i.val)).probability given ≠ 0 := by
    rw [table_outside] at positive
    exact ne_of_gt positive
  exact mul_div_cancel_right₀ _ hne

theorem seeded_inside_outside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (event : (PositionInside K → Q) → Bool) :
    (ν.product (FiniteDistribution.table μ)).probability
      (fun x => (decide (x.1 = seed) && given (fun i => x.2 i.val)) &&
        event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event *
        (ν.weight seed *
          (FiniteDistribution.table (fun i : PositionOutside K => μ i.val)).probability given) := by
  simp_rw [Bool.and_assoc, Bool.and_comm (given _)]
  rw [probability_product_and ν (FiniteDistribution.table μ)
    (fun s => decide (s = seed))
    (fun x : P → Q => event (fun i => x i.val) && given (fun i => x i.val)),
    table_inside_outside]
  have hseed : ν.probability (fun s => decide (s = seed)) = ν.weight seed := by
    simp [FiniteDistribution.probability]
  rw [hseed]
  ring

theorem conditioned_seed_inside (ν : FiniteDistribution S)
    (μ : P → FiniteDistribution Q) (seed : S) (K : Finset P)
    (given : (PositionOutside K → Q) → Bool)
    (positive : 0 < (ν.product (FiniteDistribution.table μ)).probability
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)))
    (event : (PositionInside K → Q) → Bool) :
    ((ν.product (FiniteDistribution.table μ)).condition
      (fun x => decide (x.1 = seed) && given (fun i => x.2 i.val)) positive).probability
        (fun x => event (fun i => x.2 i.val)) =
      (FiniteDistribution.table (fun i : PositionInside K => μ i.val)).probability event := by
  have hgiven := seeded_inside_outside ν μ seed K given (fun _ => true)
  simp only [Bool.and_true, FiniteDistribution.probability_true, one_mul] at hgiven
  rw [FiniteDistribution.probability_condition, seeded_inside_outside, hgiven]
  exact mul_div_cancel_right₀ _ (ne_of_gt (hgiven ▸ positive))

theorem table_reindex (μ : FiniteDistribution Q) {A : Type} [Fintype A] [DecidableEq A]
    {r : ℕ} (e : Fin r ≃ A) :
    (FiniteDistribution.table (fun _ : A => μ)).transport (coordinateReindex e) =
      μ.iid r := by
  apply FiniteDistribution.eq_of_weight_eq
  intro x
  change (∏ a, μ.weight (x (e.symm a))) = ∏ i, μ.weight (x i)
  exact e.symm.prod_comp (fun i => μ.weight (x i))

theorem conditioned_incidence_reindex
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma))
    (event : (Fin r → O × N) → Bool) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).probability
          (fun x => event (fun i => incidence name (x (e i).val))) =
      ((μ.pushforward (incidence name)).iid r).probability event := by
  classical
  let given : (PositionOutside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => decide ((fun i => incidence name (x i)) = observed)
  let insideEvent : (PositionInside (zeroSet J gamma) → O × Fin 3) → Bool :=
    fun x => event (fun i => incidence name (x (e i)))
  have h := conditioned_inside (fun _ : P => μ) (zeroSet J gamma)
    given positive insideEvent
  change _ = _ at h
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.probability_pushforward]
  rw [← table_reindex μ e, FiniteDistribution.probability_transport]
  exact h

theorem conditioned_incidence_distribution
    {O N D : Type} [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    [Zero D] [DecidableEq D]
    (μ : FiniteDistribution (O × Fin 3))
    (J : Finset P) (name : O → Fin 3 → N) (gamma : RawCoefficients J D)
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)))
    {r : ℕ} (e : Fin r ≃ PositionInside (zeroSet J gamma)) :
    (((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed))
        positive).pushforward
          (fun x i => incidence name (x (e i).val))) =
      (μ.pushforward (incidence name)).iid r := by
  classical
  apply FiniteDistribution.eq_of_weight_eq
  intro questions
  have h := conditioned_incidence_reindex μ J name gamma observed positive e
    (fun x => decide (x = questions))
  calc
    _ = ((FiniteDistribution.table (fun _ : P => μ)).condition
        (fun x => decide (outsideRecord (zeroSet J gamma) name x = observed)) positive).probability
          (fun x => decide ((fun i => incidence name (x (e i).val)) = questions)) := by
      unfold FiniteDistribution.pushforward FiniteDistribution.probability
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : (fun i => incidence name (x (e i).val)) = questions <;> simp [hx]
    _ = _ := h
    _ = _ := by simp [FiniteDistribution.probability]

omit [Fintype P] in

theorem clean_mask_independent (ν : FiniteDistribution S)
    (μ : FiniteDistribution Q) (clean : S → Finset P) (K : Finset P)
    (questionEvent : Q → Bool) :
    (ν.product μ).probability (fun x => decide (clean x.1 = K) && questionEvent x.2) =
      ν.probability (fun s => decide (clean s = K)) * μ.probability questionEvent := by
  exact probability_product_and ν μ (fun s => decide (clean s = K)) questionEvent

end
end DFVSGames.Clean.ProductLaw

namespace DFVSGames.Clean.WeightedPartition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Ω H : Type*} [Fintype Ω] [Fintype H] [DecidableEq H]

def fibre (observe : Ω → H) (h : H) : Ω → Bool :=
  fun x => decide (observe x = h)

theorem sum_fibre_inter (μ : FiniteDistribution Ω) (observe : Ω → H)
    (event : Ω → Bool) :
    (∑ h, μ.probability (fun x => fibre observe h x && event x)) =
      μ.probability event := by
  classical
  unfold FiniteDistribution.probability fibre
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : event x = true <;> simp [hx]

theorem sum_fibre_bound (μ : FiniteDistribution Ω) (observe : Ω → H)
    (bound : H → ℝ) :
    (∑ h, μ.probability (fibre observe h) * bound h) =
      μ.expectation (fun x => bound (observe x)) := by
  classical
  unfold FiniteDistribution.probability FiniteDistribution.expectation fibre
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [decide_eq_true_eq, ite_mul, zero_mul]
  simp

theorem probability_le_conditional_bounds (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : H → ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound h) :
    μ.probability event ≤ μ.expectation (fun x => bound (observe x)) := by
  rw [← sum_fibre_inter μ observe event, ← sum_fibre_bound μ observe bound]
  apply Finset.sum_le_sum
  intro h _
  by_cases positive : 0 < μ.probability (fibre observe h)
  · rw [μ.probability_inter_eq_mul_conditional (fibre observe h) event positive]
    exact mul_le_mul_of_nonneg_left (conditional h positive) positive.le
  · have zero : μ.probability (fibre observe h) = 0 :=
      le_antisymm (le_of_not_gt positive) (μ.probability_nonnegative _)
    rw [μ.probability_and_eq_zero_of_probability_eq_zero (fibre observe h) event zero,
      zero, zero_mul]

theorem probability_le_of_conditional_le (μ : FiniteDistribution Ω)
    (observe : Ω → H) (event : Ω → Bool) (bound : ℝ)
    (conditional : ∀ h (positive : 0 < μ.probability (fibre observe h)),
      (μ.condition (fibre observe h) positive).probability event ≤ bound) :
    μ.probability event ≤ bound := by
  have estimate := probability_le_conditional_bounds μ observe event
    (fun _ => bound) conditional
  have constant : μ.expectation (fun _ => bound) = bound := by
    rw [FiniteDistribution.expectation, ← Finset.sum_mul, μ.normalized, one_mul]
  simpa only [constant] using estimate

end
end DFVSGames.Clean.WeightedPartition

namespace DFVSGames.Soundness.ConditionalSimulation

open Foundations.Games ConditionalIncidences IncidenceExtraction
open RepeatedGameBounds

noncomputable section

instance firstInputFintype {P R O : Type} [Fintype P] [Fintype R] [Fintype O] :
    Fintype (ZeroInformation.FirstInput P R O) := by
  classical
  exact Fintype.ofEquiv ((P → O) × ZeroInformation.FirstRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

instance secondInputFintype {P R O N : Type}
    [Fintype P] [Fintype R] [Fintype O] [Fintype N] :
    Fintype (ZeroInformation.SecondInput P R O N) := by
  classical
  exact Fintype.ofEquiv ((P → Sum O N) × ZeroInformation.SecondRow P R)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.question, q.row)
      left_inv := fun p => by cases p; rfl
      right_inv := fun q => by cases q; rfl }

def incidenceGame {O N : Type} [Fintype O] [Fintype N]
    (g : Incidence O N) (mu : FiniteDistribution (O × N)) :
    Foundations.Games.Game O N Triple Bool :=
  Simulation.weightedGame ⟨g.namedAccepts⟩ mu

def actualLocalSimulation
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma)) :
    IncidenceExtraction.LocalSimulation
      (Simulation.predicateGame ((incidenceGame g mu).repetition (zeroSet J gamma).card))
      (ActualProjection.predicateGame (R := R) g (membershipBool J)) where
  questionA qa := localFirstFromH J g.name gamma observed reference
    (fun j => qa (enumerate.symm j))
  questionB qb := localSecondFromH J g.name gamma observed reference
    (fun j => qb (enumerate.symm j))
  answerA _ answer i := answer.2 (enumerate i).val
  answerB _ answer i := answer.2.2 (enumerate i).val
  sound := by
    classical
    intro qa qb answerA answerB haccept
    change ((incidenceGame g mu).repetition (zeroSet J gamma).card).accepts _ _ _ _ = true
    rw [Foundations.Games.Game.repetition_accepts_iff]
    intro i
    change decide (g.namedAccepts (qa i) (qb i)
      (answerA.2 (enumerate i).val) (answerB.2.2 (enumerate i).val)) = true
    rw [decide_eq_true_eq]
    have hj : (enumerate i).val ∈ J := zeroSet_subset J gamma (enumerate i).property
    have hsingle : membershipBool J (enumerate i).val = true := by
      simp [membershipBool, hj]
    have hname : (localSecondFromH J g.name gamma observed reference
        (fun j => qb (enumerate.symm j))).question (enumerate i).val = Sum.inr (qb i) := by
      simpa using localSecondFromH_question_inside J g.name gamma observed reference
        (fun j => qb (enumerate.symm j)) (enumerate i)
    have h := ActualProjection.accepts_implies_named_incidence g (membershipBool J)
      _ _ answerA answerB haccept (enumerate i).val hsingle (qb i) hname
    simpa only [localFirstFromH_question_inside, Equiv.symm_apply_apply] using h

theorem actual_conditioned_strategy_success_le_repeated_value
    {P R O N : Type} [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
    [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (mu : FiniteDistribution (O × N))
    (enumerate : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : IncidenceExtraction.Strategies
      (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
      (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)) :
    (Simulation.reconstructedGame
      ((incidenceGame g mu).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference mu enumerate)).success
        (Simulation.strategyPair strategy) ≤
      ((incidenceGame g mu).repetition (zeroSet J gamma).card).value := by
  exact (Simulation.reconstructedGame_success_le
    ((incidenceGame g mu).repetition (zeroSet J gamma).card)
    (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualLocalSimulation J g gamma observed reference mu enumerate) strategy).trans
      (((incidenceGame g mu).repetition (zeroSet J gamma).card).success_le_value _)

end
end DFVSGames.Soundness.ConditionalSimulation

namespace DFVSGames.Soundness.ConditionalGameLaw
open scoped BigOperators
open Foundations.Games
open ConditionalIncidences ConditionalSimulation IncidenceExtraction RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

theorem uniform_probability_decide {Ω : Type} [Fintype Ω] [Nonempty Ω]
    (event : Ω → Prop) [DecidablePred event] :
    (FiniteDistribution.uniform Ω).probability (fun x => decide (event x)) =
      (∑ x, if event x then (1 : ℝ) else 0) / (Fintype.card Ω : ℝ) := by
  classical
  calc
    _ = (FiniteDistribution.uniform Ω).expectation
        (fun x => if event x then (1 : ℝ) else 0) := by
      unfold FiniteDistribution.probability FiniteDistribution.expectation
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : event x <;> simp [hx]
    _ = _ := FiniteDistribution.expectation_uniform _

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

abbrev OuterStrategy := IncidenceExtraction.Strategies
  (ZeroInformation.FirstInput P R O) (ZeroInformation.SecondInput P R O N)
  (ActualProjection.FirstAnswer P) (ActualProjection.SecondAnswer P)

def actualWin (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) (draw : Draw P O) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (actualFirst J gamma draw) (actualSecond J g.name gamma draw)

def conditionedWinProbability (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ := by
  classical
  letI : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  exact (FiniteDistribution.uniform (RawObservationFibre J g.name gamma observed)).probability
    (fun sample => decide (actualWin J g gamma strategy sample.val.2))

def reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (questions : Fin (zeroSet J gamma).card → O × N) : Prop :=
  strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
    (localFirstFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).1))
    (localSecondFromH J g.name gamma observed reference (fun j => (questions (e.symm j)).2))

omit [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N] in
theorem actualWin_iff_reconstructedEvent (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j)
    (sample : RawObservationFibre J g.name gamma observed) :
    actualWin J g gamma strategy sample.val.2 ↔
      reconstructedEvent J g gamma observed reference e strategy
        (fun i => incidence g.name (sample.val.2 (e i).val)) := by
  unfold actualWin reconstructedEvent
  simp only [incidence, Equiv.apply_symm_apply]
  rw [localFirstFromH_correct J g.name gamma observed distinct reference sample,
    localSecondFromH_correct J g.name gamma observed reference sample]

omit [Fintype N] in
theorem conditionedWinProbability_eq_fresh (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let : Nonempty (RawObservationFibre J g.name gamma observed) := ⟨reference⟩
  have hpos : 0 < Fintype.card (RawObservationFibre J g.name gamma observed) := Fintype.card_pos
  unfold conditionedWinProbability
  rw [uniform_probability_decide]
  have hraw := raw_conditional_event_reindex_real J g.name gamma observed hpos
    (zeroSet J gamma).card e (reconstructedEvent J g gamma observed reference e strategy)
  simpa only [← actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct]
    using hraw

def incidenceLaw [Nonempty O] (g : Incidence O N) : FiniteDistribution (O × N) :=
  (FiniteDistribution.uniform (O × Fin 3)).pushforward (incidence g.name)

theorem reconstructed_success_eq_fresh_average [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) :
    (Simulation.reconstructedGame
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card)
      (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (actualLocalSimulation J g gamma observed reference (incidenceLaw g) e)).success
        (Simulation.strategyPair strategy) =
      (∑ fresh : Fin (zeroSet J gamma).card → O × Fin 3,
        if reconstructedEvent J g gamma observed reference e strategy
          (fun i => incidence g.name (fresh i)) then (1:ℝ) else 0) /
          Fintype.card (Fin (zeroSet J gamma).card → O × Fin 3) := by
  classical
  let G := (incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card
  let outer := ActualProjection.predicateGame (R := R) g (membershipBool J)
  let r := actualLocalSimulation J g gamma observed reference (incidenceLaw g) e
  change (G.questions.pushforward (fun q => (r.questionA q.1, r.questionB q.2))).probability
    (fun q => decide (strategy.wins outer q.1 q.2)) = _
  rw [FiniteDistribution.probability_pushforward]
  change (((incidenceLaw g).iid (zeroSet J gamma).card).transport
    (Foundations.Games.Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability
      (fun q => decide (strategy.wins outer (r.questionA q.1) (r.questionB q.2))) = _
  rw [FiniteDistribution.probability_transport]
  unfold incidenceLaw
  rw [FiniteDistribution.iid_pushforward, FiniteDistribution.iid_uniform,
    FiniteDistribution.probability_pushforward]
  change (FiniteDistribution.uniform (Fin (zeroSet J gamma).card → O × Fin 3)).probability
    (fun fresh => decide (reconstructedEvent J g gamma observed reference e strategy
      (fun i => incidence g.name (fresh i)))) = _
  exact uniform_probability_decide _

theorem conditioned_probability_le_repeated_value [Nonempty O]
    (J : Finset P) (g : Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    conditionedWinProbability J g gamma observed reference strategy ≤
      ((incidenceGame g (incidenceLaw g)).repetition (zeroSet J gamma).card).value := by
  rw [conditionedWinProbability_eq_fresh J g gamma observed reference e strategy distinct,
    ← reconstructed_success_eq_fresh_average J g gamma observed reference e strategy]
  exact actual_conditioned_strategy_success_le_repeated_value
    J g gamma observed reference (incidenceLaw g) e strategy

end
end DFVSGames.Soundness.ConditionalGameLaw

namespace DFVSGames.Clean.UpperBound

open scoped BigOperators
open Foundations.Games
open Soundness
open Soundness.ConditionalIncidences Soundness.ConditionalSimulation
open Soundness.ConditionalGameLaw Soundness.RepeatedGameBounds

noncomputable section
attribute [local instance] Classical.propDecidable

variable {P R O N : Type}
  [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]
  [Fintype O] [DecidableEq O] [Fintype N] [DecidableEq N]

def fixedAdviceSuccess (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N)) : ℝ :=
  (FiniteDistribution.table (fun _ : P => μ)).probability
    (fun draw => decide (actualWin J g gamma strategy draw))

omit [DecidableEq R] [Fintype N] in
private theorem reference_of_positive_inline_UpperBound
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (name : O → Fin 3 → N) (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) name draw = observed))) :
    Nonempty (RawObservationFibre J name gamma observed) := by
  classical
  have exists_draw : ∃ draw : Draw P O,
      outsideRecord (zeroSet J gamma) name draw = observed := by
    by_contra h
    have absent : ∀ draw : Draw P O,
        outsideRecord (zeroSet J gamma) name draw ≠ observed := by
      simpa only [not_exists] using h
    simp [FiniteDistribution.probability, absent] at positive
  obtain ⟨draw, equality⟩ := exists_draw
  exact ⟨⟨(gamma, draw), rfl, equality⟩⟩

theorem conditioned_success_le_repeated_value_with_reference
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (reference : RawObservationFibre J g.name gamma observed)
    (e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let event : (Fin (zeroSet J gamma).card → O × N) → Bool :=
    fun questions => decide (reconstructedEvent J g gamma observed reference e strategy questions)
  have agree : ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) =
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability
      (fun draw => event (fun i => incidence g.name (draw (e i).val))) := by
    unfold FiniteDistribution.probability FiniteDistribution.condition
    apply Finset.sum_congr rfl
    intro draw _
    by_cases hdraw : outsideRecord (zeroSet J gamma) g.name draw = observed
    · let sample : RawObservationFibre J g.name gamma observed :=
        ⟨(gamma, draw), rfl, hdraw⟩
      have equivalent : actualWin J g gamma strategy draw ↔
          reconstructedEvent J g gamma observed reference e strategy
            (fun i => incidence g.name (draw (e i).val)) :=
        actualWin_iff_reconstructedEvent J g gamma observed reference e strategy distinct sample
      simp only [event, decide_eq_true_eq, equivalent]
    · simp [hdraw]
  have distribution_law :=
    ProductLaw.conditioned_incidence_reindex μ J g.name gamma observed positive e event
  apply (le_of_eq (agree.trans distribution_law)).trans
  let G := (incidenceGame g (μ.pushforward (incidence g.name))).repetition (zeroSet J gamma).card
  let simulation := actualLocalSimulation J g gamma observed reference
    (μ.pushforward (incidence g.name)) e
  let induced := Simulation.strategyPair (simulation.induced strategy)
  refine le_trans ?_ (G.success_le_value induced)
  change ((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).probability event ≤
    (((μ.pushforward (incidence g.name)).iid (zeroSet J gamma).card).transport
      (Game.tupleQuestionEquiv (zeroSet J gamma).card)).probability (G.wins induced)
  rw [FiniteDistribution.probability_transport]
  apply FiniteDistribution.probability_mono
  intro questions hwin
  have houter : strategy.wins (ActualProjection.predicateGame (R := R) g (membershipBool J))
      (simulation.questionA (fun i => (questions i).1))
      (simulation.questionB (fun i => (questions i).2)) :=
    of_decide_eq_true hwin
  exact simulation.induced_wins strategy _ _ houter

theorem conditioned_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (observed : PositionOutside (zeroSet J gamma) → O × N)
    (positive : 0 < (FiniteDistribution.table (fun _ : P => μ)).probability
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed)))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    ((FiniteDistribution.table (fun _ : P => μ)).condition
      (fun draw => decide (outsideRecord (zeroSet J gamma) g.name draw = observed))
        positive).probability (fun draw => decide (actualWin J g gamma strategy draw)) ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  classical
  let reference := Classical.choice (reference_of_positive_inline_UpperBound μ J g.name gamma observed positive)
  let e : Fin (zeroSet J gamma).card ≃ PositionInside (zeroSet J gamma) :=
    (Fintype.equivFinOfCardEq (by simp [PositionInside])).symm
  exact conditioned_success_le_repeated_value_with_reference
    μ J g gamma observed positive reference e strategy distinct

theorem fixed_advice_success_le_repeated_value
    (μ : FiniteDistribution (O × Fin 3)) (J : Finset P)
    (g : IncidenceExtraction.Incidence O N)
    (gamma : RawCoefficients J (ZeroInformation.Bits R))
    (strategy : OuterStrategy (P := P) (R := R) (O := O) (N := N))
    (distinct : ∀ o i j, g.name o i = g.name o j → i = j) :
    fixedAdviceSuccess μ J g gamma strategy ≤
      ((incidenceGame g (μ.pushforward (incidence g.name))).repetition
        (zeroSet J gamma).card).value := by
  unfold fixedAdviceSuccess
  apply WeightedPartition.probability_le_of_conditional_le
    _ (outsideRecord (zeroSet J gamma) g.name)
  intro observed positive
  exact conditioned_success_le_repeated_value μ J g gamma observed positive strategy distinct

end
end DFVSGames.Clean.UpperBound

namespace DFVSGames.Foundations.Games

open scoped BigOperators
noncomputable section

namespace FiniteDistribution

theorem pushforward_eq_of_agree_on_support
    {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]
    (μ : FiniteDistribution Ω) (f g : Ω → Γ)
    (h : ∀ x, μ.weight x ≠ 0 → f x = g x) :
    μ.pushforward f = μ.pushforward g := by
  classical
  apply eq_of_weight_eq
  intro y
  simp only [pushforward]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : μ.weight x = 0
  · simp [hx]
  · rw [h x hx]

theorem product_pushforward
    {Ω Γ A B : Type*} [Fintype Ω] [Fintype Γ] [Fintype A] [Fintype B]
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ)
    (f : Ω → A) (g : Γ → B) :
    (μ.product ν).pushforward (fun z => (f z.1, g z.2)) =
      (μ.pushforward f).product (ν.pushforward g) := by
  classical
  apply eq_of_weight_eq
  rintro ⟨a, b⟩
  simp only [pushforward, product]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hx : f x = a <;> by_cases hy : g y = b <;> simp [hx, hy]

theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

theorem table_repair_pushforward
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (repair : Q → A → A)
    (hrepair : ∀ q a, (responses q).weight a ≠ 0 → repair q a = a) (q : Q) :
    (table responses).pushforward (fun answers => repair q (answers q)) =
      responses q := by
  calc
    _ = (table responses).pushforward (fun answers => answers q) := by
      apply pushforward_eq_of_agree_on_support
      intro answers h
      exact hrepair q (answers q) (table_row_weight_ne_zero responses answers h q)
    _ = responses q := table_eval_pushforward responses q

end FiniteDistribution

namespace KernelSampling

abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

theorem read_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed => (readLeft seed x, readRight seed y)) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => answers x) (fun answers => answers y),
    FiniteDistribution.table_eval_pushforward, FiniteDistribution.table_eval_pushforward]

theorem repaired_joint_pushforward {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B)
    (repairLeft : Q₁ → A → A) (repairRight : Q₂ → B → B)
    (hleft : ∀ x a, (left x).weight a ≠ 0 → repairLeft x a = a)
    (hright : ∀ y b, (right y).weight b ≠ 0 → repairRight y b = b)
    (x : Q₁) (y : Q₂) :
    (seedLaw left right).pushforward (fun seed =>
      (repairLeft x (readLeft seed x), repairRight y (readRight seed y))) =
      (left x).product (right y) := by
  unfold seedLaw readLeft readRight
  rw [FiniteDistribution.product_pushforward
      (FiniteDistribution.table left) (FiniteDistribution.table right)
      (fun answers => repairLeft x (answers x)) (fun answers => repairRight y (answers y)),
    FiniteDistribution.table_repair_pushforward left repairLeft hleft,
    FiniteDistribution.table_repair_pushforward right repairRight hright]

variable {I A B S : Type*} [DecidableEq I]

def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

def completedRight (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) : I → B :=
  Function.update (readRight seed q) j q.1

@[simp] theorem completedLeft_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) :
    completedLeft j seed q j = q.1 := by simp [completedLeft]

@[simp] theorem completedRight_coordinate (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : B × S) :
    completedRight j seed q j = q.1 := by simp [completedRight]

private theorem update_eq_of_coordinate_inline_KernelSampling (xs : I → A) (j : I) (a : A)
    (h : xs j = a) : Function.update xs j a = xs := by
  funext i
  by_cases hi : i = j <;> simp [Function.update, hi, h]

theorem completed_joint_pushforward
    [Fintype I] [Fintype A] [Fintype B] [Fintype S]
    [DecidableEq A] [DecidableEq B] [DecidableEq S]
    (left : (A × S) → FiniteDistribution (I → A))
    (right : (B × S) → FiniteDistribution (I → B)) (j : I)
    (hleft : ∀ q xs, (left q).weight xs ≠ 0 → xs j = q.1)
    (hright : ∀ q ys, (right q).weight ys ≠ 0 → ys j = q.1)
    (x : A × S) (y : B × S) :
    (seedLaw left right).pushforward
        (fun seed => (completedLeft j seed x, completedRight j seed y)) =
      (left x).product (right y) := by
  apply repaired_joint_pushforward left right
    (fun q xs => Function.update xs j q.1) (fun q ys => Function.update ys j q.1)
  · intro q xs h
    exact update_eq_of_coordinate_inline_KernelSampling xs j q.1 (hleft q xs h)
  · intro q ys h
    exact update_eq_of_coordinate_inline_KernelSampling ys j q.1 (hright q ys h)

end KernelSampling
end
end DFVSGames.Foundations.Games

end OAI
