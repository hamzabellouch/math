import Mathlib
import OAI.Computability.MaxCut.Games.AnswerBridge

namespace OAI

namespace MaxCutGames.Clean.UpperBound

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

/-- The true weighted occurrence/position experiment at fixed visible advice. -/
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

/-- On each positive public observation fibre, the full agreement event is
bounded by ordinary repetition. The reference draw is fixed public padding,
not an extra input depending on the still hidden question pair. -/
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

/-- All outside observations are genuinely averaged with their actual weights.
The result permits arbitrary repeated occurrence IDs and correlated local
answers across the entire clean tuple. -/
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
end MaxCutGames.Clean.UpperBound

/-!
Exact sampling of two conditional kernels from one finite weighted shared seed.
The seed consists of independent full response tables and is independent of the
questions. Supported-coordinate repairs preserve the sampled laws and enforce
the designated coordinate even on seeds of weight zero. The seed is not claimed
to be uniform: the kernel weights may be arbitrary real numbers.
-/

namespace MaxCutGames.Foundations.Games

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

/-- Applying separate maps to independent samples preserves their independence. -/
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

/-- A full response table of nonzero weight uses a supported answer in every row. -/
theorem table_row_weight_ne_zero
    {Q A : Type*} [Fintype Q] [Fintype A] [DecidableEq Q]
    (responses : Q → FiniteDistribution A) (answers : Q → A)
    (h : (table responses).weight answers ≠ 0) (q : Q) :
    (responses q).weight (answers q) ≠ 0 := by
  intro hq
  apply h
  change (∏ r, (responses r).weight (answers r)) = 0
  exact Finset.prod_eq_zero (Finset.mem_univ q) hq

/-- Repairing table entries only off each row's support leaves its exact law intact. -/
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

/-- A single seed supplies a full local table to each side. -/
abbrev Seed (Q₁ Q₂ A B : Type*) := (Q₁ → A) × (Q₂ → B)

def readLeft {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₁) : A := seed.1 q
def readRight {Q₁ Q₂ A B : Type*} (seed : Seed Q₁ Q₂ A B) (q : Q₂) : B := seed.2 q

/-- The fixed weighted seed law; it does not depend on the sampled questions. -/
def seedLaw {Q₁ Q₂ A B : Type*}
    [Fintype Q₁] [Fintype Q₂] [Fintype A] [Fintype B]
    [DecidableEq Q₁] [DecidableEq Q₂]
    (left : Q₁ → FiniteDistribution A) (right : Q₂ → FiniteDistribution B) :
    FiniteDistribution (Seed Q₁ Q₂ A B) :=
  (FiniteDistribution.table left).product (FiniteDistribution.table right)

/-- The two reads have exactly the product of the requested conditional laws. -/
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

/-- Separate supported repairs retain the exact joint product law. -/
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

/-- Restore the designated coordinate on every left table read. -/
def completedLeft (j : I)
    (seed : Seed (A × S) (B × S) (I → A) (I → B)) (q : A × S) : I → A :=
  Function.update (readLeft seed q) j q.1

/-- Restore the designated coordinate on every right table read. -/
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

/-- Exact conditional completion from a finite weighted shared seed. The reads
always restore the specified coordinates, including on seeds of weight zero;
the support hypotheses ensure that this repair preserves the requested laws. -/
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
end MaxCutGames.Foundations.Games

/-! Finite shared randomness is an actual convex mixture of distributions. -/

namespace MaxCutGames.Foundations.Games.FiniteDistribution

open scoped BigOperators
noncomputable section

variable {Seed Ω : Type*} [Fintype Seed] [Fintype Ω]

def mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) : FiniteDistribution Ω where
  weight x := ∑ seed, seedLaw.weight seed * (laws seed).weight x
  nonnegative x := Finset.sum_nonneg fun seed _ =>
    mul_nonneg (seedLaw.nonnegative seed) ((laws seed).nonnegative x)
  normalized := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, (laws _).normalized, mul_one]
    exact seedLaw.normalized

theorem probability_mixture (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) :
    (seedLaw.mixture laws).probability event =
      ∑ seed, seedLaw.weight seed * (laws seed).probability event := by
  unfold probability mixture
  calc
    _ = ∑ x, ∑ seed,
        seedLaw.weight seed * (if event x then (laws seed).weight x else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      cases event x <;> simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro seed _
      rw [Finset.mul_sum]

theorem probability_mixture_le (seedLaw : FiniteDistribution Seed)
    (laws : Seed → FiniteDistribution Ω) (event : Ω → Bool) (bound : ℝ)
    (h : ∀ seed, (laws seed).probability event ≤ bound) :
    (seedLaw.mixture laws).probability event ≤ bound := by
  rw [probability_mixture]
  calc
    _ ≤ ∑ seed, seedLaw.weight seed * bound :=
      Finset.sum_le_sum fun seed _ =>
        mul_le_mul_of_nonneg_left (h seed) (seedLaw.nonnegative seed)
    _ = bound := by rw [← Finset.sum_mul, seedLaw.normalized, one_mul]

end
end MaxCutGames.Foundations.Games.FiniteDistribution

end OAI
