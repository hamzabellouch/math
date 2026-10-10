import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import OAI.Computability.UniqueGames.Foundations.ValueLemmas
import OAI.Computability.UniqueGames.Games.FactorizationLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticRateLemmas

namespace OAI

section

/-!
Finite conditional projection kernels for the Dinur--Steurer argument.
The outer distribution samples the right question and the inner distribution
samples the left question conditional on it. These are genuine normalized
finite distributions; no norm inequality or repetition claim is a field.
-/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

structure ProjectionKernel (Q₁ Q₂ A₁ A₂ : Type*)
    [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] where
  outer : FiniteDistribution Q₂
  inner : Q₂ → FiniteDistribution Q₁
  accepts : Q₁ → Q₂ → A₁ → A₂ → Bool
  projection : ∀ x y a b b', accepts x y a b = true →
    accepts x y a b' = true → b = b'

namespace ProjectionKernel
variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def toGame (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : Game Q₁ Q₂ A₁ A₂ where
  questions :=
    { weight := fun q => K.outer.weight q.2 * (K.inner q.2).weight q.1
      nonnegative := fun q => mul_nonneg (K.outer.nonnegative _) ((K.inner _).nonnegative _)
      normalized := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        simp_rw [← Finset.mul_sum, FiniteDistribution.normalized, mul_one]
        exact K.outer.normalized }
  accepts := K.accepts

theorem toGame_isProjection (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    IsProjection K.toGame := K.projection

/-- Apply the projection operator to an arbitrary real assignment table. -/
def apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) : ℝ :=
  ∑ x, (K.inner y).weight x * ∑ a, if K.accepts x y a b then f x a else 0

/-- Squared Hilbert norm, with the actual right-question marginal. -/
def energy (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Q₁ → A₁ → ℝ) : ℝ :=
  ∑ y, K.outer.weight y * ∑ b, K.apply f y b ^ 2

def assignment (labels : Q₁ → A₁) (x : Q₁) (a : A₁) : ℝ := by
  classical
  exact if labels x = a then 1 else 0

def assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) : ℝ := K.energy (assignment labels)

/-- Maximum squared collision norm of an ordinary deterministic left strategy. -/
def collisionValue [Nonempty A₁] (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : ℝ := by
  classical
  exact Finset.univ.sup' Finset.univ_nonempty K.assignmentEnergy

def vectorEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Ω → Q₁ → A₁ → ℝ) : ℝ := ∑ ω, K.energy (f ω)

def vectorMass (f : Ω → Q₁ → A₁ → ℝ) (x : Q₁) : ℝ :=
  ∑ ω, (∑ a, f ω x a) ^ 2

theorem energy_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) : 0 ≤ K.energy f := by
  exact Finset.sum_nonneg fun y _ => mul_nonneg (K.outer.nonnegative y)
    (Finset.sum_nonneg fun b _ => sq_nonneg _)

theorem assignmentEnergy_le_collisionValue [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.collisionValue := by
  classical
  exact Finset.le_sup' _ (Finset.mem_univ labels)

theorem collisionValue_le_iff [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (bound : ℝ) :
    K.collisionValue ≤ bound ↔ ∀ labels, K.assignmentEnergy labels ≤ bound := by
  classical
  simp [collisionValue, Finset.sup'_le_iff]

theorem exists_optimal_assignment [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    ∃ labels, K.assignmentEnergy labels = K.collisionValue := by
  classical
  obtain ⟨labels, _, h⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Q₁ → A₁))) Finset.univ_nonempty K.assignmentEnergy
  exact ⟨labels, h.symm⟩

theorem collisionValue_nonneg [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : 0 ≤ K.collisionValue := by
  obtain ⟨labels, h⟩ := K.exists_optimal_assignment
  rw [← h]
  exact K.energy_nonneg _

@[simp] theorem apply_assignment (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    K.apply (assignment labels) y b =
      ∑ x, if K.accepts x y (labels x) b then (K.inner y).weight x else 0 := by
  classical
  unfold apply assignment
  apply Finset.sum_congr rfl
  intro x _
  have hsum : (∑ a, if K.accepts x y a b then
      (if labels x = a then (1 : ℝ) else 0) else 0) =
      if K.accepts x y (labels x) b then (1 : ℝ) else 0 := by
    have hpoint (a : A₁) :
        (if K.accepts x y a b then (if labels x = a then (1 : ℝ) else 0) else 0) =
        (if a = labels x then (if K.accepts x y a b then (1 : ℝ) else 0) else 0) := by
      by_cases h : a = labels x
      · subst a
        simp
      · simp [h, Ne.symm h]
    simp_rw [hpoint]
    simp
  rw [hsum]
  by_cases h : K.accepts x y (labels x) b = true <;> simp [h]

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-!
Every finite projection game has an exact conditional-kernel representation.
The right question uses its original marginal. Conditional left-question laws
are normalized original rows; zero rows use the original left marginal as a
fallback. Their zero outer weight makes the reconstruction identity valid on
all rows without positivity or support hypotheses.
-/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

def leftQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₁ where
  weight x := ∑ y, G.questions.weight (x, y)
  nonnegative x := Finset.sum_nonneg fun y _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [← Fintype.sum_prod_type]
    exact G.questions.normalized

def rightQuestionMarginal (G : Game Q₁ Q₂ A₁ A₂) : FiniteDistribution Q₂ where
  weight y := ∑ x, G.questions.weight (x, y)
  nonnegative y := Finset.sum_nonneg fun x _ => G.questions.nonnegative (x, y)
  normalized := by
    rw [Finset.sum_comm, ← Fintype.sum_prod_type]
    exact G.questions.normalized

/-- The fallback exists even when the question types were not supplied with
`Nonempty` instances: it is a marginal of the game's actual probability law. -/
def leftGivenRight (G : Game Q₁ Q₂ A₁ A₂) (y : Q₂) : FiniteDistribution Q₁ :=
  UniqueGamesTheorem.Foundations.Repetition.normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G)

/-- Exact disintegration, including right questions of marginal probability
zero. The conditional law is never assumed to reconstruct the question law. -/
theorem rightQuestionMarginal_mul_leftGivenRight
    (G : Game Q₁ Q₂ A₁ A₂) (x : Q₁) (y : Q₂) :
    (rightQuestionMarginal G).weight y * (leftGivenRight G y).weight x =
      G.questions.weight (x, y) :=
  UniqueGamesTheorem.Foundations.Repetition.sum_mul_normalizeOr
    (fun x => G.questions.weight (x, y))
    (fun x => G.questions.nonnegative (x, y)) (leftQuestionMarginal G) x

/-- A projection game's predicate and actual question distribution determine
the conditional kernel used by the collision argument. -/
def kernelOfGame (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    ProjectionKernel Q₁ Q₂ A₁ A₂ where
  outer := rightQuestionMarginal G
  inner := leftGivenRight G
  accepts := G.accepts
  projection := hG

@[simp] theorem kernelOfGame_question_weight
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) (q : Q₁ × Q₂) :
    (kernelOfGame G hG).toGame.questions.weight q = G.questions.weight q :=
  rightQuestionMarginal_mul_leftGivenRight G q.1 q.2

@[simp] theorem toGame_kernelOfGame
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame = G := by
  have hq : (kernelOfGame G hG).toGame.questions = G.questions :=
    FiniteDistribution.eq_of_weight_eq (kernelOfGame_question_weight G hG)
  calc
    _ = { questions := G.questions, accepts := G.accepts } := by
      change Game.mk (kernelOfGame G hG).toGame.questions G.accepts =
        Game.mk G.questions G.accepts
      rw [hq]
    _ = G := by cases G; rfl

@[simp] theorem kernelOfGame_success
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G)
    (strategy : Strategy Q₁ Q₂ A₁ A₂) :
    (kernelOfGame G hG).toGame.success strategy = G.success strategy := by
  rw [toGame_kernelOfGame]

@[simp] theorem kernelOfGame_value [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) (hG : IsProjection G) :
    (kernelOfGame G hG).toGame.value = G.value := by
  rw [toGame_kernelOfGame]

end
end UniqueGamesTheorem.Repetition

end

section

/-!
Collision norms are unchanged by bijective encodings of either player's
questions and answers. The distributions, acceptance predicate, and assignment
tables are transported together. This provides the finite-tuple regrouping
needed to pass from one product step to arbitrary parallel repetition.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators

noncomputable section

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

/-- Transport both normalized question laws and the projection predicate. -/
def reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) : ProjectionKernel R₁ R₂ B₁ B₂ where
  outer := K.outer.transport eQ₂
  inner y := (K.inner (eQ₂.symm y)).transport eQ₁
  accepts x y a b := K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
  projection := by
    intro x y a b b' hb hb'
    exact eA₂.symm.injective (K.projection _ _ _ _ _ hb hb')

/-- Reindexing the operator equals pulling back its assignment table. -/
theorem apply_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂)
    (f : R₁ → B₁ → ℝ) (y : R₂) (b : B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).apply f y b =
      K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) := by
  classical
  unfold apply
  change (∑ x, (K.inner (eQ₂.symm y)).weight (eQ₁.symm x) *
    ∑ a, if K.accepts (eQ₁.symm x) (eQ₂.symm y) (eA₁.symm a) (eA₂.symm b)
      then f x a else 0) = _
  refine Fintype.sum_equiv eQ₁.symm _ _ ?_
  intro x
  simp only [Equiv.apply_symm_apply]
  congr 1
  refine Fintype.sum_equiv eA₁.symm _ _ ?_
  intro a
  simp only [Equiv.apply_symm_apply]

theorem energy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (f : R₁ → B₁ → ℝ) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).energy f =
      K.energy (fun x a => f (eQ₁ x) (eA₁ a)) := by
  classical
  unfold energy
  simp_rw [apply_reindex]
  change (∑ y, K.outer.weight (eQ₂.symm y) *
    ∑ b, K.apply (fun x a => f (eQ₁ x) (eA₁ a)) (eQ₂.symm y) (eA₂.symm b) ^ 2) = _
  refine Fintype.sum_equiv eQ₂.symm _ _ ?_
  intro y
  congr 1
  exact Fintype.sum_equiv eA₂.symm _ _ (fun _ => rfl)

theorem assignmentEnergy_reindex (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) (labels : R₁ → B₁) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy labels =
      K.assignmentEnergy (fun x => eA₁.symm (labels (eQ₁ x))) := by
  classical
  unfold assignmentEnergy
  rw [energy_reindex]
  congr 1
  funext x a
  unfold assignment
  have h : labels (eQ₁ x) = eA₁ a ↔ eA₁.symm (labels (eQ₁ x)) = a := by
    constructor
    · intro ha
      rw [ha, Equiv.symm_apply_apply]
    · intro ha
      calc
        labels (eQ₁ x) = eA₁ (eA₁.symm (labels (eQ₁ x))) :=
          (eA₁.apply_symm_apply _).symm
        _ = eA₁ a := congrArg eA₁ ha
  rw [h]

/-- No strategy is lost under bijective question and answer encodings. -/
theorem collisionValue_reindex [Nonempty A₁] [Nonempty B₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (eQ₁ : Q₁ ≃ R₁) (eQ₂ : Q₂ ≃ R₂)
    (eA₁ : A₁ ≃ B₁) (eA₂ : A₂ ≃ B₂) :
    (K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue = K.collisionValue := by
  classical
  apply le_antisymm
  · apply ((K.reindex eQ₁ eQ₂ eA₁ eA₂).collisionValue_le_iff _).2
    intro labels
    rw [assignmentEnergy_reindex]
    exact K.assignmentEnergy_le_collisionValue _
  · apply (K.collisionValue_le_iff _).2
    intro labels
    have h := (K.reindex eQ₁ eQ₂ eA₁ eA₂).assignmentEnergy_le_collisionValue
      (fun x => eA₁ (labels (eQ₁.symm x)))
    simpa only [assignmentEnergy_reindex, Equiv.symm_apply_apply] using h

end
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-! A conjunction product cannot have greater classical value than either
factor. The proof freezes the other factor's question pair as a shared random
seed, obtaining ordinary local strategies and then using finite derandomization.
No assertion of independence of success events is used. -/

namespace UniqueGamesTheorem.Repetition

open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace FiniteLaw

variable {Ω Γ : Type*} [Fintype Ω] [Fintype Γ]

theorem probability_product_eq_left_expectation
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (event : Ω × Γ → Bool) :
    (μ.product ν).probability event =
      μ.expectation (fun x => ν.probability (fun y => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.expectation, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : event (x, y) = true <;> simp [h]

theorem probability_product_eq_right_expectation
    (μ : FiniteDistribution Ω) (ν : FiniteDistribution Γ) (event : Ω × Γ → Bool) :
    (μ.product ν).probability event =
      ν.expectation (fun y => μ.probability (fun x => event (x, y))) := by
  simp only [FiniteDistribution.probability, FiniteDistribution.product,
    FiniteDistribution.expectation, Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : event (x, y) = true <;> simp [h, mul_comm]

theorem expectation_mono (μ : FiniteDistribution Ω) {f g : Ω → ℝ}
    (h : ∀ x, f x ≤ g x) : μ.expectation f ≤ μ.expectation g := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (h x) (μ.nonnegative x)

end FiniteLaw

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂]

def leftFactorStrategy
    (s : Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂))
    (r : R₁ × R₂) : Strategy Q₁ Q₂ A₁ A₂ :=
  (fun x => (s.1 (x, r.1)).1, fun y => (s.2 (y, r.2)).1)

def rightFactorStrategy
    (s : Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂))
    (q : Q₁ × Q₂) : Strategy R₁ R₂ B₁ B₂ :=
  (fun x => (s.1 (q.1, x)).2, fun y => (s.2 (q.2, y)).2)

theorem success_product_le_left [Nonempty A₁] [Nonempty A₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (s : Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂)) :
    (product G H).success s ≤ G.value := by
  change ((G.questions.product H.questions).transport productQuestionEquiv).probability _ ≤ _
  rw [FiniteDistribution.probability_transport,
    FiniteLaw.probability_product_eq_right_expectation]
  calc
    _ ≤ H.questions.expectation (fun r => G.success (leftFactorStrategy s r)) := by
      apply FiniteLaw.expectation_mono
      intro r
      apply FiniteDistribution.probability_mono
      intro q h
      exact (Bool.and_eq_true_iff.mp h).1
    _ ≤ G.value := G.randomized_success_le_value H.questions (leftFactorStrategy s)

theorem success_product_le_right [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂)
    (s : Strategy (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂)) :
    (product G H).success s ≤ H.value := by
  change ((G.questions.product H.questions).transport productQuestionEquiv).probability _ ≤ _
  rw [FiniteDistribution.probability_transport,
    FiniteLaw.probability_product_eq_left_expectation]
  calc
    _ ≤ G.questions.expectation (fun q => H.success (rightFactorStrategy s q)) := by
      apply FiniteLaw.expectation_mono
      intro q
      apply FiniteDistribution.probability_mono
      intro r h
      exact (Bool.and_eq_true_iff.mp h).2
    _ ≤ H.value := H.randomized_success_le_value G.questions (rightFactorStrategy s)

theorem product_value_le_min [Nonempty A₁] [Nonempty A₂]
    [Nonempty B₁] [Nonempty B₂]
    (G : Game Q₁ Q₂ A₁ A₂) (H : Game R₁ R₂ B₁ B₂) :
    (product G H).value ≤ min G.value H.value := by
  apply ((product G H).value_le_iff _).2
  intro s
  exact le_min (success_product_le_left G H s) (success_product_le_right G H s)

end
end UniqueGamesTheorem.Repetition

end

section

/-! Comparison of the actual classical game value with the squared collision
norm. Both directions are proved for the normalized conditional kernel, including
partial projection constraints and zero-weight questions. -/

namespace UniqueGamesTheorem.Repetition
open UniqueGamesTheorem.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]

theorem sq_expectation_le_expectation_sq {Ω : Type*} [Fintype Ω]
    (μ : FiniteDistribution Ω) (f : Ω → ℝ) :
    μ.expectation f ^ 2 ≤ μ.expectation (fun x => f x ^ 2) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset Ω))
    (r := fun x => μ.weight x * f x)
    (f := μ.weight) (g := fun x => μ.weight x * f x ^ 2)
    (fun x _ => μ.nonnegative x)
    (fun x _ => mul_nonneg (μ.nonnegative x) (sq_nonneg _))
    (fun x _ => by ring_nf; exact le_rfl)
  simpa only [μ.normalized, one_mul, FiniteDistribution.expectation] using h

theorem apply_assignment_nonneg (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) (b : A₂) :
    0 ≤ K.apply (assignment labels) y b := by
  rw [apply_assignment]
  exact (K.inner y).probability_nonnegative (fun x => K.accepts x y (labels x) b)

/-- The projected distribution has total mass at most one; missing mass is the
possibility that a partial projection rejects the chosen left answer. -/
theorem sum_apply_assignment_le_one (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (y : Q₂) :
    (∑ b, K.apply (assignment labels) y b) ≤ 1 := by
  classical
  simp only [apply_assignment]
  rw [Finset.sum_comm, ← (K.inner y).normalized]
  apply Finset.sum_le_sum
  intro x _
  by_cases hex : ∃ b, K.accepts x y (labels x) b = true
  · obtain ⟨b₀, hb₀⟩ := hex
    have hiff : ∀ b, K.accepts x y (labels x) b = true ↔ b = b₀ := by
      intro b
      constructor
      · intro hb
        exact K.projection x y (labels x) b b₀ hb hb₀
      · rintro rfl
        exact hb₀
    simp only [hiff]
    simp
  · have hnone : ∀ b, K.accepts x y (labels x) b ≠ true := by
      intro b hb
      exact hex ⟨b, hb⟩
    simpa [hnone] using (K.inner y).nonnegative x

theorem success_eq_outer_apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s =
      K.outer.expectation (fun y => K.apply (assignment s.1) y (s.2 y)) := by
  classical
  simp only [Game.success, Game.wins, toGame, FiniteDistribution.probability,
    FiniteDistribution.expectation, apply_assignment, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : K.accepts x y (s.1 x) (s.2 y) = true <;> simp [h]

theorem success_sq_le_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (s : Strategy Q₁ Q₂ A₁ A₂) :
    K.toGame.success s ^ 2 ≤ K.assignmentEnergy s.1 := by
  rw [success_eq_outer_apply]
  calc
    _ ≤ K.outer.expectation
        (fun y => K.apply (assignment s.1) y (s.2 y) ^ 2) :=
      sq_expectation_le_expectation_sq K.outer _
    _ ≤ K.assignmentEnergy s.1 := by
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      exact Finset.single_le_sum (fun b _ => sq_nonneg _) (Finset.mem_univ (s.2 y))

theorem value_sq_le_collisionValue [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.toGame.value ^ 2 ≤ K.collisionValue := by
  obtain ⟨s, hs⟩ := K.toGame.exists_optimal_strategy
  rw [← hs]
  exact (K.success_sq_le_assignmentEnergy s).trans (K.assignmentEnergy_le_collisionValue s.1)

/-- Choose the actual best right answer separately at each right question. -/
theorem exists_best_response [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    ∃ answers : Q₂ → A₂, ∀ y b,
      K.apply (assignment labels) y b ≤ K.apply (assignment labels) y (answers y) := by
  classical
  have h : ∀ y, ∃ b : A₂, ∀ b',
      K.apply (assignment labels) y b' ≤ K.apply (assignment labels) y b := by
    intro y
    obtain ⟨b, _, hb⟩ := Finset.exists_mem_eq_sup'
      (s := (Finset.univ : Finset A₂)) Finset.univ_nonempty
      (fun b => K.apply (assignment labels) y b)
    refine ⟨b, fun b' => ?_⟩
    rw [← hb]
    exact Finset.le_sup' _ (Finset.mem_univ b')
  exact ⟨fun y => Classical.choose (h y), fun y b => Classical.choose_spec (h y) b⟩

theorem assignmentEnergy_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (labels : Q₁ → A₁) :
    K.assignmentEnergy labels ≤ K.toGame.value := by
  obtain ⟨answers, hanswers⟩ := K.exists_best_response labels
  calc
    _ ≤ K.toGame.success (labels, answers) := by
      rw [success_eq_outer_apply]
      apply Finset.sum_le_sum
      intro y _
      apply mul_le_mul_of_nonneg_left _ (K.outer.nonnegative y)
      calc
        _ ≤ ∑ b, K.apply (assignment labels) y b *
            K.apply (assignment labels) y (answers y) := by
          apply Finset.sum_le_sum
          intro b _
          rw [pow_two]
          exact mul_le_mul_of_nonneg_left (hanswers y b)
            (K.apply_assignment_nonneg labels y b)
        _ = (∑ b, K.apply (assignment labels) y b) *
            K.apply (assignment labels) y (answers y) := (Finset.sum_mul _ _ _).symm
        _ ≤ 1 * K.apply (assignment labels) y (answers y) :=
          mul_le_mul_of_nonneg_right (K.sum_apply_assignment_le_one labels y)
            (K.apply_assignment_nonneg labels y (answers y))
        _ = _ := one_mul _
    _ ≤ K.toGame.value := K.toGame.success_le_value _

theorem collisionValue_le_value [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    K.collisionValue ≤ K.toGame.value :=
  (K.collisionValue_le_iff _).mpr K.assignmentEnergy_le_value

theorem collisionValue_le_one [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) : K.collisionValue ≤ 1 :=
  K.collisionValue_le_value.trans K.toGame.value_le_one

end ProjectionKernel
end
end UniqueGamesTheorem.Repetition

end

section

/-!
Determinization of a nonnegative vector with one label chosen per vertex.
Every vertex retains its total mass. The objective is an arbitrary nonnegative
weighted sum of squares of linear functionals, so coefficients may have either
sign. Sampling complete label tables gives the original vector as its mean;
finite variance and an attained maximum then supply a deterministic table.
-/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open UniqueGamesTheorem.Foundations.Games

noncomputable section

variable {V A T : Type*} [Fintype V] [Fintype A] [Fintype T]

/-- The mass at each vertex, before or after determinization. -/
def rowMass (h : V → A → ℝ) (v : V) : ℝ := ∑ a, h v a

/-- Move the full mass of each row to its selected label. -/
def deterministicVector [DecidableEq A] (h : V → A → ℝ) (labels : V → A)
    (v : V) (a : A) : ℝ :=
  if a = labels v then rowMass h v else 0

omit [Fintype V] in
@[simp] theorem deterministicVector_rowMass [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (v : V) :
    rowMass (deterministicVector h labels) v = rowMass h v := by
  simp [rowMass, deterministicVector]

omit [Fintype V] in
theorem rowMass_nonnegative (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a) (v : V) :
    0 ≤ rowMass h v :=
  Finset.sum_nonneg (fun a _ => hh v a)

omit [Fintype V] in
theorem deterministicVector_nonnegative [DecidableEq A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (labels : V → A) (v : V) (a : A) :
    0 ≤ deterministicVector h labels v a := by
  unfold deterministicVector
  split
  · exact rowMass_nonnegative h hh v
  · exact le_rfl

@[simp] theorem deterministicVector_linear_image [DecidableEq A]
    (h : V → A → ℝ) (labels : V → A) (c : V → A → ℝ) :
    (∑ v, ∑ a, c v a * deterministicVector h labels v a) =
      ∑ v, c v (labels v) * rowMass h v := by
  simp [deterministicVector, mul_ite]

omit [Fintype V] in
theorem entry_eq_zero_of_rowMass_eq_zero (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (hz : rowMass h v = 0) (a : A) :
    h v a = 0 := by
  have hle : h v a ≤ rowMass h v :=
    Finset.single_le_sum (fun b _ => hh v b) (Finset.mem_univ a)
  exact le_antisymm (hz ▸ hle) (hh v a)

/-- A zero row is harmless and uses a fixed fallback label. -/
def rowLaw [Nonempty A] (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (v : V) : FiniteDistribution A := by
  classical
  exact if hz : rowMass h v = 0 then
    { weight := fun a => if a = Classical.choice (inferInstance : Nonempty A) then 1 else 0
      nonnegative := fun a => by split <;> norm_num
      normalized := by simp }
  else
    { weight := fun a => h v a / rowMass h v
      nonnegative := fun a => div_nonneg (hh v a) (rowMass_nonnegative h hh v)
      normalized := by
        simp only [div_eq_mul_inv]
        rw [← Finset.sum_mul]
        exact mul_inv_cancel₀ hz }

omit [Fintype V] in
theorem rowLaw_expectation_mul_mass [Nonempty A] (h : V → A → ℝ)
    (hh : ∀ v a, 0 ≤ h v a) (v : V) (f : A → ℝ) :
    (rowLaw h hh v).expectation (fun a => f a * rowMass h v) =
      ∑ a, f a * h v a := by
  classical
  by_cases hz : rowMass h v = 0
  · have he : ∀ a, h v a = 0 := entry_eq_zero_of_rowMass_eq_zero h hh v hz
    simp [FiniteDistribution.expectation, hz, he]
  · simp only [rowLaw, hz, ↓reduceDIte, FiniteDistribution.expectation]
    apply Finset.sum_congr rfl
    intro a _
    field_simp [hz]

/-- Finite Jensen for the square, proved by expanding nonnegative variance. -/
theorem square_expectation_le {Ω : Type*} [Fintype Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    law.expectation f ^ 2 ≤ law.expectation (fun x => f x ^ 2) := by
  let m := law.expectation f
  have h : 0 ≤ law.expectation (fun x => (f x - m) ^ 2) := by
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (law.nonnegative x) (sq_nonneg _)
  have he : law.expectation (fun x => (f x - m) ^ 2) =
      law.expectation (fun x => f x ^ 2) - m ^ 2 := by
    unfold FiniteDistribution.expectation
    calc
      _ = ∑ x, ((law.weight x * f x ^ 2 - 2 * m * (law.weight x * f x)) +
          law.weight x * m ^ 2) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.sum_mul, law.normalized]
        change (law.expectation (fun x => f x ^ 2) - 2 * m * m) + 1 * m ^ 2 = _
        simp only [FiniteDistribution.expectation]
        ring
  rw [he] at h
  dsimp [m] at h
  linarith

theorem exists_expectation_le {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (law : FiniteDistribution Ω) (f : Ω → ℝ) :
    ∃ x, law.expectation f ≤ f x := by
  classical
  let M := Finset.univ.sup' Finset.univ_nonempty f
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset Ω)) Finset.univ_nonempty f
  refine ⟨x, ?_⟩
  calc
    law.expectation f ≤ ∑ y, law.weight y * M := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left
        (Finset.le_sup' f (Finset.mem_univ y)) (law.nonnegative y)
    _ = M := by rw [← Finset.sum_mul, law.normalized, one_mul]
    _ = f x := hx

/-- One label per vertex preserves every row's mass and can only improve the
nonnegative weighted squared image under any fixed linear map. In particular,
the same theorem applies separately at each coordinate of a vector-valued
assignment; no product or independence property of those coordinates is used. -/
theorem exists_deterministic_preserving_mass [Nonempty A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, c t v (labels v) * rowMass h v) ^ 2 := by
  classical
  let law := FiniteDistribution.table (rowLaw h hh)
  let X (t : T) (labels : V → A) : ℝ :=
    ∑ v, c t v (labels v) * rowMass h v
  have hmean (t : T) : law.expectation (X t) = ∑ v, ∑ a, c t v a * h v a := by
    change (∑ labels : V → A, law.weight labels *
      ∑ v, c t v (labels v) * rowMass h v) = _
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    change (FiniteDistribution.table (rowLaw h hh)).expectation
      (fun labels => c t v (labels v) * rowMass h v) = _
    exact (FiniteDistribution.expectation_table_eval (rowLaw h hh) v
      (fun a => c t v a * rowMass h v)).trans
        (rowLaw_expectation_mul_mass h hh v (c t v))
  have hjensen (t : T) : (∑ v, ∑ a, c t v a * h v a) ^ 2 ≤
      law.expectation (fun labels => X t labels ^ 2) := by
    rw [← hmean]
    exact square_expectation_le law (X t)
  have hsum : (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
      ∑ t, w t * law.expectation (fun labels => X t labels ^ 2) := by
    apply Finset.sum_le_sum
    intro t _
    exact mul_le_mul_of_nonneg_left (hjensen t) (hw t)
  have heq : (∑ t, w t * law.expectation (fun labels => X t labels ^ 2)) =
      law.expectation (fun labels => ∑ t, w t * X t labels ^ 2) := by
    unfold FiniteDistribution.expectation
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro labels _
    apply Finset.sum_congr rfl
    intro t _
    ring
  obtain ⟨labels, hlabels⟩ := exists_expectation_le law
    (fun labels => ∑ t, w t * X t labels ^ 2)
  rw [heq] at hsum
  exact ⟨labels, hsum.trans hlabels⟩

/-- The same conclusion stated directly as a deterministic nonnegative vector.
Its row masses are exactly those of the original vector. -/
theorem exists_deterministic_vector [Nonempty A] [DecidableEq A]
    (h : V → A → ℝ) (hh : ∀ v a, 0 ≤ h v a)
    (w : T → ℝ) (hw : ∀ t, 0 ≤ w t) (c : T → V → A → ℝ) :
    ∃ labels : V → A,
      (∀ v a, 0 ≤ deterministicVector h labels v a) ∧
      (∀ v, rowMass (deterministicVector h labels) v = rowMass h v) ∧
      (∑ t, w t * (∑ v, ∑ a, c t v a * h v a) ^ 2) ≤
        ∑ t, w t * (∑ v, ∑ a, c t v a * deterministicVector h labels v a) ^ 2 := by
  obtain ⟨labels, hlabels⟩ := exists_deterministic_preserving_mass h hh w hw c
  refine ⟨labels, deterministicVector_nonnegative h hh labels,
    deterministicVector_rowMass h labels, ?_⟩
  simpa only [deterministicVector_linear_image] using hlabels

end

end UniqueGamesTheorem.Repetition

end

end OAI
