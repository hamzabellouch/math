import Mathlib
import OAI.Computability.DirectedFeedback.Games.SharedSampling

namespace OAI


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
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

def apply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) : ℝ :=
  ∑ x, (K.inner y).weight x * ∑ a, if K.accepts x y a b then f x a else 0

def energy (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Q₁ → A₁ → ℝ) : ℝ :=
  ∑ y, K.outer.weight y * ∑ b, K.apply f y b ^ 2

def assignment (labels : Q₁ → A₁) (x : Q₁) (a : A₁) : ℝ := by
  classical
  exact if labels x = a then 1 else 0

def assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) : ℝ := K.energy (assignment labels)

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
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel

open Foundations.Games
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

abbrev SymmetricEdge (Q₁ Q₂ : Type*) := Q₂ × Q₁ × Q₁

def symmetricLeft (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.1

def symmetricRight (e : SymmetricEdge Q₁ Q₂) : Q₁ := e.2.2

def symmetricDistribution (K : ProjectionKernel Q₁ Q₂ A₁ A₂) :
    FiniteDistribution (SymmetricEdge Q₁ Q₂) where
  weight e := K.outer.weight e.1 * (K.inner e.1).weight e.2.1 *
    (K.inner e.1).weight e.2.2
  nonnegative e := mul_nonneg
    (mul_nonneg (K.outer.nonnegative _) ((K.inner _).nonnegative _))
    ((K.inner _).nonnegative _)
  normalized := by
    rw [Fintype.sum_prod_type]
    calc
      _ = ∑ y, K.outer.weight y := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Fintype.sum_prod_type]
        calc
          _ = ∑ x, K.outer.weight y * (K.inner y).weight x := by
            apply Finset.sum_congr rfl
            intro x _
            dsimp only
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
          _ = K.outer.weight y := by
            rw [← Finset.mul_sum, (K.inner y).normalized, mul_one]
      _ = 1 := K.outer.normalized

def symmetricAccept (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (e : SymmetricEdge Q₁ Q₂) (a a' : A₁) : Bool := by
  classical
  exact decide (∃ b, K.accepts e.2.1 e.1 a b = true ∧
    K.accepts e.2.2 e.1 a' b = true)

def singleLabelVector (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ)
    (ω : Ω) (x : Q₁) (b : A₁) : ℝ := by
  classical
  exact if a x ω = b then f x ω else 0

theorem sum_projection_gates (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (x x' : Q₁) (a a' : A₁) (r s : ℝ) :
    (∑ b, (if K.accepts x y a b then r else 0) *
      (if K.accepts x' y a' b then s else 0)) =
        if K.symmetricAccept (y, x, x') a a' then r * s else 0 := by
  classical
  by_cases hex : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true
  · obtain ⟨b₀, hb₀, hb₀'⟩ := hex
    have hex' : ∃ b, K.accepts x y a b = true ∧ K.accepts x' y a' b = true :=
      ⟨b₀, hb₀, hb₀'⟩
    simp only [symmetricAccept, hex', decide_true, ite_true]
    calc
      _ = (if K.accepts x y a b₀ then r else 0) *
          (if K.accepts x' y a' b₀ then s else 0) := by
        apply Finset.sum_eq_single b₀
        · intro b _ hne
          have hb : K.accepts x y a b ≠ true := by
            intro hb
            exact hne (K.projection x y a b b₀ hb hb₀)
          simp [hb]
        · simp
      _ = r * s := by simp [hb₀, hb₀']
  · simp only [symmetricAccept, hex, decide_false, Bool.false_eq_true, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : K.accepts x y a b = true
    · have hb' : K.accepts x' y a' b ≠ true := fun hb' => hex ⟨b, hb, hb'⟩
      simp [hb']
    · simp [hb]

theorem apply_single_label (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (f : Q₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => if labels x = a then f x else 0) y b =
      ∑ x, (K.inner y).weight x * (if K.accepts x y (labels x) b then f x else 0) := by
  classical
  unfold apply
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  calc
    _ = ∑ a, if labels x = a then
        (if K.accepts x y (labels x) b then f x else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : labels x = a
      · subst a
        simp
      · simp [ha]
    _ = _ := by simp

theorem energy_single_label (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) (f : Q₁ → ℝ) :
    K.energy (fun x a => if labels x = a then f x else 0) =
      K.symmetricDistribution.expectation (fun e =>
        if K.symmetricAccept e (labels (symmetricLeft e)) (labels (symmetricRight e))
          then f (symmetricLeft e) * f (symmetricRight e) else 0) := by
  classical
  have hexpand (y : Q₂) :
      (∑ b, (∑ x, (K.inner y).weight x *
        (if K.accepts x y (labels x) b then f x else 0)) ^ 2) =
      ∑ x, ∑ x', (K.inner y).weight x * (K.inner y).weight x' *
        (if K.symmetricAccept (y, x, x') (labels x) (labels x')
          then f x * f x' else 0) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x' _
    calc
      _ = (K.inner y).weight x * (K.inner y).weight x' *
          ∑ b, (if K.accepts x y (labels x) b then f x else 0) *
            (if K.accepts x' y (labels x') b then f x' else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [K.sum_projection_gates]
  unfold energy
  simp_rw [K.apply_single_label, hexpand]
  simp only [FiniteDistribution.expectation, symmetricDistribution,
    Fintype.sum_prod_type, symmetricLeft, symmetricRight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  simp only [mul_assoc]
  rfl

theorem vectorEnergy_singleLabelVector (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (a : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ) :
    K.vectorEnergy (singleLabelVector a f) =
      pairEnergy K.symmetricDistribution symmetricLeft symmetricRight K.symmetricAccept a f := by
  classical
  unfold vectorEnergy singleLabelVector
  simp_rw [K.energy_single_label]
  unfold pairEnergy FiniteDistribution.expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]

theorem symmetric_probability_eq_assignmentEnergy (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (labels : Q₁ → A₁) :
    K.symmetricDistribution.probability (fun e =>
      K.symmetricAccept e (labels (symmetricLeft e)) (labels (symmetricRight e))) =
        K.assignmentEnergy labels := by
  classical
  change _ = K.energy (fun x a => if labels x = a then (1 : ℝ) else 0)
  rw [K.energy_single_label]
  simp only [FiniteDistribution.probability, FiniteDistribution.expectation,
    mul_ite, mul_one, mul_zero]

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

def linearCoefficient (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (t : Q₂ × A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner t.1).weight x * (if K.accepts x t.1 a t.2 then 1 else 0)

theorem apply_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply h y b = ∑ x, ∑ a, K.linearCoefficient (y, b) x a * h x a := by
  unfold apply
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : K.accepts x y a b = true <;> simp [linearCoefficient, ha]

theorem energy_eq_linearCoefficient_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) :
    K.energy h = ∑ t : Q₂ × A₂, K.outer.weight t.1 *
      (∑ x, ∑ a, K.linearCoefficient t x a * h x a) ^ 2 := by
  rw [Fintype.sum_prod_type]
  simp_rw [← K.apply_eq_linearCoefficient_sum, ← Finset.mul_sum]
  rfl

theorem exists_energy_le_deterministicVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Q₁ → A₁ → ℝ) (hh : ∀ x a, 0 ≤ h x a) :
    ∃ labels : Q₁ → A₁,
      K.energy h ≤ K.energy (deterministicVector h labels) := by
  classical
  obtain ⟨labels, _, _, hlabels⟩ := exists_deterministic_vector h hh
    (fun t : Q₂ × A₂ => K.outer.weight t.1)
    (fun t => K.outer.nonnegative t.1) K.linearCoefficient
  refine ⟨labels, ?_⟩
  rw [K.energy_eq_linearCoefficient_sum, K.energy_eq_linearCoefficient_sum]
  exact hlabels

def vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) (ω : Ω) : ℝ :=
  rowMass (h ω) x

omit [Fintype Ω] in
omit [Fintype Q₁] in
theorem vectorAmplitude_nonnegative (h : Ω → Q₁ → A₁ → ℝ)
    (hh : ∀ ω x a, 0 ≤ h ω x a) (x : Q₁) (ω : Ω) :
    0 ≤ vectorAmplitude h x ω :=
  rowMass_nonnegative (h ω) (hh ω) x

omit [Fintype Q₁] in
@[simp] theorem rowSquareMass_vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) :
    rowSquareMass (vectorAmplitude h) x = vectorMass h x := rfl

theorem exists_vectorEnergy_le_singleLabelVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Ω → Q₁ → A₁ → ℝ) (hh : ∀ ω x a, 0 ≤ h ω x a) :
    ∃ labels : Q₁ → Ω → A₁,
      K.vectorEnergy h ≤ K.vectorEnergy (singleLabelVector labels (vectorAmplitude h)) := by
  classical
  have hex (ω : Ω) := K.exists_energy_le_deterministicVector (h ω) (hh ω)
  let labels (ω : Ω) : Q₁ → A₁ := Classical.choose (hex ω)
  have hlabels (ω : Ω) : K.energy (h ω) ≤
      K.energy (deterministicVector (h ω) (labels ω)) := Classical.choose_spec (hex ω)
  refine ⟨fun x ω => labels ω x, ?_⟩
  apply Finset.sum_le_sum
  intro ω _
  have heq : deterministicVector (h ω) (labels ω) =
      singleLabelVector (fun x ω => labels ω x) (vectorAmplitude h) ω := by
    funext x a
    by_cases ha : a = labels ω x
    · simp [deterministicVector, singleLabelVector, vectorAmplitude, ha]
    · simp [deterministicVector, singleLabelVector, ha, Ne.symm ha]
  exact heq ▸ hlabels ω

theorem exists_mass_preserving_singleLabelVector [Nonempty A₁]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (h : Ω → Q₁ → A₁ → ℝ) (hh : ∀ ω x a, 0 ≤ h ω x a) :
    ∃ (labels : Q₁ → Ω → A₁) (f : Q₁ → Ω → ℝ),
      (∀ x ω, 0 ≤ f x ω) ∧
      (∀ x, rowSquareMass f x = vectorMass h x) ∧
      K.vectorEnergy h ≤ K.vectorEnergy (singleLabelVector labels f) := by
  obtain ⟨labels, hlabels⟩ := K.exists_vectorEnergy_le_singleLabelVector h hh
  exact ⟨labels, vectorAmplitude h, vectorAmplitude_nonnegative h hh,
    rowSquareMass_vectorAmplitude h, hlabels⟩

end

end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
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
end DFVSGames.Repetition


namespace DFVSGames.Repetition.ProjectionKernel

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

private theorem distribution_nonempty_inline_RoundingKernel {T : Type*} [Fintype T]
    (μ : FiniteDistribution T) : Nonempty T := by
  by_contra h
  have : IsEmpty T := not_nonempty_iff.mp h
  have hz : (∑ t, μ.weight t) = 0 := by simp
  linarith [μ.normalized]

theorem vectorEnergy_le_gap_rate [Nonempty A₁] [Nonempty A₂]
    (K : ProjectionKernel Q₁ Q₂ A₁ A₂) (f : Ω → Q₁ → A₁ → ℝ)
    (hf : ∀ ω x a, 0 ≤ f ω x a) (hmass : ∀ x, vectorMass f x ≤ 1)
    {g : ℝ} (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hvalue : K.toGame.value ≤ 1 - g) :
    K.vectorEnergy f ≤ 1 - g ^ 2 / 8 := by
  classical
  let : Nonempty Q₂ := distribution_nonempty_inline_RoundingKernel K.outer
  let : Nonempty Q₁ := distribution_nonempty_inline_RoundingKernel
    (K.inner (Classical.choice (inferInstance : Nonempty Q₂)))
  rcases isEmpty_or_nonempty Ω with hΩ | hΩ
  · let : IsEmpty Ω := hΩ
    have hzero : K.vectorEnergy f = 0 := by simp [vectorEnergy]
    rw [hzero]
    have hsq : g * g ≤ (1 : ℝ) * 1 := mul_le_mul hg1 hg1 hg0 (by norm_num)
    nlinarith
  · let : Nonempty Ω := hΩ
    obtain ⟨labels, hdet⟩ := K.exists_vectorEnergy_le_singleLabelVector f hf
    have hnonneg := vectorAmplitude_nonnegative f hf
    have hrow : ∀ x, rowSquareMass (vectorAmplitude f) x ≤ 1 := by
      intro x
      rw [rowSquareMass_vectorAmplitude]
      exact hmass x
    rw [K.vectorEnergy_singleLabelVector] at hdet
    by_cases hg : g = 0
    · subst g
      simp only [zero_pow (by decide : 2 ≠ 0), zero_div, sub_zero]
      let fallback : A₁ := Classical.choice inferInstance
      have hpad := pairEnergy_le_padded K.symmetricDistribution symmetricLeft
        symmetricRight K.symmetricAccept labels (vectorAmplitude f) hnonneg fallback
      have hone := pairEnergy_le_one_of_unit_rows K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept
        (paddedLabel labels fallback) (paddedAmplitude (vectorAmplitude f))
        (paddedAmplitude_row (vectorAmplitude f) hrow)
      exact hdet.trans (hpad.trans hone)
    · have hgpos : 0 < g := lt_of_le_of_ne hg0 (Ne.symm hg)
      have hscore (a : Q₁ → A₁) :
          partialLabelScore K.symmetricDistribution symmetricLeft symmetricRight
            K.symmetricAccept a ≤ 1 - g := by
        unfold partialLabelScore
        rw [K.symmetric_probability_eq_assignmentEnergy]
        exact (K.assignmentEnergy_le_collisionValue a).trans
          (K.collisionValue_le_value.trans hvalue)
      exact hdet.trans (pairEnergy_le_of_labeling_gap K.symmetricDistribution
        symmetricLeft symmetricRight K.symmetricAccept labels (vectorAmplitude f)
        hnonneg hrow hgpos hscore)

end
end DFVSGames.Repetition.ProjectionKernel


namespace DFVSGames.Repetition

open scoped BigOperators

noncomputable section

variable {X A Y B U D Z C I : Type*}
  [Fintype X] [Fintype A] [Fintype U] [Fintype D] [Fintype I]

def kernelApply (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (y : Y) (b : B) : ℝ :=
  ∑ x, ∑ a, K y b x a * f x a

def tensorKernel (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (yz : Y × Z) (bc : B × C) (xu : X × U) (ad : A × D) : ℝ :=
  K yz.1 bc.1 xu.1 ad.1 * L yz.2 bc.2 xu.2 ad.2

theorem kernelApply_tensor
    (K : Y → B → X → A → ℝ) (L : Z → C → U → D → ℝ)
    (f : (X × U) → (A × D) → ℝ) (y : Y) (z : Z) (b : B) (c : C) :
    kernelApply (tensorKernel K L) f (y,z) (b,c) =
      kernelApply K (fun x a => kernelApply L (fun u d => f (x,u) (a,d)) z c) y b := by
  classical
  simp only [kernelApply, tensorKernel, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Finset.mul_sum, mul_assoc]

theorem kernelApply_nonnegative
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ)
    (hK : ∀ y b x a, 0 ≤ K y b x a) (hf : ∀ x a, 0 ≤ f x a)
    (y : Y) (b : B) : 0 ≤ kernelApply K f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (hK y b x a) (hf x a)

theorem kernelApply_sum
    (K : Y → B → X → A → ℝ) (f : I → X → A → ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => ∑ i, f i x a) y b =
      ∑ i, kernelApply K (f i) y b := by
  classical
  simp only [kernelApply, Finset.mul_sum]
  calc
    (∑ x, ∑ a, ∑ i, K y b x a * f i x a) =
        ∑ x, ∑ i, ∑ a, K y b x a * f i x a := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by rw [Finset.sum_comm]

theorem kernelApply_smul
    (K : Y → B → X → A → ℝ) (f : X → A → ℝ) (r : ℝ) (y : Y) (b : B) :
    kernelApply K (fun x a => r * f x a) y b = r * kernelApply K f y b := by
  simp only [kernelApply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro a _
  exact mul_left_comm _ _ _

omit [Fintype X] in

theorem kernelApply_slice_mass
    (L : Z → C → U → D → ℝ) (f : (X × U) → (A × D) → ℝ)
    (x : X) (z : Z) (c : C) :
    (∑ a, kernelApply L (fun u d => f (x,u) (a,d)) z c) =
      kernelApply L (fun u d => ∑ a, f (x,u) (a,d)) z c := by
  symm
  exact kernelApply_sum L (fun a u d => f (x,u) (a,d)) z c

end
end DFVSGames.Repetition


namespace DFVSGames.Repetition
open DFVSGames.Foundations.Games
open scoped BigOperators
noncomputable section

namespace ProjectionKernel

variable {Q₁ Q₂ A₁ A₂ R₁ R₂ B₁ B₂ I : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂]
  [Fintype R₁] [Fintype R₂] [Fintype B₁] [Fintype B₂] [Fintype I]

def coefficients (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (y : Q₂) (b : A₂) (x : Q₁) (a : A₁) : ℝ :=
  (K.inner y).weight x * if K.accepts x y a b then 1 else 0

theorem apply_eq_kernelApply (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply f y b = kernelApply K.coefficients f y b := by
  classical
  unfold apply kernelApply coefficients
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : K.accepts x y a b = true <;> simp [h]

theorem apply_nonnegative (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (hf : ∀ x a, 0 ≤ f x a) (y : Q₂) (b : A₂) :
    0 ≤ K.apply f y b := by
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg ((K.inner y).nonnegative x)
  apply Finset.sum_nonneg
  intro a _
  split
  · exact hf x a
  · exact le_rfl

theorem apply_sum (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : I → Q₁ → A₁ → ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => ∑ i, f i x a) y b = ∑ i, K.apply (f i) y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_sum _ _ _ _

theorem apply_smul (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (f : Q₁ → A₁ → ℝ) (r : ℝ) (y : Q₂) (b : A₂) :
    K.apply (fun x a => r * f x a) y b = r * K.apply f y b := by
  simp_rw [apply_eq_kernelApply]
  exact kernelApply_smul _ _ _ _ _

def product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    ProjectionKernel (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂) where
  outer := K.outer.product H.outer
  inner q := (K.inner q.1).product (H.inner q.2)
  accepts x y a b := K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2
  projection x y a b b' hb hb' := by
    have h₁ := Bool.and_eq_true_iff.mp hb
    have h₂ := Bool.and_eq_true_iff.mp hb'
    exact Prod.ext (K.projection _ _ _ _ _ h₁.1 h₂.1)
      (H.projection _ _ _ _ _ h₁.2 h₂.2)

theorem coefficients_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).coefficients = tensorKernel K.coefficients H.coefficients := by
  funext yz bc xu ad
  unfold coefficients product tensorKernel FiniteDistribution.product
  by_cases hk : K.accepts xu.1 yz.1 ad.1 bc.1 = true <;>
    by_cases hh : H.accepts xu.2 yz.2 ad.2 bc.2 = true <;> simp [hk, hh]

theorem apply_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂)
    (f : (Q₁ × R₁) → (A₁ × B₁) → ℝ)
    (y : Q₂) (z : R₂) (b : A₂) (c : B₂) :
    (K.product H).apply f (y,z) (b,c) =
      K.apply (fun x a => H.apply (fun u d => f (x,u) (a,d)) z c) y b := by
  simp_rw [apply_eq_kernelApply]
  rw [coefficients_product]
  exact kernelApply_tensor _ _ _ _ _ _ _

theorem toGame_product (K : ProjectionKernel Q₁ Q₂ A₁ A₂)
    (H : ProjectionKernel R₁ R₂ B₁ B₂) :
    (K.product H).toGame = DFVSGames.Repetition.product K.toGame H.toGame := by
  have hquestions : (K.product H).toGame.questions =
      (DFVSGames.Repetition.product K.toGame H.toGame).questions := by
    apply FiniteDistribution.eq_of_weight_eq
    intro q
    change (K.outer.weight q.2.1 * H.outer.weight q.2.2) *
      ((K.inner q.2.1).weight q.1.1 * (H.inner q.2.2).weight q.1.2) =
      (K.outer.weight q.2.1 * (K.inner q.2.1).weight q.1.1) *
        (H.outer.weight q.2.2 * (H.inner q.2.2).weight q.1.2)
    ring
  exact congrArg
    (fun questions : FiniteDistribution ((Q₁ × R₁) × (Q₂ × R₂)) =>
      ({ questions := questions
         accepts := fun x y a b =>
           K.accepts x.1 y.1 a.1 b.1 && H.accepts x.2 y.2 a.2 b.2 } :
        Game (Q₁ × R₁) (Q₂ × R₂) (A₁ × B₁) (A₂ × B₂))) hquestions

end ProjectionKernel
end
end DFVSGames.Repetition

end OAI
