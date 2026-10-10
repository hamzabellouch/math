import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Sum
import OAI.Computability.UniqueGames.Foundations.FiniteTrialsLemmas
import OAI.Computability.UniqueGames.Repetition.AnalyticCheegerLemmas
import OAI.Computability.UniqueGames.Repetition.CollisionLemmas

namespace OAI

section

/-! Finite vertex-specific padding of nonnegative vectors to unit squared row
mass. The new coordinates can only increase any nonnegative relation energy. -/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

def rowSquareMass (f : V → Ω → ℝ) (v : V) : ℝ := ∑ ω, (f v ω) ^ 2

def paddedAmplitude [DecidableEq V] (f : V → Ω → ℝ) (v : V) : Ω ⊕ V → ℝ
  | Sum.inl ω => f v ω
  | Sum.inr w => if v = w then Real.sqrt (1 - rowSquareMass f v) else 0

def paddedLabel (a : V → Ω → A) (fallback : A) (v : V) : Ω ⊕ V → A
  | Sum.inl ω => a v ω
  | Sum.inr _ => fallback

omit [Fintype V] in
theorem paddedAmplitude_nonnegative [DecidableEq V] (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (v : V) (ω : Ω ⊕ V) :
    0 ≤ paddedAmplitude f v ω := by
  cases ω with
  | inl ω => exact hf v ω
  | inr w =>
      simp only [paddedAmplitude]
      split
      · exact Real.sqrt_nonneg _
      · exact le_rfl

theorem paddedAmplitude_row [DecidableEq V] (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v ≤ 1) (v : V) :
    rowSquareMass (paddedAmplitude f) v = 1 := by
  have hs : Real.sqrt (1 - rowSquareMass f v) ^ 2 = 1 - rowSquareMass f v :=
    Real.sq_sqrt (sub_nonneg.mpr (hrow v))
  simp only [rowSquareMass] at hs
  simp only [rowSquareMass, Fintype.sum_sum_type, paddedAmplitude]
  simp only [ite_pow, zero_pow (by decide : 2 ≠ 0)]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ v), hs]
  ring

def pairEnergy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then f (left e) ω * f (right e) ω else 0

def pairOverlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) : ℝ :=
  ν.expectation fun e => ∑ ω,
    if R e (a (left e) ω) (a (right e) ω)
      then min ((f (left e) ω) ^ 2) ((f (right e) ω) ^ 2) else 0

omit [Fintype V] in
theorem pairEnergy_nonnegative (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) : 0 ≤ pairEnergy ν left right R a f := by
  apply Finset.sum_nonneg
  intro e _
  apply mul_nonneg (ν.nonnegative e)
  apply Finset.sum_nonneg
  intro ω _
  split
  · exact mul_nonneg (hf (left e) ω) (hf (right e) ω)
  · exact le_rfl

theorem pairEnergy_le_padded [DecidableEq V] (ν : FiniteDistribution E)
    (left right : E → V) (R : E → A → A → Bool)
    (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (fallback : A) :
    pairEnergy ν left right R a f ≤
      pairEnergy ν left right R (paddedLabel a fallback) (paddedAmplitude f) := by
  unfold pairEnergy FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro e _
  apply mul_le_mul_of_nonneg_left _ (ν.nonnegative e)
  dsimp only
  rw [Fintype.sum_sum_type]
  simp only [paddedLabel, paddedAmplitude]
  have hnonneg : 0 ≤ ∑ w : V,
      if R e fallback fallback then
        (if left e = w then Real.sqrt (1 - rowSquareMass f (left e)) else 0) *
          (if right e = w then Real.sqrt (1 - rowSquareMass f (right e)) else 0)
      else 0 := by
    apply Finset.sum_nonneg
    intro w _
    split
    · exact mul_nonneg (paddedAmplitude_nonnegative f hf (left e) (Sum.inr w))
        (paddedAmplitude_nonnegative f hf (right e) (Sum.inr w))
    · exact le_rfl
  exact le_add_of_nonneg_right hnonneg

end
end UniqueGamesTheorem.Repetition

end

section

/-! Flatten the genuine finite occurrence law together with the auxiliary
coordinate into the Cheeger inequality. The occurrence may retain hidden
information; both endpoint label tables still depend only on their vertex. -/

namespace UniqueGamesTheorem.Repetition

open scoped BigOperators
open Foundations.Games

noncomputable section

variable {V A Ω E : Type*} [Fintype V] [Fintype Ω] [Fintype E]

omit [Fintype V] in
theorem pairQuadraticMass_eq_one (ν : FiniteDistribution E) (left right : E → V)
    (f : V → Ω → ℝ) (hrow : ∀ v, rowSquareMass f v = 1) :
    Analytic.quadraticMass (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2) = 1 := by
  unfold Analytic.quadraticMass
  rw [Fintype.sum_prod_type]
  have he (e : E) :
      (∑ ω, ν.weight e * ((f (left e) ω) ^ 2 + (f (right e) ω) ^ 2) / 2) =
        ν.weight e := by
    calc
      _ = ν.weight e *
          ((∑ ω, (f (left e) ω) ^ 2) + (∑ ω, (f (right e) ω) ^ 2)) / 2 := by
        simp only [div_eq_mul_inv, mul_add, add_mul, Finset.sum_add_distrib,
          Finset.mul_sum, Finset.sum_mul]
      _ = ν.weight e := by
        change ν.weight e * (rowSquareMass f (left e) + rowSquareMass f (right e)) / 2 = _
        rw [hrow, hrow]
        ring
  simp_rw [he]
  exact ν.normalized

omit [Fintype V] in
theorem pairGatedCorrelation_eq_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedCorrelation (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairEnergy ν left right R a f := by
  simp only [Analytic.gatedCorrelation, pairEnergy, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero, mul_assoc]

omit [Fintype V] in
theorem pairGatedMinimum_eq_overlap (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ) :
    Analytic.gatedMinimum (fun p : E × Ω => ν.weight p.1)
      (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
      (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2)) =
      pairOverlap ν left right R a f := by
  simp only [Analytic.gatedMinimum, pairOverlap, FiniteDistribution.expectation,
    Fintype.sum_prod_type, Finset.mul_sum, mul_ite, mul_zero]

omit [Fintype V] in
theorem pairEnergy_le_one_of_unit_rows (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hrow : ∀ v, rowSquareMass f v = 1) : pairEnergy ν left right R a f ≤ 1 := by
  have h := Analytic.gatedCorrelation_le_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1)
  rw [pairGatedCorrelation_eq_energy, pairQuadraticMass_eq_one ν left right f hrow] at h
  exact h

omit [Fintype V] in
/-- The overlap used by finite threshold sampling is large whenever the
actual weighted occurrence energy is large. -/
theorem pairOverlap_ge_energy (ν : FiniteDistribution E) (left right : E → V)
    (R : E → A → A → Bool) (a : V → Ω → A) (f : V → Ω → ℝ)
    (hf : ∀ v ω, 0 ≤ f v ω) (hrow : ∀ v, rowSquareMass f v = 1) :
    1 - Real.sqrt (2 * (1 - pairEnergy ν left right R a f)) ≤
      pairOverlap ν left right R a f := by
  have h := Analytic.gatedMinimum_unit_mass (fun p : E × Ω => ν.weight p.1)
    (fun p => f (left p.1) p.2) (fun p => f (right p.1) p.2)
    (fun p => R p.1 (a (left p.1) p.2) (a (right p.1) p.2))
    (fun p => ν.nonnegative p.1) (fun p => hf (left p.1) p.2)
    (fun p => hf (right p.1) p.2) (pairQuadraticMass_eq_one ν left right f hrow)
  rw [pairGatedCorrelation_eq_energy, pairGatedMinimum_eq_overlap] at h
  exact h

end
end UniqueGamesTheorem.Repetition

end

section

/-!
The collision norm as an actual finite distribution on symmetrized edges.
An edge retains the hidden common right question, while each label remains a
function of its own left question.  Projection uniqueness turns the sum over
common right answers into a Boolean compatibility predicate exactly.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

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

/-- A coordinate has one possible nonzero label at each question. -/
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

/-- Coordinate expansion and the symmetrized edge law agree exactly. -/
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

/-- Ordinary deterministic labelings give the collision assignment energy. -/
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
end UniqueGamesTheorem.Repetition.ProjectionKernel

end

section

/-!
Apply finite positive-vector determinization to the actual projection kernel.
The target coordinates retain both the right question and the right answer.
The selected label may depend on the auxiliary coordinate, but only on its own
left question. Every question's squared vector mass is preserved exactly.
-/

namespace UniqueGamesTheorem.Repetition.ProjectionKernel

open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable {Q₁ Q₂ A₁ A₂ Ω : Type*}
  [Fintype Q₁] [Fintype Q₂] [Fintype A₁] [Fintype A₂] [Fintype Ω]

/-- Explicit matrix coefficients of the projection operator. -/
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

/-- Scalar kernel determinization preserves the whole mass at every question. -/
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

/-- The amplitude at a question is the sum of its original label entries. -/
def vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) (ω : Ω) : ℝ :=
  rowMass (h ω) x

omit [Fintype Q₁] [Fintype Ω] in
theorem vectorAmplitude_nonnegative (h : Ω → Q₁ → A₁ → ℝ)
    (hh : ∀ ω x a, 0 ≤ h ω x a) (x : Q₁) (ω : Ω) :
    0 ≤ vectorAmplitude h x ω :=
  rowMass_nonnegative (h ω) (hh ω) x

omit [Fintype Q₁] in
@[simp] theorem rowSquareMass_vectorAmplitude (h : Ω → Q₁ → A₁ → ℝ) (x : Q₁) :
    rowSquareMass (vectorAmplitude h) x = vectorMass h x := rfl

/-- Auxiliary coordinates are determinized separately; they need not be
independent, normalized, or nonempty. -/
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

/-- Package the deterministic labels, amplitudes, exact mass preservation, and
energy inequality for use by the finite threshold-rounding construction. -/
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

end UniqueGamesTheorem.Repetition.ProjectionKernel

end

end OAI
