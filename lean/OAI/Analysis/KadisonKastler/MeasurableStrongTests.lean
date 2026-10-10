import OAI.Analysis.KadisonKastler.CountableStrongMembership
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

namespace OAI

/-! # Measurability of countable strong approximation conditions

Only vector evaluation is required to be measurable. Countable tests
then give a measurable implementer condition without placing the norm
topology on the operator algebra.
-/

namespace KadisonKastler

open MeasureTheory

noncomputable section

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H]

def PrefixStrongTests (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H) (p : X) : Prop :=
  ∀ m k : ℕ, ∃ q : ℕ, ∀ l ≤ m, ‖(T p - S p q) (ξ l)‖ < 1 / (k + 1 : ℝ)

omit [MeasurableSpace X] [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] in
theorem prefixStrongTests_iff (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H) (p : X) :
    PrefixStrongTests ξ T S p ↔ CountableStrongTests ξ (Set.range (S p)) (T p) := by
  constructor
  · intro h m k
    obtain ⟨q, hq⟩ := h m k
    exact ⟨S p q, ⟨q, rfl⟩, hq⟩
  · intro h m k
    obtain ⟨a, ⟨q, rfl⟩, ha⟩ := h m k
    exact ⟨q, ha⟩

omit [CompleteSpace H] in
/-- Every condition is a countable combination of measurable vector-norm
inequalities. The operator maps need not be norm measurable. -/
theorem measurableSet_prefixStrongTests (ξ : ℕ → H) (T : X → H →L[ℂ] H)
    (S : X → ℕ → H →L[ℂ] H)
    (h : ∀ q l, Measurable (fun p => (T p - S p q) (ξ l))) :
    MeasurableSet {p | PrefixStrongTests ξ T S p} := by
  simp only [PrefixStrongTests, Set.ofPred_forall, Set.ofPred_exists]
  apply MeasurableSet.iInter
  intro m
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iUnion
  intro q
  apply MeasurableSet.iInter
  intro l
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_lt (h q l).norm measurable_const

omit [CompleteSpace H] in
theorem measurableSet_countableStrongTests_range
    (ξ : ℕ → H) (T : X → H →L[ℂ] H) (S : X → ℕ → H →L[ℂ] H)
    (h : ∀ q l, Measurable (fun p => (T p - S p q) (ξ l))) :
    MeasurableSet {p | CountableStrongTests ξ (Set.range (S p)) (T p)} := by
  simpa only [← prefixStrongTests_iff] using measurableSet_prefixStrongTests ξ T S h

omit [CompleteSpace H] in
/-- An operator norm bound is a countable measurable condition when
evaluations on a dense vector family are measurable. -/
theorem measurableSet_operator_norm_le (ξ : ℕ → H) (hξ : DenseRange ξ)
    (T : X → H →L[ℂ] H) {a : ℝ} (ha : 0 ≤ a)
    (hT : ∀ n, Measurable (fun p => T p (ξ n))) :
    MeasurableSet {p | ‖T p‖ ≤ a} := by
  have heq : {p | ‖T p‖ ≤ a} = ⋂ n : ℕ, {p | ‖T p (ξ n)‖ ≤ a * ‖ξ n‖} := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, norm_le_iff_dense_vector_tests ξ hξ _ ha]
  rw [heq]
  exact MeasurableSet.iInter fun n => measurableSet_le (hT n).norm measurable_const

end

end KadisonKastler

end OAI
