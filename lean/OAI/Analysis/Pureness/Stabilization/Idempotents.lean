import OAI.Analysis.Pureness.Stabilization.Weights

namespace OAI
noncomputable section
open scoped ENNReal
namespace CuntzTrace

theorem ennreal_add_self_eq_iff (r : ℝ≥0∞) : r + r = r ↔ r = 0 ∨ r = ∞ := by
  constructor
  · intro h
    by_cases ht : r = ∞
    · exact Or.inr ht
    · left
      by_contra hz
      exact (ENNReal.lt_add_right ht hz).ne h.symm
  · rintro (rfl | rfl) <;> simp

def idealIndicator {α : Type*} (I : Set α) (a : α) : ℝ≥0∞ :=
  @ite _ (a ∈ I) (Classical.propDecidable _) 0 ∞

@[simp] theorem idealIndicator_eq_zero {α : Type*} (I : Set α) (a : α) :
    idealIndicator I a = 0 ↔ a ∈ I := by
  classical
  simp [idealIndicator]

theorem idealIndicator_add_eq_iff {α : Type*} (I J : Set α) :
    (fun a => idealIndicator I a + idealIndicator J a) = idealIndicator I ↔ I ⊆ J := by
  classical
  constructor
  · intro h a ha
    have := congrFun h a
    simpa [idealIndicator, ha] using this
  · intro h
    funext a
    by_cases ha : a ∈ I
    · simp [idealIndicator, ha, h ha]
    · simp [idealIndicator, ha]

theorem idempotent_function_iff_indicator {α : Type*} (f : α → ℝ≥0∞) :
    (∀ a, f a + f a = f a) ↔ f = idealIndicator {a | f a = 0} := by
  classical
  constructor
  · intro h
    funext a
    rcases (ennreal_add_self_eq_iff (f a)).mp (h a) with hz | ht
    · simp [idealIndicator, hz]
    · simp [idealIndicator, ht]
  · intro h a
    rw [h]
    simp only [idealIndicator]
    split <;> simp

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
namespace ExtendedTrace

theorem isClosed_zeroSet (τ : ExtendedTrace A) : IsClosed {a | τ a = 0} := by
  simpa only [Set.preimage, Set.mem_Iic, nonpos_iff_eq_zero] using
    τ.lowerSemicontinuous.isClosed_preimage 0

theorem idempotent_iff_zero_or_top (τ : ExtendedTrace A) :
    (∀ a, τ a + τ a = τ a) ↔ ∀ a, τ a = 0 ∨ τ a = ∞ := by
  simp only [ennreal_add_self_eq_iff]

theorem idempotent_eq_indicator (τ : ExtendedTrace A)
    (h : ∀ a, τ a + τ a = τ a) :
    (fun a => τ a) = idealIndicator {a | τ a = 0} :=
  (idempotent_function_iff_indicator _).mp h

end ExtendedTrace
end CuntzTrace

end

end OAI
