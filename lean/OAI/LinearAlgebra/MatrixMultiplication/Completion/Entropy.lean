import OAI.LinearAlgebra.MatrixMultiplication.Completion.Conditioning

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLaws

open MatrixMultiplication.Foundation
open scoped BigOperators
attribute [local instance 10000] Classical.propDecidable Classical.decEq

variable {A : Type*} [Fintype A]

theorem entropy_scaled_law (p : FiniteLaw A) (s : ℝ) :
    finiteEntropy (fun a => s * p.mass a) = entropyTerm s + s * finiteEntropy p.mass := by
  simp only [finiteEntropy, entropyTerm_mul, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, p.total, one_mul]

theorem mass_eq_event_mul_condition (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) (a : {a // P a}) :
    p.mass a.val = eventMass p P * (condition p P h).mass a := by
  rw [condition_mass, mul_div_cancel₀ _ h.ne']

theorem event_entropy (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) :
    (∑ a : {a // P a}, entropyTerm (p.mass a.val)) =
      entropyTerm (eventMass p P) + eventMass p P * finiteEntropy (condition p P h).mass := by
  conv_lhs => enter [2, a]; rw [mass_eq_event_mul_condition p P h a]
  exact entropy_scaled_law (condition p P h) (eventMass p P)

theorem condition_entropy_mul (p : FiniteLaw A) (P : A → Prop)
    (h : 0 < eventMass p P) :
    eventMass p P * finiteEntropy (condition p P h).mass =
      (∑ a : {a // P a}, entropyTerm (p.mass a.val)) - entropyTerm (eventMass p P) := by
  linarith [event_entropy p P h]

theorem eventMass_add_complement (p : FiniteLaw A) (P : A → Prop) :
    eventMass p P + eventMass p (fun a => ¬ P a) = 1 := by
  rw [eventMass, eventMass, sum_subtype_indicator, sum_subtype_indicator,
    ← Finset.sum_add_distrib]
  calc
    (∑ a, ((if P a then p.mass a else 0) + (if ¬ P a then p.mass a else 0))) =
        ∑ a, p.mass a := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : P a <;> simp [h]
    _ = _ := p.total

theorem entropy_sum_event_complement (p : FiniteLaw A) (P : A → Prop) :
    (∑ a : {a // P a}, entropyTerm (p.mass a.val)) +
      (∑ a : {a // ¬ P a}, entropyTerm (p.mass a.val)) = finiteEntropy p.mass := by
  rw [sum_subtype_indicator P (fun a => entropyTerm (p.mass a)),
    sum_subtype_indicator (fun a => ¬ P a) (fun a => entropyTerm (p.mass a)),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : P a <;> simp [h]

theorem entropy_event_split (p : FiniteLaw A) (P : A → Prop)
    (hP : 0 < eventMass p P) (hQ : 0 < eventMass p (fun a => ¬ P a)) :
    finiteEntropy p.mass =
      entropyTerm (eventMass p P) + entropyTerm (eventMass p (fun a => ¬ P a)) +
      eventMass p P * finiteEntropy (condition p P hP).mass +
      eventMass p (fun a => ¬ P a) * finiteEntropy (condition p (fun a => ¬ P a) hQ).mass := by
  rw [← entropy_sum_event_complement p P, event_entropy p P hP,
    event_entropy p (fun a => ¬ P a) hQ]
  ring

theorem condition_entropy_of_removed_event (p : FiniteLaw A) (P : A → Prop)
    (hP : 0 < eventMass p P) (removedMass removedEntropy : ℝ)
    (hmass : eventMass p (fun a => ¬ P a) = removedMass)
    (hremoved : (∑ a : {a // ¬ P a}, entropyTerm (p.mass a.val)) =
      entropyTerm removedMass + removedMass * removedEntropy) :
    finiteEntropy (condition p P hP).mass =
      (finiteEntropy p.mass - entropyTerm removedMass -
        entropyTerm (1 - removedMass) - removedMass * removedEntropy) /
        (1 - removedMass) := by
  have hevent : eventMass p P = 1 - removedMass := by
    linarith [eventMass_add_complement p P]
  have hsum := entropy_sum_event_complement p P
  have hc := condition_entropy_mul p P hP
  rw [hremoved] at hsum
  rw [hevent] at hc
  apply (eq_div_iff (by linarith : 1 - removedMass ≠ 0)).mpr
  nlinarith

end MatrixMultiplication.CompletionLaws

end

end OAI
