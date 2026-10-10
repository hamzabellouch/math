import OAI.GroupTheory.PolycyclicRecognition.Geometry.RootIntervalSupports

namespace OAI

/-! # The unused interval indices contribute only the group identity -/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {L N I : Type*} [AddCommGroup L] [Module ℝ L] [Group N]
  [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N]

omit [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N] in
/-- Padding the fixed endpoint word does not enlarge any recurrence cell. -/
theorem rootIntervalSupport_of_le (Exp : L → N) (hzero : Exp 0 = 1)
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r R : ℝ) (j : ℕ) (hj : m ≤ j) (hR : 0 ≤ R) :
    rootIntervalSupport Exp letters X s r R j = {1} := by
  ext u
  constructor
  · rintro ⟨t, _, rfl⟩
    simp [rootIntervalSample, rootIntervalDirection, Nat.not_lt.mpr hj, hzero]
  · rintro rfl
    refine ⟨0, ?_, ?_⟩
    · simpa using hR
    · simp [rootIntervalSample, rootIntervalDirection, Nat.not_lt.mpr hj, hzero]

omit [MeasurableSpace N] [TopologicalSpace N] [BorelSpace N] [T2Space N] in
/-- A finite collection of denominator bounds covers the padded family. -/
theorem rootIntervalSupport_mul_mem_padded (Exp : L → N) (hzero : Exp 0 = 1)
    {m : ℕ} (letters : Fin m → I) (X : I → L) (s : I → ℝ)
    (r R : ℝ) (hR : 0 ≤ R) {Q Q' : Set N} (hQQ : Q ⊆ Q')
    (hfinite : ∀ j : Fin m, ∀ x ∈ Q,
      ∀ u ∈ rootIntervalSupport Exp letters X s r R j.val, x * u ∈ Q') :
    ∀ j : ℕ, ∀ x ∈ Q, ∀ u ∈ rootIntervalSupport Exp letters X s r R j, x * u ∈ Q' := by
  intro j x hx u hu
  by_cases hj : j < m
  · exact hfinite ⟨j, hj⟩ x hx u hu
  · rw [rootIntervalSupport_of_le Exp hzero letters X s r R j (Nat.le_of_not_gt hj) hR] at hu
    have he : u = 1 := mem_singleton_iff.mp hu
    simpa only [he, mul_one] using hQQ hx

end PolycyclicRecognition

end

end OAI
