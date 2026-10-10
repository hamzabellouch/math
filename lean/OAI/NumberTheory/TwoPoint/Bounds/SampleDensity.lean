import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages
import OAI.NumberTheory.TwoPoint.Circuits.FourierCorrection

namespace OAI

/-! Exact densities on the Boolean cube induced by a finite sampling map. -/

namespace TwoPointCorrelations

open Finset

/-- Density relative to uniform measure of a finite uniformly sampled map. -/
noncomputable def sampleDensity {α : Type*} [Fintype α] {n : ℕ}
    (sample : α → BooleanCube n) (x : BooleanCube n) : ℝ :=
  (Fintype.card (BooleanCube n) : ℝ) / Fintype.card α *
    ∑ a, if sample a = x then 1 else 0

lemma sampleDensity_nonneg {α : Type*} [Fintype α] {n : ℕ}
    (sample : α → BooleanCube n) (x : BooleanCube n) : 0 ≤ sampleDensity sample x := by
  unfold sampleDensity
  positivity

/-- Expectations against the induced density are exactly empirical averages. -/
lemma sampleDensity_expectation {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) (F : BooleanCube n → ℝ) :
    cubeAverage (fun x => sampleDensity sample x * F x) =
      uniformAverage (fun a => F (sample a)) := by
  have hα : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcube : (Fintype.card (BooleanCube n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ x : BooleanCube n,
      (∑ a, if sample a = x then (1 : ℝ) else 0) * F x) = ∑ a, F (sample a) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  unfold cubeAverage sampleDensity uniformAverage
  calc
    _ = ((Fintype.card (BooleanCube n) : ℝ) / Fintype.card α *
        (∑ x : BooleanCube n, (∑ a, if sample a = x then (1 : ℝ) else 0) * F x)) /
          Fintype.card (BooleanCube n) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by rw [hsum]; field_simp

lemma sampleDensity_mean {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) : cubeAverage (sampleDensity sample) = 1 := by
  simpa using sampleDensity_expectation sample (fun _ => 1)

lemma sampleDensity_walshCoefficient {α : Type*} [Fintype α] [Nonempty α] {n : ℕ}
    (sample : α → BooleanCube n) (S : Finset (Fin n)) :
    walshCoefficient (sampleDensity sample) S = uniformAverage (fun a => walsh S (sample a)) :=
  sampleDensity_expectation sample (walsh S)

end TwoPointCorrelations

end OAI
