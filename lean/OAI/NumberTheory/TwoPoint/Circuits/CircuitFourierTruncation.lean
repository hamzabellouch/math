import OAI.NumberTheory.TwoPoint.Circuits.CircuitWalshExpansion

namespace OAI

/-! The canonical low-degree approximation and its exact Fourier-tail error. -/

namespace TwoPointCorrelations

open Finset
open scoped Classical

noncomputable def walshTruncation {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ)
    (x : BooleanCube n) : ℝ :=
  ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ t),
    walshCoefficient f S * walsh S x

lemma walshTruncation_degree {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    WalshDegreeLE (walshTruncation f t) t := ⟨walshCoefficient f, fun _ => rfl⟩

lemma walshTruncation_coefficient {n : ℕ} (f : BooleanCube n → ℝ)
    (t : ℕ) (S : Finset (Fin n)) :
    walshCoefficient (walshTruncation f t) S =
      if S.card ≤ t then walshCoefficient f S else 0 := by
  unfold walshCoefficient walshTruncation
  simp only [sum_mul]
  rw [cubeAverage_sum]
  simp_rw [mul_assoc, cubeAverage_mul_const, cubeAverage_walsh_mul]
  simp [walshCoefficient]

lemma walshCoefficient_sub {n : ℕ} (f g : BooleanCube n → ℝ)
    (S : Finset (Fin n)) :
    walshCoefficient (fun x => f x - g x) S =
      walshCoefficient f S - walshCoefficient g S := by
  unfold walshCoefficient
  simp only [sub_mul, cubeAverage_sub]

theorem walshTruncation_error {n : ℕ} (f : BooleanCube n → ℝ) (t : ℕ) :
    cubeAverage (fun x => (f x - walshTruncation f t x) ^ 2) =
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => t < S.card),
        (walshCoefficient f S) ^ 2 := by
  rw [walsh_parseval, sum_filter]
  apply sum_congr rfl
  intro S _
  rw [walshCoefficient_sub, walshTruncation_coefficient]
  by_cases hS : S.card ≤ t
  · simp [hS, Nat.not_lt.mpr hS]
  · simp [hS, Nat.lt_of_not_ge hS]

end TwoPointCorrelations

end OAI
