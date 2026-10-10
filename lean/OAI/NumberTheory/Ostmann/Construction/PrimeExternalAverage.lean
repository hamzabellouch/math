import OAI.NumberTheory.Ostmann.Characters.MixedBoundedPhaseStatistic
import OAI.NumberTheory.Ostmann.Construction.GiantCoprimeIntervals

namespace OAI

/-! # Passing from the integer/prime comparison law to two prime giants -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def primeExternalAverage {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) : ℂ :=
  ∑ s : transferFrequencyRange N, ∑ y : B → A, ((∏ b, ν b (y b) : ℝ) : ℂ) *
    complexPrimeInterval 1 0 r w (fun z =>
      complexPrimeInterval 1 0 u v (fun x => F s.val y x z))

noncomputable def leftPrimeDensity (u x : ℝ) : ℝ :=
  if (⌊Real.exp x⌋₊).Prime ∧ Real.exp u ≤ (⌊Real.exp x⌋₊ : ℝ)
  then Real.exp u / (⌊Real.exp x⌋₊ : ℝ) else 0

theorem leftPrimeDensity_nonneg (u x : ℝ) : 0 ≤ leftPrimeDensity u x := by
  unfold leftPrimeDensity
  split_ifs <;> positivity

theorem leftPrimeDensity_le_one (u x : ℝ) : leftPrimeDensity u x ≤ 1 := by
  unfold leftPrimeDensity
  split_ifs with h
  · exact (div_le_one (Nat.cast_pos.mpr h.1.pos)).mpr h.2
  · exact zero_le_one

theorem leftPrimeDensity_norm_le_one (u x : ℝ) : ‖(leftPrimeDensity u x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_of_nonneg (leftPrimeDensity_nonneg u x)] using
    leftPrimeDensity_le_one u x

theorem complexPrimeInterval_as_integer (u v center : ℝ) (F : ℝ → ℂ) :
    complexPrimeInterval 1 0 u v F = (Real.exp (center - u) : ℂ) *
      complexIntegerInterval 1 0 u v center (fun x => (leftPrimeDensity u x : ℂ) * F x) := by
  unfold complexPrimeInterval complexIntegerInterval
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_le _).trans_lt (Finset.mem_Ioc.mp hp).1
  have hlow : Real.exp u ≤ (p : ℝ) := by
    exact (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hp).1).le
  simp only [leftPrimeDensity, Real.exp_log hp0, Nat.floor_natCast,
    integerResidueAtom, Nat.modEq_one, ite_true, and_true]
  by_cases hprime : p.Prime
  · simp only [hprime, hlow, and_self, ite_true, Complex.ofReal_div]
    have he : Real.exp (center - u) * Real.exp u * Real.exp (-center) = 1 := by
      rw [← Real.exp_add, ← Real.exp_add]
      ring_nf
      exact Real.exp_zero
    have heC : (Real.exp (center - u) : ℂ) * (Real.exp u : ℂ) * (Real.exp (-center) : ℂ) = 1 := by
      exact_mod_cast he
    calc
      _ = ((Real.exp (center - u) : ℂ) * (Real.exp u : ℂ) * (Real.exp (-center) : ℂ)) *
          (F (Real.log p) * ((p : ℝ) : ℂ)⁻¹) := by rw [heC]; ring
      _ = _ := by ring
  · simp only [hprime, false_and, ite_false, Complex.ofReal_zero, zero_mul, mul_zero]

theorem primeExternalAverage_as_mixed {B A : Type*} [Fintype B] [Fintype A]
    (ν : B → A → ℝ) (N : ℕ) (u v r w center : ℝ)
    (F : ℤ → (B → A) → ℝ → ℝ → ℂ) :
    primeExternalAverage ν N u v r w F = (Real.exp (center - u) : ℂ) *
      mixedExternalAverage ν N u v r w center
        (fun s y x z => (leftPrimeDensity u x : ℂ) * F s y x z) := by
  simp only [primeExternalAverage, mixedExternalAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro y _
  rw [show (fun z => complexPrimeInterval 1 0 u v (fun x => F s.val y x z)) =
      (fun z => (Real.exp (center - u) : ℂ) * complexIntegerInterval 1 0 u v center
        (fun x => (leftPrimeDensity u x : ℂ) * F s.val y x z)) from
      funext (fun z => complexPrimeInterval_as_integer u v center _)]
  simp only [complexPrimeInterval, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- The same bulk symmetrization applies to two genuine prime giants. Only
one explicit scalar is lost when passing to the integer comparison law. -/
theorem primeExternalAverage_bounded_statistic_cauchy {B A : Type*} [Fintype B] [Fintype A]
    (n m : ℕ) (slot : (TreeLeafIndex n × Fin m) ↪ B)
    (ν : B → A → ℝ) (hν : ∀ b a, 0 ≤ ν b a)
    (hidentical : ∀ j k, ν (slot j) = ν (slot k))
    (N : ℕ) (u v r w center : ℝ)
    (F H P : ℤ → (B → A) → ℝ → ℝ → ℂ)
    (hH : ∀ e s y x z, H s (selectedBulkSample slot e y) x z = H s y x z)
    (hP : ∀ e s y x z, P s (selectedBulkSample slot e y) x z = P s y x z)
    (hPnorm : ∀ s y x z, ‖P s y x z‖ ≤ 1)
    (W : ℝ → ℝ → ℝ) (hW : ∀ x z, 0 ≤ W x z) :
    ‖primeExternalAverage ν N u v r w
      (fun s y x z => ((P s y x z * H s y x z) * F s y x z) * W x z)‖ ^ 2 ≤
    Real.exp (center - u) ^ 2 *
    (mixedExternalAverage ν N u v r w center (fun _ _ x z => (W x z : ℂ))).re *
    (mixedExternalAverage ν N u v r w center (fun s y x z =>
      (‖mixedBulkSymmetrize n m slot F s y x z‖ ^ 2 : ℂ) *
        ((W x z : ℂ) * (‖H s y x z‖ ^ 2 : ℝ)))).re := by
  let Q := fun s y x z => (leftPrimeDensity u x : ℂ) * P s y x z
  have hQ (e s y x z) : Q s (selectedBulkSample slot e y) x z = Q s y x z := by
    dsimp only [Q]
    rw [hP]
  have hQnorm (s y x z) : ‖Q s y x z‖ ≤ 1 := by
    dsimp only [Q]
    rw [norm_mul]
    exact (mul_le_mul (leftPrimeDensity_norm_le_one u x) (hPnorm s y x z)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hc := mixedBulkSymmetrize_bounded_statistic_cauchy n m slot ν hν hidentical N
    u v r w center F H Q hH hQ hQnorm W hW
  have heq : (fun s y x z => (leftPrimeDensity u x : ℂ) *
      (((P s y x z * H s y x z) * F s y x z) * W x z)) =
      (fun s y x z => ((Q s y x z * H s y x z) * F s y x z) * W x z) := by
    funext s y x z
    dsimp only [Q]
    ring
  rw [primeExternalAverage_as_mixed ν N u v r w center, heq, norm_mul, mul_pow]
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  exact (mul_le_mul_of_nonneg_left hc (sq_nonneg _)).trans_eq (by ring)

end Ostmann

end OAI
