import OAI.NumberTheory.Ostmann.Arithmetic.MovingPrimeArithmeticTransfer

namespace OAI

/-! # The original giant-only transfer, including its exact diagonal -/

namespace Ostmann
open scoped Classical BigOperators ComplexConjugate

/-- The entire Cauchy--Schwarz, positive-integer extension and forced-pivot
substitution. The inherited prime laws remain in `μ` and `c`; the integer
variable has no prime-specific transform attached to it. -/
theorem moving_giant_transfer {Y A : Type*} [Fintype Y] [Fintype A]
    (P I : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hPI : P ⊆ I)
    (hI : ∀ p ∈ I, 0 < p)
    (μ : Y → ℝ) (hμ : ∀ y, 0 ≤ μ y) (hμmass : ∑ y, μ y = 1)
    (w : ℕ → ℝ) (hw : ∀ p ∈ I, 0 ≤ w p) (Z : ℝ) (hZ : 0 ≤ Z)
    (hmass : ∑ p : P, Z * w p / (p : ℝ) = 1)
    (U : Y → ℕ) (hU : ∀ y, 0 < U y)
    (row : ∀ y, (p : P) → Fin ((p : ℕ) * U y) → ℂ)
    (hrow : ∀ y p, (∑ t, ‖row y p t‖ ^ 2) ≤ (p : ℕ) * (U y : ℝ))
    (L : Y → A → ℕ) (v : Y → A → ℤ) (c : Y → ℕ → A → ℂ)
    (hcoprime : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (L y a).Coprime (p * U y))
    (N H V : ℕ)
    (hv : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → (v y a).natAbs ≤ N)
    (hL : ∀ y p, p ∈ I → ∀ a, c y p a ≠ 0 → L y a ≤ H)
    (hscale : ∀ y, μ y ≠ 0 → ∀ p, p ∈ I → 2 * N * H ≤ V * (p * U y)) :
    ‖∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ a, row y p (positiveIntegerPivotKey _
        (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a‖ ^ 2 ≤
      Z * ((∑ y, μ y * (U y : ℝ) *
        ∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
        (∑ y, ((μ y * (U y : ℝ) : ℝ) : ℂ) *
          movingGiantOffDiagonal I V (U y) (L y) (v y) w (c y)).re) := by
  let B : ∀ y p, Fin (p * U y) → ℂ := fun y p =>
    if hp : 0 < p * U y then
      groupedCoefficient (fun a => positiveIntegerPivotKey _ hp (L y a) (v y a)) (c y p)
    else fun _ => 0
  have ht := moving_prime_row_transfer P I hP hPI μ hμ hμmass w hw Z hZ hmass U row B hrow
  have hleft : (∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ t, row y p t * B y p t) =
      ∑ y, (μ y : ℂ) * ∑ p : P, ((Z * w p / (p : ℝ) : ℝ) : ℂ) *
      ∑ a, row y p (positiveIntegerPivotKey _
        (Nat.mul_pos (hP p p.property).pos (hU y)) (L y a) (v y a)) * c y p a := by
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    apply Finset.sum_congr rfl
    intro p _
    congr 1
    simp only [B, dite_eq_left (Nat.mul_pos (hP p p.property).pos (hU y))]
    exact (pivot_residue_grouping _ (row y p) (c y p)).symm
  rw [hleft] at ht
  apply ht.trans_eq
  congr 1
  have hs (y : Y) (hy : μ y ≠ 0) :
      (∑ p ∈ I, w p * ∑ t, ‖B y p t‖ ^ 2) =
        (∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
          (movingGiantOffDiagonal I V (U y) (L y) (v y) w (c y)).re := by
    have hsplit (p : ℕ) (hp : p ∈ I) : (∑ t, ‖B y p t‖ ^ 2) =
        (pivotDiagonal (L y) (v y) (c y p)).re +
        (pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re := by
      have hpU := Nat.mul_pos (hI p hp) (hU y)
      let : NeZero (p * U y) := ⟨hpU.ne'⟩
      simpa only [B, dite_eq_left hpU, positiveIntegerPivotKey] using
        pivot_square_split_on_support (p * U y) (L y) (v y) (c y p) (hcoprime y p hp)
    calc
      _ = ∑ p ∈ I, w p * ((pivotDiagonal (L y) (v y) (c y p)).re +
          (pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [hsplit p hp]
      _ = (∑ p ∈ I, w p * (pivotDiagonal (L y) (v y) (c y p)).re) +
          (∑ p ∈ I, (w p : ℂ) * pivotOffDiagonal (p * U y) (L y) (v y) (c y p)).re := by
        simp only [mul_add, Finset.sum_add_distrib, Complex.re_sum,
          Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      _ = _ := by rw [movingGiantOffDiagonal_eq I hI (U y) (hU y) N H V
        (L y) (v y) w (c y) (hv y) (hL y) (hscale y hy)]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : μ y = 0
  · simp only [hy, zero_mul, zero_add]
  · rw [hs y hy, mul_add]

end Ostmann

end OAI
