import OAI.NumberTheory.Ostmann.Arithmetic.MovingSlotLines

namespace OAI

/-! # Integrating the actual moving-giant line systems on their full support -/

namespace Ostmann
open scoped BigOperators Classical

noncomputable def movingSlotLineProbability {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → List (MovingSlotReversal (Fin n)))
    (current : J → MovingSlotReversal (Fin n)) (external : Bool)
    (x : Fin n → A) (a : A) : ℝ :=
  let _ : Fact (prime a).Prime := ⟨hprime a⟩
  let φ := integerLineReduction value x (prime a)
  internalLineProbability external
    (fun j => ((movingSlotLine (path j) (current j)).normalized φ).1)
    (fun j => ((movingSlotLine (path j) (current j)).normalized φ).2)

theorem movingSlotLineProbability_eq_flags {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → List (MovingSlotReversal (Fin n)))
    (current : J → MovingSlotReversal (Fin n)) (base : J) (external : Bool)
    (x : Fin n → A) (a : A)
    (hpath : ∀ j s, s ∈ path j →
      let φ := integerLineReduction value x (prime a)
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : let φ := integerLineReduction value x (prime a)
      φ (current base).polynomial.v ≠ 0 ∧ φ (current base).polynomial.w ≠ 0) :
    movingSlotLineProbability value prime hprime path current external x a =
      internalLineFlagWeight external (prime a) (fun s => arithmeticTestFlag
        (prime a ∣ (integerTestValue value
          (lineTestPolynomials (fun j => movingSlotLine (path j) (current j)) base s) x).natAbs)) := by
  let : Fact (prime a).Prime := ⟨hprime a⟩
  let φ := integerLineReduction value x (prime a)
  have hsteps (j : J) : ∀ s ∈ (path j).map MovingSlotReversal.polynomial,
      φ s.v ≠ 0 ∧ φ s.w ≠ 0 ∧ φ s.u ≠ 0 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    exact hpath j t ht
  have hd (j : J) : φ (movingSlotLine (path j) (current j)).denominator ≠ 0 :=
    movingPolynomialAncestors_denominator _ φ (fun s hs => (hsteps j s hs).2.2)
  have hr := movingHistoryLine_nonzero _ _ _ φ (hsteps base) hcurrent.1 hcurrent.2
  have hz := (movingSlotLine (path base) (current base)).normalized_zero_iff φ (hd base)
  have hr' : ((movingSlotLine (path base) (current base)).normalized φ).1 ≠ 0 ∨
      ((movingSlotLine (path base) (current base)).normalized φ).2 ≠ 0 :=
    hr.imp (fun h h₀ => h (hz.1.mp h₀)) (fun h h₀ => h (hz.2.mp h₀))
  unfold movingSlotLineProbability
  rw [internalLineProbability_eq_flags external _ base φ hd hr']
  change internalLineFlagWeight external (prime a) (fun s => arithmeticTestFlag
    (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (prime a)))
      (fun i => (value (x i) : ZMod (prime a)))
      (lineTestPolynomials (fun j => movingSlotLine (path j) (current j)) base s) = 0)) = _
  rw [line_divisibility_flags_eq]

theorem internalLineFlagWeight_le_scalar {J : Type*} (external : Bool) (p : ℕ)
    (flags : Bool ⊕ J → Bool) :
    internalLineFlagWeight external p flags ≤ internalLineScalar external p := by
  unfold internalLineFlagWeight
  split_ifs
  · rfl
  · exact internalLineScalar_nonneg external p

/-- The remaining weight may be large. Its bound is imposed only after the
one-over-prime line scalars have been included, exactly as in (8.20). -/
theorem line_product_multiplier_bound {A J O : Type*} [Fintype J]
    (prime : A → ℕ) (external : J → Bool) (representative : J → A)
    (weight : ℂ) (B : ℝ)
    (h : ‖weight‖ * ∏ j, internalLineScalar (external j) (prime (representative j)) ≤ B)
    (flags : J × (Bool ⊕ O) → Bool) :
    ‖weight * ∏ j, (internalLineFlagWeight (external j) (prime (representative j))
      (fun s => flags (j, s)) : ℂ)‖ ≤ B := by
  rw [norm_mul, norm_prod]
  have he (j : J) : ‖(internalLineFlagWeight (external j) (prime (representative j))
      (fun s => flags (j, s)) : ℂ)‖ =
      internalLineFlagWeight (external j) (prime (representative j)) (fun s => flags (j, s)) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (internalLineFlagWeight_nonneg _ _ _)]
  simp_rw [he]
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg weight)
  exact Finset.prod_le_prod₀ (fun _ _ => internalLineFlagWeight_nonneg _ _ _)
    (fun _ _ => internalLineFlagWeight_le_scalar _ _ _)

/-- On the original full support the actual line counts can be inserted into
the same signed expression. No line identity is requested on rejected samples. -/
theorem moving_line_product_on_support {A J O : Type*} [Fintype J] {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (path : J → O → List (MovingSlotReversal (Fin n)))
    (current : J → O → MovingSlotReversal (Fin n)) (base : J → O)
    (external : J → Bool) (representative : J → A) (x : Fin n → A) (weight : ℂ)
    (hpath : weight ≠ 0 → ∀ j o s, s ∈ path j o →
      let φ := integerLineReduction value x (prime (representative j))
      φ s.polynomial.v ≠ 0 ∧ φ s.polynomial.w ≠ 0 ∧ φ s.polynomial.u ≠ 0)
    (hcurrent : weight ≠ 0 → ∀ j,
      let φ := integerLineReduction value x (prime (representative j))
      φ (current j (base j)).polynomial.v ≠ 0 ∧ φ (current j (base j)).polynomial.w ≠ 0) :
    weight * ∏ j, (movingSlotLineProbability value prime hprime (path j) (current j)
        (external j) x (representative j) : ℂ) =
      weight * ∏ j, (internalLineFlagWeight (external j) (prime (representative j))
        (fun s => arithmeticTestFlag (prime (representative j) ∣
          (integerTestValue value (lineTestPolynomials
            (fun o => movingSlotLine (path j o) (current j o)) (base j) s) x).natAbs)) : ℂ) := by
  by_cases hw : weight = 0
  · simp only [hw, zero_mul]
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg (fun r : ℝ => (r : ℂ))
      (movingSlotLineProbability_eq_flags value prime hprime (path j) (current j) (base j)
        (external j) x (representative j) (hpath hw j) (hcurrent hw j))

end Ostmann

end OAI
