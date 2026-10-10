import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineIntegration

namespace OAI

/-! # Signed symbolic replacement for the actual integrated line factors -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def integerLineReduction {A : Type*} {n : ℕ} (value : A → ℤ)
    (x : Fin n → A) (p : ℕ) : MvPolynomial (Fin n) ℤ →+* ZMod p :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) (fun j => (value (x j) : ZMod p))

noncomputable def sampledLineProbability {A J : Type*} {n : ℕ} (value : A → ℤ)
    (L : J → PolynomialGiantLine (Fin n)) (external : Bool)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (x : Fin n → A) (p : P) : ℝ :=
  let _ : Fact p.val.Prime := ⟨hprime p p.property⟩
  internalLineProbability external (fun j => ((L j).normalized (integerLineReduction value x p)).1)
    (fun j => ((L j).normalized (integerLineReduction value x p)).2)

theorem sampledLineProbability_eq_flagWeight {A J : Type*} {n : ℕ} (value : A → ℤ)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (external : Bool)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (x : Fin n → A) (p : P)
    (hd : ∀ j, integerLineReduction value x p (L j).denominator ≠ 0)
    (hrow : integerLineReduction value x p (L i).a ≠ 0 ∨
      integerLineReduction value x p (L i).b ≠ 0) :
    sampledLineProbability value L external P hprime x p =
      internalLineFlagWeight external p (fun s => arithmeticTestFlag
        (p.val ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) := by
  let _ : Fact p.val.Prime := ⟨hprime p p.property⟩
  have hr : ((L i).normalized (integerLineReduction value x p)).1 ≠ 0 ∨
      ((L i).normalized (integerLineReduction value x p)).2 ≠ 0 := by
    have hz := (L i).normalized_zero_iff (integerLineReduction value x p) (hd i)
    exact hrow.imp (fun h h₀ => h (hz.1.mp h₀)) (fun h h₀ => h (hz.2.mp h₀))
  unfold sampledLineProbability
  rw [internalLineProbability_eq_flags external L i _ hd hr]
  change internalLineFlagWeight external p (fun s => arithmeticTestFlag
    (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p.val))
      (fun j => (value (x j) : ZMod p.val)) (lineTestPolynomials L i s) = 0)) = _
  rw [line_divisibility_flags_eq value L i x p.val]

/-- Keep the amplitude, including the spectator factors, signed while replacing
the coefficient and rank flags of one internal prime. -/
theorem integer_line_flag_comparison_le {A J : Type*} [Fintype A] [Fintype J]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (external : Bool)
    (μ : Fin n → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ j a, μ j a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V H : ℝ) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hvalue : ∀ s x, |(integerTestValue value (lineTestPolynomials L i s) x : ℝ)| ≤ H)
    (F : (Fin n → A) → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x p, ‖F x p‖ ≤ B) :
    ‖∑ x, ∑ p ∈ P, ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
      ((internalLineFlagWeight external p (fun s => arithmeticTestFlag
          (p ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))‖ ≤
      2 * B * ∑ s, (((lineTestPolynomials L i s).totalDegree : ℝ) * α +
        (Real.log H / V) * β) := by
  let Ψ : (Fin n → A) → ℕ → (Bool ⊕ J → Bool) → ℂ :=
    fun x p flags => F x p * (internalLineFlagWeight external p flags : ℂ)
  have hΨ (x : Fin n → A) (p : ℕ) (flags : Bool ⊕ J → Bool) : ‖Ψ x p flags‖ ≤ B := by
    dsimp only [Ψ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (internalLineFlagWeight_nonneg external p flags)]
    calc
      _ ≤ ‖F x p‖ * 1 := mul_le_mul_of_nonneg_left
        (internalLineFlagWeight_le_one external p flags) (norm_nonneg _)
      _ ≤ B := by simpa using hF x p
  have h := integer_polynomial_symbolic_comparison_le value hinj (lineTestPolynomials L i)
    μ hμ hmass α hα hmax P hprime ν hν hνmass β V H hβ hV hH hνmax hsize hvalue
    Ψ B hB hΨ
  simpa only [Ψ, mul_sub, mul_assoc] using h

/-- The same estimate expressed using the actual simultaneous line counts.
No rank, feasibility, or probability formula is assumed. -/
theorem sampled_line_probability_comparison_le {A J : Type*} [Fintype A] [Fintype J]
    {n : ℕ} (value : A → ℤ) (hinj : Function.Injective value)
    (L : J → PolynomialGiantLine (Fin n)) (i : J) (external : Bool)
    (μ : Fin n → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α : ℝ) (hα : 0 ≤ α) (hmax : ∀ j a, μ j a ≤ α)
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (ν : ℕ → ℝ) (hν : ∀ p ∈ P, 0 ≤ ν p) (hνmass : ∑ p ∈ P, ν p = 1)
    (β V H : ℝ) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hνmax : ∀ p ∈ P, ν p ≤ β) (hsize : ∀ p ∈ P, V ≤ Real.log (p : ℝ))
    (hvalue : ∀ s x, |(integerTestValue value (lineTestPolynomials L i s) x : ℝ)| ≤ H)
    (hd : ∀ (x : Fin n → A) (p : P) j, integerLineReduction value x p (L j).denominator ≠ 0)
    (hrow : ∀ (x : Fin n → A) (p : P),
      integerLineReduction value x p (L i).a ≠ 0 ∨
      integerLineReduction value x p (L i).b ≠ 0)
    (F : (Fin n → A) → ℕ → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x p, ‖F x p‖ ≤ B) :
    ‖∑ x, ∑ p : P, ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
      ((sampledLineProbability value L external P hprime x p : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))‖ ≤
      2 * B * ∑ s, (((lineTestPolynomials L i s).totalDegree : ℝ) * α +
        (Real.log H / V) * β) := by
  have heq (x : Fin n → A) (p : P) :=
    sampledLineProbability_eq_flagWeight value L i external P hprime x p (hd x p) (hrow x p)
  simp_rw [heq]
  let term := fun x p => ((productPrior μ x * ν p : ℝ) : ℂ) * F x p *
    ((internalLineFlagWeight external p (fun s => arithmeticTestFlag
      (p ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) : ℂ) -
        (internalLineFlagWeight external p
          (fun s => arithmeticTestFlag (lineTestPolynomials L i s = 0)) : ℂ))
  change ‖∑ x, ∑ p : P, term x p‖ ≤ _
  have hs : (∑ x, ∑ p : P, term x p) = ∑ x, ∑ p ∈ P, term x p := by
    apply Finset.sum_congr rfl
    intro x _
    exact (Finset.sum_subtype P (fun _ => Iff.rfl) (term x)).symm
  rw [hs]
  exact integer_line_flag_comparison_le value hinj L i external μ hμ hmass α hα hmax
    P hprime ν hν hνmass β V H hβ hV hH hνmax hsize hvalue F B hB hF

end Ostmann

end OAI
