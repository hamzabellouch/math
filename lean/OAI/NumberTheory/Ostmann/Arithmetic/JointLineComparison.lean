import OAI.NumberTheory.Ostmann.Arithmetic.JointSampledComparison
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineIntegration
import OAI.NumberTheory.Ostmann.Arithmetic.ArithmeticLineComparison

namespace OAI

/-! # Simultaneous signed replacement of every internal-prime line factor -/

namespace Ostmann

open scoped BigOperators Classical

noncomputable def sampledPrimeLineProbability {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (L : J → PolynomialGiantLine (Fin (n + 1))) (coordinate : Fin (n + 1))
    (external : Bool) (x : Fin (n + 1) → A) : ℝ :=
  let _ : Fact (prime (x coordinate)).Prime := ⟨hprime _⟩
  let φ := integerLineReduction value x (prime (x coordinate))
  internalLineProbability external (fun j => ((L j).normalized φ).1)
    (fun j => ((L j).normalized φ).2)

theorem sampledPrimeLineProbability_eq_flags {A J : Type*} {n : ℕ}
    (value : A → ℤ) (prime : A → ℕ) (hprime : ∀ a, (prime a).Prime)
    (L : J → PolynomialGiantLine (Fin (n + 1))) (i : J) (coordinate : Fin (n + 1))
    (external : Bool) (x : Fin (n + 1) → A)
    (hd : ∀ j, integerLineReduction value x (prime (x coordinate)) (L j).denominator ≠ 0)
    (hrow : integerLineReduction value x (prime (x coordinate)) (L i).a ≠ 0 ∨
      integerLineReduction value x (prime (x coordinate)) (L i).b ≠ 0) :
    sampledPrimeLineProbability value prime hprime L coordinate external x =
      internalLineFlagWeight external (prime (x coordinate)) (fun s => arithmeticTestFlag
        (prime (x coordinate) ∣ (integerTestValue value (lineTestPolynomials L i s) x).natAbs)) := by
  let _ : Fact (prime (x coordinate)).Prime := ⟨hprime _⟩
  let φ := integerLineReduction value x (prime (x coordinate))
  have hr : ((L i).normalized φ).1 ≠ 0 ∨ ((L i).normalized φ).2 ≠ 0 := by
    have hz := (L i).normalized_zero_iff φ (hd i)
    exact hrow.imp (fun h h₀ => h (hz.1.mp h₀)) (fun h h₀ => h (hz.2.mp h₀))
  change internalLineProbability external (fun j => ((L j).normalized φ).1)
    (fun j => ((L j).normalized φ).2) = _
  rw [internalLineProbability_eq_flags external L i φ hd hr]
  exact congrArg (internalLineFlagWeight external (prime (x coordinate)))
    (line_divisibility_flags_eq value L i x (prime (x coordinate))).symm

theorem joint_line_flag_comparison_le {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (J : I → Type*) [∀ b, Fintype (J b)] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (L : ∀ b, J b → PolynomialGiantLine (Fin (n + 1))) (i : ∀ b, J b)
    (coordinate : I → Fin (n + 1)) (external : Bool)
    (habsent : ∀ b s, coordinate b ∉ (lineTestPolynomials (L b) (i b) s).vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ b a, μ (coordinate b) a ≤ β)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ b s x, |(integerTestValue value (lineTestPolynomials (L b) (i b) s) x : ℝ)| ≤ H)
    (F : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∑ x, (productPrior μ x : ℂ) * F x *
      (((∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
          (fun s => arithmeticTestFlag (prime (x (coordinate b)) ∣
            (integerTestValue value (lineTestPolynomials (L b) (i b) s) x).natAbs)) : ℝ) : ℂ) -
       ((∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
          (fun s => arithmeticTestFlag (lineTestPolynomials (L b) (i b) s = 0)) : ℝ) : ℂ))‖ ≤
      2 * B * ∑ bs : (Σ b, Bool ⊕ J b),
        (((lineTestPolynomials (L bs.1) (i bs.1) bs.2).totalDegree : ℝ) * α + (Real.log H / V) * β) := by
  let T := Σ b, Bool ⊕ J b
  let tests : T → MvPolynomial (Fin (n + 1)) ℤ := fun bs => lineTestPolynomials (L bs.1) (i bs.1) bs.2
  let Ψ : (Fin (n + 1) → A) → (T → Bool) → ℂ := fun x flags =>
    F x * ((∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
      (fun s => flags ⟨b, s⟩) : ℝ) : ℂ)
  have hΨ (x : Fin (n + 1) → A) (flags : T → Bool) : ‖Ψ x flags‖ ≤ B := by
    have hn : 0 ≤ ∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
        (fun s => flags ⟨b, s⟩) :=
      Finset.prod_nonneg fun b _ => internalLineFlagWeight_nonneg _ _ _
    have hl : (∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
        (fun s => flags ⟨b, s⟩)) ≤ 1 :=
      Finset.prod_le_one₀ (fun b _ => internalLineFlagWeight_nonneg _ _ _)
        (fun b _ => internalLineFlagWeight_le_one _ _ _)
    dsimp only [Ψ]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
    exact (mul_le_mul_of_nonneg_left hl (norm_nonneg _)).trans (by simpa using hF x)
  have h := joint_sampled_polynomial_comparison_le value hinj prime hpInj hprime tests
    (fun bs => coordinate bs.1) (fun bs => habsent bs.1 bs.2) μ hμ hmass α β V H
    hα hβ hV hH hmax (fun bs => hpmax bs.1) (fun _ a _ => hsize a) (fun bs => hvalue bs.1 bs.2) Ψ B hB hΨ
  simpa only [Ψ, tests, mul_sub, mul_assoc] using h

/-- All local integrals can be replaced together even when their coefficient
polynomials depend on the other sampled internal primes. -/
theorem joint_line_probability_comparison_le {A I : Type*} [Fintype A] [Nonempty A] [Fintype I]
    (J : I → Type*) [∀ b, Fintype (J b)] {n : ℕ}
    (value : A → ℤ) (hinj : Function.Injective value)
    (prime : A → ℕ) (hpInj : Function.Injective prime) (hprime : ∀ a, (prime a).Prime)
    (L : ∀ b, J b → PolynomialGiantLine (Fin (n + 1))) (i : ∀ b, J b)
    (coordinate : I → Fin (n + 1)) (external : Bool)
    (habsent : ∀ b s, coordinate b ∉ (lineTestPolynomials (L b) (i b) s).vars)
    (μ : Fin (n + 1) → A → ℝ) (hμ : ∀ j a, 0 ≤ μ j a)
    (hmass : ∀ j, ∑ a, μ j a = 1)
    (α β V H : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hV : 0 < V) (hH : 1 ≤ H)
    (hmax : ∀ j a, μ j a ≤ α) (hpmax : ∀ b a, μ (coordinate b) a ≤ β)
    (hsize : ∀ a, V ≤ Real.log (prime a : ℝ))
    (hvalue : ∀ b s x, |(integerTestValue value (lineTestPolynomials (L b) (i b) s) x : ℝ)| ≤ H)
    (hd : ∀ x b j, integerLineReduction value x (prime (x (coordinate b))) (L b j).denominator ≠ 0)
    (hrow : ∀ x b, integerLineReduction value x (prime (x (coordinate b))) (L b (i b)).a ≠ 0 ∨
      integerLineReduction value x (prime (x (coordinate b))) (L b (i b)).b ≠ 0)
    (F : (Fin (n + 1) → A) → ℂ) (B : ℝ) (hB : 0 ≤ B) (hF : ∀ x, ‖F x‖ ≤ B) :
    ‖∑ x, (productPrior μ x : ℂ) * F x *
      (((∏ b, sampledPrimeLineProbability value prime hprime (L b) (coordinate b) external x : ℝ) : ℂ) -
       ((∏ b, internalLineFlagWeight external (prime (x (coordinate b)))
          (fun s => arithmeticTestFlag (lineTestPolynomials (L b) (i b) s = 0)) : ℝ) : ℂ))‖ ≤
      2 * B * ∑ bs : (Σ b, Bool ⊕ J b),
        (((lineTestPolynomials (L bs.1) (i bs.1) bs.2).totalDegree : ℝ) * α + (Real.log H / V) * β) := by
  have heq (x : Fin (n + 1) → A) (b : I) :=
    sampledPrimeLineProbability_eq_flags value prime hprime (L b) (i b) (coordinate b)
      external x (hd x b) (hrow x b)
  simp_rw [heq]
  exact joint_line_flag_comparison_le J value hinj prime hpInj hprime L i coordinate external
    habsent μ hμ hmass α β V H hα hβ hV hH hmax hpmax hsize hvalue F B hB hF

end Ostmann

end OAI
