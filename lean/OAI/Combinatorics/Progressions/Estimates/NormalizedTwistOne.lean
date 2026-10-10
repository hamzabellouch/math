import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open scoped BigOperators Classical NNReal

noncomputable def one (X Y : Type*) [Fintype X] [Fintype Y] :
    NormalizedPolynomialTwist X Y 1 1 0 where
  modulus := 1
  modulus_pos := by norm_num
  modulus_bound := by norm_num
  cover := 1
  cover_pos := by norm_num
  cover_bound := by norm_num
  mask := fun _ => 1
  mask_bound := fun _ => by simp only [norm_one, le_rfl]
  smooth := fun _ => 1
  smooth_bound := fun _ => by simp only [norm_one, le_rfl]
  smooth_lipschitz := LipschitzWith.const 1

@[simp] theorem one_eval {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    (one X (Σ j, J j)).eval N poly u = 1 := by
  simp only [eval, one, mul_one]

theorem normalization_of_one_comparison
    {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights Ψ)
    (site : Ω → Ψ → X → ℤ) (H : (X → ℤ) → ℂ) {ε : ℝ}
    (hcompare : ‖p.complexMean (fun x => q.complexMean (fun y =>
        (one X (Σ j, J j)).eval N poly (site x y))) -
      (𝔼 u ∈ integerBox N, (one X (Σ j, J j)).eval N poly u * H u)‖ ≤ ε) :
    ‖(𝔼 u ∈ integerBox N, H u) - 1‖ ≤ ε := by
  simpa only [one_eval, one_mul, FiniteProbabilityWeights.complexMean_const,
    norm_sub_rev] using hcompare

theorem normalization_bounds_of_one_comparison
    {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ} {J : Fin m → Type*}
    [∀ j, Fintype (J j)] (N : X → ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Ω Ψ : Type*} [Fintype Ω] [Fintype Ψ]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights Ψ)
    (site : Ω → Ψ → X → ℤ) (H : (X → ℤ) → ℂ) {ε : ℝ} (hε : ε ≤ 1 / 2)
    (hcompare : ‖p.complexMean (fun x => q.complexMean (fun y =>
        (one X (Σ j, J j)).eval N poly (site x y))) -
      (𝔼 u ∈ integerBox N, (one X (Σ j, J j)).eval N poly u * H u)‖ ≤ ε) :
    1 / 2 ≤ (𝔼 u ∈ integerBox N, H u).re ∧
      (𝔼 u ∈ integerBox N, H u).re ≤ 3 / 2 := by
  have h := normalization_of_one_comparison N poly p q site H hcompare
  have hr := (Complex.abs_re_le_norm ((𝔼 u ∈ integerBox N, H u) - 1)).trans h
  simp only [Complex.sub_re, Complex.one_re] at hr
  have hab := abs_le.mp hr
  constructor <;> linarith

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
