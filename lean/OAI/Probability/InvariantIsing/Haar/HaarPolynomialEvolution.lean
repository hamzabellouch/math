import OAI.Probability.InvariantIsing.Haar.HaarPolynomialMinimum

namespace OAI

/-! Positivity comparison for polynomial supersolutions of the rotation heat equation. -/
noncomputable section
open Matrix MvPolynomial Set
namespace InvariantIsing

theorem haarPolynomial_evolution_nonneg {N : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (p : ℝ → MatrixPolynomial N) (dp : ℝ → SpecialOrthogonal N → ℝ)
    (hc : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => haarPolynomialValue (p z.1) z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ))
    (hi : ∀ U : SpecialOrthogonal N, 0 ≤ haarPolynomialValue (p 0) U)
    (hd : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      HasDerivAt (fun s => haarPolynomialValue (p s) U) (dp t U) t)
    (hpde : ∀ t ∈ Ioc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialLaplacian N (p t)) U ≤ dp t U) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ U : SpecialOrthogonal N,
      0 ≤ haarPolynomialValue (p t) U := by
  let W (t : ℝ) (U : SpecialOrthogonal N) := Real.exp (-t)*haarPolynomialValue (p t) U
  let D (z : ℝ × SpecialOrthogonal N) :=
    Real.exp (-z.1)*(dp z.1 z.2-haarPolynomialValue (p z.1) z.2)
  let B (t : ℝ) (U : SpecialOrthogonal N) :=
    Real.exp (-t)*haarPolynomialValue (haarPolynomialLaplacian N (p t)) U
  have hcW : ContinuousOn (fun z : ℝ × SpecialOrthogonal N => W z.1 z.2)
      (Icc (0 : ℝ) T ×ˢ Set.univ) :=
    (Real.continuous_exp.comp continuous_fst.neg).continuousOn.mul hc
  have hiW : ∀ U, 0 ≤ W 0 U := by simpa only [W,neg_zero,Real.exp_zero,one_mul] using hi
  have hdW (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (U : SpecialOrthogonal N) :
      HasDerivAt (fun s => W s U) (D (t,U)) t := by
    have he : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      convert ((hasDerivAt_id t).fun_neg).exp using 1
      all_goals simp only [id_eq,mul_neg,mul_one]
    convert he.mul (hd t ht U) using 1
    dsimp only [D]
    ring
  have hP (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (U : SpecialOrthogonal N) :
      B t U-W t U ≤ D (t,U) := by
    dsimp only [B,W,D]
    nlinarith [mul_le_mul_of_nonneg_left (hpde t ht U) (Real.exp_pos (-t)).le]
  have hS (t : ℝ) (_ : t ∈ Icc (0 : ℝ) T) (U : SpecialOrthogonal N)
      (hm : ∀ V, W t U ≤ W t V) : 0 ≤ B t U := by
    apply mul_nonneg (Real.exp_pos (-t)).le
    apply haarPolynomialLaplacian_nonneg_at_min
    intro V
    exact (mul_le_mul_iff_right₀ (Real.exp_pos (-t))).mp (hm V)
  have hz := compact_parabolic_nonneg hT W D B hcW hiW hdW hP hS
  intro t ht U
  exact nonneg_of_mul_nonneg_right (hz t ht U) (Real.exp_pos (-t))

end InvariantIsing

end

end OAI
