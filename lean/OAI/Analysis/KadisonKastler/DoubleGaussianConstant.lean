import OAI.Analysis.KadisonKastler.DoubleGaussianAnalytic
import OAI.Analysis.KadisonKastler.PeriodicStripExtension

namespace OAI

/-! # Constancy along the quotient of two commuting KMS actions -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H} (Ω : H)
  (U V : Multiplicative ℝ →* unitary (H →L[ℂ] H))
  (hU : ∀ x, Continuous (fun t : ℝ => (U (Multiplicative.ofAdd t) : H →L[ℂ] H) x))
  (hV : ∀ x, Continuous (fun t : ℝ => (V (Multiplicative.ofAdd t) : H →L[ℂ] H) x))

theorem doubleGaussian_diagonal_coefficient_constant
    (hnU : ∀ t a, a ∈ M → unitaryConj (U t) a ∈ M)
    (hnV : ∀ t a, a ∈ M → unitaryConj (V t) a ∈ M)
    (hcomm : ∀ s t, Commute (U s : H →L[ℂ] H) (V t : H →L[ℂ] H))
    (hKU : VectorStateKMS M Ω U) (hKV : VectorStateKMS M Ω V)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M)
    (r : ℝ) (hr : 0 < r) (t : ℝ) :
    productVectorState Ω (doubleGaussianStateAverage U V hU hV a r hr t (-t) * b) =
      productVectorState Ω (doubleGaussianStateAverage U V hU hV a r hr 0 0 * b) := by
  let D := doubleGaussianStateAverage U V hU hV a r hr
  let f : ℂ → ℂ := fun z => productVectorState Ω (D z (-z) * b)
  have hd : Differentiable ℂ f :=
    (innerSL ℂ Ω).differentiable.comp
      (doubleGaussianStateAverage_diagonal_differentiable U V hU hV a r hr (b Ω))
  have he (s : ℝ) : f ((s : ℂ) + Complex.I) = f s := by
    have h₁ := doubleGaussianStateAverage_first_shift Ω U V hU hV hnU hnV hKU
      a b ha hb r hr (s : ℂ) (-(s : ℂ) - Complex.I)
    have h₂ := doubleGaussianStateAverage_second_shift Ω U V hU hV hnU hcomm hnV hKV
      a b ha hb r hr (s : ℂ) (-(s : ℂ) - Complex.I)
    have hneg : -((s : ℂ) + Complex.I) = -(s : ℂ) - Complex.I := by ring
    dsimp [f, D]
    rw [hneg]
    exact h₁.trans (by simpa only [sub_add_cancel] using h₂.symm)
  have hbnd : ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.im → z.im ≤ 1 → ‖f z‖ ≤ C := by
    let B := (Real.exp r * Real.sqrt (Real.pi / r)) ^ 2 * ‖a‖
    refine ⟨‖Ω‖ * (B * ‖b Ω‖), ?_⟩
    intro z hz₀ hz₁
    apply (norm_inner_le_norm Ω _).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg Ω)
    exact ((D z (-z)).le_opNorm (b Ω)).trans
      (mul_le_mul_of_nonneg_right
        (doubleGaussianStateAverage_diagonal_bound U V hU hV a r hr z hz₀ hz₁) (norm_nonneg _))
  have h := bounded_matching_strip_constant he hd.continuous.continuousOn
    hd.differentiableOn hbnd (t : ℂ) (by simp) (by simp)
  simpa only [f, D, neg_zero, Complex.ofReal_neg] using h

end

end KadisonKastler

end OAI
