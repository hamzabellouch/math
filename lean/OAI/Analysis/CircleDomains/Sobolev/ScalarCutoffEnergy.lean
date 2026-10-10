import OAI.Analysis.CircleDomains.Sobolev.SmoothScalarCutoffWitness

namespace OAI

/-! Pointwise energy control for the actual product-and-chain-rule
field. Constants depend only on the fixed smooth cutoffs. -/
open Set Function MeasureTheory
noncomputable section
namespace CircleDomainRigidity

lemma scalar_cutoff_energy_algebra {u₀ u₁ d₀ d₁ a b c C : ℝ}
    (hC : 0 ≤ C) (ha : |a| ≤ 1) (hb : |b| ≤ 1)
    (hc : |c| ≤ C) (hd₀ : |d₀| ≤ C) (hd₁ : |d₁| ≤ C) :
    (a*b)^2 + (|a*(c*u₀)+d₀*b|+|a*(c*u₁)+d₁*b|)^2 ≤
      (1+8*C^2)*(1+(|u₀|+|u₁|)^2) := by
  have hab : |a*b| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul ha hb (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)
  have hd (u d : ℝ) (hd : |d| ≤ C) : |a*(c*u)+d*b| ≤ C*|u|+C := by
    calc
      _ ≤ |a| * (|c| * |u|)+|d| * |b| := by simpa only [abs_mul] using abs_add_le (a*(c*u)) (d*b)
      _ ≤ 1*(C*|u|)+C*1 := add_le_add
        (mul_le_mul ha (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)) zero_le_one)
        (mul_le_mul hd hb (abs_nonneg _) hC)
      _ = _ := by ring
  have hs : |a*(c*u₀)+d₀*b|+|a*(c*u₁)+d₁*b| ≤ C*((|u₀|+|u₁|)+2) := by
    nlinarith [hd u₀ d₀ hd₀, hd u₁ d₁ hd₁]
  have hs2 := sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg hC (by positivity)) |>.mpr hs
  have hab2 : (a*b)^2 ≤ 1 := by
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg (a*b)) zero_le_one).mpr hab
  have hquad : ((|u₀|+|u₁|)+2)^2 ≤ 8*(1+(|u₀|+|u₁|)^2) := by
    nlinarith [sq_nonneg ((|u₀|+|u₁|)-2)]
  have hmul := mul_le_mul_of_nonneg_left hquad (sq_nonneg C)
  nlinarith [sq_nonneg (|u₀|+|u₁|)]

lemma smoothScalarCutoffWitness_energy {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hFu : ∀ t, F t ∈ Icc 0 1)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ t, ‖deriv F t‖ ≤ C)
    {η : EuclideanPlane → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsη : HasCompactSupport η) (hηu : ∀ x, η x ∈ Icc 0 1)
    (hηd : ∀ x, ‖fderiv ℝ η x‖ ≤ C) (x : EuclideanPlane) :
    let Q := smoothScalarCutoffWitness hu W hsu hF hFu hC hη hsη
    (η x*F (u x))^2 + (|Q.weakGrad x 0|+|Q.weakGrad x 1|)^2 ≤
      (1+8*C^2)*(1+(|W.weakGrad x 0|+|W.weakGrad x 1|)^2) := by
  dsimp only
  rw [smoothScalarCutoffWitness_gradient, smoothScalarCutoffWitness_gradient]
  have hd (i : Fin 2) : |fderiv ℝ η x (EuclideanSpace.single i 1)| ≤ C := by
    have he := (fderiv ℝ η x).le_opNorm (EuclideanSpace.single i 1)
    simpa only [Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
      using he.trans (mul_le_mul_of_nonneg_right (hηd x) (norm_nonneg _))
  apply scalar_cutoff_energy_algebra hC0
  · exact abs_le.mpr ⟨by linarith [(hηu x).1], (hηu x).2⟩
  · exact abs_le.mpr ⟨by linarith [(hFu (u x)).1], (hFu (u x)).2⟩
  · exact hC (u x)
  · exact hd 0
  · exact hd 1

end CircleDomainRigidity

end

end OAI
