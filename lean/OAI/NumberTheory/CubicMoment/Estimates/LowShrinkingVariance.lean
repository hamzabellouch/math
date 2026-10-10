import OAI.NumberTheory.CubicMoment.Estimates.LowFiniteProfile
import OAI.NumberTheory.CubicMoment.Estimates.ShrinkingVariance

namespace OAI

/-! The profile derivative loss is fixed before the logarithmic saving
is chosen. No height-dependent analytic hypothesis is introduced. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

theorem low_shrinking_variance_remainder
    (hpnt : PrimaryPrimePNT)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (f : 𝓢(ℝ,ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ d : ℕ, ∀ j : ℕ, ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧
      ∀ (J c : ℝ) (hJ : 1 ≤ J), |c| ≤ 2 →
      ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t)
            (affineSchwartzProfile f J c (by linarith)) A-
          varianceZeroMode S β (affineSchwartzProfile f J c (by linarith)) A‖) T ≤
        K*J^d*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨I,hfamily⟩ := low_variance_remainder_finite_seminorm hpnt hMV hC hHuxley
  obtain ⟨L,D,hD,hop⟩ := normProfileFourier_finite_seminorm I
  obtain ⟨d,E,hE,hshrink⟩ := affineSchwartzProfile_finite_cost f L
  refine ⟨d,?_⟩
  intro j
  obtain ⟨K,Ct,hK,hbound⟩ := hfamily j
  refine ⟨K*(1+D*E),Ct,by positivity,?_⟩
  intro J c hJ hc S β Z A T M u hZ hA hT hM hS hβ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) _).trans hA
  let V := affineSchwartzProfile f J c (by linarith : J ≠ 0)
  have hVc := affineSchwartzProfile_compact f hf J c (by linarith)
  have hb := hbound V hVc (V.smooth ⊤) S β Z A T M u hZ hA hT hM hS hβ
  rw [←normProfileFourierCLM_apply V hVc] at hb
  have hcost := (hop V).trans (mul_le_mul_of_nonneg_left (hshrink J c hJ hc) hD.le)
  have hp : 1 ≤ J^d := one_le_pow₀ hJ
  have ht : K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
      (normProfileFourierCLM V)) ≤ K*(1+D*E)*J^d := by
    apply (mul_le_mul_of_nonneg_left (show
        1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierCLM V) ≤ (1+D*E)*J^d from by nlinarith) hK.le).trans_eq
    ring
  apply hb.trans
  gcongr

end CubicFirstMoment

end

end OAI
