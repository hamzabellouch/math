import OAI.NumberTheory.CubicMoment.Estimates.SmallBFiniteProfile
import OAI.NumberTheory.CubicMoment.Estimates.ShrinkingProfile

namespace OAI

/-! Uniform small-B remainder for a fixed cutoff narrowed at any polynomial scale. -/
noncomputable section
open scoped BigOperators ContDiff SchwartzMap
namespace CubicFirstMoment

lemma affineSchwartzProfile_compact (f : 𝓢(ℝ,ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) (J c : ℝ) (hJ : J ≠ 0) :
    HasCompactSupport (affineSchwartzProfile f J c hJ : ℝ → ℂ) := by
  have hh := (hf.comp_smul hJ).comp_homeomorph (Homeomorph.addRight (-c))
  change HasCompactSupport (fun x => f (J*(x+(-c)))) at hh
  change HasCompactSupport (fun x => f (J*(x-c)))
  simpa only [sub_eq_add_neg] using hh

theorem smallB_shrinking_variance_remainder
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (f : 𝓢(ℝ,ℂ))
    (hf : HasCompactSupport (f : ℝ → ℂ)) :
    ∃ (d : ℕ) (K : ℝ), 0 < K ∧
      ∀ (J c : ℝ) (hJ : 1 ≤ J), |c| ≤ 2 →
      ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T u : ℝ),
      65536 ≤ Z → Z^(3/2:ℝ) ≤ A → Z^(1/50:ℝ) ≤ T →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      dyadicHeightMean (fun t =>
        ‖smoothedDispersionVariance S β (u+t)
            (affineSchwartzProfile f J c (by linarith)) A-
          varianceZeroMode S β (affineSchwartzProfile f J c (by linarith)) A‖) T ≤
        K*J^d*A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ)*∑ b ∈ S, ‖β b‖^2 := by
  obtain ⟨I,K,hK,hbound⟩ := smallB_variance_remainder_finite_seminorm hMV hC hHuxley
  obtain ⟨L,D,hD,hop⟩ := normProfileFourier_finite_seminorm I
  obtain ⟨d,E,hE,hshrink⟩ := affineSchwartzProfile_finite_cost f L
  refine ⟨d,K*(1+D*E),by positivity,?_⟩
  intro J c hJ hc S β Z A T u hZ hA hT hS
  let V := affineSchwartzProfile f J c (by linarith : J ≠ 0)
  have hVc := affineSchwartzProfile_compact f hf J c (by linarith)
  have hb := hbound V hVc (V.smooth ⊤) S β Z A T u hZ hA hT hS
  rw [← normProfileFourierCLM_apply V hVc] at hb
  have hcost := (hop V).trans (mul_le_mul_of_nonneg_left (hshrink J c hJ hc) hD.le)
  have hp : 1 ≤ J^d := one_le_pow₀ hJ
  have ht : K*(1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
      (normProfileFourierCLM V)) ≤ K*(1+D*E)*J^d := by
    apply (mul_le_mul_of_nonneg_left (show
        1+(I.sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2))
          (normProfileFourierCLM V) ≤ (1+D*E)*J^d from by nlinarith) hK.le).trans_eq
    ring
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) (3/2:ℝ)).trans hA
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ht
      (Real.rpow_nonneg hA0 _)) (Real.rpow_nonneg (by linarith) _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

end CubicFirstMoment

end

end OAI
