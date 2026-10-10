import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailVarianceLog
import OAI.NumberTheory.CubicMoment.Estimates.HeightBilinearScale

namespace OAI

/-! Arbitrary logarithmic saving for the original small-B Gauss
bilinear form, with an explicit outer-length logarithmic cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_bilinear_log_saving
    {C Mα Mβ : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) (hMα : 0 ≤ Mα) (hMβ : 0 ≤ Mβ)
    (k dα dβ : ℕ) (Q : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (P S : Finset Eisenstein) (α β : Eisenstein → ℂ)
      (Z A T u : ℝ), 65536 ≤ Z → Z^(27/25:ℝ) ≤ A →
      A ≤ Z^2/(1+Real.log Z)^(3*(2*k+dα+dβ)) → Z^(1/50:ℝ) ≤ T →
      (∀ a ∈ P, primary a ∧ A ≤ norm a ∧ norm a ≤ Q*A) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ a ∈ P, ‖α a‖^2) ≤ Mα*A*(1+Real.log Z)^dα →
      (∑ b ∈ S, ‖β b‖^2) ≤ Mβ*Z*(1+Real.log Z)^dβ →
      dyadicHeightMean (fun t =>
        ‖∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)‖) T ≤
      K*A^(5/6:ℝ)*Z^(5/6:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,hK,hvariance⟩ := primeGroupTail_variance_log_saving hMV hC hHuxley
    (fun x => (dispersionCutoff Q x:ℂ)) (dispersionCutoff_complex_compact Q)
    (dispersionCutoff_complex_smooth Q) (2*k+dα) dβ
  refine ⟨2*(Real.sqrt (Mα*(K*Mβ))+1),by positivity,?_⟩
  intro P S α β Z A T u hZ hA hAhi hT hP hS hα hβ
  have hZ₁ : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  have hT₀ : 0 < T := (Real.rpow_pos_of_pos hZp _).trans_le hT
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ₁]
  let V := fun x => (dispersionCutoff Q x:ℂ)
  let f := fun t => ∑ a ∈ P, ∑ b ∈ S, α a*β b*gauss (a*b)*normTwist (u+t) (a*b)
  have hf : Continuous f := by
    apply continuous_finsetSum
    intro a ha
    apply continuous_finsetSum
    intro b hb
    exact continuous_const.mul ((continuous_normTwist (a*b)).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id))
  have hPV : ∀ a ∈ P, 1 ≤ dispersionCutoff Q (norm a/A) := by
    intro a ha
    rw [dispersionCutoff_one (show norm a/A ∈ Set.Icc (1:ℝ) Q from
      ⟨(le_div_iff₀ hA₀).mpr (by simpa using (hP a ha).2.1),
        (div_le_iff₀ hA₀).mpr (by simpa only [mul_comm] using (hP a ha).2.2)⟩)]
  have hvarnonneg : 0 ≤ dyadicHeightMean
      (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T := by
    apply dyadicHeightMean_nonneg
      (f := fun t => ‖smoothedDispersionVariance S β (u+t) V A‖)
      _ hT₀ (fun _ => _root_.norm_nonneg _)
    exact ((continuous_smoothedDispersionVariance S (fun b hb => (hS b hb).1) β V
      (dispersionCutoff_complex_compact Q) (dispersionCutoff_complex_smooth Q) hA₀).comp
      (show Continuous (fun t : ℝ => u+t) from continuous_const.add continuous_id)).norm
  have herror := height_bilinear_full_variance_bound_sq P S α β u
    (fun a ha => (hP a ha).1) (fun b hb => (hS b hb).1)
    (dispersionCutoff Q) (dispersionCutoff_nonneg Q)
    (dispersionCutoff_complex_compact Q) (dispersionCutoff_complex_smooth Q) hA₀ hT₀ hPV
  have hmass := hvariance S β Z A T u Mβ hZ hA hAhi hT hMβ hS hβ
  have hmass' : dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
      (K*Mβ)*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^(2*k+dα) := by
    simpa only [mul_assoc] using hmass
  exact height_bilinear_error_log_saving hf hT₀ hMα (mul_nonneg hK.le hMβ)
    hA₀ hZp hL k dα (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    hvarnonneg herror hα hmass'

end CubicFirstMoment

end

end OAI
