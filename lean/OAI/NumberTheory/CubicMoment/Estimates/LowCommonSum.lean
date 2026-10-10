import OAI.NumberTheory.CubicMoment.Estimates.LowCommonBlock
import OAI.NumberTheory.CubicMoment.Estimates.CommonWeightSum
import OAI.NumberTheory.CubicMoment.Estimates.SmallBCommonSum

namespace OAI

/-! Summing the literal common-factor blocks costs a convergent arithmetic
series, without a power of the short-variable length. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment.ProfileControl

theorem low_common_sum_height_log_saving
    (hpnt : PrimaryPrimePNT) (j : ℕ)
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve) :
    ∃ (K : ℝ) (Ct : ℕ), 0 < K ∧ ∀ (P : PoissonProfileBudget)
      (S I : Finset Eisenstein) (β : Eisenstein → ℂ) (Z A T M u : ℝ),
      (65536:ℝ)^2 ≤ Z → Z^(3/2:ℝ) ≤ A → (1+Real.log Z)^Ct ≤ T → 0 ≤ M →
      I ⊆ commonRowFactors S → (∀ k ∈ I, norm k ≤ Z^(1/2:ℝ)) →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∀ b ∈ S, ‖β b‖ ≤ M) →
      dyadicHeightMean (fun t => ‖∑ k ∈ I, commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T ≤
      (K*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j := by
  obtain ⟨K₀,Ct,hK₀,hblock⟩ := low_common_block_height_log_saving hpnt j hMV hC hHuxley
  obtain ⟨D,hD,hweight⟩ := common_factor_weight_sum_bound
  refine ⟨K₀*D,Ct,by positivity,?_⟩
  intro P S I β Z A T M u hZ hA hT hM hI hnorm hS hβ
  have hZ1 : 1 ≤ Z := by nlinarith
  have hL : 0 < 1+Real.log Z := by linarith [Real.log_nonneg hZ1]
  have hTp : 0 < T := (pow_pos (by linarith [Real.log_nonneg hZ1]) _).trans_le hT
  have hS₀ : ∀ b ∈ S, primary b ∧ Squarefree b := fun b hb => ⟨(hS b hb).1,(hS b hb).2.1⟩
  have hKP : 0 < K₀*P.cost := mul_pos hK₀ P.cost_pos
  have hA0 : 0 ≤ A := (Real.rpow_nonneg (by linarith : 0 ≤ Z) _).trans hA
  let W := (K₀*P.cost)*M^2*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^j
  have hW : 0 ≤ W := by dsimp [W]; positivity
  calc
    _ ≤ ∑ k ∈ I, dyadicHeightMean (fun t => ‖commonGramBlock S
        (fun b => star (dispersionAmplitude β (u+t) b)) P.V A k‖) T :=
      dyadicHeightMean_norm_sum_le I _
        (fun k _ => continuous_commonGramBlock_height S β k P.V A u) hTp
    _ ≤ ∑ k ∈ I, W*((2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact hblock P S β Z A T M u k hZ hA hT hM
        (commonRowFactors_spec hS₀ (hI hk)).1
        (commonRowFactors_spec hS₀ (hI hk)).2 (hnorm k hk) hS hβ
    _ = W*(∑ k ∈ I, (2:ℝ)^(primaryPrimeFactors k).card*norm k^(-(5/3:ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ W*D := mul_le_mul_of_nonneg_left
      (hweight I (fun k hk => (commonRowFactors_spec hS₀ (hI hk)).1)) hW
    _ = _ := by dsimp [W]; ring

end CubicFirstMoment.ProfileControl

end

end OAI
