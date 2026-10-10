import OAI.NumberTheory.CubicMoment.Estimates.PrimeGroupTailVariance
import OAI.NumberTheory.CubicMoment.Estimates.SmallBLogScale

namespace OAI

/-! An arbitrary logarithmic saving for the actual small-B variance,
including its diagonal, under the explicit upper outer-length cutoff. -/
noncomputable section
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem primeGroupTail_variance_log_saving
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hV' : ContDiff ℝ ∞ V) (k d : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (S : Finset Eisenstein) (β : Eisenstein → ℂ)
      (Z A T u M : ℝ), 65536 ≤ Z → Z^(27/25:ℝ) ≤ A →
      A ≤ Z^2/(1+Real.log Z)^(3*(k+d)) → Z^(1/50:ℝ) ≤ T → 0 ≤ M →
      (∀ b ∈ S, primary b ∧ Squarefree b ∧ Z/2 ≤ norm b ∧ norm b ≤ Z) →
      (∑ b ∈ S, ‖β b‖^2) ≤ M*Z*(1+Real.log Z)^d →
      dyadicHeightMean (fun t => ‖smoothedDispersionVariance S β (u+t) V A‖) T ≤
      K*M*A^(2/3:ℝ)*Z^(5/3:ℝ)/(1+Real.log Z)^k := by
  obtain ⟨K,hK,hbound⟩ := primeGroupTail_full_variance_height_power hMV hC hHuxley V hV hV'
  obtain ⟨H,hH,hlog⟩ := log_power_normalization_bound (k+d)
    (s := 1/80000) (by norm_num)
  refine ⟨K*(1+H),by positivity,?_⟩
  intro S β Z A T u M hZ hA hAhi hT hM hS henergy
  have hZ₁ : 1 ≤ Z := by linarith
  have hZp : 0 < Z := by linarith
  have hA₀ : 0 < A := (Real.rpow_pos_of_pos hZp _).trans_le hA
  let L := 1+Real.log Z
  have hL : 0 < L := by dsimp [L]; linarith [Real.log_nonneg hZ₁]
  have hd := smallB_diagonal_log_scale hA₀ hZp hL k d hAhi
  have hn := smallB_nondiagonal_log_scale hA₀.le hZp hL k d (hlog Z hZ₁)
  have hz : Z^(2/3-1/80000:ℝ)*Z = Z^(5/3-1/80000:ℝ) := by
    nth_rw 2 [← Real.rpow_one Z]
    rw [← Real.rpow_add hZp]
    congr 1
    norm_num
  calc
    _ ≤ K*(A+A^(2/3:ℝ)*Z^(2/3-1/80000:ℝ))*(M*Z*L^d) :=
      (hbound S β Z A T u hZ hA hT hS).trans
        (mul_le_mul_of_nonneg_left henergy (by positivity))
    _ = (K*M)*(A*Z*L^d+A^(2/3:ℝ)*Z^(5/3-1/80000:ℝ)*L^d) := by
      rw [← hz]
      ring
    _ ≤ (K*M)*(A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k+
        H*A^(2/3:ℝ)*Z^(5/3:ℝ)/L^k) :=
      mul_le_mul_of_nonneg_left (add_le_add hd hn) (mul_nonneg hK.le hM)
    _ = _ := by dsimp [L]; ring

end CubicFirstMoment

end

end OAI
