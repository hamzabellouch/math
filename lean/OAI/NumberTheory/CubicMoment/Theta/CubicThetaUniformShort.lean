import OAI.NumberTheory.CubicMoment.Transform.MetaplecticUniformWeights
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedShort

namespace OAI

/-! A uniform finite primal bound on the enlarged transition range
required by the actual fixed theta dilation. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

private lemma uniform_short_square_root_factor {A X R T ε : ℝ}
    (hA : 0 ≤ A) (hX : 0 < X) (hR : 0 ≤ R) :
    Real.sqrt (A*X^(1+ε)*Real.sqrt R*T) =
      Real.sqrt A*Real.sqrt X*X^(ε/2)*R^(1/4:ℝ)*Real.sqrt T := by
  have hx : Real.sqrt (X^(1+ε)) = Real.sqrt X*X^(ε/2) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hX.le,←Real.rpow_add hX]
    congr 1
    ring
  have hr : Real.sqrt (Real.sqrt R) = R^(1/4:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hR]
    norm_num
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hA (Real.rpow_nonneg hX.le _)) (Real.sqrt_nonneg _)),
    Real.sqrt_mul (mul_nonneg hA (Real.rpow_nonneg hX.le _)),Real.sqrt_mul hA,hx,hr]
  ring

theorem UniformLogWeights.cubicTheta_completed_short_mean
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    {ι : Type*} {W : ι → ℝ → ℂ} (h : UniformLogWeights W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ i, ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (Y X T u : ℝ), 1 ≤ Y → 0 < X → 1 ≤ T → X ≤ Y^B →
      X ≤ 729*Real.sqrt (norm r)*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ (W i) X (t+u)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  let S := Real.exp h.radius
  have hS : 1 ≤ S := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr h.radius_nonneg
  have hcut : ∀ i x, S < x → W i x = 0 := h.upper_support
  obtain ⟨M,hM,hsize⟩ := h.uniform_norm_bound
  let ε := 2*η/(B+1)
  have hε : 0 < ε := div_pos (by positivity) (by positivity)
  obtain ⟨D,hD,hbound⟩ := metaplecticHeightCompleted_short_scaled_mean hε hMV hC
  let A := C*D*S^(1+ε)*(1+2*S)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨Real.sqrt (A*729)*M,by positivity,?_⟩
  intro i r hr ℓ Y X T u hY hX hT hXY hshort
  have hYp := zero_lt_one.trans_le hY
  have hR := norm_pos_of_ne_zero (primary_ne_zero hr)
  have he : B*(ε/2) ≤ η := by
    have hh := div_mul_cancel₀ (2*η) (show B+1 ≠ 0 by positivity)
    change ε*(B+1) = 2*η at hh
    nlinarith
  have hpower : X^(ε/2) ≤ Y^η := by
    calc
      _ ≤ (Y^B)^(ε/2) := Real.rpow_le_rpow hX.le hXY (by positivity)
      _ = Y^(B*(ε/2)) := (Real.rpow_mul hYp.le _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hY he
  have hscale : Real.sqrt ((729:ℝ)^2*norm r)=729*Real.sqrt (norm r) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤729^2),Real.sqrt_sq (by norm_num)]
  by_cases hSX : 1 ≤ S*X
  · have hh := hbound r hr ℓ (W i) X S M T u ((729:ℝ)^2*norm r) hX hS (hcut i) (hsize i) hSX hM hT
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_norm (primary_ne_zero hr)))
      (by simpa only [hscale] using hshort)
    apply hh.trans
    change Real.sqrt (A*X^(1+ε)*Real.sqrt ((729:ℝ)^2*norm r)*T)*M ≤ _
    rw [hscale,show A*X^(1+ε)*(729*Real.sqrt (norm r))*T=
      (A*729)*X^(1+ε)*Real.sqrt (norm r)*T by ring,
      uniform_short_square_root_factor (mul_nonneg hA (by norm_num)) hX hR.le]
    calc
      _ = (Real.sqrt (A*729)*M)*Real.sqrt X*X^(ε/2)*norm r^(1/4:ℝ)*Real.sqrt T := by ring
      _ ≤ _ := by gcongr
  · have hz (t : ℝ) := metaplecticHeightCompleted_zero_of_small_support r ℓ (W i) hX
      (lt_of_not_ge hSX) (hcut i) (t+u)
    simp_rw [hz,norm_zero]
    rw [intervalIntegral.integral_zero,zero_div]
    positivity


end CubicFirstMoment

end

end OAI
