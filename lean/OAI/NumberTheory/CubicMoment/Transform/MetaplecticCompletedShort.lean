import OAI.NumberTheory.CubicMoment.Transform.MetaplecticShortScale

namespace OAI

/-! The short angular completed mean, with the fixed smooth weight's
actual support and size bounds constructed, including the empty range. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

lemma metaplecticHeightCompleted_zero_of_small_support (r : Eisenstein) (ℓ : ℤ)
    (W : ℝ → ℂ) {X S : ℝ} (hX : 0 < X) (hSX : S*X < 1)
    (hcut : ∀ x : ℝ, S < x → W x = 0) (t : ℝ) :
    metaplecticHeightCompleted r ℓ W X t = 0 := by
  unfold metaplecticHeightCompleted
  have hz (du : PrimaryArgument × PrimaryArgument) :
      metaplecticPrimalCoefficient r ℓ W X (metaplecticPrimaryPair du)*
        mellinPhase t (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))) = 0 := by
    have hp : primary (metaplecticCubeProduct (metaplecticPrimaryPair du)) := by
      apply primary_mul du.2.property
      simpa only [pow_succ,pow_zero,one_mul,metaplecticPrimaryPair] using
        primary_mul (primary_mul du.1.property du.1.property) du.1.property
    have hn := one_le_norm (primary_ne_zero hp)
    have hw : W (norm (metaplecticCubeProduct (metaplecticPrimaryPair du))/X) = 0 :=
      hcut _ ((lt_div_iff₀ hX).mpr (hSX.trans_le hn))
    simp [metaplecticPrimalCoefficient,hw]
  simp_rw [hz,tsum_zero]

private lemma short_square_root_factor {A X R T ε : ℝ}
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

theorem metaplectic_completed_short_mean
    {C : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hc : Continuous W)
    {η B : ℝ} (hη : 0 < η) (hB : 0 ≤ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ r : Eisenstein, primary r →
      ∀ (ℓ : ℤ) (Y X T u : ℝ), 1 ≤ Y → 0 < X → 1 ≤ T → X ≤ Y^B →
      X ≤ Real.sqrt (norm r)*T^2 →
      (∫ t in T..2*T, ‖metaplecticHeightCompleted r ℓ W X (t+u)‖)/T ≤
        K*Real.sqrt X*Y^η*norm r^(1/4:ℝ)*Real.sqrt T := by
  obtain ⟨S₀,hS₀⟩ := hW.isCompact.isBounded.exists_norm_le
  let S := max S₀ 1
  have hS : 1 ≤ S := le_max_right _ _
  have hcut : ∀ x : ℝ, S < x → W x = 0 := by
    intro x hx
    by_contra hn
    have hh := hS₀ x (subset_tsupport W hn)
    rw [Real.norm_eq_abs] at hh
    have hs : S₀ ≤ S := le_max_left _ _
    linarith [le_abs_self x]
  obtain ⟨M₀,hM₀⟩ := (hW.isCompact.image hc).isBounded.exists_norm_le
  let M := max M₀ 0
  have hM : 0 ≤ M := le_max_right _ _
  have hsize : ∀ x : ℝ, ‖W x‖ ≤ M := by
    intro x
    by_cases hx : W x = 0
    · simpa only [hx,norm_zero] using hM
    · exact (hM₀ _ ⟨x,subset_tsupport W hx,rfl⟩).trans (le_max_left _ _)
  let ε := 2*η/(B+1)
  have hε : 0 < ε := div_pos (by positivity) (by positivity)
  obtain ⟨D,hD,hbound⟩ := metaplecticHeightCompleted_short_scaled_mean hε hMV hC
  let A := C*D*S^(1+ε)*(1+2*S)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨Real.sqrt A*M,by positivity,?_⟩
  intro r hr ℓ Y X T u hY hX hT hXY hshort
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
  by_cases hSX : 1 ≤ S*X
  · have hh := hbound r hr ℓ W X S M T u (norm r) hX hS hcut hsize hSX hM hT
      (one_le_norm (primary_ne_zero hr)) hshort
    apply hh.trans
    change Real.sqrt (A*X^(1+ε)*Real.sqrt (norm r)*T)*M ≤ _
    rw [short_square_root_factor hA hX hR.le]
    calc
      _ = (Real.sqrt A*M)*Real.sqrt X*X^(ε/2)*norm r^(1/4:ℝ)*Real.sqrt T := by ring
      _ ≤ _ := by gcongr
  · have hz (t : ℝ) := metaplecticHeightCompleted_zero_of_small_support r ℓ W hX
      (lt_of_not_ge hSX) hcut (t+u)
    simp_rw [hz,norm_zero]
    rw [intervalIntegral.integral_zero,zero_div]
    positivity

end CubicFirstMoment

end

end OAI
