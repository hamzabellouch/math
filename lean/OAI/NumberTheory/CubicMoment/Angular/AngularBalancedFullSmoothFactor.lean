import OAI.NumberTheory.CubicMoment.Angular.AngularFullSmoothFactor
import OAI.NumberTheory.CubicMoment.Angular.AngularLogBalancedSmallParts

namespace OAI

/-! The actual short-inverse full-factor bound for balanced rows. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
 theorem balanced_angular_short_full_smooth_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (v q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y Z t : ℝ),
      Y₀ ≤ Y → ShortArithmeticFactor F A → F ≤ Y^(1001/1000:ℝ) →
      v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      9*norm v^2*norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ norm v < norm a.1) →
      (∑ a ∈ P, ‖primaryAngularShortSmoothSum ℓ A a.1 a.2 q η W Z t‖^2) ≤ C*Y^(111/50:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := balanced_angular_smalltwist_smooth_partition_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := balanced_angular_smalltwist_log_partition_power hpub ℓ W hW hpos hsm hGI hGQ
  refine ⟨max C₁ C₂,max 2 (max T₁ T₂),hC₁.trans (le_max_left _ _),by have := le_max_left (2:ℝ) (max T₁ T₂); linarith,?_⟩
  intro P v q η A F Y Z t hY hA hF hv hq h3 hqv hη hZY hYZ hsize ht hP
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hFZ := full_dyad_above_sqrt (show 1 < Y by linarith) hF hYZ
  rcases hA with rfl | rfl | rfl
  · calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [primaryAngularShortSmoothSum_moebius ℓ hFZ a.1 a.2 q η W hWlow t,norm_zero]
        norm_num
      _ ≤ _ := mul_nonneg (hC₁.trans (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _)
  · simp_rw [primaryAngularShortSmoothSum_zeta]
    apply (hbound₁ P v q η Y Z t
      ((le_max_left T₁ T₂).trans ((le_max_right _ _).trans hY))
      hv hq h3 hqv hη hZY hYZ hsize ht hP).trans
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (hC₁.trans (le_max_left _ _))
  · simp_rw [primaryAngularShortSmoothSum_log]
    exact (hbound₂ P v q η Y Z t
      ((le_max_right T₁ T₂).trans ((le_max_right _ _).trans hY))
      hv hq h3 hqv hη hZY hYZ hsize ht hP).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))


end CubicFirstMoment

end

end OAI
