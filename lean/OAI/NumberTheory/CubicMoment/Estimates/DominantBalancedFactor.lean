import OAI.NumberTheory.CubicMoment.Estimates.BalancedFullSmoothFactor
import OAI.NumberTheory.CubicMoment.Estimates.DominantSmoothSizes

namespace OAI

/-! The actual full factor on a balanced conductor pairs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem dominant_balanced_full_factor (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (D : ℝ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
      ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3:ℝ) ∧
        norm a.2 ≤ Y^(1/3:ℝ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryShortSmoothSum A a.1 a.2 q η W (X/2) t‖^2) ≤ K*Y^(111/50:ℝ) := by
  classical
  obtain ⟨K,T₁,hK,hT₁,hbound⟩ := balanced_short_full_smooth_partition_power hpub W hW hpos hsm hWlow hGI hGQ
  obtain ⟨T₂,hT₂,hscale⟩ := eventual_dominant_smooth_scales D
  obtain ⟨T₃,hT₃,hlocal⟩ := eventual_small_part_modulus_size
  refine ⟨K,max T₁ (max T₂ T₃),hK,hT₂.trans ((le_max_left _ _).trans (le_max_right _ _)),?_⟩
  intro P q η A F Y X t hY hA hF hq hη hqY ht hXlo hXhi hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hYT₂ : T₂ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hY)
  have hYT₃ : T₃ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hY)
  have hY2 : 2 ≤ Y := hT₂.trans hYT₂
  have hY1 : 1 ≤ Y := by linarith
  have hY0 : 0 < Y := by linarith
  have hs := hscale Y hYT₂
  have hXs := hs.2.2.1 X hXlo hXhi
  have h3 : norm (3:Eisenstein) = 9 := by
    change Complex.normSq (3:ℂ) = 9
    norm_num [Complex.normSq]
  have hvq : norm (3*q) ≤ Y^(1/10000:ℝ) := by
    rw [norm_mul_eq,h3]
    exact hs.2.2.2 (norm q) hqY
  have hqsmall : norm q ≤ Y^(1/10000:ℝ) := hqY.trans
    (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  have hsize := hlocal Y (norm (3*q)) (norm q) hYT₃
    (norm_nonneg _) (norm_nonneg _) hvq hqsmall
  apply hbound P (3*q) q η A F Y (X/2) t hYT₁ hA (hF.trans hs.2.1)
    (mul_ne_zero (by norm_num) hq) hq (dvd_mul_right _ _) (dvd_mul_left _ _) hη
    hXs.2 hXs.1 hsize ht
  intro a ha
  have hp := hP a ha
  refine ⟨hp.1,?_,?_,?_⟩
  · exact hp.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  · exact hp.2.2.1.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
  · exact small_part_smaller_than_row (by linarith) hvq hp.2.2.2

end CubicFirstMoment

end

end OAI
