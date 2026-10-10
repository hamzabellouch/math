import OAI.NumberTheory.CubicMoment.Angular.AngularFullSmoothFactor
import OAI.NumberTheory.CubicMoment.Estimates.DominantSmoothSizes

namespace OAI

/-! The actual full factor on a first-configuration conductor dyad. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem angular_dominant_first_full_factor (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) (D : ℝ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
      ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, gramDyad Y a) →
      (∑ a ∈ P, ‖primaryAngularShortSmoothSum ℓ A a 1 q η W (X/2) t‖^2) ≤ K*Y^(58/25:ℝ) := by
  classical
  obtain ⟨K,T₁,hK,hT₁,hbound⟩ := first_angular_short_full_smooth_partition_power hpub ℓ W hW hpos hsm hWlow hGI hGQ
  obtain ⟨T₂,hT₂,hscale⟩ := eventual_dominant_smooth_scales D
  obtain ⟨T₃,hT₃,hlocal⟩ := eventual_small_part_conductor_size
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
  have hsize := hlocal Y 1 (norm (3*q)) (norm q) hYT₃ (by norm_num)
    (norm_nonneg _) (norm_nonneg _) (Real.one_le_rpow hY1 (by norm_num)) hvq hqsmall
  have hb : primary (1:Eisenstein) := by norm_num [primary]
  have h1 : norm (1:Eisenstein) = 1 := by
    change Complex.normSq (1:ℂ) = 1
    norm_num [Complex.normSq]
  have hsb : Squarefree (1:Eisenstein) := squarefree_one
  apply hbound P (3*q) 1 q η A F (2*Y) Y (X/2) t hYT₁ hA (hF.trans hs.2.1)
    hb hsb (mul_ne_zero (by norm_num) hq) hq (dvd_mul_right _ _) (dvd_mul_left _ _) hη
    (by linarith) hs.1 hXs.2 hXs.1
  · simpa only [h1,one_mul] using hsize
  · exact ht
  · intro a ha
    have hp := hP a ha
    refine ⟨hp.1,hp.2.1,hp.2.2.2.le,?_ ,?_⟩
    · exact isCoprime_one_right
    · have hyr : Y^(1/1000:ℝ) ≤ Y := by
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hY1 (show (1/1000:ℝ) ≤ 1 by norm_num)
      have hyl : Y^(1/1000:ℝ) ≤ norm a := hyr.trans hp.2.2.1
      exact small_part_smaller_than_row (by linarith) hvq hyl

end CubicFirstMoment

end

end OAI
