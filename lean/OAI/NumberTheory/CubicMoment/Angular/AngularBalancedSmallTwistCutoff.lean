import OAI.NumberTheory.CubicMoment.Angular.AngularBalancedSmallTwistPower
import OAI.NumberTheory.CubicMoment.Estimates.BalancedCutoff

namespace OAI

/-! The natural cutoff and lower rescaled length for a small-twisted
full sum, uniformly up to the required height Y^0.37. -/
noncomputable section
open Filter Set
open scoped ContDiff BigOperators
namespace CubicFirstMoment

 theorem balanced_angular_smalltwist_smooth_power_at_height (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) → 1 ≤ N →
      N ≤ Y^(17/50:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b ≤ Y^(17/50:ℝ) → norm q ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(9/5:ℝ) := by
  obtain ⟨C,hC,hbound⟩ := balanced_angular_smalltwist_smooth_power hpub ℓ W hW hpos hsm hGI hGQ
  obtain ⟨A,hA,hcut⟩ := eventual_balanced_natural_cutoff
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (show (0:ℝ) < 998/1000 by norm_num)).eventually_ge_atTop (9:ℝ))
  refine ⟨C,max A T,hC,hA.trans (le_max_left _ _),?_⟩
  intro P b q η N Y Z t hY hb hsb hq hη hsmall hN hNY hZY hYZ hbY hqY ht hP
  have hYA : A ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := hA.trans hYA
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hB : norm b*norm q^2 ≤ Y^(171/500:ℝ) := by
    calc
      _ ≤ Y^(17/50:ℝ)*(Y^(1/1000:ℝ))^2 :=
        mul_le_mul hbY (pow_le_pow_left₀ (norm_nonneg q) hqY 2)
          (sq_nonneg _) (Real.rpow_nonneg hY0.le _)
      _ = _ := by
        rw [← Real.rpow_mul_natCast hY0.le,← Real.rpow_add hY0]
        norm_num
  have h9 : 9 ≤ Y^(998/1000:ℝ) := hT Y ((le_max_right _ _).trans hY)
  have hZ : 9*norm q ≤ Z := by
    calc
      _ ≤ 9*Y^(1/1000:ℝ) := mul_le_mul_of_nonneg_left hqY (by norm_num)
      _ ≤ Y^(998/1000:ℝ)*Y^(1/1000:ℝ) :=
        mul_le_mul_of_nonneg_right h9 (Real.rpow_nonneg hY0.le _)
      _ = Y^(999/1000:ℝ) := by rw [← Real.rpow_add hY0]; norm_num
      _ ≤ Z := hYZ
  have hJ : 1 ≤ Y^(1/2:ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hc := hcut Y N (norm b*norm q^2) Z t hYA (by linarith)
    (by positivity [norm_nonneg b]) hNY hB hYZ ht
  apply hbound P b q η N Y Z (Y^(1/2:ℝ)) t hb hsb hq hη hsmall hN hY1 hZ hJ
    (hNY.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)))
    (hZY.trans (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))) le_rfl hqY hP
  simpa only [mul_assoc] using hc

end CubicFirstMoment

end

end OAI
