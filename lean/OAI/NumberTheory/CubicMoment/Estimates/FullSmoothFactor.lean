import OAI.NumberTheory.CubicMoment.Estimates.LogSmallPartTransfer

namespace OAI

/-! Exact classification of the full smooth factors from the short inverse.
The short Möbius alternative vanishes once the dyad lies above its support. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def primaryShortSmoothSum (A : EisensteinArithmeticFunction) (a b q : Eisenstein)
    (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ) (Z t : ℝ) : ℂ :=
  ∑' x : Eisenstein, if primary x then
    ((MvPowerSeries.coeff (idealExponentOf x) A:ℝ):ℂ)*
      (mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x))*W (norm x/Z)
    else 0

lemma primaryShortSmoothSum_eq_polynomial (A : EisensteinArithmeticFunction)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ) (W : ℝ → ℂ)
    {B Z : ℝ} (hZ : 0 < Z) (hW : ∀ x : ℝ, B < x → W x = 0) (t : ℝ) :
    primaryShortSmoothSum A a b q η W Z t =
      primaryIdealPolynomial (B*Z) A (fun x =>
        mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*mellinPhase t (norm x)*W (norm x/Z)) := by
  rw [primaryIdealPolynomial_eq_elements]
  unfold primaryShortSmoothSum
  rw [primary_weighted_smooth_finite _ W hZ hW]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma primaryShortSmoothSum_zeta (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryShortSmoothSum idealZeta a b q η W Z t = primarySmallTwistSmoothSum a b q η W Z t := by
  simp only [primaryShortSmoothSum,primarySmallTwistSmoothSum,MvPowerSeries.coeff_apply,
    idealZeta,Complex.ofReal_one,one_mul]

lemma primaryShortSmoothSum_log (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (Z t : ℝ) :
    primaryShortSmoothSum idealLogNorm a b q η W Z t = primarySmallTwistLogSmoothSum a b q η W Z t := by
  unfold primaryShortSmoothSum primarySmallTwistLogSmoothSum
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · simp only [ite_eq_left hx,MvPowerSeries.coeff_apply,idealLogNorm,
      idealExponentOf_norm (primary_ne_zero hx)]
  · simp only [ite_eq_right hx]

lemma primaryShortSmoothSum_moebius {F Z : ℝ} (hFZ : Real.sqrt F < Z)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (hWlow : ∀ x : ℝ, x < 1 → W x = 0) (t : ℝ) :
    primaryShortSmoothSum (shortIdealMoebius F) a b q η W Z t = 0 := by
  have hZ : 0 < Z := (Real.sqrt_nonneg F).trans_lt hFZ
  unfold primaryShortSmoothSum
  trans ∑' _x : Eisenstein, (0:ℂ)
  swap
  · exact tsum_zero
  apply tsum_congr
  intro x
  by_cases hx : primary x
  · rw [ite_eq_left hx]
    by_cases hn : idealExponentNorm (idealExponentOf x) ≤ Real.sqrt F
    · have hxZ : norm x/Z < 1 := (div_lt_one hZ).mpr (by
        rw [idealExponentOf_norm (primary_ne_zero hx)] at hn
        exact hn.trans_lt hFZ)
      rw [hWlow _ hxZ,mul_zero]
    · simp only [MvPowerSeries.coeff_apply,shortIdealMoebius,hn,ite_false,
        Complex.ofReal_zero,zero_mul]
  · rw [ite_eq_right hx]

lemma primaryShortSmoothSum_classify {F Z : ℝ} {A : EisensteinArithmeticFunction}
    (hA : ShortArithmeticFactor F A) (hFZ : Real.sqrt F < Z)
    (a b q : Eisenstein) (η : MulChar (Residues q) ℂ)
    (W : ℝ → ℂ) (hWlow : ∀ x : ℝ, x < 1 → W x = 0) (t : ℝ) :
    primaryShortSmoothSum A a b q η W Z t = 0 ∨
    primaryShortSmoothSum A a b q η W Z t = primarySmallTwistSmoothSum a b q η W Z t ∨
    primaryShortSmoothSum A a b q η W Z t = primarySmallTwistLogSmoothSum a b q η W Z t := by
  rcases hA with rfl | rfl | rfl
  · exact Or.inl (primaryShortSmoothSum_moebius hFZ a b q η W hWlow t)
  · exact Or.inr (Or.inl (primaryShortSmoothSum_zeta a b q η W Z t))
  · exact Or.inr (Or.inr (primaryShortSmoothSum_log a b q η W Z t))

lemma full_dyad_above_sqrt {F Y Z : ℝ} (hY : 1 < Y)
    (hF : F ≤ Y^(1001/1000:ℝ)) (hZ : Y^(999/1000:ℝ) ≤ Z) : Real.sqrt F < Z := by
  apply lt_of_lt_of_le _ hZ
  have hY0 : 0 < Y := zero_lt_one.trans hY
  have hs : Real.sqrt F ≤ Y^(1001/2000:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · exact Real.rpow_nonneg hY0.le _
    · have he : (Y^(1001/2000:ℝ))^2 = Y^(1001/1000:ℝ) := by
        rw [← Real.rpow_mul_natCast hY0.le]
        norm_num
      rwa [he]
  exact hs.trans_lt (Real.rpow_lt_rpow_of_exponent_lt hY (by norm_num))

 theorem first_short_full_smooth_partition_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (v b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F N Y Z t : ℝ),
      Y₀ ≤ Y → ShortArithmeticFactor F A → F ≤ Y^(1001/1000:ℝ) →
      primary b → Squarefree b → v ≠ 0 → q ≠ 0 → (3:Eisenstein) ∣ v → q ∣ v →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      1 ≤ N → N ≤ Y^(1001/1000:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b*(9*norm v^2*norm q)^2 ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ norm v < norm a) →
      (∑ a ∈ P, ‖primaryShortSmoothSum A a b q η W Z t‖^2) ≤ C*Y^(58/25:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := first_smalltwist_smooth_partition_power hpub W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := first_smalltwist_log_partition_power hpub W hW hpos hsm hGI hGQ
  refine ⟨max C₁ C₂,max 2 (max T₁ T₂),hC₁.trans (le_max_left _ _),by have := le_max_left (2:ℝ) (max T₁ T₂); linarith,?_⟩
  intro P v b q η A F N Y Z t hY hA hF hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht hP
  have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
  have hY1 : 1 ≤ Y := by linarith
  have hFZ := full_dyad_above_sqrt (show 1 < Y by linarith) hF hYZ
  rcases hA with rfl | rfl | rfl
  · calc
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro a _
        rw [primaryShortSmoothSum_moebius hFZ a b q η W hWlow t,norm_zero]
        norm_num
      _ ≤ _ := mul_nonneg (hC₁.trans (le_max_left _ _)) (Real.rpow_nonneg (by linarith) _)
  · simp_rw [primaryShortSmoothSum_zeta]
    apply (hbound₁ P v b q η N Y Z t
      ((le_max_left T₁ T₂).trans ((le_max_right _ _).trans hY))
      hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht hP).trans
    exact mul_le_mul (le_max_left _ _) (Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num))
      (Real.rpow_nonneg (by linarith) _) (hC₁.trans (le_max_left _ _))
  · simp_rw [primaryShortSmoothSum_log]
    exact (hbound₂ P v b q η N Y Z t
      ((le_max_right T₁ T₂).trans ((le_max_right _ _).trans hY))
      hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hsize ht hP).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (by linarith) _))

end CubicFirstMoment

end

end OAI
