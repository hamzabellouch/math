import OAI.NumberTheory.CubicMoment.Angular.AngularSmallTwistSmoothMoment
import OAI.NumberTheory.CubicMoment.Estimates.DominantSmoothPower
import OAI.NumberTheory.CubicMoment.Estimates.NaturalDualCutoff
import OAI.NumberTheory.CubicMoment.Estimates.SmallTwistPower

namespace OAI

/-! An explicit positive saving for dominant smooth factors with a small
extra finite character, including all Euler rescaling costs. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

 theorem first_angular_smalltwist_smooth_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b q : Eisenstein)
      (η : MulChar (Residues q) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → q ≠ 0 →
      (AngularUnitCompatible q η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) q) →
      1 ≤ N → 1 ≤ Y → 9*norm q ≤ Z → 1 ≤ J →
      N ≤ Y^(101/100:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(3/4:ℝ) →
      norm q ≤ Y^(1/1000:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b*norm q^2/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-(1/1000:ℝ)) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(23/10:ℝ) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := primary_angular_smalltwist_smooth_cubic_moment hpub ℓ
    (show (0:ℝ) < 1/100 by norm_num) W hW hpos hsm
    (show (0:ℝ) < 1/1000 by norm_num) 2 2 hGI hGQ
  obtain ⟨K,hK,henv⟩ := dominant_cubic_envelope
  refine ⟨C*K*(9:ℝ)^(3/100:ℝ)+18*D*(9:ℝ)^(1/50:ℝ),by positivity,?_⟩
  intro P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ hNY hZY hJY hqY hP hcut
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hZ1 : 1 ≤ Z := (by nlinarith [one_le_norm hq] : (1:ℝ) ≤ 9*norm q).trans hZ
  have hbound' := hbound P b q η N Y Z J t hb hsb hq hη hsmall hN hY hZ hJ
    (hZY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)))
    (hJY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))) hP hcut
  have hcard : (P.card:ℝ) ≤ 18*N := by
    have hsub : P ⊆ primaryElementBall N :=
      fun a ha => mem_primaryElementBall.mpr ⟨(hP a ha).1,(hP a ha).2.2.1⟩
    exact (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
      (primaryElementBall_card_le (by linarith))
  have hq3 := small_modulus_rpow hY (show (0:ℝ) ≤ 3/100 by norm_num) hqY
  have hq2 := small_modulus_rpow hY (show (0:ℝ) ≤ 1/50 by norm_num) hqY
  norm_num only [div_div] at hq3 hq2
  have hm : C*Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*q)^(3*(1/100:ℝ)) ≤
      (C*K*(9:ℝ)^(3/100:ℝ))*Y^(23/10:ℝ) := by
    calc
      _ ≤ (C*(K*Y^(9/4:ℝ)))*((9:ℝ)^(3/100:ℝ)*Y^((3/100:ℝ)/1000)) := by
        apply mul_le_mul _ (by convert hq3 using 1 <;> norm_num) (Real.rpow_nonneg (norm_nonneg (3*q)) _) (by positivity)
        have h := mul_le_mul_of_nonneg_left (henv N Z J Y hY hN hZ1 hJ hNY hZY hJY) hC
        simpa only [mul_assoc] using h
      _ = (C*K*(9:ℝ)^(3/100:ℝ))*Y^((9/4:ℝ)+(3/100)/1000) := by
        rw [Real.rpow_add hY0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)
  have ht : D*P.card*Y^(-(2:ℝ)*2)*norm (3*q)^(2*(1/100:ℝ)) ≤
      (18*D*(9:ℝ)^(1/50:ℝ))*Y^(23/10:ℝ) := by
    have hpow : Y^(-(2:ℝ)*2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)
    calc
      _ ≤ (D*(18*Y^(101/100:ℝ))*1)*((9:ℝ)^(1/50:ℝ)*Y^((1/50:ℝ)/1000)) := by
        apply mul_le_mul _ (by convert hq2 using 1 <;> norm_num) (Real.rpow_nonneg (norm_nonneg (3*q)) _) (by positivity)
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (hcard.trans (mul_le_mul_of_nonneg_left hNY (by norm_num))) hD) hpow (by positivity) (by positivity)
      _ = (18*D*(9:ℝ)^(1/50:ℝ))*Y^((101/100:ℝ)+(1/50)/1000) := by
        rw [Real.rpow_add hY0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by positivity)
  exact hbound'.trans (by nlinarith [hm,ht])

end CubicFirstMoment

end

end OAI
