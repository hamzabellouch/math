import OAI.NumberTheory.CubicMoment.Estimates.MixedSmoothMoment
import OAI.NumberTheory.CubicMoment.Estimates.ShortFactorMoments

namespace OAI

/-! A quantitative gap for a dominant full smooth factor in the first
exceptional configuration. The natural dual cutoff is kept explicit. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma dominant_cubic_envelope :
    ∃ K : ℝ, 0 < K ∧ ∀ N Z J Y : ℝ, 1 ≤ Y → 1 ≤ N → 1 ≤ Z → 1 ≤ J →
      N ≤ Y^(101/100:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(3/4:ℝ) →
      Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ)) ≤ K*Y^(9/4:ℝ) := by
  let K : ℝ := (2:ℝ)^(1/100:ℝ)*(3+(2:ℝ)^(2/3:ℝ))
  refine ⟨K,by dsimp [K]; positivity,?_⟩
  intro N Z J Y hY hN hZ hJ hNY hZY hJY
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hQ : N*(2*J) ≤ 2*Y^(44/25:ℝ) := by
    calc
      _ ≤ Y^(101/100:ℝ)*(2*Y^(3/4:ℝ)) := by gcongr
      _ = 2*(Y^(101/100:ℝ)*Y^(3/4:ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hY0]; norm_num
  have hpow (s : ℝ) (hs : 0 ≤ s) :
      (N*(2*J))^s ≤ (2:ℝ)^s*Y^((44/25)*s) := by
    calc
      _ ≤ (2*Y^(44/25:ℝ))^s := Real.rpow_le_rpow (by positivity) hQ hs
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hY0.le _),
        ← Real.rpow_mul hY0.le]
  have hsmall := hpow (1/100) (by norm_num)
  have hlarge := hpow (2/3) (by norm_num)
  norm_num at hsmall hlarge
  have hnF : N ≤ Y^(88/75:ℝ) := hNY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hjF : J ≤ Y^(88/75:ℝ) := hJY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have hF : N+2*J+(N*(2*J))^(2/3:ℝ) ≤
      (3+(2:ℝ)^(2/3:ℝ))*Y^(88/75:ℝ) := by nlinarith
  calc
    _ ≤ Y^(101/100:ℝ)*((2:ℝ)^(1/100:ℝ)*Y^(11/625:ℝ))*
        ((3+(2:ℝ)^(2/3:ℝ))*Y^(88/75:ℝ)) := by
      exact mul_le_mul (mul_le_mul hZY hsmall (by positivity) (by positivity)) hF
        (by positivity) (by positivity)
    _ = K*Y^((101/100:ℝ)+11/625+88/75) := by
      dsimp [K]
      rw [Real.rpow_add hY0,Real.rpow_add hY0]
      ring
    _ ≤ K*Y^(9/4:ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)) (by dsimp [K]; positivity)

theorem first_mixed_smooth_power (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Finset Eisenstein) (b : Eisenstein) (N Y Z J t : ℝ),
      primary b → Squarefree b → 1 ≤ N → 1 ≤ Y → 9 ≤ Z → 1 ≤ J →
      N ≤ Y^(101/100:ℝ) → Z ≤ Y^(101/100:ℝ) → J ≤ Y^(3/4:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧
        IsCoprime a b ∧ ¬ IsUnit (a*b)) →
      ((243*N*norm b/(2*Real.pi)^2)*(1+|t|)^2)/(Z*J) ≤ Y^(-(1/1000:ℝ)) →
      (∑ a ∈ P, ‖primaryMixedSmoothSum a b W Z t‖^2) ≤ C*Y^(9/4:ℝ) := by
  obtain ⟨C,D,hC,hD,hbound⟩ := primary_mixed_smooth_cubic_moment hpub
    (show (0:ℝ) < 1/100 by norm_num) W hW hpos hsm
    (show (0:ℝ) < 1/1000 by norm_num) 2 2 hGI hGQ
  obtain ⟨K,hK,henv⟩ := dominant_cubic_envelope
  refine ⟨C*K+18*D,by positivity,?_⟩
  intro P b N Y Z J t hb hsb hN hY hZ hJ hNY hZY hJY hP hcut
  have hZ1 : 1 ≤ Z := by linarith
  have hbound' := hbound P b N Y Z J t hb hsb hN hY hZ hJ
    (hZY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num)))
    (hJY.trans (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))) hP hcut
  have hcard : (P.card:ℝ) ≤ 18*N := by
    have hsub : P ⊆ primaryElementBall N :=
      fun a ha => mem_primaryElementBall.mpr ⟨(hP a ha).1,(hP a ha).2.2.1⟩
    exact (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans
      (primaryElementBall_card_le (by linarith))
  have hpow : Y^(-(2:ℝ)*2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hY (by norm_num)
  have hNY' : N ≤ Y^(9/4:ℝ) := hNY.trans
    (Real.rpow_le_rpow_of_exponent_le hY (by norm_num))
  have htail : D*P.card*Y^(-(2:ℝ)*2) ≤ (18*D)*Y^(9/4:ℝ) := by
    calc
      _ ≤ D*(18*N)*1 := mul_le_mul
        (mul_le_mul_of_nonneg_left hcard hD) hpow (by positivity) (by positivity)
      _ ≤ (18*D)*Y^(9/4:ℝ) := by nlinarith
  calc
    _ ≤ C*Z*(N*(2*J))^(1/100:ℝ)*(N+2*J+(N*(2*J))^(2/3:ℝ)) +
        D*P.card*Y^(-(2:ℝ)*2) := hbound'
    _ ≤ C*(K*Y^(9/4:ℝ))+(18*D)*Y^(9/4:ℝ) := by
      apply add_le_add _ htail
      have h := mul_le_mul_of_nonneg_left (henv N Z J Y hY hN hZ1 hJ hNY hZY hJY) hC
      simpa only [mul_assoc] using h
    _ = _ := by ring

end CubicFirstMoment

end

end OAI
