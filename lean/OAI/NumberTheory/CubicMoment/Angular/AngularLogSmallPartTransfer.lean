import OAI.NumberTheory.CubicMoment.Angular.AngularSmallPartTransfer

namespace OAI

/-! Logarithmic full factors after the exact small-prime row partition. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
 theorem first_angular_smalltwist_log_partition_power (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C Y₀ : ℝ, 0 ≤ C ∧ 1 ≤ Y₀ ∧
      ∀ (P : Finset Eisenstein) (v b q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (N Y Z t : ℝ), Y₀ ≤ Y → primary b → Squarefree b → v ≠ 0 → q ≠ 0 →
      (3:Eisenstein) ∣ v → q ∣ v →
      (AngularUnitCompatible q η ℓ) →
      1 ≤ N →
      N ≤ Y^(1001/1000:ℝ) → Z ≤ Y^(1001/1000:ℝ) → Y^(999/1000:ℝ) ≤ Z →
      norm b*(9*norm v^2*norm q)^2 ≤ Y^(1/1000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b ∧ norm v < norm a) →
      (∑ a ∈ P, ‖primaryAngularSmallTwistLogSmoothSum ℓ a b q η W Z t‖^2) ≤ C*Y^(58/25:ℝ) := by
  obtain ⟨C₁,T₁,hC₁,hT₁,hbound₁⟩ := first_angular_smalltwist_smooth_partition_power hpub ℓ
    W hW hpos hsm hGI hGQ
  obtain ⟨C₂,T₂,hC₂,hT₂,hbound₂⟩ := first_angular_smalltwist_smooth_partition_power hpub ℓ
    (logSmoothWeight W) (logSmoothWeight_compact hW) (logSmoothWeight_positive hpos)
    (logSmoothWeight_smooth hpos hsm) hGI hGQ
  refine ⟨80802*C₁+2*C₂,max T₁ T₂,by positivity,hT₁.trans (le_max_left _ _),?_⟩
  intro P v b q η N Y Z t hY hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hB ht hP
  have hYT₁ : T₁ ≤ Y := (le_max_left _ _).trans hY
  have hYT₂ : T₂ ≤ Y := (le_max_right _ _).trans hY
  have hY1 : 1 ≤ Y := hT₁.trans hYT₁
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hZ1 : 1 ≤ Z := (Real.one_le_rpow hY1 (by norm_num : (0:ℝ) ≤ 999/1000)).trans hYZ
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ1
  have hb₁ := hbound₁ P v b q η N Y Z t hYT₁ hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hB ht hP
  have hb₂ := hbound₂ P v b q η N Y Z t hYT₂ hb hsb hv hq h3 hqv hη hN hNY hZY hYZ hB ht hP
  have hlog : Real.log Z ≤ 201*Y^(1/200:ℝ) := by
    have hlogZ := Real.log_le_log hZ0 hZY
    rw [Real.log_rpow hY0] at hlogZ
    have hlogY := Real.log_le_rpow_div hY0.le (show (0:ℝ) < 1/200 by norm_num)
    have hpow : 0 ≤ Y^(1/200:ℝ) := Real.rpow_nonneg hY0.le _
    norm_num at hlogY
    nlinarith
  have hlog2 : (Real.log Z)^2 ≤ 40401*Y^(1/100:ℝ) := by
    have h := pow_le_pow_left₀ (Real.log_nonneg hZ1) hlog 2
    have hp : (Y^(1/200:ℝ))^2 = Y^(1/100:ℝ) := by
      rw [← Real.rpow_mul_natCast hY0.le]
      norm_num
    simpa only [mul_pow,hp,show (201:ℝ)^2 = 40401 by norm_num] using h
  have hrow (a : Eisenstein) :
      ‖primaryAngularSmallTwistLogSmoothSum ℓ a b q η W Z t‖^2 ≤
        2*(Real.log Z)^2*‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2+
        2*‖primaryAngularSmallTwistSmoothSum ℓ a b q η (logSmoothWeight W) Z t‖^2 := by
    exact primary_log_smooth_sq_le
      (fun x => mixedCubic a b x*η (Ideal.Quotient.mk (modulus q) x)*theta ℓ x*mellinPhase t (norm x)) W hW hZ0
  calc
    _ ≤ ∑ a ∈ P, (2*(Real.log Z)^2*‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2+
        2*‖primaryAngularSmallTwistSmoothSum ℓ a b q η (logSmoothWeight W) Z t‖^2) :=
      Finset.sum_le_sum (fun a _ => hrow a)
    _ = 2*(Real.log Z)^2*(∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η W Z t‖^2)+
        2*(∑ a ∈ P, ‖primaryAngularSmallTwistSmoothSum ℓ a b q η (logSmoothWeight W) Z t‖^2) := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    _ ≤ 2*(40401*Y^(1/100:ℝ))*(C₁*Y^(231/100:ℝ))+2*(C₂*Y^(231/100:ℝ)) := by
      apply add_le_add _ (mul_le_mul_of_nonneg_left hb₂ (by norm_num))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlog2 (by norm_num)) hb₁
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
    _ ≤ (80802*C₁+2*C₂)*Y^(58/25:ℝ) := by
      have hp : Y^(1/100:ℝ)*Y^(231/100:ℝ) = Y^(58/25:ℝ) := by
        rw [← Real.rpow_add hY0]
        norm_num
      have hm : Y^(231/100:ℝ) ≤ Y^(58/25:ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_left hm (show 0 ≤ 2*C₂ by positivity)]


end CubicFirstMoment

end

end OAI
