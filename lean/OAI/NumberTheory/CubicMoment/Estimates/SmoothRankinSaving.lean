import OAI.NumberTheory.CubicMoment.Estimates.SquarefreeRankin

namespace OAI

/-! The actual smooth-number discard on the exp(sqrt(log X)) scale.
Only the ordinary prime number theorem is used. -/
noncomputable section
open Filter Asymptotics
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma primaryPrime_reciprocal_exp_bound (hpnt : PrimaryPrimePNT) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
      (∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) ≤ C*(1+Real.log T) := by
  obtain ⟨C,hC,hbound⟩ := primaryPrime_reciprocal_upper hpnt
  let K : ℝ := 1+|Real.log (Real.log 2)|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg (Real.log (Real.log 2))]
  refine ⟨C*K,mul_pos hC (zero_lt_one.trans_le hK),?_⟩
  intro T hT
  have h2 : (2:ℝ) ≤ Real.exp T := by
    have htwo : (2:ℝ) ≤ Real.exp 1 := by
      convert Real.add_one_le_exp (1:ℝ) using 1; norm_num
    exact htwo.trans (Real.exp_le_exp.mpr hT)
  have hb := hbound (Real.exp T) h2
  simp only [Real.log_exp] at hb
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT
  calc
    _ ≤ C/T+C*(Real.log T-Real.log (Real.log 2)) := hb
    _ ≤ C+C*(Real.log T+|Real.log (Real.log 2)|) :=
      add_le_add (div_le_self hC.le hT)
        (mul_le_mul_of_nonneg_left (by linarith [neg_le_abs (Real.log (Real.log 2))]) hC.le)
    _ ≤ C*K*(1+Real.log T) := by
      dsimp [K]
      nlinarith [mul_nonneg (abs_nonneg (Real.log (Real.log 2))) hlog]

private lemma exp_rankin_absorption {κ C D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, 1 ≤ T ∧
      Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) ≤ T^(-D) := by
  have hsmall := ((isLittleO_rpow_exp_pos_mul_atTop (C+D) hκ).const_mul_left
    (Real.exp C)).def zero_lt_one
  filter_upwards [hsmall,eventually_ge_atTop (1:ℝ)] with T ht hT
  refine ⟨hT,?_⟩
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have ht' : Real.exp C*T^(C+D) ≤ Real.exp (κ*T) := by
    simpa only [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      (Real.rpow_nonneg hT0.le _)),Real.norm_of_nonneg (Real.exp_nonneg _),one_mul] using ht
  have heq : Real.exp (-κ*T)*Real.exp (C*(1+Real.log T)) =
      (Real.exp C*T^C)/Real.exp (κ*T) := by
    have he : Real.exp (C*(1+Real.log T)) = Real.exp C*T^C := by
      rw [Real.rpow_def_of_pos hT0,←Real.exp_add]
      congr 1
      ring
    rw [he,show -κ*T = -(κ*T) by ring,Real.exp_neg,div_eq_mul_inv]
    ring
  rw [heq,Real.rpow_neg hT0.le,←one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.rpow_pos_of_pos hT0 D)).mpr
  rw [one_mul]
  rw [mul_assoc,←Real.rpow_add hT0]
  exact ht'

theorem smooth_squarefree_log_saving (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ T : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      Real.exp (κ*T^2) ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b, norm p ≤ Real.exp T) →
      (S.card:ℝ) ≤ B*T^(-D) := by
  obtain ⟨C,hC,hprime⟩ := primaryPrime_reciprocal_exp_bound hpnt
  filter_upwards [exp_rankin_absorption (C := Real.exp 1*C) (D := D) hκ]
    with T hT
  intro B S hB hS hsize hsmooth
  have hT0 : 0 < T := zero_lt_one.trans_le hT.1
  have hB0 : 0 < B := (Real.exp_pos _).trans_le hB
  have hlogB : κ*T^2 ≤ Real.log B := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hB
  have hlogdiv : κ*T ≤ Real.log B/T := by
    apply (le_div_iff₀ hT0).mpr
    nlinarith [hlogB]
  have hpower : B^(1-T⁻¹) ≤ B*Real.exp (-κ*T) := by
    calc
      _ = B*Real.exp (-(Real.log B/T)) := by
        calc
          _ = Real.exp (Real.log B*(1-T⁻¹)) := Real.rpow_def_of_pos hB0 _
          _ = Real.exp (Real.log B)*Real.exp (-(Real.log B/T)) := by
            rw [←Real.exp_add]
            congr 1
            ring
          _ = _ := by rw [Real.exp_log hB0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hB0.le
  have hraw := smooth_squarefree_rankin_bound S hS hB0.le
    (Real.exp_le_exp.mpr hT.1) hsize hsmooth
  simp only [Real.log_exp] at hraw
  calc
    _ ≤ B^(1-T⁻¹)*Real.exp (Real.exp 1*
        ∑ p ∈ primeCutoff (Real.exp T), (norm p)⁻¹) := hraw
    _ ≤ (B*Real.exp (-κ*T))*Real.exp (Real.exp 1*C*(1+Real.log T)) := by
      apply mul_le_mul hpower
      · apply Real.exp_le_exp.mpr
        have h := mul_le_mul_of_nonneg_left (hprime T hT.1) (Real.exp_nonneg 1)
        simpa only [mul_assoc] using h
      · exact Real.exp_nonneg _
      · positivity
    _ = B*(Real.exp (-κ*T)*Real.exp (Real.exp 1*C*(1+Real.log T))) := by ring
    _ ≤ B*T^(-D) := mul_le_mul_of_nonneg_left hT.2 hB0.le

/-- The manuscript's actual long-prime cutoff. The exponent D is
arbitrary, so this discards the terms having no prime above exp(sqrt(log X)). -/
theorem smooth_squarefree_discard (hpnt : PrimaryPrimePNT)
    {κ D : ℝ} (hκ : 0 < κ) :
    ∀ᶠ X : ℝ in atTop, ∀ (B : ℝ) (S : Finset Eisenstein),
      X^κ ≤ B →
      (∀ b ∈ S, primary b ∧ Squarefree b) →
      (∀ b ∈ S, norm b ≤ B) →
      (∀ b ∈ S, ∀ p ∈ primaryPrimeFactors b,
        norm p ≤ Real.exp (Real.sqrt (Real.log X))) →
      (S.card:ℝ) ≤ B*(Real.log X)^(-D) := by
  have ht : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [ht.eventually (smooth_squarefree_log_saving (D := 2*D) hpnt hκ),
    eventually_gt_atTop (1:ℝ)] with X hsave hX
  intro B S hB hS hsize hsmooth
  have hlog : 0 < Real.log X := Real.log_pos hX
  have he : Real.exp (κ*(Real.sqrt (Real.log X))^2) = X^κ := by
    rw [Real.sq_sqrt hlog.le,Real.rpow_def_of_pos (zero_lt_one.trans hX)]
    congr 1
    ring
  have h := hsave B S (he.symm ▸ hB) hS hsize hsmooth
  convert h using 1
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hlog.le]
  congr 2
  ring

end CubicFirstMoment

end

end OAI
