import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTCharacterDisk

namespace OAI

/-! Transfer the normalized disk expansion back to the actual L-functions.
Every zero in the finite disk lies left of the line of evaluation, so its
logarithmic-derivative contribution has nonnegative real part.
-/

namespace TwoPointCorrelations

open Complex Finset
open scoped BigOperators Classical

variable {q : ℕ} [NeZero q]

noncomputable def mrtCharacterPhysicalPoint (t : ℝ) (z : ℂ) : ℂ :=
  (2 : ℂ) + Complex.I * (t : ℂ) + (3 / 2 : ℂ) * z

noncomputable def mrtCharacterRealDiskPoint (σ : ℝ) : ℂ :=
  (((2 / 3 : ℝ) * (σ - 2) : ℝ) : ℂ)

lemma mrtCharacterPhysicalPoint_real (σ t : ℝ) :
    mrtCharacterPhysicalPoint t (mrtCharacterRealDiskPoint σ) =
      (σ : ℂ) + Complex.I * (t : ℂ) := by
  unfold mrtCharacterPhysicalPoint mrtCharacterRealDiskPoint
  push_cast
  ring

lemma mrtCharacterNormalizedLFunction_deriv (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ) :
    deriv (mrtCharacterNormalizedLFunction χ t) z =
      (deriv (DirichletCharacter.LFunction χ) (mrtCharacterPhysicalPoint t z) * (3 / 2 : ℂ)) /
        DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) := by
  have ha : HasDerivAt (mrtCharacterPhysicalPoint t) (3 / 2 : ℂ) z := by
    exact (hasDerivAt_const_mul (3 / 2 : ℂ)).const_add
      ((2 : ℂ) + Complex.I * (t : ℂ))
  exact (((DirichletCharacter.differentiable_LFunction hχ _).hasDerivAt.comp z ha).div_const
    (DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)))).deriv

lemma mrtCharacterNormalized_logderiv_eq (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) (z : ℂ)
    (hn : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0) :
    deriv (mrtCharacterNormalizedLFunction χ t) z / mrtCharacterNormalizedLFunction χ t z =
      (3 / 2 : ℂ) *
        (deriv (DirichletCharacter.LFunction χ) (mrtCharacterPhysicalPoint t z) /
          DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z)) := by
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  rw [mrtCharacterNormalizedLFunction_deriv χ hχ]
  change (_ / _) / (DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) / _) = _
  field_simp [hn, hc]

lemma mrtCharacterNormalizedZeros_physical_zero (χ : DirichletCharacter ℂ q)
    (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t ρ) = 0 := by
  have hzero : mrtCharacterNormalizedLFunction χ t ρ = 0 := hρ.2
  have hc : DirichletCharacter.LFunction χ ((2 : ℂ) + Complex.I * (t : ℂ)) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inr (by
      intro h; have := congrArg Complex.re h; norm_num at this)) (by norm_num)
  exact (div_eq_zero_iff.mp hzero).resolve_right hc

lemma mrtCharacterNormalizedZeros_re (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    ρ.re < -(2 / 3 : ℝ) := by
  by_contra! h
  have hs : 1 ≤ (mrtCharacterPhysicalPoint t ρ).re := by
    norm_num [mrtCharacterPhysicalPoint, Complex.mul_re]
    linarith
  exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) hs
    (mrtCharacterNormalizedZeros_physical_zero χ t hρ)

lemma mrtCharacterRealDiskPoint_norm {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    ‖mrtCharacterRealDiskPoint σ‖ ≤ 3 / 4 := by
  rw [mrtCharacterRealDiskPoint, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> linarith

lemma mrtCharacter_zeroTerm_re_nonneg (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ : ℝ} (hσ : 1 < σ)
    {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    0 ≤ (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) /
      (mrtCharacterRealDiskPoint σ - ρ)).re := by
  have hr := mrtCharacterNormalizedZeros_re χ hχ t hρ
  have hd : 0 ≤ (mrtCharacterRealDiskPoint σ - ρ).re := by
    simp only [Complex.sub_re, mrtCharacterRealDiskPoint, Complex.ofReal_re]
    linarith
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hd) (Complex.normSq_nonneg _)

/-- A logarithmic-derivative upper bound to the right of one, obtained by
dropping the nonnegative zero terms from the actual finite expansion. -/
theorem mrtCharacter_neg_logderiv_re_le (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        (2 / 3 : ℝ) * mrtCharacterLogDerivativeConstant *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) := by
  let z := mrtCharacterRealDiskPoint σ
  have hp : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0 := by
    rw [mrtCharacterPhysicalPoint_real]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hn : mrtCharacterNormalizedLFunction χ t z ≠ 0 := by
    exact div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have he := mrtCharacterNormalized_logderiv χ hχ t (mrtCharacterRealDiskPoint_norm hσ hσ2) hn
  have hre := (Complex.abs_re_le_norm _).trans he
  have hs : 0 ≤ ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
      (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) / (z - ρ)).re := by
    apply sum_nonneg
    intro ρ hρ
    exact mrtCharacter_zeroTerm_re_nonneg χ hχ t hσ
      ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ)
  rw [Complex.sub_re, Complex.re_sum] at hre
  have hlow := (abs_le.mp hre).1
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, mrtCharacterPhysicalPoint_real] at hlow
  norm_num [Complex.mul_re] at hlow
  simp only [neg_div, Complex.neg_re]
  nlinarith

lemma mrtCharacter_zero_multiplicity_pos (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {ρ : ℂ} (hρ : ρ ∈ mrtCharacterNormalizedZeros χ t) :
    1 ≤ (analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat := by
  have hf : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      AnalyticAt ℂ (mrtCharacterNormalizedLFunction χ t) z := by
    intro z _
    exact (mrtCharacterNormalizedLFunction_differentiable χ hχ t).analyticAt z
  have hf0 : mrtCharacterNormalizedLFunction χ t 0 ≠ 0 := by
    rw [mrtCharacterNormalizedLFunction_zero]
    exact one_ne_zero
  have hfinite := Erdos970.lem_m_rho_is_nat (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (mrtCharacterNormalizedLFunction χ t) hf hf0
    (by norm_num) ρ hρ
  have hpos := Erdos970.lem_m_rho_ge_1 (15 / 16) (7 / 8)
    (by norm_num) (by norm_num) (mrtCharacterNormalizedLFunction χ t) hf hf0
    (by norm_num) ρ hρ
  simpa using ENat.toNat_le_toNat hpos hfinite

lemma mrtCharacter_real_zero_mem (χ : DirichletCharacter ℂ q)
    (t : ℝ) {β : ℝ} (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    mrtCharacterRealDiskPoint β ∈ mrtCharacterNormalizedZeros χ t := by
  have hn : ‖mrtCharacterRealDiskPoint β‖ ≤ 7 / 8 := by
    rw [mrtCharacterRealDiskPoint, Complex.norm_real, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  refine ⟨by simpa using hn, ?_⟩
  change DirichletCharacter.LFunction χ
    (mrtCharacterPhysicalPoint t (mrtCharacterRealDiskPoint β)) / _ = 0
  rw [mrtCharacterPhysicalPoint_real, hzero, zero_div]

/-- A zero at height `t` contributes its full reciprocal distance; the
other zeros have nonnegative real contributions. -/
lemma mrtCharacter_zero_sum_lower (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (t : ℝ) {σ β : ℝ} (hσ : 1 < σ) (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (3 / 2 : ℝ) / (σ - β) ≤
      ∑ ρ ∈ (mrtCharacterNormalizedZeros_finite χ hχ t).toFinset,
        (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) ρ).toNat : ℂ) /
          (mrtCharacterRealDiskPoint σ - ρ)).re := by
  let w := mrtCharacterRealDiskPoint β
  have hw := mrtCharacter_real_zero_mem χ t hβ hβ1 hzero
  have hm := mrtCharacter_zero_multiplicity_pos χ hχ t hw
  have hd0 : 0 < σ - β := by linarith
  have hd : 0 < (2 / 3 : ℝ) * (σ - β) := mul_pos (by norm_num) hd0
  have hdiff : mrtCharacterRealDiskPoint σ - w =
      (((2 / 3 : ℝ) * (σ - β) : ℝ) : ℂ) := by
    dsimp [w, mrtCharacterRealDiskPoint]
    push_cast
    ring
  have hterm : (3 / 2 : ℝ) / (σ - β) ≤
      (((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) w).toNat : ℂ) /
        (mrtCharacterRealDiskPoint σ - w)).re := by
    rw [hdiff]
    change (3 / 2 : ℝ) / (σ - β) ≤
      ((((analyticOrderAt (mrtCharacterNormalizedLFunction χ t) w).toNat : ℝ) : ℂ) /
        (((2 / 3 : ℝ) * (σ - β) : ℝ) : ℂ)).re
    rw [← Complex.ofReal_div, Complex.ofReal_re]
    calc
      _ = 1 / ((2 / 3 : ℝ) * (σ - β)) := by field_simp [ne_of_gt hd0]
      _ ≤ _ := div_le_div_of_nonneg_right (by exact_mod_cast hm) hd.le
  exact hterm.trans (single_le_sum
    (fun ρ hρ => mrtCharacter_zeroTerm_re_nonneg χ hχ t hσ
      ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mp hρ))
    ((mrtCharacterNormalizedZeros_finite χ hχ t).mem_toFinset.mpr hw))

/-- The one-zero upper bound, with its negative reciprocal term retained. -/
theorem mrtCharacter_neg_logderiv_re_le_of_zero (χ : DirichletCharacter ℂ q)
    (hχ : χ ≠ 1) (t : ℝ) {σ β : ℝ} (hσ : 1 < σ) (hσ2 : σ ≤ 2)
    (hβ : 3 / 4 ≤ β) (hβ1 : β ≤ 1)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + Complex.I * (t : ℂ)) = 0) :
    (-deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + Complex.I * (t : ℂ)) /
      DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * (t : ℂ))).re ≤
        (2 / 3 : ℝ) * mrtCharacterLogDerivativeConstant *
          Real.log ((2 * q : ℝ) * mrtCharacterInverseConstant * (|t| + 4)) - 1 / (σ - β) := by
  let z := mrtCharacterRealDiskPoint σ
  have hp : DirichletCharacter.LFunction χ (mrtCharacterPhysicalPoint t z) ≠ 0 := by
    rw [mrtCharacterPhysicalPoint_real]
    exact χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by simpa using hσ.le)
  have hn : mrtCharacterNormalizedLFunction χ t z ≠ 0 :=
    div_ne_zero hp (χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num))
  have he := mrtCharacterNormalized_logderiv χ hχ t (mrtCharacterRealDiskPoint_norm hσ hσ2) hn
  have hre := (Complex.abs_re_le_norm _).trans he
  have hs := mrtCharacter_zero_sum_lower χ hχ t hσ hβ hβ1 hzero
  have hfrac : (3 / 2 : ℝ) / (σ - β) = (3 / 2 : ℝ) * (1 / (σ - β)) := by ring
  rw [hfrac] at hs
  rw [Complex.sub_re, Complex.re_sum] at hre
  have hlow := (abs_le.mp hre).1
  rw [mrtCharacterNormalized_logderiv_eq χ hχ t z hp, mrtCharacterPhysicalPoint_real] at hlow
  norm_num [Complex.mul_re] at hlow
  simp only [neg_div, Complex.neg_re]
  nlinarith

end TwoPointCorrelations

end OAI
