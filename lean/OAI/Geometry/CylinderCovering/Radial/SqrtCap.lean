import OAI.Geometry.CylinderCovering.Radial.SqrtCapDefinitions
import OAI.Geometry.CylinderCovering.Angular.Taylor

namespace OAI

noncomputable section
namespace CylinderCovering.RadialSqrtCap
open Set MeasureTheory
open scoped Interval

lemma profile_nonneg (r : ℝ) : 0 ≤ profile r := by unfold profile RadialCaps.H; positivity

lemma profile_le_one {r : ℝ} (hr : |r| ≤ 1) : profile r ≤ 1 := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hr).1, (abs_le.mp hr).2]
  have hr4 : r ^ 4 ≤ 1 := by nlinarith only [hr2, sq_nonneg r]
  unfold profile RadialCaps.H
  linarith

lemma speedSq_nonneg (r : ℝ) : 0 ≤ speedSq r := by unfold speedSq RadialCaps.D0 RadialCaps.G; positivity

lemma speedSq_le_three {r : ℝ} (hr : |r| ≤ 1) : speedSq r ≤ 3 := by
  have hr2 : r ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp hr).1, (abs_le.mp hr).2]
  have hh : ((1 + r ^ 2) / 2) ^ 2 ≤ 1 := by nlinarith only [hr2, sq_nonneg r]
  unfold speedSq RadialCaps.D0 RadialCaps.G
  linarith

lemma cap_sq {β ε r : ℝ} (hβ : 0 ≤ β) :
    cap β ε r ^ 2 = 1 + 2 * ε ^ 2 * (profile r + β) := by
  apply Real.sq_sqrt
  positivity [profile_nonneg r]

lemma cap_nonneg (β ε r : ℝ) : 0 ≤ cap β ε r := Real.sqrt_nonneg _

lemma cap_ge_one {β ε r : ℝ} (hβ : 0 ≤ β) : 1 ≤ cap β ε r := by
  have hs := cap_sq (ε := ε) (r := r) hβ
  have hn := cap_nonneg β ε r
  have hp := mul_nonneg (sq_nonneg ε) (add_nonneg (profile_nonneg r) hβ)
  nlinarith only [hs, hn, hp]

lemma cap_continuous (β ε : ℝ) : Continuous (cap β ε) := by
  unfold cap RadialCaps.sqrtCap RadialCaps.H
  fun_prop

lemma cap_rationalization {β ε r : ℝ} (hβ : 0 ≤ β) :
    cap β ε r = 1 + ε ^ 2 * ((profile r + β) -
      2 * ε ^ 2 * (profile r + β) ^ 2 / (cap β ε r + 1) ^ 2) := by
  have hs := cap_sq (ε := ε) (r := r) hβ
  have hd : cap β ε r + 1 ≠ 0 := by have := cap_nonneg β ε r; linarith
  field_simp
  nlinarith only [hs, sq_nonneg (cap β ε r - 1)]

lemma cap_padding {β ε r : ℝ} (hβ : 0 ≤ β) (hr : |r| ≤ 1)
    (hsmall : ε ^ 2 * (1 + β) ^ 2 ≤ β) :
    1 + ε ^ 2 * (profile r + β / 2) ≤ cap β ε r := by
  have hH0 := profile_nonneg r
  have hH1 := profile_le_one hr
  have hA0 : 0 ≤ profile r + β / 2 := by positivity
  have hA1 : (profile r + β / 2) ^ 2 ≤ (1 + β) ^ 2 := by
    nlinarith only [hH0, hH1, hβ]
  have hprod := mul_le_mul_of_nonneg_left hA1 (sq_nonneg ε)
  have hh : ε ^ 2 * (profile r + β / 2) ^ 2 ≤ β := hprod.trans hsmall
  have hlast := mul_le_mul_of_nonneg_left hh (sq_nonneg ε)
  have hs := cap_sq (ε := ε) (r := r) hβ
  have hn := cap_nonneg β ε r
  nlinarith only [hs, hn, hlast, mul_nonneg (sq_nonneg ε) hA0]

lemma integrand_remainder {β ε r : ℝ} (hβ : 0 ≤ β) (he : |ε| ≤ 1) (hr : |r| ≤ 1) :
    |cap β ε r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * speedSq r)) -
      (1 / 2 + ε ^ 2 * (profile r + β - speedSq r / 4))| ≤
      (7 + 5 * β) * ε ^ 4 := by
  let A := profile r + β
  let D := speedSq r
  let B := 1 / 2 + ε ^ 2 * A
  let R := 1 / Real.sqrt (1 + ε ^ 2 * D) - (1 - ε ^ 2 * D / 2)
  have hA0 : 0 ≤ A := add_nonneg (profile_nonneg r) hβ
  have hA1 : A ≤ 1 + β := by dsimp [A]; linarith only [profile_le_one hr]
  have hD0 : 0 ≤ D := speedSq_nonneg r
  have hD1 : D ≤ 3 := speedSq_le_three hr
  have he2 : ε ^ 2 ≤ 1 := by nlinarith only [(abs_le.mp he).1, (abs_le.mp he).2]
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hB1 : B ≤ 3 / 2 + β := by
    have hh := mul_le_mul_of_nonneg_right he2 hA0
    dsimp [B]
    nlinarith only [hh, hA1]
  have hD2 : D ^ 2 ≤ 9 := by nlinarith only [hD0, hD1]
  have hR : |R| ≤ (27 / 8) * ε ^ 4 := by
    have hh := AngularTaylor.inv_sqrt_remainder (mul_nonneg (sq_nonneg ε) hD0)
    have hp := mul_le_mul_of_nonneg_left hD2 (sq_nonneg (ε ^ 2))
    dsimp [R]
    nlinarith only [hh, hp]
  have hBR : |B * R| ≤ (3 / 2 + β) * ((27 / 8) * ε ^ 4) := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact mul_le_mul hB1 hR (abs_nonneg R) (by positivity)
  have hAD0 : 0 ≤ A * D := mul_nonneg hA0 hD0
  have hAD1 : A * D ≤ (1 + β) * 3 := mul_le_mul hA1 hD1 hD0 (by positivity)
  have hp : |ε ^ 4 * A * D / 2| ≤ ε ^ 4 * ((1 + β) * 3) / 2 := by
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [mul_le_mul_of_nonneg_left hAD1 (by positivity : 0 ≤ ε ^ 4)]
  have hid : cap β ε r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D)) -
      (1 / 2 + ε ^ 2 * (A - D / 4)) = B * R - ε ^ 4 * A * D / 2 := by
    rw [cap_sq hβ]
    dsimp [A, B, R]
    ring
  change |cap β ε r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * D)) -
    (1 / 2 + ε ^ 2 * (A - D / 4))| ≤ _
  rw [hid]
  have hh := abs_sub (B * R) (ε ^ 4 * A * D / 2)
  have hβe := mul_nonneg hβ (by positivity : 0 ≤ ε ^ 4)
  calc
    _ ≤ (3 / 2 + β) * ((27 / 8) * ε ^ 4) + ε ^ 4 * ((1 + β) * 3) / 2 :=
      hh.trans (add_le_add hBR hp)
    _ ≤ (7 + 5 * β) * ε ^ 4 := by
      apply sub_nonneg.mp
      have heq : (7 + 5 * β) * ε ^ 4 -
          ((3 / 2 + β) * ((27 / 8) * ε ^ 4) + ε ^ 4 * ((1 + β) * 3) / 2) =
          (7 / 16) * ε ^ 4 + (1 / 8) * β * ε ^ 4 := by ring
      rw [heq]
      positivity

lemma coefficient_eq (β r : ℝ) :
    profile r + β - speedSq r / 4 = β - 1 / 16 - r ^ 2 / 8 + 7 * r ^ 4 / 16 := by
  unfold profile RadialCaps.H speedSq RadialCaps.D0 RadialCaps.G
  ring

lemma coefficient_integral (β : ℝ) :
    (∫ r in (-1 : ℝ)..1, profile r + β - speedSq r / 4) = 2 * β - 1 / 30 := by
  simp_rw [coefficient_eq]
  have hf : IntervalIntegrable (fun r : ℝ => β - 1 / 16 - r ^ 2 / 8) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hg : IntervalIntegrable (fun r : ℝ => 7 * r ^ 4 / 16) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hh : IntervalIntegrable (fun r : ℝ => r ^ 2 / 8) volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _) hh,
    intervalIntegral.integral_div, intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, integral_pow, integral_pow, intervalIntegral.integral_const]
  norm_num
  ring

lemma integrand_continuous (β ε : ℝ) :
    Continuous (fun r => cap β ε r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * speedSq r))) := by
  apply Continuous.div ((cap_continuous β ε).pow 2)
  · unfold speedSq RadialCaps.D0 RadialCaps.G
    fun_prop
  · intro r
    have hh := speedSq_nonneg r
    positivity

theorem cost_expansion {β ε : ℝ} (hβ : 0 ≤ β) (he : |ε| ≤ 1) :
    |cost β ε - (1 + (2 * β - 1 / 30) * ε ^ 2)| ≤ (14 + 10 * β) * ε ^ 4 := by
  let f := fun r => cap β ε r ^ 2 / (2 * Real.sqrt (1 + ε ^ 2 * speedSq r))
  let g := fun r => 1 / 2 + ε ^ 2 * (profile r + β - speedSq r / 4)
  have hf : IntervalIntegrable f volume (-1) 1 := (integrand_continuous β ε).intervalIntegrable _ _
  have hg : IntervalIntegrable g volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    unfold profile RadialCaps.H speedSq RadialCaps.D0 RadialCaps.G
    fun_prop
  have hi : (∫ r in (-1 : ℝ)..1, g r) = 1 + (2 * β - 1 / 30) * ε ^ 2 := by
    dsimp [g]
    have hh : IntervalIntegrable (fun r => ε ^ 2 * (profile r + β - speedSq r / 4))
        volume (-1) 1 := by
      apply Continuous.intervalIntegrable
      unfold profile RadialCaps.H speedSq RadialCaps.D0 RadialCaps.G
      fun_prop
    rw [intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _) hh,
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, coefficient_integral]
    norm_num
    ring
  have hb : ∀ r ∈ Ι (-1 : ℝ) 1, ‖f r - g r‖ ≤ (7 + 5 * β) * ε ^ 4 := by
    intro r hr
    rw [Set.uIoc_of_le (by norm_num)] at hr
    rw [Real.norm_eq_abs]
    exact integrand_remainder hβ he (abs_le.mpr ⟨hr.1.le, hr.2⟩)
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [intervalIntegral.integral_sub hf hg, hi, Real.norm_eq_abs] at hh
  change |(∫ r in (-1 : ℝ)..1, f r) - (1 + (2 * β - 1 / 30) * ε ^ 2)| ≤ _
  norm_num at hh
  nlinarith only [hh]

theorem exists_padding_threshold {β : ℝ} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      9 * ε ≤ β ∧ ∀ r : ℝ, |r| ≤ 1 →
        1 + ε ^ 2 * (profile r + β / 2) ≤ cap β ε r := by
  let δ := min 1 (min (β / 9) (β / (1 + β) ^ 2))
  have hden : 0 < (1 + β) ^ 2 := by positivity
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε he hεδ
  have he1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have heβ : ε < β / 9 := lt_of_lt_of_le hεδ ((min_le_right _ _).trans (min_le_left _ _))
  have hec : ε < β / (1 + β) ^ 2 :=
    lt_of_lt_of_le hεδ ((min_le_right _ _).trans (min_le_right _ _))
  have he2 : ε ^ 2 ≤ ε := by nlinarith only [he, he1]
  have hsmall : ε ^ 2 * (1 + β) ^ 2 ≤ β := by
    have hh := (lt_div_iff₀ hden).mp hec
    exact (mul_le_mul_of_nonneg_right he2 hden.le).trans hh.le
  refine ⟨by linarith only [heβ], ?_⟩
  intro r hr
  exact cap_padding hβ.le hr hsmall

theorem exists_saving_threshold {β : ℝ} (hβ : 0 < β) (hβ1 : β < 1 / 60) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ → cost β ε < 1 := by
  let C := 14 + 10 * β
  let c := 1 / 30 - 2 * β
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : 0 < c := by dsimp [c]; linarith
  let δ := min 1 (c / C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro ε he hεδ
  have he1 : ε < 1 := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hec : ε < c / C := lt_of_lt_of_le hεδ (min_le_right _ _)
  have he2 : ε ^ 2 ≤ ε := by nlinarith only [he, he1]
  have hsmall : C * ε ^ 2 < c := by
    have hh := (lt_div_iff₀ hC).mp hec
    nlinarith only [hh, mul_le_mul_of_nonneg_left he2 hC.le]
  have hp := mul_lt_mul_of_pos_right hsmall (sq_pos_of_pos he)
  have hh := (abs_le.mp (cost_expansion hβ.le (abs_le.mpr ⟨by linarith, he1.le⟩))).2
  dsimp [C, c] at hp
  nlinarith only [hp, hh]

end CylinderCovering.RadialSqrtCap

end

end OAI
