import OAI.Geometry.EinsteinFour.Variance
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Smooth approximation of the scalar test used in the weighted-variance
argument, with domination by the actual square-root energy. -/

namespace PositiveEinsteinFour.Variance

open MeasureTheory Filter
open scoped Topology

noncomputable section

def hRegularizedArgument (b ε : ℝ) : ℝ := Real.sqrt (b ^ 2 + ε ^ 2)

def hRegularizedValue (b ε : ℝ) : ℝ := MomentObstruction.H (hRegularizedArgument b ε)

def hRegularizedDerivative (b ε : ℝ) : ℝ :=
  derivativeRatio (hRegularizedArgument b ε) /
    (2 * Real.sqrt (hRegularizedArgument b ε)) * (b / hRegularizedArgument b ε)

def hRegularizedEnergy (b ε E K : ℝ) : ℝ :=
  derivativeRatio (hRegularizedArgument b ε) ^ 2 *
    (b / hRegularizedArgument b ε) ^ 2 * E / (4 * hRegularizedArgument b ε * K)

def hLimitEnergy (b E K : ℝ) : ℝ := derivativeRatio b ^ 2 * E / (4 * b * K)

theorem hRegularizedArgument_pos (b ε : ℝ) (hε : 0 < ε) :
    0 < hRegularizedArgument b ε := by
  apply Real.sqrt_pos.2
  have he : 0 < ε ^ 2 := sq_pos_of_pos hε
  nlinarith [sq_nonneg b]

theorem le_hRegularizedArgument (b ε : ℝ) (_hb : 0 ≤ b) :
    b ≤ hRegularizedArgument b ε := by
  unfold hRegularizedArgument
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg ε]

theorem hRegularizedArgument_le_three (b ε : ℝ) (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hε : ε ∈ Set.Icc (0 : ℝ) 1) : hRegularizedArgument b ε ≤ 3 := by
  unfold hRegularizedArgument
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · have hb2 : b ^ 2 ≤ 4 := by
      nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), hb.2]
    have he2 : ε ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hε.1 (sub_nonneg.mpr hε.2), hε.2]
    nlinarith

theorem continuous_hRegularizedArgument : Continuous (fun x : ℝ × ℝ =>
    hRegularizedArgument x.1 x.2) := by
  unfold hRegularizedArgument
  fun_prop

theorem continuous_H : Continuous MomentObstruction.H := by
  unfold MomentObstruction.H
  fun_prop

theorem hRegularizedArgument_zero (b : ℝ) (hb : 0 ≤ b) :
    hRegularizedArgument b 0 = b := by
  simp only [hRegularizedArgument, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
    Real.sqrt_sq_eq_abs, abs_of_nonneg hb]

theorem hasDerivAt_hRegularizedArgument (b ε : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun x => hRegularizedArgument x ε) (b / hRegularizedArgument b ε) b := by
  have hp : 0 < b ^ 2 + ε ^ 2 := by nlinarith [sq_nonneg b, sq_pos_of_pos hε]
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hp)).comp b
    (((hasDerivAt_id b).pow 2).add_const (ε ^ 2))
  convert h using 1
  · rfl
  · dsimp [hRegularizedArgument]
    ring

theorem hasDerivAt_hRegularizedValue (b ε : ℝ) (hε : 0 < ε) :
    HasDerivAt (fun x => hRegularizedValue x ε) (hRegularizedDerivative b ε) b := by
  exact (hasDerivAt_H (hRegularizedArgument_pos b ε hε)).comp b
    (hasDerivAt_hRegularizedArgument b ε hε)

theorem hRegularizedDerivative_sq (b ε : ℝ) (hε : 0 < ε) :
    hRegularizedDerivative b ε ^ 2 =
      derivativeRatio (hRegularizedArgument b ε) ^ 2 * (b / hRegularizedArgument b ε) ^ 2 /
        (4 * hRegularizedArgument b ε) := by
  have hr := hRegularizedArgument_pos b ε hε
  have hs := Real.sq_sqrt hr.le
  unfold hRegularizedDerivative
  simp only [mul_pow, div_pow, hs]
  norm_num
  ring

theorem hRegularizedEnergy_eq_derivative (b ε E K : ℝ) (hε : 0 < ε) :
    hRegularizedEnergy b ε E K = hRegularizedDerivative b ε ^ 2 * E / K := by
  rw [hRegularizedDerivative_sq b ε hε]
  unfold hRegularizedEnergy
  ring

theorem hRegularizedGradient_energy {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b ε K : ℝ) (q : F) (hε : 0 < ε) :
    ‖hRegularizedDerivative b ε • q‖ ^ 2 / K = hRegularizedEnergy b ε (‖q‖ ^ 2) K := by
  rw [hRegularizedEnergy_eq_derivative b ε (‖q‖ ^ 2) K hε,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

theorem hLimitEnergy_sqrt_energy (b E K : ℝ) :
    hLimitEnergy b E K = derivativeRatio b ^ 2 * (E / (4 * b)) / K := by
  unfold hLimitEnergy
  ring

theorem derivativeRatio_bounds_three {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 3) :
    0 ≤ derivativeRatio b ∧ derivativeRatio b ^ 2 ≤ 4 := by
  have ht : 0 ≤ b ^ 2 := sq_nonneg b
  have ht9 : b ^ 2 ≤ 9 := by
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), hb.2]
  have hlow : 0 ≤ b ^ 2 * (16 - b ^ 2) :=
    mul_nonneg ht (by linarith)
  have hupp : 0 ≤ (b ^ 2 - 8) ^ 2 := sq_nonneg _
  have hnonneg : 0 ≤ derivativeRatio b := by unfold derivativeRatio; nlinarith
  have hupper : derivativeRatio b ≤ 3 / 2 := by unfold derivativeRatio; nlinarith
  exact ⟨hnonneg, by nlinarith⟩

theorem hRegularizedEnergy_nonneg {b ε E K : ℝ} (hε : 0 < ε)
    (hE : 0 ≤ E) (hK : 0 < K) : 0 ≤ hRegularizedEnergy b ε E K := by
  have hr := hRegularizedArgument_pos b ε hε
  unfold hRegularizedEnergy
  positivity

/-- Uniform domination includes the zero face with Lean's totalized division. -/
theorem hRegularizedEnergy_le {b ε E K : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hE : 0 ≤ E) (hK : 1 ≤ K) :
    hRegularizedEnergy b ε E K ≤ E / b := by
  let r := hRegularizedArgument b ε
  have hr : 0 < r := hRegularizedArgument_pos b ε hε.1
  have hbr : b ≤ r := le_hRegularizedArgument b ε hb.1
  have hr3 : r ≤ 3 := hRegularizedArgument_le_three b ε hb ⟨hε.1.le, hε.2⟩
  have hratio := (derivativeRatio_bounds_three ⟨hr.le, hr3⟩).2
  by_cases hz : b = 0
  · simp [hRegularizedEnergy, hz]
  have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hz)
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hfrac : (b / r) ^ 2 ≤ 1 := by
    have hx : b / r ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hb.1 hr.le, (div_le_one hr).2 hbr⟩
    have hsq := mul_le_mul hx.2 hx.2 hx.1 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [hsq]
  have hnum : derivativeRatio r ^ 2 * (b / r) ^ 2 * E ≤ 4 * E := by
    have h1 := mul_le_mul hratio hfrac (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
    nlinarith [mul_le_mul_of_nonneg_right h1 hE]
  have hden : 4 * b ≤ 4 * r * K := by
    have hx := mul_le_mul_of_nonneg_left hK hr.le
    nlinarith
  change derivativeRatio r ^ 2 * (b / r) ^ 2 * E / (4 * r * K) ≤ E / b
  apply (div_le_iff₀ (by positivity : 0 < 4 * r * K)).2
  have hdiv := mul_le_mul_of_nonneg_left hden (div_nonneg hE hb.1)
  have hid : E / b * (4 * b) = 4 * E := by field_simp
  rw [hid] at hdiv
  exact hnum.trans hdiv

theorem tendsto_hRegularizedArgument (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (hRegularizedArgument b) (𝓝 0) (𝓝 b) := by
  have hc : Continuous (fun ε : ℝ => hRegularizedArgument b ε) :=
    continuous_hRegularizedArgument.comp (continuous_const.prodMk continuous_id)
  simpa only [hRegularizedArgument_zero b hb] using hc.tendsto 0

theorem tendsto_hRegularizedValue (b : ℝ) (hb : 0 ≤ b) :
    Tendsto (hRegularizedValue b) (𝓝 0) (𝓝 (MomentObstruction.H b)) :=
  continuous_H.continuousAt.tendsto.comp (tendsto_hRegularizedArgument b hb)

theorem tendsto_hRegularizedEnergy (b E K : ℝ) (hb : 0 ≤ b) (hK : K ≠ 0) :
    Tendsto (fun ε => hRegularizedEnergy b ε E K) (𝓝 0) (𝓝 (hLimitEnergy b E K)) := by
  by_cases hz : b = 0
  · subst b
    simp [hRegularizedEnergy, hLimitEnergy]
  have hr := tendsto_hRegularizedArgument b hb
  have hd : Tendsto (fun ε => derivativeRatio (hRegularizedArgument b ε)) (𝓝 0)
      (𝓝 (derivativeRatio b)) := by
    unfold derivativeRatio
    exact (tendsto_const_nhds.add ((hr.pow 2).div_const 8)).sub ((hr.pow 4).div_const 128)
  have h : Tendsto (fun ε => derivativeRatio (hRegularizedArgument b ε) ^ 2 *
      (b / hRegularizedArgument b ε) ^ 2 * E / (4 * hRegularizedArgument b ε * K))
      (𝓝 0) (𝓝 (derivativeRatio b ^ 2 * (b / b) ^ 2 * E / (4 * b * K))) :=
    (((hd.pow 2).mul ((tendsto_const_nhds.div hr hz).pow 2)).mul
      tendsto_const_nhds).div ((tendsto_const_nhds.mul hr).mul tendsto_const_nhds)
        (mul_ne_zero (mul_ne_zero (by norm_num) hz) hK)
  simpa only [hRegularizedEnergy, hLimitEnergy, div_self hz, one_pow, mul_one] using h


theorem abs_H_le_four {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 3) :
    |MomentObstruction.H b| ≤ 4 := by
  have hs0 : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hsq : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt hb.1
  have hs2 : Real.sqrt b ≤ 2 := by nlinarith [hb.2]
  have hb2 : b ^ 2 ≤ 9 := by
    nlinarith [mul_nonneg hb.1 (sub_nonneg.mpr hb.2), hb.2]
  have hb4 : b ^ 4 ≤ 81 := by
    have hprod := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hb2)
    nlinarith
  have hp0 : 0 ≤ 1 + b ^ 2 / 40 - b ^ 4 / 1152 := by nlinarith [sq_nonneg b]
  have hp2 : 1 + b ^ 2 / 40 - b ^ 4 / 1152 ≤ 2 := by
    nlinarith [sq_nonneg (b ^ 2)]
  unfold MomentObstruction.H
  rw [abs_of_nonneg (mul_nonneg hs0 hp0)]
  exact (mul_le_mul hs2 hp2 hp0 (by norm_num)).trans (by norm_num)

theorem hLimitEnergy_nonneg {b E K : ℝ} (hb : 0 ≤ b) (hE : 0 ≤ E) (hK : 0 ≤ K) :
    0 ≤ hLimitEnergy b E K := by
  unfold hLimitEnergy
  positivity

theorem hLimitEnergy_le {b E K : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 2)
    (hE : 0 ≤ E) (hK : 1 ≤ K) : hLimitEnergy b E K ≤ E / b := by
  by_cases hz : b = 0
  · simp [hLimitEnergy, hz]
  have hbpos : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hz)
  have hKpos : 0 < K := lt_of_lt_of_le (by norm_num) hK
  have hratio := (derivativeRatio_bounds_three ⟨hb.1, hb.2.trans (by norm_num)⟩).2
  unfold hLimitEnergy
  apply (div_le_iff₀ (by positivity : 0 < 4 * b * K)).2
  have hid : E / b * (4 * b * K) = 4 * E * K := by field_simp
  rw [hid]
  have hm := mul_le_mul_of_nonneg_right hratio hE
  have hEK := mul_le_mul_of_nonneg_left hK hE
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem aemeasurable_hRegularizedArgument {b : Ω → ℝ} (hb : AEMeasurable b μ) (ε : ℝ) :
    AEMeasurable (fun x => hRegularizedArgument (b x) ε) μ := by
  exact ((hb.pow_const 2).add aemeasurable_const).sqrt

theorem aemeasurable_hRegularizedValue {b : Ω → ℝ} (hb : AEMeasurable b μ) (ε : ℝ) :
    AEMeasurable (fun x => hRegularizedValue (b x) ε) μ :=
  continuous_H.measurable.comp_aemeasurable (aemeasurable_hRegularizedArgument hb ε)

theorem aemeasurable_hRegularizedEnergy {b E K : Ω → ℝ}
    (hb : AEMeasurable b μ) (hE : AEMeasurable E μ) (hK : AEMeasurable K μ) (ε : ℝ) :
    AEMeasurable (fun x => hRegularizedEnergy (b x) ε (E x) (K x)) μ := by
  have hr := aemeasurable_hRegularizedArgument hb ε
  have hd : AEMeasurable (fun x => derivativeRatio (hRegularizedArgument (b x) ε)) μ :=
    (aemeasurable_const.add ((hr.pow_const 2).div_const 8)).sub ((hr.pow_const 4).div_const 128)
  exact (((hd.pow_const 2).mul ((hb.div hr).pow_const 2)).mul hE).div
    ((aemeasurable_const.mul hr).mul hK)

theorem integrable_hLimitEnergy {b E K : Ω → ℝ}
    (hb : AEMeasurable b μ) (hE : AEMeasurable E μ) (hK : AEMeasurable K μ)
    (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (hE0 : ∀ᵐ x ∂μ, 0 ≤ E x) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hdom : Integrable (fun x => E x / b x) μ) :
    Integrable (fun x => hLimitEnergy (b x) (E x) (K x)) μ := by
  have hd : AEMeasurable (fun x => derivativeRatio (b x)) μ :=
    (aemeasurable_const.add ((hb.pow_const 2).div_const 8)).sub ((hb.pow_const 4).div_const 128)
  have hm : AEMeasurable (fun x => hLimitEnergy (b x) (E x) (K x)) μ :=
    ((hd.pow_const 2).mul hE).div ((aemeasurable_const.mul hb).mul hK)
  apply hdom.mono' hm.aestronglyMeasurable
  filter_upwards [hb2, hE0, hK1] with x hx hEx hKx
  rw [Real.norm_eq_abs, abs_of_nonneg (hLimitEnergy_nonneg hx.1 hEx (by linarith))]
  exact hLimitEnergy_le hx hEx hKx

theorem integral_hRegularizedEnergy_tendsto {b E K : Ω → ℝ}
    (hb : AEMeasurable b μ) (hE : AEMeasurable E μ) (hK : AEMeasurable K μ)
    (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (hE0 : ∀ᵐ x ∂μ, 0 ≤ E x) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hdom : Integrable (fun x => E x / b x) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, hRegularizedEnergy (b x) (ε n) (E x) (K x) ∂μ) atTop
      (𝓝 (∫ x, hLimitEnergy (b x) (E x) (K x) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => E x / b x)
  · intro n
    exact (aemeasurable_hRegularizedEnergy hb hE hK (ε n)).aestronglyMeasurable
  · exact hdom
  · intro n
    filter_upwards [hb2, hE0, hK1] with x hx hEx hKx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (hRegularizedEnergy_nonneg (hε n).1 hEx (by linarith))]
    exact hRegularizedEnergy_le hx (hε n) hEx hKx
  · filter_upwards [hb2, hK1] with x hx hKx
    exact (tendsto_hRegularizedEnergy (b x) (E x) (K x) hx.1 (by linarith)).comp hlim

theorem integral_hRegularizedValue_pow_tendsto [IsFiniteMeasure μ] {b : Ω → ℝ}
    (hb : AEMeasurable b μ) (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun n => ∫ x, hRegularizedValue (b x) (ε n) ^ k ∂μ) atTop
      (𝓝 (∫ x, MomentObstruction.H (b x) ^ k ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ) ^ k)
  · intro n
    exact ((aemeasurable_hRegularizedValue hb (ε n)).pow_const k).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    filter_upwards [hb2] with x hx
    have hr := hRegularizedArgument_le_three (b x) (ε n) hx ⟨(hε n).1.le, (hε n).2⟩
    have hh := abs_H_le_four ⟨(hRegularizedArgument_pos (b x) (ε n) (hε n).1).le, hr⟩
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hh k
  · filter_upwards [hb2] with x hx
    exact ((tendsto_hRegularizedValue (b x) hx.1).comp hlim).pow k

/-- Smooth weighted variance passes to the singular square-root test with
an actual integrable domination, rather than a formal limiting premise. -/
theorem H_variance_of_regularized [IsFiniteMeasure μ] {b E K : Ω → ℝ}
    (hb : AEMeasurable b μ) (hE : AEMeasurable E μ) (hK : AEMeasurable K μ)
    (hb2 : ∀ᵐ x ∂μ, b x ∈ Set.Icc (0 : ℝ) 2)
    (hE0 : ∀ᵐ x ∂μ, 0 ≤ E x) (hK1 : ∀ᵐ x ∂μ, 1 ≤ K x)
    (hdom : Integrable (fun x => E x / b x) μ)
    (ε : ℕ → ℝ) (hε : ∀ n, ε n ∈ Set.Ioc (0 : ℝ) 1)
    (hlim : Tendsto ε atTop (𝓝 0))
    (hvariance : ∀ n, (∫ x, hRegularizedValue (b x) (ε n) ^ 2 ∂μ) -
      (∫ x, hRegularizedValue (b x) (ε n) ∂μ) ^ 2 ≤
        ∫ x, hRegularizedEnergy (b x) (ε n) (E x) (K x) ∂μ) :
    (∫ x, MomentObstruction.H (b x) ^ 2 ∂μ) -
      (∫ x, MomentObstruction.H (b x) ∂μ) ^ 2 ≤
        ∫ x, hLimitEnergy (b x) (E x) (K x) ∂μ := by
  have h1 := integral_hRegularizedValue_pow_tendsto hb hb2 ε hε hlim 1
  simp only [pow_one] at h1
  have h2 := integral_hRegularizedValue_pow_tendsto hb hb2 ε hε hlim 2
  have he := integral_hRegularizedEnergy_tendsto hb hE hK hb2 hE0 hK1 hdom ε hε hlim
  exact le_of_tendsto_of_tendsto (h2.sub (h1.pow 2)) he (Filter.Eventually.of_forall hvariance)

end
end PositiveEinsteinFour.Variance

end OAI
