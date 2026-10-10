import OAI.Probability.FreeIsing.Brownian.Martingale
import OAI.Probability.FreeIsing.Cavity.BaseMoments

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367

def standardGaussianThirdMoment : ℝ :=
  ∫ x : ℝ, |x| ^ 3 ∂gaussianReal 0 1

theorem standardGaussianThirdMoment_nonneg : 0 ≤ standardGaussianThirdMoment :=
  integral_nonneg (fun _ => by positivity)

theorem integrable_standardGaussian_abs_pow (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 1) := by
  apply (integrable_one_add_abs_pow_gaussian p).mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ |x| ^ p)]
    exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) p

theorem standardGaussianThirdMoment_le :
    standardGaussianThirdMoment ≤ Real.exp 18 := by
  calc
    standardGaussianThirdMoment ≤
        ∫ x : ℝ, (1 + |x|) ^ 3 ∂gaussianReal 0 1 := by
      apply integral_mono (integrable_standardGaussian_abs_pow 3)
        (integrable_one_add_abs_pow_gaussian 3)
      intro x
      exact pow_le_pow_left₀ (abs_nonneg x) (by linarith) 3
    _ ≤ Real.exp 18 := by
      convert (integral_one_add_abs_pow_gaussian_le (p := 3) (by omega)) using 1
      norm_num

theorem gaussianReal_map_sqrt_mul (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply Subtype.ext
    simp [Real.sq_sqrt v.coe_nonneg]

theorem integrable_gaussianReal_abs_pow (v : ℝ≥0) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (gaussianReal 0 v) := by
  rw [← gaussianReal_map_sqrt_mul v]
  apply (integrable_map_measure (by fun_prop) (by fun_prop)).mpr
  simpa only [Function.comp_def, abs_mul, mul_pow,
    abs_of_nonneg (Real.sqrt_nonneg (v : ℝ))] using
    (integrable_standardGaussian_abs_pow p).const_mul (Real.sqrt (v : ℝ) ^ p)

theorem integral_gaussianReal_abs_pow (v : ℝ≥0) (p : ℕ) :
    (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 v) =
      Real.sqrt (v : ℝ) ^ p * (∫ x : ℝ, |x| ^ p ∂gaussianReal 0 1) := by
  rw [← gaussianReal_map_sqrt_mul v, integral_map (by fun_prop) (by fun_prop)]
  simp only [abs_mul, mul_pow, abs_of_nonneg (Real.sqrt_nonneg (v : ℝ)),
    integral_const_mul]

theorem integral_abs_cube_of_gaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, |X ω| ^ 3 ∂P) = standardGaussianThirdMoment * (v : ℝ) * Real.sqrt v := by
  have heq := hX.integral_comp (f := fun x : ℝ => |x| ^ 3) (by fun_prop)
  change (∫ ω, |X ω| ^ 3 ∂P) = _ at heq
  rw [heq, integral_gaussianReal_abs_pow]
  rw [show Real.sqrt (v : ℝ) ^ 3 = (v : ℝ) * Real.sqrt v by
    rw [pow_succ, Real.sq_sqrt v.coe_nonneg]]
  unfold standardGaussianThirdMoment
  ring

theorem abs_sq_sub_sq_le_of_abs_sub_le {x y K : ℝ}
    (_hK : 0 ≤ K) (hxy : |y - x| ≤ K) :
    |y ^ 2 - x ^ 2| ≤ 2 * K * |x| + K ^ 2 := by
  have hrewrite : y ^ 2 - x ^ 2 = 2 * x * (y - x) + (y - x) ^ 2 := by ring
  rw [hrewrite]
  calc
    |2 * x * (y - x) + (y - x) ^ 2| ≤
        |2 * x * (y - x)| + |(y - x) ^ 2| := abs_add_le _ _
    _ = 2 * |x| * |y - x| + |y - x| ^ 2 := by
      simp only [abs_mul, abs_pow]
      norm_num
    _ ≤ 2 * |x| * K + K ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hxy (by positivity))
        (pow_le_pow_left₀ (abs_nonneg _) hxy 2)
    _ = _ := by ring

theorem integral_abs_sq_sub_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (hbound : ∀ᵐ ω ∂P, |Y ω - X ω| ≤ K) :
    Integrable (fun ω => |Y ω ^ 2 - X ω ^ 2|) P ∧
    (∫ ω, |Y ω ^ 2 - X ω ^ 2| ∂P) ≤
      2 * K * Real.sqrt (∫ ω, X ω ^ 2 ∂P) + K ^ 2 := by
  have hXL2 : MemLp X 2 P :=
    (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr hX2
  have hXabs : Integrable (fun ω => |X ω|) P := hXL2.integrable (by norm_num) |>.abs
  have hdom := (hXabs.const_mul (2 * K)).add (integrable_const (K ^ 2))
  have hle : ∀ᵐ ω ∂P, |Y ω ^ 2 - X ω ^ 2| ≤ 2 * K * |X ω| + K ^ 2 := by
    filter_upwards [hbound] with ω hω
    exact abs_sq_sub_sq_le_of_abs_sub_le hK hω
  have hint : Integrable (fun ω => |Y ω ^ 2 - X ω ^ 2|) P := by
    apply hdom.mono' ((hY.pow_const 2).sub (hX.pow_const 2)).abs.aestronglyMeasurable
    filter_upwards [hle] with ω hω
    simpa only [Real.norm_eq_abs, abs_abs, Pi.add_apply, Pi.sub_apply] using hω
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, |Y ω ^ 2 - X ω ^ 2| ∂P) ≤
        ∫ ω, 2 * K * |X ω| + K ^ 2 ∂P := integral_mono_ae hint hdom hle
    _ = 2 * K * (∫ ω, |X ω| ∂P) + K ^ 2 := by
      rw [integral_add (hXabs.const_mul _) (integrable_const _), integral_const_mul]
      simp
    _ ≤ _ := by
      gcongr
      exact integral_abs_le_sqrt_integral_sq hX hX2

theorem integral_abs_cube_le_of_bounded_perturbation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X Y : Ω → ℝ} {K : ℝ} (hK : 0 ≤ K) (hY : AEMeasurable Y P)
    (hX3 : Integrable (fun ω => |X ω| ^ 3) P)
    (hbound : ∀ᵐ ω ∂P, |Y ω - X ω| ≤ K) :
    Integrable (fun ω => |Y ω| ^ 3) P ∧
    (∫ ω, |Y ω| ^ 3 ∂P) ≤ 4 * ((∫ ω, |X ω| ^ 3 ∂P) + K ^ 3) := by
  have hint := integrable_abs_pow_of_bounded_perturbation 3 hK hY hX3 hbound
  have hdom := (hX3.add (integrable_const (K ^ 3))).const_mul 4
  refine ⟨hint, ?_⟩
  calc
    (∫ ω, |Y ω| ^ 3 ∂P) ≤ ∫ ω, 4 * (|X ω| ^ 3 + K ^ 3) ∂P := by
      apply integral_mono_ae hint hdom
      filter_upwards [hbound] with ω hω
      have ht : |Y ω| ≤ |X ω| + K := by
        calc
          |Y ω| = |Y ω - X ω + X ω| := by congr 1; ring
          _ ≤ |Y ω - X ω| + |X ω| := abs_add_le _ _
          _ ≤ |X ω| + K := by linarith
      exact (pow_le_pow_left₀ (abs_nonneg _) ht 3).trans
        (by convert add_pow_le (abs_nonneg (X ω)) hK 3 using 1; norm_num)
    _ = _ := by
      rw [integral_const_mul, integral_add hX3 (integrable_const _)]
      simp

theorem integrable_abs_pow_of_gaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) (p : ℕ) :
    Integrable (fun ω => |X ω| ^ p) P := by
  have hi := integrable_gaussianReal_abs_pow v p
  rw [← hX.map_eq] at hi
  exact hi.comp_aemeasurable hX.aemeasurable

theorem preBrownian_hasLaw_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (fun ω => B t ω - B s ω) (gaussianReal 0 (t - s)) P := by
  simpa only [add_tsub_cancel_of_le hst] using (hB.shift s).hasLaw_eval (t - s)

theorem preBrownian_integral_abs_increment_cube
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, |B t ω - B s ω| ^ 3 ∂P) =
      standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) := by
  simpa only [NNReal.coe_sub hst] using
    integral_abs_cube_of_gaussianLaw (preBrownian_hasLaw_increment hB hst)

theorem preBrownian_bounded_drift_increment_moments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : ∀ t, AEMeasurable (W t) P)
    {s t : ℝ≥0} (hst : s ≤ t) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P,
      |(W t ω - W s ω) - (B t ω - B s ω)| ≤ L * ((t : ℝ) - (s : ℝ))) :
    Integrable (fun ω => |(W t ω - W s ω) ^ 2 - (B t ω - B s ω) ^ 2|) P ∧
    (∫ ω, |(W t ω - W s ω) ^ 2 - (B t ω - B s ω) ^ 2| ∂P) ≤
      2 * (L * ((t : ℝ) - (s : ℝ))) * Real.sqrt ((t : ℝ) - (s : ℝ)) +
        (L * ((t : ℝ) - (s : ℝ))) ^ 2 ∧
    Integrable (fun ω => |W t ω - W s ω| ^ 3) P ∧
    (∫ ω, |W t ω - W s ω| ^ 3 ∂P) ≤
      4 * (standardGaussianThirdMoment * ((t : ℝ) - (s : ℝ)) *
        Real.sqrt ((t : ℝ) - (s : ℝ)) + (L * ((t : ℝ) - (s : ℝ))) ^ 3) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hLaw := preBrownian_hasLaw_increment hB hst
  have hX2 : Integrable (fun ω => (B t ω - B s ω) ^ 2) P := by
    simpa only [sq_abs] using integrable_abs_pow_of_gaussianLaw hLaw 2
  have hsecond : (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - (s : ℝ) := by
    simpa only [add_tsub_cancel_of_le hst, NNReal.coe_sub hst] using
      preBrownian_integral_sq (hB.shift s) (t - s)
  have hK : 0 ≤ L * ((t : ℝ) - (s : ℝ)) :=
    mul_nonneg hL (sub_nonneg.mpr hst)
  obtain ⟨hquadInt, hquad⟩ := integral_abs_sq_sub_sq_le hK hLaw.aemeasurable
    ((hW t).sub (hW s)) hX2 hbound
  obtain ⟨hcubicInt, hcubic⟩ := integral_abs_cube_le_of_bounded_perturbation hK
    ((hW t).sub (hW s)) (integrable_abs_pow_of_gaussianLaw hLaw 3) hbound
  rw [hsecond] at hquad
  rw [preBrownian_integral_abs_increment_cube hB hst] at hcubic
  exact ⟨hquadInt, hquad, hcubicInt, hcubic⟩

end Problem367

end

end OAI
