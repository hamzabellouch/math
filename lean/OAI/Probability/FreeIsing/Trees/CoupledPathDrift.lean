import OAI.Probability.FreeIsing.Trees.CoupledPathProducts

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_abs_mul_le_sqrt_moments {U Z : Ω → ℝ}
    (hU : MemLp U 2 μ) (hZ : MemLp Z 2 μ) :
    (∫ ω, |U ω| * |Z ω| ∂μ) ≤
      Real.sqrt (∫ ω, U ω ^ 2 ∂μ) * Real.sqrt (∫ ω, Z ω ^ 2 ∂μ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    norm_num [Real.holderConjugate_iff]
  have h := integral_mul_norm_le_Lp_mul_Lq hpq (by simpa using hU) (by simpa using hZ)
  simpa only [Real.norm_eq_abs, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow] using h

theorem integral_weighted_abs_mul_le {U Z w : Ω → ℝ} {C : ℝ}
    (hU : MemLp U 2 μ) (hZ : MemLp Z 2 μ) (hw : Measurable w)
    (hw0 : ∀ ω, 0 ≤ w ω) (hwC : ∀ ω, w ω ≤ C) :
    Integrable (fun ω => |U ω| * w ω * |Z ω|) μ ∧
    (∫ ω, |U ω| * w ω * |Z ω| ∂μ) ≤
      Real.sqrt (C * ∫ ω, U ω ^ 2 ∂μ) *
        Real.sqrt (∫ ω, w ω * Z ω ^ 2 ∂μ) := by
  let F := fun ω => U ω * Real.sqrt (w ω)
  let G := fun ω => Z ω * Real.sqrt (w ω)
  have hwt : MemLp (fun ω => Real.sqrt (w ω)) (⊤ : ENNReal) μ := by
    apply memLp_top_of_bound hw.sqrt.aestronglyMeasurable (Real.sqrt C)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (hwC ω)
  have hF : MemLp F 2 μ := hU.mul hwt
  have hG : MemLp G 2 μ := hZ.mul hwt
  have hFsq (ω : Ω) : F ω ^ 2 = w ω * U ω ^ 2 := by
    dsimp [F]
    rw [mul_pow, Real.sq_sqrt (hw0 ω), mul_comm]
  have hGsq (ω : Ω) : G ω ^ 2 = w ω * Z ω ^ 2 := by
    dsimp [G]
    rw [mul_pow, Real.sq_sqrt (hw0 ω), mul_comm]
  have hprod (ω : Ω) : |F ω| * |G ω| = |U ω| * w ω * |Z ω| := by
    dsimp [F, G]
    rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc
      |U ω| * Real.sqrt (w ω) * (|Z ω| * Real.sqrt (w ω)) =
          |U ω| * |Z ω| * (Real.sqrt (w ω)) ^ 2 := by ring
      _ = |U ω| * w ω * |Z ω| := by rw [Real.sq_sqrt (hw0 ω)]; ring
  have hI : Integrable (fun ω => |U ω| * w ω * |Z ω|) μ := by
    have h := hF.norm.integrable_mul hG.norm
    change Integrable (fun ω => ‖F ω‖ * ‖G ω‖) μ at h
    simpa only [Real.norm_eq_abs, Pi.mul_apply, hprod] using h
  have hcs := integral_abs_mul_le_sqrt_moments hF hG
  simp_rw [hprod, hFsq, hGsq] at hcs
  have hFbound : (∫ ω, w ω * U ω ^ 2 ∂μ) ≤ C * ∫ ω, U ω ^ 2 ∂μ := by
    have hint : Integrable (fun ω => w ω * U ω ^ 2) μ := by
      simpa only [hFsq] using hF.integrable_sq
    calc
      (∫ ω, w ω * U ω ^ 2 ∂μ) ≤ ∫ ω, C * U ω ^ 2 ∂μ :=
        integral_mono hint (hU.integrable_sq.const_mul C)
          (fun ω => mul_le_mul_of_nonneg_right (hwC ω) (sq_nonneg _))
      _ = C * ∫ ω, U ω ^ 2 ∂μ := integral_const_mul _ _
  exact ⟨hI, hcs.trans (mul_le_mul_of_nonneg_right
    (Real.sqrt_le_sqrt hFbound) (Real.sqrt_nonneg _))⟩

theorem integral_abs_mul_prod_responseAttenuation_sq_sub_sq_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X Y : ι → Ω → ℝ} {U : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    (hU : MemLp U 2 μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => |U ω| * |P ω ^ 2 - P' ω ^ 2|) μ ∧
      (∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ) ≤
        2 * Real.sqrt (2 * ∫ ω, U ω ^ 2 ∂μ) *
          Real.sqrt (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) := by
  dsimp only
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
  let w := fun ω => P ω ^ 2 + P' ω ^ 2
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hw : Measurable w := (hP.pow_const 2).add (hP'.pow_const 2)
  have hw0 (ω : Ω) : 0 ≤ w ω := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hw2 (ω : Ω) : w ω ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    dsimp only [w]
    nlinarith
  have hZ : MemLp Z 2 μ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  have hbound := integral_weighted_abs_mul_le hU hZ hw hw0 hw2
  have hpoint (ω : Ω) : |U ω| * |P ω ^ 2 - P' ω ^ 2| ≤
      2 * (|U ω| * w ω * |Z ω|) := by
    calc
      |U ω| * |P ω ^ 2 - P' ω ^ 2| ≤ |U ω| * (2 * w ω * |Z ω|) :=
        mul_le_mul_of_nonneg_left
          (abs_prod_responseAttenuation_sq_sub_sq_le s
            (fun i => X i ω) (fun i => Y i ω) hθ) (abs_nonneg _)
      _ = _ := by ring
  have hDiff : Integrable (fun ω => |U ω| * |P ω ^ 2 - P' ω ^ 2|) μ := by
    apply (hbound.1.const_mul 2).mono'
      (hU.aestronglyMeasurable.aemeasurable.abs.aestronglyMeasurable.mul
        (((hP.pow_const 2).sub (hP'.pow_const 2)).abs.aestronglyMeasurable))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    exact hpoint ω
  refine ⟨hDiff, ?_⟩
  calc
    (∫ ω, |U ω| * |P ω ^ 2 - P' ω ^ 2| ∂μ) ≤
        ∫ ω, 2 * (|U ω| * w ω * |Z ω|) ∂μ :=
      integral_mono hDiff (hbound.1.const_mul 2) hpoint
    _ = 2 * ∫ ω, |U ω| * w ω * |Z ω| ∂μ := integral_const_mul _ _
    _ ≤ 2 * (Real.sqrt (2 * ∫ ω, U ω ^ 2 ∂μ) *
        Real.sqrt (∫ ω, w ω * Z ω ^ 2 ∂μ)) :=
      mul_le_mul_of_nonneg_left hbound.2 (by norm_num)
    _ = _ := by ring

theorem integral_mul_prod_responseAttenuation_sq_le
    {ι : Type*} (s : Finset ι) {theta : ℝ} (hθ : theta ^ 2 ≤ 1)
    {X : ι → Ω → ℝ} {U : Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hU : MemLp U 2 μ) :
    Integrable (fun ω => U ω ^ 2 *
      (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2) μ ∧
    (∫ ω, U ω ^ 2 * (∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 ∂μ) ≤
      ∫ ω, U ω ^ 2 ∂μ := by
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hpoint (ω : Ω) : U ω ^ 2 * P ω ^ 2 ≤ U ω ^ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    change 0 < P ω at hp
    change P ω ≤ 1 at hl
    have hsq : P ω ^ 2 ≤ 1 := by nlinarith
    simpa using mul_le_mul_of_nonneg_left hsq (sq_nonneg (U ω))
  have hint : Integrable (fun ω => U ω ^ 2 * P ω ^ 2) μ := by
    apply hU.integrable_sq.mono'
      ((hU.aestronglyMeasurable.pow 2).mul ((hP.pow_const 2).aestronglyMeasurable))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpoint ω
  exact ⟨hint, integral_mono hint hU.integrable_sq hpoint⟩

end Probability

end Problem367

end

end OAI
