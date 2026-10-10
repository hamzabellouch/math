import OAI.Probability.FreeIsing.Energy.CoupledAttenuation

namespace OAI

noncomputable section

open MeasureTheory

namespace Problem367

private theorem sub_le_mul_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a - b ≤ a * (Real.log a - Real.log b) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have hm := mul_le_mul_of_nonneg_left h ha.le
  have hcancel : a * (b / a) = b := by field_simp
  nlinarith

theorem abs_sub_le_max_mul_abs_log_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a - b| ≤ max a b * |Real.log a - Real.log b| := by
  rcases le_total b a with hba | hab
  · rw [max_eq_left hba, abs_of_nonneg (sub_nonneg.mpr hba),
      abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hb hba))]
    exact sub_le_mul_log_sub ha hb
  · rw [max_eq_right hab, abs_of_nonpos (sub_nonpos.mpr hab),
      abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log ha hab))]
    have h := sub_le_mul_log_sub hb ha
    nlinarith

theorem positive_sub_sq_le_log_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (a - b) ^ 2 ≤ (a ^ 2 + b ^ 2) * (Real.log a - Real.log b) ^ 2 := by
  have h := abs_sub_le_max_mul_abs_log_sub ha hb
  have hmax : 0 ≤ max a b := le_trans ha.le (le_max_left _ _)
  have hs := (sq_le_sq₀ (abs_nonneg (a - b))
    (mul_nonneg hmax (abs_nonneg _))).2 h
  rw [sq_abs, mul_pow, sq_abs] at hs
  have hmaxsq : (max a b) ^ 2 ≤ a ^ 2 + b ^ 2 := by
    rcases le_total b a with hba | hab
    · rw [max_eq_left hba]
      nlinarith [sq_nonneg b]
    · rw [max_eq_right hab]
      nlinarith [sq_nonneg a]
  exact hs.trans (mul_le_mul_of_nonneg_right hmaxsq (sq_nonneg _))

theorem abs_sq_sub_sq_le_log_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a ^ 2 - b ^ 2| ≤ 2 * (a ^ 2 + b ^ 2) * |Real.log a - Real.log b| := by
  have h := abs_sub_le_max_mul_abs_log_sub (sq_pos_of_pos ha) (sq_pos_of_pos hb)
  rw [Real.log_pow, Real.log_pow, ← mul_sub, abs_mul] at h
  norm_num at h
  have hmax : max (a ^ 2) (b ^ 2) ≤ a ^ 2 + b ^ 2 := by
    exact max_le (by nlinarith [sq_nonneg b]) (by nlinarith [sq_nonneg a])
  calc
    |a ^ 2 - b ^ 2| ≤ max (a ^ 2) (b ^ 2) * (2 * |Real.log a - Real.log b|) := h
    _ ≤ (a ^ 2 + b ^ 2) * (2 * |Real.log a - Real.log b|) :=
      mul_le_mul_of_nonneg_right hmax (by positivity)
    _ = _ := by ring

theorem log_prod_responseAttenuation_sub {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    Real.log (∏ i ∈ s, responseAttenuation theta (x i)) -
        Real.log (∏ i ∈ s, responseAttenuation theta (y i)) =
      ∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i))) := by
  rw [Real.log_prod (fun i _ => (responseAttenuation_pos hθ (x i)).ne'),
    Real.log_prod (fun i _ => (responseAttenuation_pos hθ (y i)).ne'),
    Finset.sum_sub_distrib]

theorem prod_responseAttenuation_sub_sq_le {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    ((∏ i ∈ s, responseAttenuation theta (x i)) -
        (∏ i ∈ s, responseAttenuation theta (y i))) ^ 2 ≤
      ((∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 +
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i)))) ^ 2 := by
  have h := positive_sub_sq_le_log_weight
    (prod_responseAttenuation_pos s x hθ) (prod_responseAttenuation_pos s y hθ)
  rwa [log_prod_responseAttenuation_sub s x y hθ] at h

theorem abs_prod_responseAttenuation_sq_sub_sq_le {ι : Type*} (s : Finset ι)
    (x y : ι → ℝ) {theta : ℝ} (hθ : theta ^ 2 ≤ 1) :
    |(∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 -
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2| ≤
      2 * ((∏ i ∈ s, responseAttenuation theta (x i)) ^ 2 +
        (∏ i ∈ s, responseAttenuation theta (y i)) ^ 2) *
      |∑ i ∈ s, (Real.log (responseAttenuation theta (x i)) -
        Real.log (responseAttenuation theta (y i)))| := by
  have h := abs_sq_sub_sq_le_log_weight
    (prod_responseAttenuation_pos s x hθ) (prod_responseAttenuation_pos s y hθ)
  rwa [log_prod_responseAttenuation_sub s x y hθ] at h

section Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_sq_sum_le_card_sq (s : Finset ι) (D : ι → Ω → ℝ)
    (hD : ∀ i ∈ s, MemLp (D i) 2 μ) {S : ℝ}
    (hS : ∀ i ∈ s, (∫ ω, D i ω ^ 2 ∂μ) ≤ S) :
    (∫ ω, (∑ i ∈ s, D i ω) ^ 2 ∂μ) ≤ (s.card : ℝ) ^ 2 * S := by
  have hSum : MemLp (fun ω => ∑ i ∈ s, D i ω) 2 μ := memLp_finsetSum s hD
  have hInt := integrable_finsetSum s (fun i hi => (hD i hi).integrable_sq)
  calc
    (∫ ω, (∑ i ∈ s, D i ω) ^ 2 ∂μ) ≤
        ∫ ω, (s.card : ℝ) * ∑ i ∈ s, D i ω ^ 2 ∂μ := by
      apply integral_mono hSum.integrable_sq (hInt.const_mul _)
      intro ω
      simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => D i ω)
    _ = (s.card : ℝ) * ∑ i ∈ s, ∫ ω, D i ω ^ 2 ∂μ := by
      rw [integral_const_mul, integral_finsetSum s (fun i hi => (hD i hi).integrable_sq)]
    _ ≤ (s.card : ℝ) * ∑ _i ∈ s, S := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum hS) (Nat.cast_nonneg _)
    _ = (s.card : ℝ) ^ 2 * S := by simp [pow_two, mul_assoc]

theorem measurable_responseAttenuation (theta : ℝ) : Measurable (responseAttenuation theta) := by
  have ht : Measurable Real.tanh := lipschitzWith_tanh_response.continuous.measurable
  exact (measurable_const.sub (ht.pow_const 2)).div
    (measurable_const.sub (measurable_const.mul (ht.pow_const 2)))

theorem measurable_prod_responseAttenuation (s : Finset ι) (theta : ℝ)
    {X : ι → Ω → ℝ} (hX : ∀ i ∈ s, Measurable (X i)) :
    Measurable (fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)) :=
  s.measurable_prod (fun i hi => (measurable_responseAttenuation theta).comp (hX i hi))

theorem memLp_sum_log_responseAttenuation_sub (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    MemLp (fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))) 2 μ := by
  apply memLp_finsetSum s
  intro i hi
  have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
  exact (memLp_two_iff_integrable_sq
    (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
      (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))

theorem integral_prod_responseAttenuation_sub_sq_le (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ) :
    let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
    let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
    let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
    Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ ∧
      Integrable (fun ω => (P ω - P' ω) ^ 2) μ ∧
      (∫ ω, (P ω - P' ω) ^ 2 ∂μ) ≤
        ∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ := by
  dsimp only
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let Z := fun ω => ∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω)))
  have hP : Measurable P := measurable_prod_responseAttenuation s theta hX
  have hP' : Measurable P' := measurable_prod_responseAttenuation s theta hY
  have hZ : MemLp Z 2 μ := memLp_sum_log_responseAttenuation_sub s hθ hX hY hInt
  have hweight (ω : Ω) : P ω ^ 2 + P' ω ^ 2 ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    nlinarith
  have hQ : Integrable (fun ω => (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2) μ := by
    apply (hZ.integrable_sq.const_mul 2).mono'
      (((hP.pow_const 2).add (hP'.pow_const 2)).aestronglyMeasurable.mul
        (hZ.aestronglyMeasurable.pow 2))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (hweight ω) (sq_nonneg _)
  have hpoint (ω : Ω) : (P ω - P' ω) ^ 2 ≤ (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 :=
    prod_responseAttenuation_sub_sq_le s (fun i => X i ω) (fun i => Y i ω) hθ
  have hDiff : Integrable (fun ω => (P ω - P' ω) ^ 2) μ := by
    apply hQ.mono' (((hP.sub hP').pow_const 2).aestronglyMeasurable)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpoint ω
  exact ⟨hQ, hDiff, integral_mono hDiff hQ hpoint⟩

theorem integral_weighted_path_log_sq_le (s : Finset ι)
    {theta : ℝ} (hθ : theta ^ 2 ≤ 1) {X Y : ι → Ω → ℝ}
    (hX : ∀ i ∈ s, Measurable (X i)) (hY : ∀ i ∈ s, Measurable (Y i))
    (hInt : ∀ i ∈ s, Integrable (fun ω => (X i ω - Y i ω) ^ 2) μ)
    {S : ℝ}
    (hS : ∀ i ∈ s, (∫ ω, (Real.log (responseAttenuation theta (X i ω)) -
      Real.log (responseAttenuation theta (Y i ω))) ^ 2 ∂μ) ≤ S) :
    (∫ ω, ((∏ i ∈ s, responseAttenuation theta (X i ω)) ^ 2 +
      (∏ i ∈ s, responseAttenuation theta (Y i ω)) ^ 2) *
      (∑ i ∈ s, (Real.log (responseAttenuation theta (X i ω)) -
        Real.log (responseAttenuation theta (Y i ω)))) ^ 2 ∂μ) ≤
      2 * (s.card : ℝ) ^ 2 * S := by
  let P := fun ω => ∏ i ∈ s, responseAttenuation theta (X i ω)
  let P' := fun ω => ∏ i ∈ s, responseAttenuation theta (Y i ω)
  let D := fun i ω => Real.log (responseAttenuation theta (X i ω)) -
    Real.log (responseAttenuation theta (Y i ω))
  let Z := fun ω => ∑ i ∈ s, D i ω
  have hQ := (integral_prod_responseAttenuation_sub_sq_le s hθ hX hY hInt).1
  have hD : ∀ i ∈ s, MemLp (D i) 2 μ := by
    intro i hi
    have hm := (lipschitzWith_log_responseAttenuation hθ).continuous.measurable
    exact (memLp_two_iff_integrable_sq
      (((hm.comp (hX i hi)).sub (hm.comp (hY i hi))).aestronglyMeasurable)).2
        (integrable_log_responseAttenuation_sub_sq hθ (hX i hi) (hY i hi) (hInt i hi))
  have hZ : MemLp Z 2 μ := memLp_finsetSum s hD
  have hw (ω : Ω) : P ω ^ 2 + P' ω ^ 2 ≤ 2 := by
    have hp := prod_responseAttenuation_pos s (fun i => X i ω) hθ
    have hp' := prod_responseAttenuation_pos s (fun i => Y i ω) hθ
    have hl := prod_attenuation_le_one s (fun i => X i ω) hθ
    have hl' := prod_attenuation_le_one s (fun i => Y i ω) hθ
    change P ω > 0 at hp
    change P' ω > 0 at hp'
    change P ω ≤ 1 at hl
    change P' ω ≤ 1 at hl'
    nlinarith
  change (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) ≤ _
  calc
    (∫ ω, (P ω ^ 2 + P' ω ^ 2) * Z ω ^ 2 ∂μ) ≤ ∫ ω, 2 * Z ω ^ 2 ∂μ :=
      integral_mono hQ (hZ.integrable_sq.const_mul 2)
        (fun ω => mul_le_mul_of_nonneg_right (hw ω) (sq_nonneg _))
    _ = 2 * ∫ ω, Z ω ^ 2 ∂μ := integral_const_mul _ _
    _ ≤ 2 * ((s.card : ℝ) ^ 2 * S) :=
      mul_le_mul_of_nonneg_left (integral_sq_sum_le_card_sq s D hD hS) (by norm_num)
    _ = _ := by ring

end Probability

end Problem367

end

end OAI
