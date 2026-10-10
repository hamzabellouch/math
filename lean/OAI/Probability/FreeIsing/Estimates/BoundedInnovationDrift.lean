import OAI.Probability.FreeIsing.Brownian.Observation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

theorem intervalIntegrable_of_measurable_norm_le_const
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hbound : ∀ t, ‖f t‖ ≤ C) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  apply (intervalIntegrable_const (c := C)).mono_fun' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall hbound

theorem lipschitzWith_intervalPrimitive_of_bound
    {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ≥0}
    (hbound : ∀ t, ‖f t‖ ≤ (C : ℝ)) (a : ℝ) :
    LipschitzWith C (fun t : ℝ => ∫ r in a..t, f r) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq, ← Real.norm_eq_abs, intervalIntegral.integral_interval_sub_left
    (intervalIntegrable_of_measurable_norm_le_const hf hbound a s)
    (intervalIntegrable_of_measurable_norm_le_const hf hbound a t)]
  simpa only [Real.dist_eq] using
    intervalIntegral.norm_integral_le_of_norm_le_const (fun r _ => hbound r)

theorem intervalIntegrable_nnreal_process_of_bound
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C : ℝ}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ C) (ω : Ω) (a b : ℝ) :
    IntervalIntegrable (fun r => m r.toNNReal ω) volume a b :=
  intervalIntegrable_of_measurable_norm_le_const
    ((hm ω).comp measurable_real_toNNReal) (fun _ => hbound _ ω) a b

theorem lipschitzWith_nnrealTimePrimitive
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ)) (ω : Ω) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) := by
  have h := lipschitzWith_intervalPrimitive_of_bound
    ((hm ω).comp measurable_real_toNNReal) (fun r => hbound _ ω) 0
  apply LipschitzWith.of_dist_le_mul
  intro s t
  exact h.dist_le_mul (s : ℝ) (t : ℝ)

theorem norm_nnrealTimePrimitive_sub_le
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ)) (ω : Ω) (s t : ℝ≥0) :
    ‖nnrealTimePrimitive m t ω - nnrealTimePrimitive m s ω‖ ≤
      (C : ℝ) * |(t : ℝ) - (s : ℝ)| := by
  exact (lipschitzWith_nnrealTimePrimitive hm hbound ω).dist_le_mul t s

theorem innovationCorrection_lipschitzWith
    {Ω : Type*} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hm : ∀ ω, Measurable (fun t => m t ω)) {C D : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ))
    (hσ : ∀ ω, ‖σ ω‖ ≤ (D : ℝ)) (ω : Ω) :
    LipschitzWith (D + C)
      (fun t : ℝ≥0 => (t : ℝ) * σ ω - nnrealTimePrimitive m t ω) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  calc
    dist ((s : ℝ) * σ ω - nnrealTimePrimitive m s ω)
        ((t : ℝ) * σ ω - nnrealTimePrimitive m t ω)
      ≤ dist ((s : ℝ) * σ ω) ((t : ℝ) * σ ω) +
          dist (nnrealTimePrimitive m s ω) (nnrealTimePrimitive m t ω) :=
        dist_sub_sub_le _ _ _ _
    _ ≤ (D : ℝ) * dist s t + (C : ℝ) * dist s t := by
      apply add_le_add
      · rw [Real.dist_eq, ← sub_mul, abs_mul]
        calc
          |(s : ℝ) - (t : ℝ)| * |σ ω| ≤
              |(s : ℝ) - (t : ℝ)| * D :=
            mul_le_mul_of_nonneg_left (hσ ω) (abs_nonneg _)
          _ = (D : ℝ) * dist s t := by rw [mul_comm]; rfl
      · exact (lipschitzWith_nnrealTimePrimitive hm hbound ω).dist_le_mul s t
    _ = ((D + C : ℝ≥0) : ℝ) * dist s t := by
      push_cast
      ring

theorem measurable_path_of_isStronglyProgressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) (ω : Ω) :
    Measurable (fun t => m t ω) := by
  have hstop (n : ℕ) : StronglyMeasurable
      (fun t : ℝ≥0 => m (min t (n : ℝ≥0)) ω) := by
    let : MeasurableSpace Ω := F n
    have htime : Measurable (fun t : ℝ≥0 =>
        (⟨min t (n : ℝ≥0), by simp⟩ : Set.Iic (n : ℝ≥0))) :=
      (measurable_id.min measurable_const).subtype_mk
    exact (hm n).comp_measurable (htime.prodMk measurable_const)
  apply (stronglyMeasurable_of_tendsto atTop hstop ?_).measurable
  apply tendsto_pi_nhds.mpr
  intro t
  apply tendsto_const_nhds.congr'
  obtain ⟨N, hN⟩ := exists_nat_ge t
  filter_upwards [eventually_ge_atTop N] with n hn
  have htn : t ≤ (n : ℝ≥0) := hN.trans (by exact_mod_cast hn)
  simp [min_eq_left htn]

theorem lipschitzWith_nnrealTimePrimitive_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) {C : ℝ≥0}
    (hbound : ∀ t ω, ‖m t ω‖ ≤ (C : ℝ)) (ω : Ω) :
    LipschitzWith C (fun t => nnrealTimePrimitive m t ω) :=
  lipschitzWith_nnrealTimePrimitive (measurable_path_of_isStronglyProgressive hm)
    hbound ω

theorem innovationCorrection_two_lipschitzWith
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hm : IsStronglyProgressive F m)
    (hbound : ∀ t ω, ‖m t ω‖ ≤ 1) (hσ : ∀ ω, ‖σ ω‖ ≤ 1) (ω : Ω) :
    LipschitzWith 2
      (fun t : ℝ≥0 => (t : ℝ) * σ ω - nnrealTimePrimitive m t ω) := by
  have h := innovationCorrection_lipschitzWith
    (measurable_path_of_isStronglyProgressive hm)
    (C := 1) (D := 1) hbound hσ ω
  norm_num at h ⊢
  exact h

def unitClip (x : ℝ) : ℝ := max (-1) (min 1 x)

theorem continuous_unitClip : Continuous unitClip :=
  continuous_const.max (continuous_const.min continuous_id)

theorem norm_unitClip_le (x : ℝ) : ‖unitClip x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem unitClip_eq_of_norm_le {x : ℝ} (h : ‖x‖ ≤ 1) : unitClip x = x := by
  have hx := abs_le.mp h
  simp only [unitClip, min_eq_right hx.2, max_eq_right hx.1]

theorem isStronglyProgressive_unitClip
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ}
    (hm : IsStronglyProgressive F m) :
    IsStronglyProgressive F (fun t ω => unitClip (m t ω)) :=
  fun t => continuous_unitClip.comp_stronglyMeasurable (hm t)

theorem unitClip_posterior_version
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hσ : ∀ᵐ ω ∂P, ‖σ ω‖ ≤ 1)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t]) (t : ℝ≥0) :
    (fun ω => unitClip (m t ω)) =ᵐ[P] P[σ | F t] := by
  have hb : ∀ᵐ ω ∂P, ‖P[σ | F t] ω‖ ≤ 1 :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hσ
  filter_upwards [hposterior t, hb] with ω heq hbω
  rw [heq, unitClip_eq_of_norm_le hbω]

theorem exists_pointwise_bounded_progressive_posterior
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} {m : ℝ≥0 → Ω → ℝ} {σ : Ω → ℝ}
    (hm : IsStronglyProgressive F m)
    (hσ : ∀ᵐ ω ∂P, ‖σ ω‖ ≤ 1)
    (hposterior : ∀ t, m t =ᵐ[P] P[σ | F t]) :
    ∃ m' : ℝ≥0 → Ω → ℝ, IsStronglyProgressive F m' ∧
      (∀ t ω, ‖m' t ω‖ ≤ 1) ∧
      (∀ t, m' t =ᵐ[P] P[σ | F t]) ∧
      (∀ ω, LipschitzWith 1 (fun t => nnrealTimePrimitive m' t ω)) := by
  refine ⟨fun t ω => unitClip (m t ω), isStronglyProgressive_unitClip hm,
    fun t ω => norm_unitClip_le _, unitClip_posterior_version hσ hposterior, ?_⟩
  intro ω
  exact lipschitzWith_nnrealTimePrimitive_of_progressive
    (isStronglyProgressive_unitClip hm) (C := 1) (fun t ω => norm_unitClip_le _) ω

end Problem367

end

end OAI
