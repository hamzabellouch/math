import Mathlib.Analysis.BoundedVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

namespace Invariant233.BVDiscrepancy

def unitMeasure : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure]

def tail (a x : ℝ) : ℂ := (Icc a 1).indicator (fun _ => 1) x

lemma measurable_tail (a : ℝ) : Measurable (tail a) :=
  measurable_const.indicator measurableSet_Icc

lemma norm_tail_le_one (a x : ℝ) : ‖tail a x‖ ≤ 1 := by
  by_cases hx : x ∈ Icc a 1 <;> simp [tail, hx]

lemma integrable_tail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (a : ℝ) :
    Integrable (fun ω => tail a (X ω)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((measurable_tail a).comp hX).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => norm_tail_le_one a (X ω)

lemma integral_tail {a : ℝ} (ha : a ∈ Icc 0 1) :
    ∫ x, tail a x ∂unitMeasure = ((1 - a : ℝ) : ℂ) := by
  simp only [tail]
  rw [integral_indicator measurableSet_Icc]
  simp only [unitMeasure, Measure.restrict_restrict measurableSet_Icc]
  rw [inter_eq_left.mpr (Icc_subset_Icc ha.1 le_rfl)]
  simp [max_eq_left (sub_nonneg.mpr ha.2)]

def coefficient (f : ℝ → ℂ) (N k : ℕ) : ℂ :=
  if k = 0 then f 0 else f ((k : ℝ) / N) - f (((k - 1 : ℕ) : ℝ) / N)

def step (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), coefficient f N k * tail ((k : ℝ) / N) x

@[simp] lemma coefficient_zero (f : ℝ → ℂ) (N : ℕ) : coefficient f N 0 = f 0 := by
  simp [coefficient]

@[simp] lemma coefficient_succ (f : ℝ → ℂ) (N k : ℕ) :
    coefficient f N (k + 1) = f (((k : ℝ) + 1) / N) - f ((k : ℝ) / N) := by
  simp [coefficient]

lemma sum_coefficient (f : ℝ → ℂ) (N r : ℕ) :
    ∑ k ∈ Finset.range (r + 1), coefficient f N k = f ((r : ℝ) / N) := by
  induction r with
  | zero => simp
  | succ r hr =>
    rw [Finset.sum_range_succ, hr, coefficient_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    abel

lemma sum_norm_coefficient_le (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∑ k ∈ Finset.range (N + 1), ‖coefficient f N k‖ ≤
      ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  rw [Finset.sum_range_succ']
  simp only [coefficient_zero, coefficient_succ]
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hv := eVariationOn.sum_le_of_monotoneOn_Iic (f := f) (s := Icc (0 : ℝ) 1) (n := N)
    (u := fun k : ℕ => (k : ℝ) / N)
    (fun i _ j _ hij => div_le_div_of_nonneg_right (Nat.cast_le.mpr hij) hNp.le)
    (fun i hi => ⟨div_nonneg (Nat.cast_nonneg _) hNp.le,
      (div_le_one hNp).mpr (Nat.cast_le.mpr hi)⟩)
  have hv' :
      ENNReal.ofReal (∑ k ∈ Finset.range N,
        ‖f (((k : ℝ) + 1) / N) - f ((k : ℝ) / N)‖) ≤
        eVariationOn f (Icc (0 : ℝ) 1) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    simpa only [edist_dist, dist_eq_norm, Nat.cast_add, Nat.cast_one] using hv
  have := (ENNReal.toReal_mono hf hv')
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at this
  linarith

lemma measurable_step (f : ℝ → ℂ) (N : ℕ) : Measurable (step f N) := by
  unfold step
  exact Finset.measurable_sum _ fun k _ => measurable_const.mul (measurable_tail _)

lemma norm_step_le (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) (x : ℝ) :
    ‖step f N x‖ ≤ ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
  calc
    ‖step f N x‖ ≤ ∑ k ∈ Finset.range (N + 1),
        ‖coefficient f N k * tail ((k : ℝ) / N) x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (N + 1), ‖coefficient f N k‖ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_tail_le_one _ _)
    _ ≤ _ := sum_norm_coefficient_le f hN hf

lemma step_eq_floor (f : ℝ → ℂ) {N : ℕ} (hN : 0 < N)
    {x : ℝ} (hx : x ∈ Icc 0 1) :
    step f N x = f ((⌊(N : ℝ) * x⌋₊ : ℝ) / N) := by
  have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hNx : 0 ≤ (N : ℝ) * x := mul_nonneg hNp.le hx.1
  have hr : ⌊(N : ℝ) * x⌋₊ ≤ N := by
    apply Nat.floor_le_of_le
    simpa using mul_le_mul_of_nonneg_left hx.2 hNp.le
  have htail (k : ℕ) : tail ((k : ℝ) / N) x =
      if k ≤ ⌊(N : ℝ) * x⌋₊ then 1 else 0 := by
    have hiff : (k : ℝ) / N ≤ x ↔ k ≤ ⌊(N : ℝ) * x⌋₊ := by
      rw [div_le_iff₀ hNp, Nat.le_floor_iff hNx]
      rw [mul_comm]
    simp [tail, Set.indicator_apply, hx.2, hiff]
  unfold step
  simp_rw [htail, mul_ite, mul_one, mul_zero]
  calc
    ∑ k ∈ Finset.range (N + 1),
        (if k ≤ ⌊(N : ℝ) * x⌋₊ then coefficient f N k else 0) =
      ∑ k ∈ Finset.range (⌊(N : ℝ) * x⌋₊ + 1), coefficient f N k := by
        calc
          _ = ∑ k ∈ Finset.range (⌊(N : ℝ) * x⌋₊ + 1),
              (if k ≤ ⌊(N : ℝ) * x⌋₊ then coefficient f N k else 0) := by
            symm
            apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hr))
            intro k hk hkr
            simp only [Finset.mem_range, not_lt] at hkr
            simp [show ¬ k ≤ ⌊(N : ℝ) * x⌋₊ by omega]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [Finset.mem_range] at hk
            simp [Nat.le_of_lt_succ hk]
    _ = _ := sum_coefficient f N _

lemma tendsto_step_of_continuousAt (f : ℝ → ℂ) {x : ℝ}
    (hx : x ∈ Icc 0 1) (hcont : ContinuousAt f x) :
    Tendsto (fun n : ℕ => step f (n + 1) x) atTop (𝓝 (f x)) := by
  have hgrid := (tendsto_nat_floor_mul_div_atTop hx.1).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hgrid' : Tendsto (fun n : ℕ =>
      (⌊(((n + 1 : ℕ) : ℝ) * x)⌋₊ : ℝ) / (n + 1 : ℕ)) atTop (𝓝 x) := by
    simpa only [Function.comp_def, mul_comm x] using hgrid
  convert hcont.tendsto.comp hgrid' using 1
  funext n
  exact step_eq_floor f (Nat.succ_pos n) hx

lemma ae_tendsto_step (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∀ᵐ x ∂unitMeasure,
      Tendsto (fun n : ℕ => step f (n + 1) x) atTop (𝓝 (f x)) := by
  have hf' : BoundedVariationOn f (uIcc (0 : ℝ) 1) := by simpa using hf
  have hdiff := hf'.ae_differentiableAt_of_mem_uIcc
  have hdiff' : ∀ᵐ x ∂unitMeasure, x ∈ Icc (0 : ℝ) 1 → DifferentiableAt ℝ f x := by
    exact ae_restrict_of_ae (by simpa using hdiff)
  filter_upwards [hdiff', ae_restrict_mem (μ := volume) measurableSet_Icc] with x hd hx
  exact tendsto_step_of_continuousAt f hx (hd hx).continuousAt

lemma ae_tendsto_step_comp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : Measurable X) (hXac : μ.map X ≪ unitMeasure)
    (f : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => step f (n + 1) (X ω)) atTop (𝓝 (f (X ω))) :=
  ae_of_ae_map hX.aemeasurable (hXac.ae_le (ae_tendsto_step f hf))

lemma integrable_tail_mul {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (a b : ℝ) : Integrable (fun ω => tail a (X ω) * tail b (Y ω)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_tail a).comp hX).mul ((measurable_tail b).comp hY)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  change ‖tail a (X ω) * tail b (Y ω)‖ ≤ 1
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖tail b (Y ω)‖ :=
      mul_le_mul_of_nonneg_right (norm_tail_le_one _ _) (norm_nonneg _)
    _ ≤ 1 := by simpa only [one_mul] using norm_tail_le_one b (Y ω)

theorem finite_test_discrepancy {Ω ι κ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (u : ι → Ω → ℂ) (v : κ → Ω → ℂ)
    (m : ι → ℂ) (n : κ → ℂ) (ε : ℝ)
    (hint : ∀ i ∈ s, ∀ j ∈ t, Integrable (fun ω => u i ω * v j ω) μ)
    (hdisc : ∀ i ∈ s, ∀ j ∈ t,
      ‖(∫ ω, u i ω * v j ω ∂μ) - m i * n j‖ ≤ ε) :
    ‖(∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) -
        (∑ i ∈ s, a i * m i) * (∑ j ∈ t, b j * n j)‖ ≤
      ε * (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) := by
  have hint' (i : ι) (hi : i ∈ s) (j : κ) (hj : j ∈ t) :
      Integrable (fun ω => (a i * u i ω) * (b j * v j ω)) μ := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using
      (hint i hi j hj).const_mul (a i * b j)
  have hI :
      (∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * b j) * (∫ ω, u i ω * v j ω ∂μ) := by
    simp_rw [Finset.sum_mul_sum]
    rw [integral_finsetSum s (fun i hi => integrable_finsetSum t (hint' i hi))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum t (hint' i hi)]
    apply Finset.sum_congr rfl
    intro j hj
    have heq : (fun ω => a i * u i ω * (b j * v j ω)) =
        fun ω => (a i * b j) * (u i ω * v j ω) := by funext ω; ring
    rw [heq, integral_const_mul]
  have hrewrite :
      (∫ ω, (∑ i ∈ s, a i * u i ω) * (∑ j ∈ t, b j * v j ω) ∂μ) -
        (∑ i ∈ s, a i * m i) * (∑ j ∈ t, b j * n j) =
      ∑ i ∈ s, ∑ j ∈ t, (a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j) := by
    rw [hI, Finset.sum_mul_sum]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hrewrite]
  calc
    ‖∑ i ∈ s, ∑ j ∈ t,
        (a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t,
        ‖(a i * b j) * ((∫ ω, u i ω * v j ω ∂μ) - m i * n j)‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => norm_sum_le _ _)
    _ ≤ ∑ i ∈ s, ∑ j ∈ t, ‖a i‖ * ‖b j‖ * ε := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul]
      exact mul_le_mul_of_nonneg_left (hdisc i hi j hj)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ε * (∑ i ∈ s, ‖a i‖) * (∑ j ∈ t, ‖b j‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

lemma integral_step (f : ℝ → ℂ) (N : ℕ) :
    ∫ x, step f N x ∂unitMeasure =
      ∑ k ∈ Finset.range (N + 1), coefficient f N k * (∫ x, tail ((k : ℝ) / N) x ∂unitMeasure) := by
  unfold step
  rw [integral_finsetSum]
  · simp only [integral_const_mul]
  · intro k hk
    exact (integrable_tail unitMeasure measurable_id _).const_mul _

theorem step_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) {N : ℕ} (hN : 0 < N) :
    ‖(∫ ω, step f N (X ω) * step g N (Y ω) ∂μ) -
      (∫ x, step f N x ∂unitMeasure) * (∫ y, step g N y ∂unitMeasure)‖ ≤
      ε * (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hgrid (k : ℕ) (hk : k ∈ Finset.range (N + 1)) :
      (k : ℝ) / N ∈ Icc (0 : ℝ) 1 := by
    have hNp : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    exact ⟨div_nonneg (Nat.cast_nonneg _) hNp.le,
      (div_le_one hNp).mpr (Nat.cast_le.mpr (Nat.le_of_lt_succ (Finset.mem_range.mp hk)))⟩
  have h := finite_test_discrepancy μ (Finset.range (N + 1)) (Finset.range (N + 1))
    (coefficient f N) (coefficient g N)
    (fun i ω => tail ((i : ℝ) / N) (X ω))
    (fun j ω => tail ((j : ℝ) / N) (Y ω))
    (fun i => ∫ x, tail ((i : ℝ) / N) x ∂unitMeasure)
    (fun j => ∫ y, tail ((j : ℝ) / N) y ∂unitMeasure) ε
    (fun i _ j _ => integrable_tail_mul μ hX hY _ _)
    (fun i hi j hj => by
      rw [integral_tail (hgrid i hi), integral_tail (hgrid j hj)]
      exact hrect _ (hgrid i hi) _ (hgrid j hj))
  rw [← integral_step f N, ← integral_step g N] at h
  change ‖(∫ ω, step f N (X ω) * step g N (Y ω) ∂μ) -
    (∫ x, step f N x ∂unitMeasure) * (∫ y, step g N y ∂unitMeasure)‖ ≤ _ at h
  apply h.trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (sum_norm_coefficient_le f hN hf) hε
  · exact sum_norm_coefficient_le g hN hg
  · exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  · positivity

lemma tendsto_integral_step (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    Tendsto (fun n : ℕ => ∫ x, step f (n + 1) x ∂unitMeasure) atTop
      (𝓝 (∫ x, f x ∂unitMeasure)) := by
  apply tendsto_integral_of_dominated_convergence
    (fun _ => ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal)
  · intro n
    exact (measurable_step f (n + 1)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (norm_step_le f (Nat.succ_pos n) hf)
  · exact ae_tendsto_step f hf

theorem boundedVariation_discrepancy_endpoint {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (haX : μ.map X ≪ unitMeasure) (haY : μ.map Y ≪ unitMeasure)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ ω, f (X ω) * g (Y ω) ∂μ) -
      (∫ x, f x ∂unitMeasure) * (∫ y, g y ∂unitMeasure)‖ ≤
      ε * (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hprod : Tendsto (fun n : ℕ =>
      ∫ ω, step f (n + 1) (X ω) * step g (n + 1) (Y ω) ∂μ) atTop
      (𝓝 (∫ ω, f (X ω) * g (Y ω) ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun _ => (‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (‖g 0‖ + (eVariationOn g (Icc (0 : ℝ) 1)).toReal))
    · intro n
      exact (((measurable_step f (n + 1)).comp hX).mul
        ((measurable_step g (n + 1)).comp hY)).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      apply Filter.Eventually.of_forall
      intro ω
      rw [norm_mul]
      exact mul_le_mul (norm_step_le f (Nat.succ_pos n) hf _)
        (norm_step_le g (Nat.succ_pos n) hg _) (norm_nonneg _) (by positivity)
    · filter_upwards [ae_tendsto_step_comp hX haX f hf,
        ae_tendsto_step_comp hY haY g hg] with ω hfx hgy
      exact hfx.mul hgy
  have hlim := (hprod.sub ((tendsto_integral_step f hf).mul
    (tendsto_integral_step g hg))).norm
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    step_discrepancy μ hX hY hε hrect f g hf hg (Nat.succ_pos n)

lemma norm_bddAbove_of_boundedVariation (f : ℝ → ℂ)
    (hf : BoundedVariationOn f (Icc (0 : ℝ) 1)) :
    BddAbove ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) := by
  refine ⟨‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  have hv := hf.dist_le hx (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
  calc
    ‖f x‖ = ‖(f x - f 0) + f 0‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x - f 0‖ + ‖f 0‖ := norm_add_le _ _
    _ ≤ ‖f 0‖ + (eVariationOn f (Icc (0 : ℝ) 1)).toReal := by
      rw [dist_eq_norm] at hv
      linarith

theorem boundedVariation_discrepancy {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (haX : μ.map X ≪ unitMeasure) (haY : μ.map Y ≪ unitMeasure)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hrect : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ‖(∫ ω, tail a (X ω) * tail b (Y ω) ∂μ) -
        ((1 - a : ℝ) : ℂ) * ((1 - b : ℝ) : ℂ)‖ ≤ ε)
    (f g : ℝ → ℂ) (hf : BoundedVariationOn f (Icc (0 : ℝ) 1))
    (hg : BoundedVariationOn g (Icc (0 : ℝ) 1)) :
    ‖(∫ ω, f (X ω) * g (Y ω) ∂μ) -
      (∫ x, f x ∂unitMeasure) * (∫ y, g y ∂unitMeasure)‖ ≤
      ε * (sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) +
        (eVariationOn f (Icc (0 : ℝ) 1)).toReal) *
        (sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) +
        (eVariationOn g (Icc (0 : ℝ) 1)).toReal) := by
  have hfs : ‖f 0‖ ≤ sSup ((fun x => ‖f x‖) '' Icc (0 : ℝ) 1) :=
    le_csSup (norm_bddAbove_of_boundedVariation f hf) ⟨0, by norm_num, rfl⟩
  have hgs : ‖g 0‖ ≤ sSup ((fun x => ‖g x‖) '' Icc (0 : ℝ) 1) :=
    le_csSup (norm_bddAbove_of_boundedVariation g hg) ⟨0, by norm_num, rfl⟩
  apply (boundedVariation_discrepancy_endpoint μ hX hY haX haY hε hrect f g hf hg).trans
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left (add_le_add hfs le_rfl) hε
  · exact add_le_add hgs le_rfl
  · positivity
  · exact mul_nonneg hε (add_nonneg ((norm_nonneg _).trans hfs) ENNReal.toReal_nonneg)

end Invariant233.BVDiscrepancy

end

end OAI
