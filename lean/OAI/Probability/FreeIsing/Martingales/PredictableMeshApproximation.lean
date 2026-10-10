import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal Topology

namespace Problem367.PredictableMesh

def point (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / (n + 1 : ℕ)

def left (n : ℕ) (t : ℝ≥0) : ℝ≥0 :=
  point n (⌈(n + 1 : ℕ) * t⌉₊ - 1)

@[simp] theorem point_zero (n : ℕ) : point n 0 = 0 := by simp [point]

@[simp] theorem left_zero (n : ℕ) : left n 0 = 0 := by simp [left]

theorem point_strictMono (n : ℕ) : StrictMono (point n) := by
  intro i j hij
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (by positivity)

theorem left_eq_of_mem_Ioc {n k : ℕ} {t : ℝ≥0}
    (ht : t ∈ Ioc (point n k) (point n (k + 1))) :
    left n t = point n k := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : ⌈(n + 1 : ℕ) * t⌉₊ = k + 1 := by
    apply (Nat.ceil_eq_iff (Nat.succ_ne_zero k)).2
    constructor
    · have := (div_lt_iff₀ hN).1 ht.1
      simpa only [mul_comm, Nat.succ_sub_one] using this
    · have := (le_div_iff₀ hN).1 ht.2
      simpa only [mul_comm, Nat.succ_sub_one] using this
  change point n (⌈(n + 1 : ℕ) * t⌉₊ - 1) = point n k
  rw [hc, Nat.add_sub_cancel]

theorem mem_mesh_Ioc {n : ℕ} {t : ℝ≥0} (ht : 0 < t) :
    t ∈ Ioc (left n t)
      (point n (⌈(n + 1 : ℕ) * t⌉₊ - 1 + 1)) := by
  have hN : (0 : ℝ≥0) < (n + 1 : ℕ) := by positivity
  have hc : 1 ≤ ⌈(n + 1 : ℕ) * t⌉₊ :=
    Nat.one_le_ceil_iff.mpr (mul_pos hN ht)
  have hh := (Nat.ceil_eq_iff (show ⌈(n + 1 : ℕ) * t⌉₊ ≠ 0 by omega)).mp rfl
  constructor
  · apply (div_lt_iff₀ hN).2
    simpa only [mul_comm] using hh.1
  · dsimp [point]
    rw [Nat.sub_add_cancel hc]
    apply (le_div_iff₀ hN).2
    simpa only [mul_comm] using hh.2

theorem left_le (n : ℕ) (t : ℝ≥0) : left n t ≤ t := by
  by_cases ht : t = 0
  · simp [ht]
  · exact (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).1.le

theorem le_left_add_width (n : ℕ) (t : ℝ≥0) :
    t ≤ left n t + 1 / (n + 1 : ℕ) := by
  by_cases ht : t = 0
  · simp [ht]
  · have h := (mem_mesh_Ioc (n := n) (pos_iff_ne_zero.mpr ht)).2
    simpa only [point, left, Nat.cast_add, Nat.cast_one, add_div] using h

theorem tendsto_left (t : ℝ≥0) : Tendsto (fun n => left n t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _)
    (fun n => show ‖(left n t : ℝ) - (t : ℝ)‖ ≤ 1 / ((n : ℝ) + 1) from ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : (left n t : ℝ) ≤ (t : ℝ) := left_le n t
  have hu := le_left_add_width n t
  have hu' : (t : ℝ) ≤ (left n t : ℝ) + 1 / ((n : ℝ) + 1) := by
    exact_mod_cast hu
  rw [Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

theorem measurable_left (n : ℕ) : Measurable (left n) := by
  exact (measurable_of_countable (fun k : ℕ => point n (k - 1))).comp
    ((measurable_const.mul measurable_id).nat_ceil)

def sample {Ω : Type*} (u : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  u (left n t) ω

theorem sample_tendsto {Ω : Type*} {u : ℝ≥0 → Ω → ℝ}
    (hu : ∀ ω, Continuous (fun t => u t ω)) (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun n => sample u n t ω) atTop (𝓝 (u t ω)) :=
  (hu ω).continuousAt.tendsto.comp (tendsto_left t)

theorem sample_stronglyAdapted {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (n : ℕ) : StronglyAdapted F (sample u n) :=
  fun t => (hu (left n t)).mono (F.mono (left_le n t))

theorem sample_isStronglyPredictable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (n : ℕ) : IsStronglyPredictable F (sample u n) := by
  apply Measurable.stronglyMeasurable
  intro s hs
  have heq : (Function.uncurry (sample u n)) ⁻¹' s =
      ({0} ×ˢ (u 0 ⁻¹' s)) ∪
        ⋃ k : ℕ, (Ioc (point n k) (point n (k + 1))) ×ˢ (u (point n k) ⁻¹' s) := by
    ext ⟨t, ω⟩
    simp only [mem_preimage, Function.uncurry_apply_pair, mem_union, mem_prod,
      mem_singleton_iff, mem_iUnion]
    constructor
    · intro h
      by_cases ht : t = 0
      · exact Or.inl ⟨ht, by simpa [ht, sample] using h⟩
      · exact Or.inr ⟨⌈(n + 1 : ℕ) * t⌉₊ - 1,
          mem_mesh_Ioc (pos_iff_ne_zero.mpr ht), h⟩
    · rintro (⟨ht, h⟩ | ⟨k, ht, h⟩)
      · simpa [ht, sample] using h
      · simpa only [sample, left_eq_of_mem_Ioc ht] using h
  rw [heq]
  apply MeasurableSet.union
  · exact measurableSet_predictable_singleton_bot_prod ((hu 0).measurable hs)
  · exact MeasurableSet.iUnion fun k =>
      measurableSet_predictable_Ioc_prod _ _ ((hu (point n k)).measurable hs)

theorem isStronglyPredictable_of_continuous {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω)) :
    IsStronglyPredictable F u := by
  apply stronglyMeasurable_of_tendsto atTop (f := fun n => Function.uncurry (sample u n))
    (fun n => sample_isStronglyPredictable hu n)
  exact tendsto_pi_nhds.mpr fun p => sample_tendsto hc p.1 p.2

theorem stronglyMeasurable_uncurry {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω)) :
    StronglyMeasurable (Function.uncurry u) :=
  stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable hc
    (fun t => (hu t).mono (F.le t))

theorem stronglyMeasurable_sample {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω)) (n : ℕ) :
    StronglyMeasurable (Function.uncurry (sample u n)) :=
  (stronglyMeasurable_uncurry hu hc).comp_measurable
    (((measurable_left n).comp measurable_fst).prodMk measurable_snd)

theorem memLp_uncurry {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω))
    (ν : Measure ℝ≥0) (P : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure P]
    (C : ℝ) (hb : ∀ t ω, |u t ω| ≤ C) :
    MemLp (Function.uncurry u) 2 (ν.prod P) :=
  MemLp.of_bound (stronglyMeasurable_uncurry hu hc).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs, Function.uncurry] using hb p.1 p.2)

theorem memLp_sample {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω))
    (ν : Measure ℝ≥0) (P : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure P]
    (C : ℝ) (hb : ∀ t ω, |u t ω| ≤ C) (n : ℕ) :
    MemLp (Function.uncurry (sample u n)) 2 (ν.prod P) :=
  MemLp.of_bound (stronglyMeasurable_sample hu hc n).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs, Function.uncurry, sample] using hb (left n p.1) p.2)

theorem tendsto_integral_sq_sample_sub
    {A Ω : Type*} [MeasurableSpace A] [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω))
    (ν : Measure A) (P : Measure Ω) [IsFiniteMeasure ν] [IsFiniteMeasure P]
    (τ : A → ℝ≥0) (hτ : Measurable τ)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t ω, |u t ω| ≤ C) :
    Tendsto (fun n => ∫ p : A × Ω,
      (sample u n (τ p.1) p.2 - u (τ p.1) p.2) ^ 2 ∂ν.prod P) atTop (𝓝 0) := by
  have hcoord : Measurable (fun p : A × Ω => (τ p.1, p.2)) :=
    (hτ.comp measurable_fst).prodMk measurable_snd
  have huM := (stronglyMeasurable_uncurry hu hc).comp_measurable hcoord
  have hsM (n : ℕ) := (stronglyMeasurable_sample hu hc n).comp_measurable hcoord
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := ν.prod P) (F := fun n p =>
      (sample u n (τ p.1) p.2 - u (τ p.1) p.2) ^ 2)
    (f := fun _ => (0 : ℝ)) (fun _ => (2 * C) ^ 2)
    (fun n => ((hsM n).sub huM).pow 2 |>.aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hlim
  · intro n
    exact Filter.Eventually.of_forall fun p => by
      have hn : |sample u n (τ p.1) p.2 - u (τ p.1) p.2| ≤ 2 * C := by
        calc
          _ ≤ |sample u n (τ p.1) p.2| + |u (τ p.1) p.2| := abs_sub _ _
          _ ≤ 2 * C := by
            dsimp [sample]
            linarith [hb (left n (τ p.1)) p.2, hb (τ p.1) p.2]
      simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by norm_num) hC)).mpr hn
  · exact Filter.Eventually.of_forall fun p => by
      simpa only [sub_self, zero_pow (by decide : 2 ≠ 0)] using
        ((sample_tendsto hc (τ p.1) p.2).sub
          (tendsto_const_nhds (x := u (τ p.1) p.2))).pow 2

theorem tendsto_time_integral_sq_sample_sub
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {F : Filtration ℝ≥0 mΩ} {u : ℝ≥0 → Ω → ℝ}
    (hu : StronglyAdapted F u) (hc : ∀ ω, Continuous (fun t => u t ω))
    (P : Measure Ω) [IsFiniteMeasure P] (T C : ℝ)
    (hC : 0 ≤ C) (hb : ∀ t ω, |u t ω| ≤ C) :
    Tendsto (fun n => ∫ p : ℝ × Ω,
      (sample u n p.1.toNNReal p.2 - u p.1.toNNReal p.2) ^ 2
        ∂(volume.restrict (Icc 0 T)).prod P) atTop (𝓝 0) :=
  tendsto_integral_sq_sample_sub hu hc (volume.restrict (Icc 0 T)) P
    Real.toNNReal (by fun_prop) C hC hb

end Problem367.PredictableMesh

end

end OAI
