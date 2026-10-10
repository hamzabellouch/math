import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Problem367.ContinuousCoefficientModulus

def pairModulus (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  ↑((Finset.range n).sup (fun i => ‖x i - y i‖₊))

theorem pairModulus_nonneg (x y : ℕ → ℝ) (n : ℕ) :
    0 ≤ pairModulus x y n := NNReal.coe_nonneg _

theorem abs_sub_le_pairModulus (x y : ℕ → ℝ) {i n : ℕ} (hi : i < n) :
    |x i - y i| ≤ pairModulus x y n := by
  have h := Finset.le_sup (f := fun j => ‖x j - y j‖₊) (Finset.mem_range.mpr hi)
  exact_mod_cast h

theorem pairModulus_le (x y : ℕ → ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i < n, |x i - y i| ≤ C) : pairModulus x y n ≤ C := by
  have h : (Finset.range n).sup (fun i => ‖x i - y i‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast hb i (Finset.mem_range.mp hi)
  exact_mod_cast h

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem stronglyMeasurable_pairModulus (x y : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (hy : ∀ i, StronglyMeasurable (y i)) (n : ℕ) :
    StronglyMeasurable (fun ω => pairModulus (fun i => x i ω) (fun i => y i ω) n) := by
  induction n with
  | zero => simpa [pairModulus] using (stronglyMeasurable_const :
      StronglyMeasurable (fun _ : Ω => (0 : ℝ)))
  | succ n ih =>
    have h := ((((hx n).measurable.sub (hy n).measurable).norm).max
      ih.measurable).stronglyMeasurable
    simpa only [pairModulus, Finset.range_add_one, Finset.sup_insert,
      NNReal.coe_max, coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply] using h

theorem memLp_pairModulus [IsFiniteMeasure μ] (x y : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (hy : ∀ i, StronglyMeasurable (y i))
    (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, i < n → ∀ᵐ ω ∂μ, |x i ω - y i ω| ≤ C) (p : ℝ≥0∞) :
    MemLp (fun ω => pairModulus (fun i => x i ω) (fun i => y i ω) n) p μ := by
  apply MemLp.of_bound (stronglyMeasurable_pairModulus x y hx hy n).aestronglyMeasurable C
  have hb' : ∀ i, ∀ᵐ ω ∂μ, i < n → |x i ω - y i ω| ≤ C := by
    intro i
    by_cases hi : i < n
    · exact (hb i hi).mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
  filter_upwards [ae_all_iff.2 hb'] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pairModulus_nonneg _ _ _)]
  exact pairModulus_le _ _ _ hC hω

theorem tendsto_pairModulus_of_uniformContinuousOn
    {I : Type*} [PseudoMetricSpace I] {S : Set I} {H : I → ℝ}
    (hH : UniformContinuousOn H S) (s t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hs : ∀ n i, i < N n → s n i ∈ S) (ht : ∀ n i, i < N n → t n i ∈ S)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (s n i) (t n i) ≤ δ n) :
    Tendsto (fun n => pairModulus (fun i => H (s n i)) (fun i => H (t n i)) (N n))
      atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hlocal⟩ := Metric.uniformContinuousOn_iff.mp hH (ε / 2) (by positivity)
  obtain ⟨n₀, hn₀⟩ := (hδ.eventually (gt_mem_nhds hη)).exists_forall_of_atTop
  refine ⟨n₀, fun n hn => ?_⟩
  have hb : pairModulus (fun i => H (s n i)) (fun i => H (t n i)) (N n) ≤ ε / 2 := by
    apply pairModulus_le _ _ _ (by positivity)
    intro i hi
    have hh := hlocal (s n i) (hs n i hi) (t n i) (ht n i hi)
      ((hdist n i hi).trans_lt (hn₀ n hn))
    simpa only [Real.dist_eq] using hh.le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pairModulus_nonneg _ _ _)]
  linarith

theorem tendsto_integral_pairModulus_pow [IsFiniteMeasure μ]
    {I : Type*} [PseudoMetricSpace I] {S : Set I} (hS : IsCompact S)
    {H : I → Ω → ℝ} (hm : ∀ t, StronglyMeasurable (H t))
    (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => H t ω) S)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t ∈ S, ∀ᵐ ω ∂μ, |H t ω| ≤ C)
    (s t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hs : ∀ n i, i < N n → s n i ∈ S) (ht : ∀ n i, i < N n → t n i ∈ S)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0))
    (hdist : ∀ n i, i < N n → dist (s n i) (t n i) ≤ δ n)
    (p : ℕ) (hp : 0 < p) :
    Tendsto (fun n => ∫ ω,
      (pairModulus (fun i => H (s n i) ω) (fun i => H (t n i) ω) (N n)) ^ p ∂μ)
      atTop (𝓝 0) := by
  let R : ℕ → Ω → ℝ := fun n ω =>
    pairModulus (fun i => H (s n i) ω) (fun i => H (t n i) ω) (N n)
  have hRm (n : ℕ) : StronglyMeasurable (R n) :=
    stronglyMeasurable_pairModulus _ _ (fun i => hm (s n i)) (fun i => hm (t n i)) (N n)
  have hRb (n : ℕ) : ∀ᵐ ω ∂μ, |R n ω| ≤ 2 * C := by
    have hb' : ∀ i, ∀ᵐ ω ∂μ, i < N n → |H (s n i) ω - H (t n i) ω| ≤ 2 * C := by
      intro i
      by_cases hi : i < N n
      · filter_upwards [hb _ (hs n i hi), hb _ (ht n i hi)] with ω hsω htω
        intro _
        exact (abs_sub _ _).trans (by linarith)
      · exact Filter.Eventually.of_forall (fun _ h => (hi h).elim)
    filter_upwards [ae_all_iff.2 hb'] with ω hω
    rw [abs_of_nonneg (pairModulus_nonneg _ _ _)]
    exact pairModulus_le _ _ _ (by positivity) hω
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => R n ω) atTop (𝓝 0) := by
    filter_upwards [hc] with ω hω
    exact tendsto_pairModulus_of_uniformContinuousOn
      (hS.uniformContinuousOn_of_continuous hω) s t N hs ht δ hδ hdist
  have hh := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun n ω => R n ω ^ p) (f := fun _ => (0 : ℝ))
    (fun _ => (2 * C) ^ p) (fun n => (hRm n).aestronglyMeasurable.pow p)
    (integrable_const _) ?_ ?_
  · simpa only [integral_zero] using hh
  · intro n
    filter_upwards [hRb n] with ω hω
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hω p
  · filter_upwards [hlim] with ω hω
    simpa only [zero_pow (Nat.ne_of_gt hp)] using hω.pow p

end Problem367.ContinuousCoefficientModulus

end

end OAI
