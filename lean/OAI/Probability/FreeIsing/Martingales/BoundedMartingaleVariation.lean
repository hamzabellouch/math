import OAI.Probability.FreeIsing.Martingales.TaylorRemainder
import OAI.Probability.FreeIsing.Martingales.TransformL2

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology NNReal

namespace Problem367.BoundedMartingaleVariation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem bounded_pow_memLp_two [IsFiniteMeasure μ]
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ C) (p : ℕ) :
    MemLp (fun ω => f ω ^ p) 2 μ := by
  apply MemLp.of_bound (hf.pow p) (C ^ p)
  filter_upwards [hb] with ω hω
  simp only [Pi.pow_apply, norm_pow, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hω p

theorem sum_sq_increment (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2) =
      x n ^ 2 - x 0 ^ 2 - 2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    ring

theorem sq_sum_sq_increment_le (x : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, (x (i + 1) - x i) ^ 2) ^ 2 ≤
      4 * x n ^ 4 + 4 * x 0 ^ 4 +
        8 * (∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 := by
  rw [sum_sq_increment]
  have h1 : (x n ^ 2 - x 0 ^ 2) ^ 2 ≤ 2 * (x n ^ 2) ^ 2 + 2 * (x 0 ^ 2) ^ 2 := by
    nlinarith [sq_nonneg (x n ^ 2 + x 0 ^ 2)]
  have h2 : (x n ^ 2 - x 0 ^ 2 -
      2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 ≤
      2 * (x n ^ 2 - x 0 ^ 2) ^ 2 +
        8 * (∑ i ∈ Finset.range n, x i * (x (i + 1) - x i)) ^ 2 := by
    nlinarith [sq_nonneg (x n ^ 2 - x 0 ^ 2 +
      2 * ∑ i ∈ Finset.range n, x i * (x (i + 1) - x i))]
  nlinarith

theorem integral_sq_quadratic_variation_le [IsProbabilityMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ∀ᵐ ω ∂μ, |M i ω| ≤ C) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, (M (i + 1) ω - M i ω) ^ 2) ^ 2 ∂μ) ≤
      16 * C ^ 4 := by
  have hm (i : ℕ) : AEStronglyMeasurable (M i) μ :=
    ((hM.stronglyMeasurable i).mono (F.le i)).aestronglyMeasurable
  have hM2 (i : ℕ) : MemLp (M i) 2 μ := by
    simpa using bounded_pow_memLp_two (hm i) hC (hb i) 1
  have hD (i : ℕ) : ∀ᵐ ω ∂μ, |M (i + 1) ω - M i ω| ≤ 2 * C := by
    filter_upwards [hb (i + 1), hb i] with ω hnext hnow
    calc
      |M (i + 1) ω - M i ω| ≤ |M (i + 1) ω| + |M i ω| := abs_sub _ _
      _ ≤ 2 * C := by linarith
  have hQ2 : MemLp (fun ω => ∑ i ∈ Finset.range n,
      (M (i + 1) ω - M i ω) ^ 2) 2 μ := by
    exact memLp_finsetSum _ (fun i hi =>
      bounded_pow_memLp_two ((hm (i + 1)).sub (hm i)) (by positivity) (hD i) 2)
  have hS2 : MemLp (fun ω => ∑ i ∈ Finset.range n,
      M i ω * (M (i + 1) ω - M i ω)) 2 μ := by
    exact memLp_finsetSum _ (fun i hi =>
      MartingaleTransformL2.bounded_mul_memLp_two (hm i)
        ((hM2 (i + 1)).sub (hM2 i)) (hb i))
  have hpowInt (i : ℕ) : Integrable (fun ω => M i ω ^ 4) μ :=
    (bounded_pow_memLp_two (hm i) hC (hb i) 4).integrable (by norm_num)
  have hpowbound (i p : ℕ) (hp : Even p) : (∫ ω, M i ω ^ p ∂μ) ≤ C ^ p := by
    calc
      _ ≤ ∫ _ : Ω, C ^ p ∂μ := by
        apply integral_mono_ae
          ((bounded_pow_memLp_two (hm i) hC (hb i) p).integrable (by norm_num))
          (integrable_const _)
        filter_upwards [hb i] with ω hω
        simpa only [hp.pow_abs] using pow_le_pow_left₀ (abs_nonneg _) hω p
      _ = _ := by simp
  have hSbound : (∫ ω, (∑ i ∈ Finset.range n,
      M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤ C ^ 4 := by
    have h := MartingaleTransformL2.integral_sq_grid_transform_le_terminal
      hM hM2 (fun i : ℕ => i) monotone_id M hM.stronglyAdapted hC hb n
    exact h.trans (by
      calc
        C ^ 2 * (∫ ω, M n ω ^ 2 ∂μ) ≤ C ^ 2 * C ^ 2 :=
          mul_le_mul_of_nonneg_left (hpowbound n 2 (by decide)) (sq_nonneg C)
        _ = C ^ 4 := by ring)
  have hmajor : (∫ ω, (∑ i ∈ Finset.range n,
      (M (i + 1) ω - M i ω) ^ 2) ^ 2 ∂μ) ≤
      4 * (∫ ω, M n ω ^ 4 ∂μ) + 4 * (∫ ω, M 0 ω ^ 4 ∂μ) +
        8 * (∫ ω, (∑ i ∈ Finset.range n,
          M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ ω, 4 * M n ω ^ 4 + 4 * M 0 ω ^ 4 +
          8 * (∑ i ∈ Finset.range n, M i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ := by
        apply integral_mono_ae hQ2.integrable_sq
          (((hpowInt n).const_mul 4).add ((hpowInt 0).const_mul 4) |>.add
            (hS2.integrable_sq.const_mul 8))
        exact Filter.Eventually.of_forall (fun ω => sq_sum_sq_increment_le (fun i => M i ω) n)
      _ = _ := by
        have h1 := integral_add ((hpowInt n).const_mul 4) ((hpowInt 0).const_mul 4)
        have h2 := integral_add
          (((hpowInt n).const_mul 4).add ((hpowInt 0).const_mul 4))
          (hS2.integrable_sq.const_mul 8)
        simp only [Pi.add_apply] at h1 h2
        rw [h1] at h2
        simpa only [integral_const_mul] using h2
  nlinarith [hpowbound n 4 (by decide), hpowbound 0 4 (by decide)]

def incrementModulus (x : ℕ → ℝ) (n : ℕ) : ℝ :=
  ↑((Finset.range n).sup (fun i => ‖x (i + 1) - x i‖₊))

theorem incrementModulus_nonneg (x : ℕ → ℝ) (n : ℕ) :
    0 ≤ incrementModulus x n := NNReal.coe_nonneg _

theorem abs_increment_le_modulus (x : ℕ → ℝ) {i n : ℕ} (hi : i < n) :
    |x (i + 1) - x i| ≤ incrementModulus x n := by
  have h := Finset.le_sup (f := fun j => ‖x (j + 1) - x j‖₊) (Finset.mem_range.mpr hi)
  exact_mod_cast h

theorem incrementModulus_le (x : ℕ → ℝ) (n : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i < n, |x (i + 1) - x i| ≤ C) : incrementModulus x n ≤ C := by
  have h : (Finset.range n).sup (fun i => ‖x (i + 1) - x i‖₊) ≤ (⟨C, hC⟩ : ℝ≥0) := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast hb i (Finset.mem_range.mp hi)
  exact_mod_cast h

theorem stronglyMeasurable_incrementModulus (x : ℕ → Ω → ℝ)
    (hx : ∀ i, StronglyMeasurable (x i)) (n : ℕ) :
    StronglyMeasurable (fun ω => incrementModulus (fun i => x i ω) n) := by
  induction n with
  | zero => simpa [incrementModulus] using (stronglyMeasurable_const :
      StronglyMeasurable (fun _ : Ω => (0 : ℝ)))
  | succ n ih =>
    have h := ((((hx (n + 1)).measurable.sub (hx n).measurable).norm).max
      ih.measurable).stronglyMeasurable
    simpa only [incrementModulus, Finset.range_add_one, Finset.sup_insert,
      NNReal.coe_max, coe_nnnorm, Real.norm_eq_abs, Pi.sub_apply] using h

theorem tendsto_incrementModulus_of_uniformContinuousOn
    {I : Type*} [PseudoMetricSpace I] {S : Set I} {x : I → ℝ}
    (hx : UniformContinuousOn x S) (t : ℕ → ℕ → I) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => incrementModulus (fun i => x (t k i)) (N k)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨η, hη, hlocal⟩ := Metric.uniformContinuousOn_iff.mp hx (ε / 2) (by positivity)
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.mp hδ η hη
  refine ⟨K, fun k hk => ?_⟩
  have hδk : δ k < η := by
    have hdk := hK k hk
    rw [Real.dist_eq, sub_zero] at hdk
    exact lt_of_le_of_lt (le_abs_self _) hdk
  have hmod : incrementModulus (fun i => x (t k i)) (N k) ≤ ε / 2 := by
    apply incrementModulus_le _ _ (by positivity)
    intro i hi
    have hdist := hlocal (t k (i + 1)) (hmem k _ hi) (t k i) (hmem k _ hi.le)
      (lt_of_le_of_lt (hmesh k i hi) hδk)
    exact le_of_lt (by simpa only [Real.dist_eq] using hdist)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (incrementModulus_nonneg _ _)]
  linarith

theorem mul_le_young (a b : ℝ) {ε : ℝ} (hε : 0 < ε) :
    a * b ≤ ε * b ^ 2 + a ^ 2 / (4 * ε) := by
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hid : (4 * ε) * (ε * b ^ 2 + a ^ 2 / (4 * ε) - a * b) =
      (2 * ε * b - a) ^ 2 := by
    field_simp
    ring
  have hnon : 0 ≤ ε * b ^ 2 + a ^ 2 / (4 * ε) - a * b := by
    apply (mul_nonneg_iff_of_pos_left (by positivity : 0 < 4 * ε)).1
    rw [hid]
    exact sq_nonneg _
  linarith

theorem tendsto_integral_sum_fourth_of_modulus [IsProbabilityMeasure μ]
    (F : ℕ → Filtration ℕ mΩ) (M : ℕ → ℕ → Ω → ℝ)
    (hM : ∀ k, Martingale (M k) (F k) μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ k i, ∀ᵐ ω ∂μ, |M k i ω| ≤ C) (N : ℕ → ℕ)
    (hmod : ∀ᵐ ω ∂μ, Tendsto
      (fun k => incrementModulus (fun i => M k i ω) (N k)) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, ∑ i ∈ Finset.range (N k),
      (M k (i + 1) ω - M k i ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  let D : ℕ → ℕ → Ω → ℝ := fun k i ω => M k (i + 1) ω - M k i ω
  let R : ℕ → Ω → ℝ := fun k ω => incrementModulus (fun i => M k i ω) (N k)
  let Q : ℕ → Ω → ℝ := fun k ω => ∑ i ∈ Finset.range (N k), D k i ω ^ 2
  have hm (k i : ℕ) : StronglyMeasurable (M k i) :=
    ((hM k).stronglyMeasurable i).mono ((F k).le i)
  have hDm (k i : ℕ) : AEStronglyMeasurable (D k i) μ :=
    ((hm k (i + 1)).sub (hm k i)).aestronglyMeasurable
  have hDb (k i : ℕ) : ∀ᵐ ω ∂μ, |D k i ω| ≤ 2 * C := by
    filter_upwards [hb k (i + 1), hb k i] with ω hn hi
    exact (abs_sub _ _).trans (by linarith)
  have hDp (k i p : ℕ) : MemLp (fun ω => D k i ω ^ p) 2 μ :=
    bounded_pow_memLp_two (hDm k i) (by positivity) (hDb k i) p
  have hRm (k : ℕ) : StronglyMeasurable (R k) :=
    stronglyMeasurable_incrementModulus (M k) (hm k) (N k)
  have hRb (k : ℕ) : ∀ᵐ ω ∂μ, |R k ω| ≤ 2 * C := by
    filter_upwards [ae_all_iff.2 (hDb k)] with ω hω
    rw [abs_of_nonneg (incrementModulus_nonneg _ _)]
    exact incrementModulus_le _ _ (by positivity) (fun i hi => hω i)
  have hRp (k p : ℕ) : MemLp (fun ω => R k ω ^ p) 2 μ :=
    bounded_pow_memLp_two (hRm k).aestronglyMeasurable (by positivity) (hRb k) p
  have hQ2 (k : ℕ) : MemLp (Q k) 2 μ :=
    memLp_finsetSum _ (fun i hi => hDp k i 2)
  have hQbound (k : ℕ) : (∫ ω, Q k ω ^ 2 ∂μ) ≤ 16 * C ^ 4 :=
    integral_sq_quadratic_variation_le (hM k) hC (hb k) (N k)
  have hRlim : Tendsto (fun k => ∫ ω, R k ω ^ 4 ∂μ) atTop (𝓝 0) := by
    have hdom (k : ℕ) : ∀ᵐ ω ∂μ, ‖R k ω ^ 4‖ ≤ (2 * C) ^ 4 := by
      filter_upwards [hRb k] with ω hω
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hω 4
    have h := tendsto_integral_of_dominated_convergence (μ := μ)
      (fun _ : Ω => (2 * C) ^ 4) (fun k => (hRm k).aestronglyMeasurable.pow 4)
      (integrable_const _) hdom
      (hmod.mono (fun ω hω => by simpa using hω.pow 4))
    simpa using h
  apply MartingaleTaylorRemainder.tendsto_zero_of_young_bound
    (C := fun k => ∫ ω, R k ω ^ 4 ∂μ) (B := 16 * C ^ 4) (by positivity)
  · intro k
    exact integral_nonneg (fun ω => Finset.sum_nonneg (fun i hi => by positivity))
  · intro ε hε k
    have hfourInt : Integrable (fun ω => ∑ i ∈ Finset.range (N k), D k i ω ^ 4) μ :=
      integrable_finsetSum _ (fun i hi => (hDp k i 4).integrable (by norm_num))
    have hpoint (ω : Ω) : (∑ i ∈ Finset.range (N k), D k i ω ^ 4) ≤
        ε * Q k ω ^ 2 + R k ω ^ 4 / (4 * ε) := by
      have hsum : (∑ i ∈ Finset.range (N k), D k i ω ^ 4) ≤ R k ω ^ 2 * Q k ω := by
        dsimp only [Q]
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i hi
        have habs : |D k i ω| ≤ R k ω :=
          abs_increment_le_modulus (fun i => M k i ω) (Finset.mem_range.mp hi)
        have hsq : D k i ω ^ 2 ≤ R k ω ^ 2 := by
          simpa only [sq_abs] using
            (sq_le_sq₀ (abs_nonneg _) (incrementModulus_nonneg _ _)).2 habs
        nlinarith [mul_le_mul_of_nonneg_right hsq (sq_nonneg (D k i ω))]
      exact hsum.trans (by
        have hh := mul_le_young (R k ω ^ 2) (Q k ω) hε
        have heq : (R k ω ^ 2) ^ 2 = R k ω ^ 4 := by ring
        rw [heq] at hh
        exact hh)
    calc
      _ ≤ ∫ ω, ε * Q k ω ^ 2 + R k ω ^ 4 / (4 * ε) ∂μ :=
        integral_mono hfourInt
          (((hQ2 k).integrable_sq.const_mul ε).add
            (((hRp k 4).integrable (by norm_num)).div_const (4 * ε))) hpoint
      _ = ε * (∫ ω, Q k ω ^ 2 ∂μ) + (∫ ω, R k ω ^ 4 ∂μ) / (4 * ε) := by
        rw [integral_add ((hQ2 k).integrable_sq.const_mul ε)
          (((hRp k 4).integrable (by norm_num)).div_const (4 * ε)),
          integral_const_mul, integral_div]
      _ ≤ ε * (16 * C ^ 4) + (∫ ω, R k ω ^ 4 ∂μ) / (4 * ε) :=
        add_le_add (mul_le_mul_of_nonneg_left (hQbound k) hε.le) le_rfl
  · exact hRlim

theorem tendsto_integral_sum_fourth_of_continuous [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M : I → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => ∫ ω, ∑ i ∈ Finset.range (N k),
      (M (t k (i + 1)) ω - M (t k i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  let G : ℕ → Filtration ℕ mΩ := fun k =>
    ⟨fun i => F (t k i), fun _ _ hij => F.mono (ht k hij), fun i => F.le (t k i)⟩
  have hMG (k : ℕ) : Martingale (fun i => M (t k i)) (G k) μ :=
    ⟨fun i => hM.stronglyMeasurable _, fun _ _ hij => hM.condExp_ae_eq (ht k hij)⟩
  apply tendsto_integral_sum_fourth_of_modulus G (fun k i => M (t k i)) hMG hC
    (fun k i => hb (t k i)) N
  filter_upwards [hc] with ω hω
  exact tendsto_incrementModulus_of_uniformContinuousOn
    (hS.uniformContinuousOn_of_continuous hω) t N hmem δ hδ hmesh

theorem tendsto_sum_integral_fourth_of_continuous [IsProbabilityMeasure μ]
    {I : Type*} [Preorder I] [PseudoMetricSpace I]
    {F : Filtration I mΩ} {M : I → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ∀ᵐ ω ∂μ, |M t ω| ≤ C)
    {S : Set I} (hS : IsCompact S) (hc : ∀ᵐ ω ∂μ, ContinuousOn (fun t => M t ω) S)
    (t : ℕ → ℕ → I) (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ)
    (hmem : ∀ k i, i ≤ N k → t k i ∈ S) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hmesh : ∀ k i, i < N k → dist (t k (i + 1)) (t k i) ≤ δ k) :
    Tendsto (fun k => ∑ i ∈ Finset.range (N k),
      ∫ ω, (M (t k (i + 1)) ω - M (t k i) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  apply (tendsto_integral_sum_fourth_of_continuous hM hC hb hS hc t ht N hmem δ hδ hmesh).congr'
  apply Filter.Eventually.of_forall
  intro k
  apply integral_finsetSum
  intro i hi
  have hm : AEStronglyMeasurable (fun ω => M (t k (i + 1)) ω - M (t k i) ω) μ :=
    (((hM.stronglyMeasurable _).mono (F.le _)).sub
      ((hM.stronglyMeasurable _).mono (F.le _))).aestronglyMeasurable
  apply (bounded_pow_memLp_two hm (show 0 ≤ 2 * C by positivity) ?_ 4).integrable (by norm_num)
  filter_upwards [hb (t k (i + 1)), hb (t k i)] with ω hn hi
  exact (abs_sub _ _).trans (by linarith)

theorem integral_quadratic_variation_le [IsProbabilityMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ} (hM : Martingale M F μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ i, ∀ᵐ ω ∂μ, |M i ω| ≤ C) (n : ℕ) :
    (∫ ω, ∑ i ∈ Finset.range n, (M (i + 1) ω - M i ω) ^ 2 ∂μ) ≤ C ^ 2 := by
  have hM2 (i : ℕ) : MemLp (M i) 2 μ := by
    simpa using bounded_pow_memLp_two
      ((hM.stronglyMeasurable i).mono (F.le i)).aestronglyMeasurable hC (hb i) 1
  have hint (i : ℕ) : Integrable (fun ω => (M (i + 1) ω - M i ω) ^ 2) μ :=
    ((hM2 (i + 1)).sub (hM2 i)).integrable_sq
  rw [integral_finsetSum _ (fun i hi => hint i)]
  rw [MartingaleTransformL2.sum_integral_sq_increment hM hM2 n]
  apply (MartingaleTransformL2.integral_sq_increment_le hM (Nat.zero_le n) (hM2 0) (hM2 n)).trans
  calc
    _ ≤ ∫ _ : Ω, C ^ 2 ∂μ := by
      apply integral_mono_ae (hM2 n).integrable_sq (integrable_const _)
      filter_upwards [hb n] with ω hω
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).2 hω
    _ = _ := by simp

end Problem367.BoundedMartingaleVariation

end

end OAI
