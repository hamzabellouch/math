import Mathlib

namespace OAI

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators ENNReal NNReal
namespace FKCRT.TreeCoding

lemma martingale_square_submartingale {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι ‹MeasurableSpace Ω›}
    {f : ι → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₂ : ∀ i, Integrable (fun ω => (f i ω)^2) μ) :
    Submartingale (fun i ω => (f i ω)^2) ℱ μ := by
  refine ⟨fun i => (hf.stronglyMeasurable i).pow 2, ?_, h₂⟩
  intro i j hij
  have hj := (even_two.convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ (ℱ.le i)
    (continuous_pow 2).lowerSemicontinuous (hf.integrable j) (h₂ j)
  filter_upwards [hj, hf.condExp_ae_eq hij] with ω hJ hM
  simpa only [Function.comp_def, hM] using hJ


lemma martingale_maximal_square_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₂ : ∀ i, Integrable (fun ω => (f i ω)^2) μ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |f k ω|} ≤ (∫ ω, (f n ω)^2 ∂μ) / ε^2 := by
  let g := fun i ω => (f i ω)^2
  let E := {ω | ε^2 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
    (fun k => g k ω)}
  have hmax := maximal_ineq (martingale_square_submartingale hf h₂)
    (fun i ω => sq_nonneg (f i ω)) (ε := (⟨ε^2, sq_nonneg ε⟩ : ℝ≥0)) n
  have hs : {ω | ∃ k ≤ n, ε ≤ |f k ω|} ⊆ E := by
    rintro ω ⟨k, hk, hω⟩
    change ε^2 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => g k ω)
    apply le_trans _ (Finset.le_sup' (fun k => g k ω) (Finset.mem_range.mpr (show k < n+1 by omega)))
    change ε^2 ≤ (f k ω)^2
    nlinarith [sq_abs (f k ω)]
  have hi : 0 ≤ ∫ ω in E, (f n ω)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  rw [ENNReal.toReal_mul] at ht
  erw [ENNReal.coe_toReal] at ht
  change ε^2 * (μ E).toReal ≤
    (ENNReal.ofReal (∫ ω in E, (f n ω)^2 ∂μ)).toReal at ht
  rw [ENNReal.toReal_ofReal hi] at ht
  have hwhole : (∫ ω in E, (f n ω)^2 ∂μ) ≤ ∫ ω, (f n ω)^2 ∂μ :=
    setIntegral_le_integral (h₂ n) (ae_of_all μ (fun _ => sq_nonneg _))
  apply (le_div_iff₀ (sq_pos_of_pos hε)).mpr
  calc
    _ ≤ μ.real E * ε^2 := mul_le_mul_of_nonneg_right (measureReal_mono hs) (sq_nonneg _)
    _ ≤ ∫ ω in E, (f n ω)^2 ∂μ := by simpa [mul_comm, measureReal_def] using ht
    _ ≤ _ := hwhole


lemma independent_sum_martingale {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hXi : ∀ k, Integrable (X k) μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0) :
    Martingale (fun n ω => ∑ k ∈ Finset.range (n+1), X k ω)
      (Filtration.natural X hXm) μ := by
  have hadp : StronglyAdapted (Filtration.natural X hXm)
      (fun n ω => ∑ k ∈ Finset.range (n+1), X k ω) := by
    intro n
    have h : ∀ k ∈ Finset.range (n+1),
        StronglyMeasurable[(Filtration.natural X hXm) n] (X k) := by
      intro k hk
      exact ((Filtration.stronglyAdapted_natural hXm) k).mono
        ((Filtration.natural X hXm).mono (show k ≤ n from by simpa using hk))
    convert Finset.stronglyMeasurable_sum _ h using 1
    ext ω
    simp

  have hint : ∀ n, Integrable (fun ω => ∑ k ∈ Finset.range (n+1), X k ω) μ := by
    intro n
    exact integrable_finsetSum _ (fun k _ => hXi k)
  apply martingale_nat hadp hint
  intro n
  have heq : (fun ω => ∑ k ∈ Finset.range (n+1+1), X k ω) =
      (fun ω => ∑ k ∈ Finset.range (n+1), X k ω) + X (n+1) := by
    funext ω
    exact Finset.sum_range_succ _ _
  rw [heq]
  filter_upwards [condExp_add (hint n) (hXi (n+1)) (Filtration.natural X hXm n),
    hX.condExp_natural_ae_eq_of_lt hXm (show n < n+1 by omega)] with ω hsum hnew
  rw [condExp_of_stronglyMeasurable (Filtration.le _ n) (hadp n) (hint n),
    Pi.add_apply, hnew, hzero, add_zero] at hsum
  exact hsum.symm


lemma independent_sum_second_moment {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX₂ : ∀ k, MemLp (X k) 2 μ) (hX : iIndepFun X μ)
    (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0) (s : Finset ι) :
    (∫ ω, (∑ k ∈ s, X k ω)^2 ∂μ) = ∑ k ∈ s, ∫ ω, (X k ω)^2 ∂μ := by
  have hS : MemLp (fun ω => ∑ k ∈ s, X k ω) 2 μ :=
    memLp_finsetSum _ (fun k _ => hX₂ k)
  have hSz : (∫ ω, ∑ k ∈ s, X k ω ∂μ) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hX₂ k).integrable (by norm_num))]
    simp only [hzero, Finset.sum_const_zero]
  rw [← variance_of_integral_eq_zero hS.aemeasurable hSz]
  have hvar := IndepFun.variance_sum (s := s) (fun k _ => hX₂ k)
    (fun _ _ _ _ hne => hX.indepFun hne)
  have hfun : (∑ k ∈ s, X k) = (fun ω => ∑ k ∈ s, X k ω) := by ext ω; simp
  rw [hfun] at hvar
  rw [hvar]
  exact Finset.sum_congr rfl (fun k _ => variance_of_integral_eq_zero
    (hX₂ k).aemeasurable (hzero k))


lemma independent_sum_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      (∑ j ∈ Finset.range n, ∫ ω, (X j ω)^2 ∂μ) / ε^2 := by
  cases n with
  | zero => simp [not_le.mpr hε]
  | succ n =>
    have hmart := independent_sum_martingale X hXm
      (fun k => (hX₂ k).integrable (by norm_num)) hX hzero
    have hmax := martingale_maximal_square_bound hmart
      (fun m => (memLp_finsetSum (Finset.range (m+1))
        (fun k _ => hX₂ k)).integrable_sq) n hε
    rw [independent_sum_second_moment X hX₂ hX hzero] at hmax
    apply le_trans (measureReal_mono ?_) hmax
    rintro ω ⟨k, hk, hω⟩
    cases k with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at hω
              exact (not_le.mpr hε hω).elim
    | succ k => exact ⟨k, by omega, hω⟩


lemma memLp_integrable_pow_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {p j : ℕ} (hX : MemLp X (p : ℝ≥0∞) μ)
    (hj : j ≤ p) : Integrable (fun ω => (X ω)^j) μ := by
  have h := (hX.mono_exponent (show (j : ℝ≥0∞) ≤ p by exact_mod_cast hj)).integrable_norm_pow'
  exact h.mono (hX.aestronglyMeasurable.pow j)
    (ae_of_all μ (fun ω => by simp only [norm_pow, Real.norm_eq_abs, abs_abs, le_refl]))


lemma independent_add_fourth_moment {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X Y : Ω → ℝ} (hXY : IndepFun X Y μ)
    (hX : MemLp X 4 μ) (hY : MemLp Y 4 μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (hY0 : ∫ ω, Y ω ∂μ = 0) :
    (∫ ω, (X ω + Y ω)^4 ∂μ) = (∫ ω, (X ω)^4 ∂μ) +
      6 * (∫ ω, (X ω)^2 ∂μ) * (∫ ω, (Y ω)^2 ∂μ) + (∫ ω, (Y ω)^4 ∂μ) := by
  have hXp : ∀ j ≤ 4, Integrable (fun ω => (X ω)^j) μ :=
    fun j hj => memLp_integrable_pow_le (p := 4) hX hj
  have hYp : ∀ j ≤ 4, Integrable (fun ω => (Y ω)^j) μ :=
    fun j hj => memLp_integrable_pow_le (p := 4) hY hj
  have hind : ∀ i j : ℕ, IndepFun (fun ω => (X ω)^i) (fun ω => (Y ω)^j) μ :=
    fun i j => hXY.comp (measurable_id.pow_const i) (measurable_id.pow_const j)
  have hprod : ∀ i ≤ 4, ∀ j ≤ 4, Integrable (fun ω => (X ω)^i * (Y ω)^j) μ :=
    fun i hi j hj => (hind i j).integrable_mul (hXp i hi) (hYp j hj)
  have hp : (fun ω => (X ω + Y ω)^4) =
      (fun ω => (X ω)^4 + 4 * ((X ω)^3 * (Y ω)^1) +
        6 * ((X ω)^2 * (Y ω)^2) + 4 * ((X ω)^1 * (Y ω)^3) + (Y ω)^4) := by
    funext ω; ring
  rw [hp]
  erw [integral_add (((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4)).add
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6) |>.add
      ((hprod 1 (by omega) 3 (by omega)).const_mul 4)) (hYp 4 le_rfl)]
  erw [integral_add (((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4)).add
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6))
      ((hprod 1 (by omega) 3 (by omega)).const_mul 4)]
  erw [integral_add ((hXp 4 le_rfl).add ((hprod 3 (by omega) 1 (by omega)).const_mul 4))
      ((hprod 2 (by omega) 2 (by omega)).const_mul 6)]
  erw [integral_add (hXp 4 le_rfl) ((hprod 3 (by omega) 1 (by omega)).const_mul 4)]
  simp only [integral_const_mul]
  rw [(hind 3 1).integral_fun_mul_eq_mul_integral (hXp 3 (by omega)).aestronglyMeasurable
      (hYp 1 (by omega)).aestronglyMeasurable,
    (hind 2 2).integral_fun_mul_eq_mul_integral (hXp 2 (by omega)).aestronglyMeasurable
      (hYp 2 (by omega)).aestronglyMeasurable,
    (hind 1 3).integral_fun_mul_eq_mul_integral (hXp 1 (by omega)).aestronglyMeasurable
      (hYp 3 (by omega)).aestronglyMeasurable]
  simp only [pow_one, hX0, hY0, mul_zero, zero_mul, add_zero]
  ring


lemma independent_sum_fourth_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (n : ℕ) :
    (∫ ω, (∑ k ∈ Finset.range n, X k ω)^4 ∂μ) ≤
      (n : ℝ) * κ + 3 * (n : ℝ)^2 * v^2 := by
  have hX₂ : ∀ k, MemLp (X k) 2 μ := fun k => (hX₄ k).mono_exponent (by norm_num)
  induction n with
  | zero => simp
  | succ n ih =>
    have hS₄ : MemLp (fun ω => ∑ k ∈ Finset.range n, X k ω) 4 μ :=
      memLp_finsetSum _ (fun k _ => hX₄ k)
    have hS0 : (∫ ω, ∑ k ∈ Finset.range n, X k ω ∂μ) = 0 := by
      rw [integral_finsetSum _ (fun k _ => (hX₄ k).integrable (by norm_num))]
      simp only [hzero, Finset.sum_const_zero]
    have hSInd : IndepFun (fun ω => ∑ k ∈ Finset.range n, X k ω) (X n) μ := by
      convert hX.indepFun_finsetSum_of_notMem hXm
        (s := Finset.range n) (i := n) (by simp) using 1
      ext ω
      simp
    have hS₂ : (∫ ω, (∑ k ∈ Finset.range n, X k ω)^2 ∂μ) ≤ (n : ℝ) * v := by
      rw [independent_sum_second_moment X hX₂ hX hzero]
      exact (Finset.sum_le_sum (fun k _ => hvar k)).trans_eq (by simp)
    have hmul : (∫ ω, (∑ k ∈ Finset.range n, X k ω)^2 ∂μ) *
        (∫ ω, (X n ω)^2 ∂μ) ≤ (n : ℝ) * v^2 := by
      have h := mul_le_mul hS₂ (hvar n) (integral_nonneg (fun _ => sq_nonneg _))
        (mul_nonneg (Nat.cast_nonneg n) hv)
      simpa only [pow_two, mul_assoc] using h
    simp only [Finset.sum_range_succ]
    rw [independent_add_fourth_moment hSInd hS₄ (hX₄ n) hS0 (hzero n)]
    push_cast
    nlinarith [hfour n, sq_nonneg v]


lemma martingale_fourth_submartingale {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ι ‹MeasurableSpace Ω›}
    {f : ι → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₄ : ∀ i, Integrable (fun ω => (f i ω)^4) μ) :
    Submartingale (fun i ω => (f i ω)^4) ℱ μ := by
  refine ⟨fun i => (hf.stronglyMeasurable i).pow 4, ?_, h₄⟩
  intro i j hij
  have hj := ((show Even (4:ℕ) by norm_num).convexOn_pow (𝕜 := ℝ)).map_condExp_le_univ
    (ℱ.le i) (continuous_pow 4).lowerSemicontinuous (hf.integrable j) (h₄ j)
  filter_upwards [hj, hf.condExp_ae_eq hij] with ω hJ hM
  simpa only [Function.comp_def, hM] using hJ


lemma martingale_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    {f : ℕ → Ω → ℝ} (hf : Martingale f ℱ μ)
    (h₄ : ∀ i, Integrable (fun ω => (f i ω)^4) μ) (n : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |f k ω|} ≤ (∫ ω, (f n ω)^4 ∂μ) / ε^4 := by
  let g := fun i ω => (f i ω)^4
  let E := {ω | ε^4 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one
    (fun k => g k ω)}
  have hmax := maximal_ineq (martingale_fourth_submartingale hf h₄)
    (fun i ω => by positivity) (ε := (⟨ε^4, by positivity⟩ : ℝ≥0)) n
  have hs : {ω | ∃ k ≤ n, ε ≤ |f k ω|} ⊆ E := by
    rintro ω ⟨k, hk, hω⟩
    change ε^4 ≤ (Finset.range (n+1)).sup' Finset.nonempty_range_add_one (fun k => g k ω)
    apply le_trans _ (Finset.le_sup' (fun k => g k ω) (Finset.mem_range.mpr (show k < n+1 by omega)))
    change ε^4 ≤ (f k ω)^4
    simpa only [← abs_pow, abs_of_nonneg (show 0 ≤ (f k ω)^4 by positivity)] using
      pow_le_pow_left₀ hε.le hω 4
  have hi : 0 ≤ ∫ ω in E, (f n ω)^4 ∂μ := integral_nonneg (fun _ => by positivity)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
  rw [ENNReal.toReal_mul] at ht
  erw [ENNReal.coe_toReal] at ht
  change ε^4 * (μ E).toReal ≤
    (ENNReal.ofReal (∫ ω in E, (f n ω)^4 ∂μ)).toReal at ht
  rw [ENNReal.toReal_ofReal hi] at ht
  have hwhole : (∫ ω in E, (f n ω)^4 ∂μ) ≤ ∫ ω, (f n ω)^4 ∂μ :=
    setIntegral_le_integral (h₄ n) (ae_of_all μ (fun _ => by positivity))
  apply (le_div_iff₀ (pow_pos hε 4)).mpr
  calc
    _ ≤ μ.real E * ε^4 := mul_le_mul_of_nonneg_right (measureReal_mono hs) (by positivity)
    _ ≤ ∫ ω in E, (f n ω)^4 ∂μ := by simpa [mul_comm, measureReal_def] using ht
    _ ≤ _ := hwhole


lemma independent_sum_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      ((n : ℝ) * κ + 3 * (n : ℝ)^2 * v^2) / ε^4 := by
  cases n with
  | zero => simp [not_le.mpr hε]
  | succ n =>
    have hmart := independent_sum_martingale X hXm
      (fun k => (hX₄ k).integrable (by norm_num)) hX hzero
    have hmax := martingale_maximal_fourth_bound hmart
      (fun m => memLp_integrable_pow_le (p := 4)
        (memLp_finsetSum (Finset.range (m+1)) (fun k _ => hX₄ k)) le_rfl) n hε
    apply le_trans (measureReal_mono ?_) (hmax.trans ?_)
    · rintro ω ⟨k, hk, hω⟩
      cases k with
      | zero => simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at hω
                exact (not_le.mpr hε hω).elim
      | succ k => exact ⟨k, by omega, hω⟩
    · exact div_le_div_of_nonneg_right (independent_sum_fourth_moment_bound X
        (fun k => (hXm k).measurable) hX₄ hX hzero hv hvar hfour (n+1)) (by positivity)


lemma block_maximal_fourth_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ) (B L : ℕ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ b < B, ∃ k ≤ L,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|} ≤
      (B : ℝ) * ((L : ℝ) * κ + 3 * (L : ℝ)^2 * v^2) / (ε^4 * (n : ℝ)^2) := by
  let E := fun b => {ω | ∃ k ≤ L,
    ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|}
  have hE : {ω | ∃ b < B, ∃ k ≤ L,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*L+j) ω|} =
      ⋃ b ∈ Finset.range B, E b := by ext ω; simp [E]
  rw [hE]
  apply (measureReal_biUnion_finset_le (Finset.range B) E).trans
  have hb : ∀ b, μ.real (E b) ≤
      ((L : ℝ) * κ + 3 * (L : ℝ)^2 * v^2) / (ε^4 * (n : ℝ)^2) := by
    intro b
    have hind := hX.precomp (g := fun j => b*L+j) (fun _ _ hjk => Nat.add_left_cancel hjk)
    have ht := independent_sum_maximal_fourth_bound (fun j => X (b*L+j))
      (fun j => hXm _) (fun j => hX₄ _) hind (fun j => hzero _) hv
      (fun j => hvar _) (fun j => hfour _) L
      (mul_pos hε (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)))
    have hs : (Real.sqrt (n : ℝ))^4 = (n : ℝ)^2 := by
      rw [show 4 = 2*2 by norm_num, pow_mul, Real.sq_sqrt (Nat.cast_nonneg n)]
    simpa only [mul_pow, hs] using ht
  exact (Finset.sum_le_sum (fun b _ => hb b)).trans_eq (by simp [mul_div_assoc])


lemma block_oscillation_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v) (hκ : 0 ≤ κ)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ b < m+1, ∃ k ≤ n/m+1,
      ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X (b*(n/m+1)+j) ω|} ≤
      (4*κ + 24*v^2) / (ε^4 * (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (hm.trans_le hmn)
  have hmnR : (m : ℝ) ≤ n := Nat.cast_le.mpr hmn
  have hL : ((n/m+1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / m := by
    push_cast
    have hdiv : (1:ℝ) ≤ (n:ℝ)/m := (le_div_iff₀ hmR).mpr (by simpa using hmnR)
    rw [mul_div_assoc]
    linarith [Nat.cast_div_le (m := n) (n := m) (α := ℝ)]
  have hB : ((m+1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    push_cast
    linarith
  have hLL : ((n/m+1 : ℕ) : ℝ)^2 ≤ (2*(n:ℝ)/m)^2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hL 2
  have hbound := block_maximal_fourth_bound X hXm hX₄ hX hzero hv hvar hfour
    (m+1) (n/m+1) (hm.trans_le hmn) hε
  apply hbound.trans
  calc
    _ ≤ (2*(m:ℝ)) * ((2*(n:ℝ)/m)*κ + 3*(2*(n:ℝ)/m)^2*v^2) /
        (ε^4*(n:ℝ)^2) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul hB
      · exact add_le_add (mul_le_mul_of_nonneg_right hL hκ)
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLL (by norm_num))
            (sq_nonneg v))
      · positivity
      · positivity
    _ = 4*κ / (ε^4*(n:ℝ)) + 24*v^2 / (ε^4*(m:ℝ)) := by
      field_simp
      ring
    _ ≤ 4*κ / (ε^4*(m:ℝ)) + 24*v^2 / (ε^4*(m:ℝ)) := by
      apply add_le_add _ le_rfl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hmnR (by positivity))
    _ = _ := by rw [add_div]


def hat (N i : ℕ) : C(unitInterval, ℝ) where
  toFun t := max 0 (1 - |(N : ℝ) * (t : ℝ) - i|)
  continuous_toFun := continuous_const.max
    (continuous_const.sub ((continuous_const.mul continuous_subtype_val).sub continuous_const).abs)


def interpolation (N : ℕ) (a : Fin (N+1) → ℝ) : C(unitInterval, ℝ) :=
  ∑ i : Fin (N+1), a i • hat N i.val


lemma tent_sum_eq_one (N : ℕ) {x : ℝ} (hx0 : 0 ≤ x) (hxN : x ≤ N) :
    (∑ i ∈ Finset.range (N+1), max 0 (1 - |x - (i : ℝ)|)) = 1 := by
  induction N with
  | zero => have hx : x = 0 := le_antisymm (by simpa using hxN) hx0
            simp [hx]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    by_cases hx : x ≤ (N : ℝ)
    · have ht : max 0 (1 - |x - ((N+1 : ℕ) : ℝ)|) = 0 := by
        rw [abs_of_nonpos (by push_cast; linarith), max_eq_left]
        push_cast
        linarith
      rw [ht, add_zero]
      exact ih hx
    · have hx1 : (N : ℝ) < x := lt_of_not_ge hx
      have hsum : (∑ i ∈ Finset.range (N+1), max 0 (1 - |x - (i : ℝ)|)) =
          max 0 (1 - |x - (N : ℝ)|) := by
        apply Finset.sum_eq_single N
        · intro i hi hiN
          have hi' : i < N := by simp only [Finset.mem_range] at hi; omega
          have hiR : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi'
          rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
        · simp
      rw [hsum, abs_of_nonneg (by linarith), max_eq_right (by push_cast at hxN; linarith),
        abs_of_nonpos (by push_cast at hxN ⊢; linarith),
        max_eq_right (by push_cast; linarith)]
      push_cast
      ring


lemma hat_nonneg (N i : ℕ) (t : unitInterval) : 0 ≤ hat N i t := le_max_left _ _


lemma hat_sum (N : ℕ) (t : unitInterval) : (∑ i : Fin (N+1), hat N i.val t) = 1 := by
  have hx0 : 0 ≤ (N : ℝ) * (t : ℝ) := mul_nonneg (Nat.cast_nonneg N) t.property.1
  have hxN : (N : ℝ) * (t : ℝ) ≤ N := by nlinarith [t.property.2, Nat.cast_nonneg N (α := ℝ)]
  change (∑ i : Fin (N+1), (fun j : ℕ => max 0 (1 - |(N : ℝ) * (t : ℝ) - j|)) i.val) = 1
  exact (Fin.sum_univ_eq_sum_range
    (fun j : ℕ => max 0 (1 - |(N : ℝ) * (t : ℝ) - j|)) (N+1)).trans
    (tent_sum_eq_one N hx0 hxN)


lemma hat_support {N i : ℕ} {t : unitInterval} (h : hat N i t ≠ 0) :
    |(N : ℝ) * (t : ℝ) - i| < 1 := by
  change max 0 (1 - |(N : ℝ) * (t : ℝ) - i|) ≠ 0 at h
  have hh : 0 < max 0 (1 - |(N : ℝ) * (t : ℝ) - i|) :=
    lt_of_le_of_ne (le_max_left _ _) (Ne.symm h)
  rw [lt_max_iff] at hh
  rcases hh with hh | hh
  · exact (lt_irrefl _ hh).elim
  · linarith


lemma interpolation_apply (N : ℕ) (a : Fin (N+1) → ℝ) (t : unitInterval) :
    interpolation N a t = ∑ i : Fin (N+1), a i * hat N i.val t := by
  simp [interpolation]


lemma interpolation_sub_const_bound (N : ℕ) (a : Fin (N+1) → ℝ) (t : unitInterval)
    {c M : ℝ} (h : ∀ i : Fin (N+1), hat N i.val t ≠ 0 → |a i - c| ≤ M) :
    |interpolation N a t - c| ≤ M := by
  have heq : interpolation N a t - c =
      ∑ i : Fin (N+1), (a i - c) * hat N i.val t := by
    rw [interpolation_apply]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hat_sum, mul_one]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i : Fin (N+1), M * hat N i.val t := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : hat N i.val t = 0
      · simp [hi]
      · rw [abs_mul, abs_of_nonneg (hat_nonneg N i.val t)]
        exact mul_le_mul_of_nonneg_right (h i hi) (hat_nonneg N i.val t)
    _ = M := by rw [← Finset.mul_sum, hat_sum, mul_one]


lemma interpolation_two_point_bound (N : ℕ) (a : Fin (N+1) → ℝ)
    (s t : unitInterval) {M : ℝ}
    (h : ∀ i j : Fin (N+1), hat N i.val s ≠ 0 → hat N j.val t ≠ 0 → |a i - a j| ≤ M) :
    |interpolation N a s - interpolation N a t| ≤ M := by
  apply interpolation_sub_const_bound
  intro i hi
  rw [abs_sub_comm]
  apply interpolation_sub_const_bound
  intro j hj
  rw [abs_sub_comm]
  exact h i j hi hj


lemma interpolation_diff_bound (N : ℕ) (a b : Fin (N+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (h : ∀ i, |a i - b i| ≤ M) :
    ‖interpolation N a - interpolation N b‖ ≤ M := by
  apply (ContinuousMap.norm_le _ hM).mpr
  intro t
  change |interpolation N a t - interpolation N b t| ≤ M
  have heq : interpolation N a t - interpolation N b t =
      interpolation N (fun i => a i - b i) t := by
    simp only [interpolation_apply, sub_mul, Finset.sum_sub_distrib]
  rw [heq]
  simpa only [sub_zero] using interpolation_sub_const_bound N (fun i => a i - b i) t
    (c := 0) (fun i _ => by simpa only [sub_zero] using h i)


lemma block_anchor_bound (S : ℕ → ℝ) {B L : ℕ} {A : ℝ}
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    (b d : ℕ) (hbd : b+d ≤ B) :
    |S ((b+d)*L) - S (b*L)| ≤ (d : ℝ) * A := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hc := h (b+d) (by omega) L le_rfl
    have heq : (b+(d+1))*L = (b+d)*L+L := by ring
    have ht := (abs_sub_le (S ((b+(d+1))*L)) (S ((b+d)*L)) (S (b*L))).trans
      (add_le_add (by simpa only [heq] using hc) (ih (by omega)))
    calc
      _ ≤ A+(d : ℝ)*A := ht
      _ = ((d+1 : ℕ) : ℝ)*A := by push_cast; ring


lemma block_grid_bound (S : ℕ → ℝ) {B L : ℕ} (hL : 0 < L) {A : ℝ} (hA : 0 ≤ A)
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    {i j D : ℕ} (hij : i ≤ j) (hj : j/L < B) (hD : j/L-i/L ≤ D) :
    |S i - S j| ≤ ((D : ℝ)+2) * A := by
  have hib : i/L ≤ j/L := Nat.div_le_div_right hij
  have hia := h (i/L) (hib.trans_lt hj) (i%L) (Nat.mod_lt i hL).le
  have hja := h (j/L) hj (j%L) (Nat.mod_lt j hL).le
  rw [Nat.mul_comm (i/L) L, Nat.div_add_mod, Nat.mul_comm L (i/L)] at hia
  rw [Nat.mul_comm (j/L) L, Nat.div_add_mod, Nat.mul_comm L (j/L)] at hja
  have hd : i/L+(j/L-i/L) = j/L := Nat.add_sub_of_le hib
  have hba := block_anchor_bound S h (i/L) (j/L-i/L) (by omega)
  rw [hd, abs_sub_comm] at hba
  have ht := (abs_sub_le (S i) (S ((i/L)*L)) (S j)).trans
    (add_le_add hia ((abs_sub_le (S ((i/L)*L)) (S ((j/L)*L)) (S j)).trans
      (add_le_add hba (by simpa only [abs_sub_comm] using hja))))
  have hDR : ((j/L-i/L : ℕ) : ℝ) ≤ D := Nat.cast_le.mpr hD
  nlinarith [mul_le_mul_of_nonneg_right hDR hA]


lemma div_diff_le_two {i j L : ℕ} (hL : 0 < L) (_hij : i ≤ j)
    (hijL : j ≤ i+2*L) : j/L-i/L ≤ 2 := by
  have hmod := Nat.mod_lt i hL
  have hrep := Nat.div_add_mod i L
  have hjb : j < (i/L+3)*L := by nlinarith
  have hd := (Nat.div_lt_iff_lt_mul hL).mpr hjb
  omega


lemma interpolation_block_modulus (S : ℕ → ℝ) {N B L : ℕ} (hL : 0 < L)
    (hNB : N/L < B) {A δ : ℝ} (hA : 0 ≤ A)
    (hδ : (N : ℝ)*δ+2 ≤ 2*(L : ℝ))
    (h : ∀ b < B, ∀ k ≤ L, |S (b*L+k) - S (b*L)| ≤ A)
    (s t : unitInterval) (hst : dist s t ≤ δ) :
    |interpolation N (fun i => S i.val) s - interpolation N (fun i => S i.val) t| ≤ 4*A := by
  apply interpolation_two_point_bound
  intro i j hi hj
  have hi' := hat_support hi
  have hj' := hat_support hj
  have hmid : |(N : ℝ)*(s : ℝ)-(N : ℝ)*(t : ℝ)| ≤ (N : ℝ)*δ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N)
  have hclose : |(i.val : ℝ)-(j.val : ℝ)| ≤ 2*(L : ℝ) := by
    have htri := (abs_sub_le (i.val : ℝ) ((N : ℝ)*(s : ℝ)) (j.val : ℝ)).trans
      (add_le_add le_rfl (abs_sub_le ((N : ℝ)*(s : ℝ)) ((N : ℝ)*(t : ℝ)) (j.val : ℝ)))
    rw [abs_sub_comm (i.val : ℝ) ((N : ℝ)*(s : ℝ))] at htri
    linarith
  have hiB : i.val/L < B := (Nat.div_le_div_right (show i.val ≤ N by omega)).trans_lt hNB
  have hjB : j.val/L < B := (Nat.div_le_div_right (show j.val ≤ N by omega)).trans_lt hNB
  rcases le_total i.val j.val with hij | hji
  · have hijL : j.val ≤ i.val+2*L := by
      have hh := (abs_le.mp hclose).1
      have hr : (j.val : ℝ) ≤ (i.val : ℝ)+2*(L : ℝ) := by linarith
      exact_mod_cast hr
    simpa only [Nat.cast_ofNat, show (2:ℝ)+2=4 by norm_num] using
      block_grid_bound S hL hA h hij hjB (div_diff_le_two hL hij hijL)
  · rw [abs_sub_comm]
    have hjiL : i.val ≤ j.val+2*L := by
      have hh := (abs_le.mp hclose).2
      have hr : (i.val : ℝ) ≤ (j.val : ℝ)+2*(L : ℝ) := by linarith
      exact_mod_cast hr
    simpa only [Nat.cast_ofNat, show (2:ℝ)+2=4 by norm_num] using
      block_grid_bound S hL hA h hji hiB (div_diff_le_two hL hji hjiL)


def tailValue (R x : ℝ) : ℝ := if R < |x| then x else 0


def centeredTail {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  tailValue R (X ω) - ∫ z, tailValue R (X z) ∂μ


lemma measurable_tailValue (R : ℝ) : Measurable (tailValue R) := by
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id.abs)
    measurable_id measurable_const


lemma tailValue_sq_le (R x : ℝ) : (tailValue R x)^2 ≤ x^2 := by
  unfold tailValue
  split_ifs <;> simp [sq_nonneg]


lemma tailValue_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    MemLp (fun ω => tailValue R (X ω)) 2 μ := by
  apply (memLp_two_iff_integrable_sq
    ((measurable_tailValue R).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable).mpr
  refine hX.integrable_sq.mono'
    (((measurable_tailValue R).comp_aemeasurable hX.aemeasurable).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_sq]
  exact tailValue_sq_le R (X ω)


lemma centeredTail_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    MemLp (centeredTail μ X R) 2 μ :=
  (tailValue_memLp hX R).sub (memLp_const _)


@[simp] lemma centeredTail_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, centeredTail μ X R ω ∂μ) = 0 := by
  simp only [centeredTail, integral_sub ((tailValue_memLp hX R).integrable (by norm_num))
    (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]


lemma centeredTail_second_moment_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, (centeredTail μ X R ω)^2 ∂μ) ≤ ∫ ω, (tailValue R (X ω))^2 ∂μ := by
  rw [← variance_of_integral_eq_zero (centeredTail_memLp hX R).aemeasurable
    (centeredTail_integral hX R)]
  change Var[fun ω => tailValue R (X ω) - ∫ z, tailValue R (X z) ∂μ; μ] ≤ _
  rw [variance_sub_const (tailValue_memLp hX R).aestronglyMeasurable,
    variance_eq_sub (tailValue_memLp hX R)]
  exact sub_le_self _ (sq_nonneg _)


lemma tail_second_moment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Tendsto (fun R : ℕ => ∫ ω, (tailValue R (X ω))^2 ∂μ) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (fun ω => (X ω)^2)
    (F := fun R : ℕ => fun ω => (tailValue R (X ω))^2) (f := fun _ => 0)
    (fun R => ((tailValue_memLp hX R).integrable_sq).aestronglyMeasurable)
    hX.integrable_sq
    (fun R => ae_of_all μ (fun ω => by
      simpa only [Real.norm_eq_abs, abs_sq] using tailValue_sq_le R (X ω)))
    (ae_of_all μ (fun ω => by
      obtain ⟨N, hN⟩ := exists_nat_gt |X ω|
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with R hR
      have hRX : ¬ (R : ℝ) < |X ω| := by exact not_lt.mpr (hN.le.trans (Nat.cast_le.mpr hR))
      simp [tailValue, hRX]))
  simpa only [integral_zero] using h


lemma centeredTail_second_moment_tendsto_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    Tendsto (fun R : ℕ => ∫ ω, (centeredTail μ X R ω)^2 ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero (fun R : ℕ => integral_nonneg (fun _ => sq_nonneg _))
    (fun R : ℕ => centeredTail_second_moment_le hX R)
  exact tail_second_moment_tendsto_zero hX


def centeredHead {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) (R : ℝ) (ω : Ω) : ℝ :=
  (X ω - tailValue R (X ω)) - ∫ z, X z - tailValue R (X z) ∂μ


lemma head_abs_le {R : ℝ} (hR : 0 ≤ R) (x : ℝ) : |x - tailValue R x| ≤ R := by
  unfold tailValue
  split_ifs with h
  · simpa using hR
  · simpa using not_lt.mp h


lemma centeredHead_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (ω : Ω) :
    |centeredHead μ X R ω| ≤ 2 * R := by
  have hm : |∫ z, X z - tailValue R (X z) ∂μ| ≤ R := by
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all μ (fun z =>
        show ‖X z - tailValue R (X z)‖ ≤ R from head_abs_le hR (X z)))
  exact (abs_sub _ _).trans (by linarith [head_abs_le hR (X ω)])


lemma centered_head_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ)
    (hX0 : ∫ ω, X ω ∂μ = 0) (R : ℝ) (ω : Ω) :
    centeredHead μ X R ω + centeredTail μ X R ω = X ω := by
  unfold centeredHead centeredTail
  rw [integral_sub (hX.integrable (by norm_num))
    ((tailValue_memLp hX R).integrable (by norm_num)), hX0]
  ring


lemma independent_sum_scaled_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {δ : ℝ} (hδ : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ δ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε * Real.sqrt n ≤ |∑ j ∈ Finset.range k, X j ω|} ≤
      δ / ε^2 := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (∑ j ∈ Finset.range n, ∫ ω, (X j ω)^2 ∂μ) ≤ (n : ℝ) * δ := by
    exact (Finset.sum_le_sum (fun j _ => hδ j)).trans_eq (by simp)
  apply (independent_sum_maximal_bound X hXm hX₂ hX hzero n
    (mul_pos hε (Real.sqrt_pos.mpr hnR))).trans
  apply (div_le_div_of_nonneg_right hs (sq_nonneg _)).trans_eq
  rw [mul_pow, Real.sq_sqrt hnR.le]
  field_simp


lemma independent_centeredTail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ) (R : ℝ) :
    iIndepFun (fun k => centeredTail μ (X k) R) μ := by
  exact hX.comp (fun k x => tailValue R x - ∫ z, tailValue R (X k z) ∂μ)
    (fun k => (measurable_tailValue R).sub measurable_const)


lemma centeredTail_scaled_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (R δ : ℝ)
    (hδ : ∀ k, ∫ ω, (tailValue R (X k ω))^2 ∂μ ≤ δ)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ k ≤ n, ε * Real.sqrt n ≤
      |∑ j ∈ Finset.range k, centeredTail μ (X j) R ω|} ≤ δ / ε^2 := by
  apply independent_sum_scaled_maximal_bound (fun k => centeredTail μ (X k) R)
    (fun k => (((measurable_tailValue R).comp (hXm k).measurable).stronglyMeasurable).sub
      stronglyMeasurable_const)
    (fun k => centeredTail_memLp (hX₂ k) R) (independent_centeredTail X hX R)
    (fun k => centeredTail_integral (hX₂ k) R) _ hn hε
  intro k
  exact (centeredTail_second_moment_le (hX₂ k) R).trans (hδ k)


def scaledWalk {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : C(unitInterval, ℝ) :=
  interpolation n (fun i => (∑ j ∈ Finset.range i.val, X j ω) / Real.sqrt n)


lemma scaledWalk_measurable {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hXm : ∀ j, Measurable (X j)) (n : ℕ) :
    @Measurable Ω C(unitInterval, ℝ) _ (borel _) (scaledWalk X n) := by
  let : MeasurableSpace C(unitInterval, ℝ) := borel _
  let : BorelSpace C(unitInterval, ℝ) := ⟨rfl⟩
  unfold scaledWalk interpolation
  apply Finset.measurable_sum
  intro i _
  exact ((Finset.measurable_sum _ (fun j _ => hXm j)).div_const _).smul_const _


lemma sum_range_block (S : ℕ → ℝ) (b L k : ℕ) :
    (∑ j ∈ Finset.range (b*L+k), S j) - (∑ j ∈ Finset.range (b*L), S j) =
      ∑ j ∈ Finset.range k, S (b*L+j) := by
  rw [Finset.sum_range_add]
  ring


lemma grid_blocks_parameters {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    n/(n/m+1) < m+1 ∧ (n : ℝ)*(1/(m : ℝ))+2 ≤ 2*((n/m+1 : ℕ) : ℝ) := by
  have hq : 1 ≤ n/m := (Nat.le_div_iff_mul_le hm).mpr (by simpa using hmn)
  have hrep := Nat.div_add_mod n m
  have hmod := Nat.mod_lt n hm
  have hn : n < (n/m+1)*m := by nlinarith
  constructor
  · exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr (by nlinarith)
  · have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    have hnR : (n : ℝ) < ((n/m : ℕ) : ℝ)*(m : ℝ)+(m : ℝ) := by exact_mod_cast (show n < (n/m)*m+m by nlinarith [hn])
    have hdiv : (n : ℝ)/(m : ℝ) < ((n/m : ℕ) : ℝ)+1 :=
      (div_lt_iff₀ hmR).mpr (by linarith)
    have hqR : (1 : ℝ) ≤ ((n/m : ℕ) : ℝ) := by exact_mod_cast hq
    push_cast
    rw [mul_one_div]
    linarith


lemma scaledWalk_modulus_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₄ : ∀ k, MemLp (X k) 4 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v κ : ℝ} (hv : 0 ≤ v) (hκ : 0 ≤ κ)
    (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    (hfour : ∀ k, ∫ ω, (X k ω)^4 ∂μ ≤ κ)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
      4*ε < |scaledWalk X n ω s - scaledWalk X n ω t|} ≤
      (4*κ+24*v^2)/(ε^4*(m : ℝ)) := by
  classical
  apply le_trans (measureReal_mono ?_) (block_oscillation_bound X hXm hX₄ hX hzero
    hv hκ hvar hfour hm hmn hε)
  rintro ω ⟨s,t,hst,hbad⟩
  by_contra hnone
  simp only [mem_ofPred_eq] at hnone
  push Not at hnone
  have hb : ∀ b < m+1, ∀ k ≤ n/m+1,
      |(∑ j ∈ Finset.range (b*(n/m+1)+k), X j ω)/Real.sqrt n -
       (∑ j ∈ Finset.range (b*(n/m+1)), X j ω)/Real.sqrt n| ≤ ε := by
    intro b hb k hk
    rw [← sub_div, sum_range_block, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (hm.trans_le hmn)))).mpr
      ((hnone b hb k hk).le)
  have hp := grid_blocks_parameters hm hmn
  have hgood := interpolation_block_modulus
    (fun i => (∑ j ∈ Finset.range i, X j ω)/Real.sqrt n)
    (Nat.succ_pos _) hp.1 hε.le hp.2 hb s t hst
  exact (not_lt_of_ge hgood) hbad


lemma scaledWalk_maximal_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, StronglyMeasurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {v : ℝ} (hvar : ∀ k, ∫ ω, (X k ω)^2 ∂μ ≤ v)
    {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε < ‖scaledWalk X n ω‖} ≤ v/ε^2 := by
  classical
  apply le_trans (measureReal_mono ?_)
    (independent_sum_scaled_maximal_bound X hXm hX₂ hX hzero hvar hn hε)
  intro ω hω
  by_contra hnone
  simp only [mem_ofPred_eq] at hnone
  push Not at hnone
  have hbound : ‖scaledWalk X n ω‖ ≤ ε := by
    apply (ContinuousMap.norm_le _ hε.le).mpr
    intro t
    change |scaledWalk X n ω t| ≤ ε
    have h := interpolation_sub_const_bound n
      (fun i => (∑ j ∈ Finset.range i.val, X j ω)/Real.sqrt n) t (c := 0) (M := ε)
    simp only [sub_zero] at h
    apply h
    intro i _
    rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))).mpr
    exact (hnone i.val (by omega)).le
  exact (not_lt_of_ge hbound) hω


lemma centeredHead_measurable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) (R : ℝ) : Measurable (centeredHead μ X R) :=
  (hX.sub ((measurable_tailValue R).comp hX)).sub measurable_const


lemma centeredHead_memLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {R : ℝ} (hR : 0 ≤ R) (p : ℝ≥0∞) : MemLp (centeredHead μ X R) p μ :=
  MemLp.of_bound (centeredHead_measurable μ hX R).aestronglyMeasurable (2*R)
    (ae_of_all μ (fun ω => centeredHead_abs_le X hR ω))


lemma centeredHead_integral {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) (R : ℝ) :
    (∫ ω, centeredHead μ X R ω ∂μ) = 0 := by
  simp only [centeredHead]
  have hi : Integrable (fun ω => X ω-tailValue R (X ω)) μ :=
    (hX.sub (tailValue_memLp hX R)).integrable (by norm_num)
  rw [integral_sub hi (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]


lemma centeredHead_moment_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : Ω → ℝ) {R : ℝ} (hR : 0 ≤ R) (j : ℕ) :
    (∫ ω, (centeredHead μ X R ω)^j ∂μ) ≤ (2*R)^j := by
  apply (le_abs_self _).trans
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => (centeredHead μ X R ω)^j)
    (ae_of_all μ (fun ω => by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (centeredHead_abs_le X hR ω) j))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h


lemma independent_centeredHead {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : iIndepFun X μ) (R : ℝ) :
    iIndepFun (fun k => centeredHead μ (X k) R) μ :=
  hX.comp (fun k x => (x-tailValue R x) - ∫ z, X k z-tailValue R (X k z) ∂μ)
    (fun _ => (measurable_id.sub (measurable_tailValue R)).sub measurable_const)


lemma scaledWalk_add {Ω : Type*} (X Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    scaledWalk (X+Y) n ω = scaledWalk X n ω + scaledWalk Y n ω := by
  ext t
  simp only [scaledWalk, interpolation_apply, Pi.add_apply, Finset.sum_add_distrib,
    add_div, add_mul, ContinuousMap.add_apply]


lemma scaledWalk_head_tail {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (hX : ∀ k, MemLp (X k) 2 μ)
    (hX0 : ∀ k, ∫ ω, X k ω ∂μ = 0) (R : ℝ) (n : ℕ) (ω : Ω) :
    scaledWalk (fun k => centeredHead μ (X k) R) n ω +
      scaledWalk (fun k => centeredTail μ (X k) R) n ω = scaledWalk X n ω := by
  rw [← scaledWalk_add]
  congr 2
  funext k ω
  exact centered_head_tail (hX k) (hX0 k) R ω


lemma path_modulus_add_le (f g : C(unitInterval, ℝ)) (s t : unitInterval) :
    |(f+g) s-(f+g) t| ≤ |f s-f t|+2*‖g‖ := by
  have hs := g.norm_coe_le_norm s
  have ht := g.norm_coe_le_norm t
  have h := abs_add_le (f s-f t) (g s-g t)
  simp only [ContinuousMap.add_apply, Real.norm_eq_abs] at *
  have heq : f s+g s-(f t+g t) = (f s-f t)+(g s-g t) := by ring
  rw [heq]
  exact h.trans (by linarith [abs_sub (g s) (g t)])


lemma finiteVariance_scaledWalk_modulus_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₂ : ∀ k, MemLp (X k) 2 μ)
    (hX : iIndepFun X μ) (hzero : ∀ k, ∫ ω, X k ω ∂μ = 0)
    {R v : ℝ} (hR : 0 ≤ R)
    (htail : ∀ k, ∫ ω, (tailValue R (X k ω))^2 ∂μ ≤ v)
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
      6*ε < |scaledWalk X n ω s-scaledWalk X n ω t|} ≤
      (4*(2*R)^4+24*((2*R)^2)^2)/(ε^4*(m : ℝ))+v/ε^2 := by
  let H := fun k => centeredHead μ (X k) R
  let T := fun k => centeredTail μ (X k) R
  have hH := scaledWalk_modulus_bound H
    (fun k => (centeredHead_measurable μ (hXm k) R).stronglyMeasurable)
    (fun k => centeredHead_memLp (hXm k) hR 4) (independent_centeredHead X hX R)
    (fun k => centeredHead_integral (hX₂ k) R) (sq_nonneg _) (by positivity)
    (fun k => centeredHead_moment_bound (X k) hR 2)
    (fun k => centeredHead_moment_bound (X k) hR 4) hm hmn hε
  have hT := scaledWalk_maximal_bound T
    (fun k => (((measurable_tailValue R).comp (hXm k)).sub measurable_const).stronglyMeasurable)
    (fun k => centeredTail_memLp (hX₂ k) R) (independent_centeredTail X hX R)
    (fun k => centeredTail_integral (hX₂ k) R)
    (fun k => (centeredTail_second_moment_le (hX₂ k) R).trans (htail k))
    (hm.trans_le hmn) hε
  apply le_trans (measureReal_mono ?_) ((measureReal_union_le _ _).trans (add_le_add hH hT))
  rintro ω ⟨s,t,hst,hbad⟩
  by_cases hh : 4*ε < |scaledWalk H n ω s-scaledWalk H n ω t|
  · exact Or.inl ⟨s,t,hst,hh⟩
  · apply Or.inr
    by_contra ht
    have hnorm : ‖scaledWalk T n ω‖ ≤ ε := not_lt.mp ht
    have hp := path_modulus_add_le (scaledWalk H n ω) (scaledWalk T n ω) s t
    rw [scaledWalk_head_tail X hX₂ hzero R] at hp
    linarith [not_lt.mp hh]


theorem iid_scaledWalk_modulus {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hXm : ∀ k, Measurable (X k)) (hX₂ : MemLp (X 0) 2 μ)
    (hX : iIndepFun X μ) (hident : ∀ k, IdentDistrib (X k) (X 0) μ μ)
    (hzero : ∫ ω, X 0 ω ∂μ = 0) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ m : ℕ, 0 < m ∧ ∀ n ≥ m,
      μ.real {ω | ∃ s t : unitInterval, dist s t ≤ 1/(m : ℝ) ∧
        ε < |scaledWalk X n ω s-scaledWalk X n ω t|} ≤ η := by
  let e := ε/6
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨R, hR⟩ := ((tail_second_moment_tendsto_zero hX₂).eventually
    (gt_mem_nhds (show (0:ℝ) < η/2*e^2 by positivity))).exists
  let v := ∫ ω, (tailValue (R : ℝ) (X 0 ω))^2 ∂μ
  have hv : v/e^2 ≤ η/2 := (div_le_iff₀ (sq_pos_of_pos he)).mpr hR.le
  let c := 4*(2*(R : ℝ))^4+24*((2*(R : ℝ))^2)^2
  have hc : Tendsto (fun m : ℕ => c/(e^4*(m : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      (tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R := ℝ)) :
        Tendsto (fun m : ℕ => (c/e^4)/(m : ℝ)) atTop (𝓝 0))
  obtain ⟨m, hm, hcm⟩ := (eventually_gt_atTop 0 |>.and
    (hc.eventually (gt_mem_nhds (half_pos hη)))).exists
  refine ⟨m,hm,fun n hmn => ?_⟩
  have hb := finiteVariance_scaledWalk_modulus_bound X hXm
    (fun k => (hident k).memLp_iff.mpr hX₂) hX
    (fun k => (hident k).integral_eq.trans hzero) (Nat.cast_nonneg R)
    (fun k => le_of_eq ((hident k).comp ((measurable_tailValue (R : ℝ)).pow_const 2)).integral_eq)
    hm hmn he
  have heq : 6*e = ε := by dsimp [e]; ring
  rw [heq] at hb
  exact hb.trans (by change c/(e^4*(m:ℝ))+v/e^2 ≤ η; linarith)


def gridPoint (N : ℕ) (i : Fin (N+1)) : unitInterval :=
  ⟨(i.val : ℝ)/(N : ℝ), by
    constructor
    · positivity
    · by_cases hN : N = 0
      · simp [hN]
      · exact (div_le_one (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).mpr
          (by exact_mod_cast Nat.le_of_lt_succ i.isLt)⟩


def pathApprox (N : ℕ) (f : C(unitInterval, ℝ)) : C(unitInterval, ℝ) :=
  interpolation N (fun i => f (gridPoint N i))


lemma continuous_interpolation (N : ℕ) : Continuous (interpolation N) := by
  unfold interpolation
  fun_prop


lemma continuous_pathApprox (N : ℕ) : Continuous (pathApprox N) := by
  apply (continuous_interpolation N).comp
  exact continuous_pi (fun i => continuous_eval_const (gridPoint N i))


lemma hat_gridPoint_dist {N : ℕ} (hN : 0 < N) (i : Fin (N+1)) (t : unitInterval)
    (hi : hat N i.val t ≠ 0) : dist (gridPoint N i) t < 1/(N : ℝ) := by
  have hh := hat_support hi
  change |(i.val:ℝ)/(N:ℝ)-(t:ℝ)| < 1/(N:ℝ)
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  rw [div_sub', abs_div, abs_of_pos hNR, div_lt_div_iff_of_pos_right hNR]
  · simpa only [abs_sub_comm, mul_comm] using hh
  · exact hNR.ne'


lemma pathApprox_error_le {N : ℕ} (hN : 0 < N) (f : C(unitInterval, ℝ))
    {ε : ℝ} (hε : 0 ≤ ε)
    (hf : ∀ s t : unitInterval, dist s t ≤ 1/(N : ℝ) → |f s-f t| ≤ ε) :
    ‖pathApprox N f-f‖ ≤ ε := by
  apply (ContinuousMap.norm_le _ hε).mpr
  intro t
  change |interpolation N (fun i => f (gridPoint N i)) t-f t| ≤ ε
  exact interpolation_sub_const_bound _ _ _ (fun i hi => hf _ _ (hat_gridPoint_dist hN i t hi).le)


lemma pathApprox_tendsto (f : C(unitInterval, ℝ)) : Tendsto (fun N => pathApprox N f) atTop (𝓝 f) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ,hδ,hd⟩ := Metric.uniformContinuous_iff.mp hu (ε/2) (by positivity)
  have ht : Tendsto (fun N : ℕ => 1/(N:ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
  filter_upwards [eventually_gt_atTop 0, ht.eventually (gt_mem_nhds hδ)] with N hN hNd
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (pathApprox_error_le hN f (by positivity : 0 ≤ ε/2) ?_) (half_lt_self hε)
  intro s t hst
  exact (hd (hst.trans_lt hNd)).le


lemma pathApprox_error_event {Ω : Type*} (X : Ω → C(unitInterval, ℝ))
    {N : ℕ} (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ) :
    {ω | δ ≤ dist (X ω) (pathApprox N (X ω))} ⊆
      {ω | ∃ s t : unitInterval, dist s t ≤ 1/(N : ℝ) ∧ δ/2 < |X ω s-X ω t|} := by
  intro ω hω
  by_contra hh
  change ¬∃ s t : unitInterval, dist s t ≤ 1/(N:ℝ) ∧ δ/2 < |X ω s-X ω t| at hh
  push Not at hh
  have hn := pathApprox_error_le hN (X ω) (by positivity : 0 ≤ δ/2) hh
  have hlt : dist (X ω) (pathApprox N (X ω)) < δ := by
    rw [dist_comm, dist_eq_norm]
    exact hn.trans_lt (half_lt_self hδ)
  exact not_lt_of_ge hω hlt

end FKCRT.TreeCoding
end

end OAI
