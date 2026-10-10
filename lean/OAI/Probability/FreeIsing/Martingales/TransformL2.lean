import OAI.Probability.FreeIsing.Stochastic.SimpleIntegralIsometry

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Problem367.MartingaleTransformL2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem condExp_increment_zero [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t) :
    μ[(fun ω => M t ω - M s ω) | F s] =ᵐ[μ] fun _ => 0 := by
  change μ[M t - M s | F s] =ᵐ[μ] fun _ => 0
  have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (F s)
  have hs := hM.condExp_ae_eq (le_refl s)
  filter_upwards [hsub, hM.condExp_ae_eq hst, hs] with ω hω htω hsω
  simpa only [Pi.sub_apply, htω, hsω, sub_self] using hω

theorem bounded_mul_memLp_two {H D : Ω → ℝ} {K : ℝ}
    (hH : AEStronglyMeasurable H μ) (hD : MemLp D 2 μ)
    (hbound : ∀ᵐ ω ∂μ, |H ω| ≤ K) :
    MemLp (fun ω => H ω * D ω) 2 μ := by
  apply hD.of_le_mul (c := K) (hH.mul hD.aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, Pi.mul_apply, abs_mul] using
    mul_le_mul_of_nonneg_right hω (abs_nonneg (D ω))

theorem integral_sq_transform [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) =
      ∑ i ∈ s, ∫ ω, (H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ := by
  let D : ℕ → Ω → ℝ := fun i ω => M (i + 1) ω - M i ω
  have hD (i : ℕ) : StronglyMeasurable[F (i + 1)] (D i) :=
    (hM.stronglyMeasurable (i + 1)).sub
      ((hM.stronglyMeasurable i).mono (F.mono (Nat.le_succ i)))
  have hD2 (i : ℕ) : MemLp (D i) 2 μ := (hM2 (i + 1)).sub (hM2 i)
  have hHD (i : ℕ) : MemLp (fun ω => H i ω * D i ω) 2 μ :=
    bounded_mul_memLp_two ((hH i).mono (F.le i)).aestronglyMeasurable
      (hD2 i) (hbound i)
  have hzero (i : ℕ) : μ[D i | F i] =ᵐ[μ] 0 :=
    condExp_increment_zero hM (Nat.le_succ i)
  apply SimpleIntegral.integral_sq_sum_of_orthogonal s (fun i ω => H i ω * D i ω)
  · intro i hi j hj
    exact (hHD i).integrable_mul (hHD j)
  · intro i hi j hj hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal F H D hH hD
        (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal F H D hH hD
          (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hji

theorem sum_integral_sq_increment [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∫ ω, (M (i + 1) ω - M i ω) ^ 2 ∂μ) =
      ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  have h := integral_sq_transform hM hM2
    (H := fun _ _ => (1 : ℝ)) (fun _ => stronglyMeasurable_const)
    (K := 1) (fun _ => Filter.Eventually.of_forall (fun _ => by simp))
    (Finset.range n)
  simp only [one_mul] at h
  rw [← h]
  congr 1
  funext ω
  congr 1
  clear h
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem integral_sq_transform_le [IsFiniteMeasure μ]
    {F : Filtration ℕ mΩ} {M H : ℕ → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ i, MemLp (M i) 2 μ)
    (hH : StronglyAdapted F H) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, (M n ω - M 0 ω) ^ 2 ∂μ := by
  rw [integral_sq_transform hM hM2 hH hbound,
    ← sum_integral_sq_increment hM hM2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hD2 := (hM2 (i + 1)).sub (hM2 i)
  have hHD := bounded_mul_memLp_two
    ((hH i).mono (F.le i)).aestronglyMeasurable hD2 (hbound i)
  rw [← integral_const_mul]
  apply integral_mono_ae hHD.integrable_sq (hD2.integrable_sq.const_mul (K ^ 2))
  filter_upwards [hbound i] with ω hω
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 hω

theorem integral_sq_increment_eq [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) =
      (∫ ω, M t ω ^ 2 ∂μ) - ∫ ω, M s ω ^ 2 ∂μ := by
  have hD2 : MemLp (fun ω => M t ω - M s ω) 2 μ := ht2.sub hs2
  have hcross : Integrable (fun ω => M s ω * (M t ω - M s ω)) μ :=
    hs2.integrable_mul hD2
  have horth : (∫ ω, M s ω * (M t ω - M s ω) ∂μ) = 0 :=
    SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (F.le s)
      (hM.stronglyMeasurable s) (hD2.integrable (by norm_num)) hcross
      (condExp_increment_zero hM hst)
  have heq : (∫ ω, M t ω ^ 2 ∂μ) =
      (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) +
        2 * (∫ ω, M s ω * (M t ω - M s ω) ∂μ) +
          ∫ ω, M s ω ^ 2 ∂μ := by
    calc
      _ = ∫ ω, (M t ω - M s ω) ^ 2 +
          2 * (M s ω * (M t ω - M s ω)) + M s ω ^ 2 ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by ring)
      _ = _ := by
        have h1 := integral_add hD2.integrable_sq (hcross.const_mul 2)
        have h2 := integral_add (hD2.integrable_sq.add (hcross.const_mul 2)) hs2.integrable_sq
        simp only [Pi.add_apply] at h1 h2
        rw [h1, integral_const_mul] at h2
        exact h2
  rw [horth] at heq
  linarith

theorem integral_sq_increment_le [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) {s t : ι} (hst : s ≤ t)
    (hs2 : MemLp (M s) 2 μ) (ht2 : MemLp (M t) 2 μ) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂μ) ≤ ∫ ω, M t ω ^ 2 ∂μ := by
  rw [integral_sq_increment_eq hM hst hs2 ht2]
  exact sub_le_self _ (integral_nonneg (fun ω => sq_nonneg _))

theorem integral_sq_grid_transform_le_terminal [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ} {M : ι → Ω → ℝ}
    (hM : Martingale M F μ) (hM2 : ∀ t, MemLp (M t) 2 μ)
    (t : ℕ → ι) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[F (t i)] (H i)) {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |H i ω| ≤ K) (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * (M (t (i + 1)) ω - M (t i) ω)) ^ 2 ∂μ) ≤
      K ^ 2 * ∫ ω, M (t n) ω ^ 2 ∂μ := by
  let G : Filtration ℕ mΩ :=
    ⟨fun i => F (t i), fun _ _ hij => F.mono (ht hij), fun i => F.le (t i)⟩
  have hMG : Martingale (fun i => M (t i)) G μ :=
    ⟨by intro i; exact hM.stronglyMeasurable (t i),
      by intro i j hij; exact hM.condExp_ae_eq (ht hij)⟩
  exact (integral_sq_transform_le hMG (fun i => hM2 (t i)) hH hK hbound n).trans
    (mul_le_mul_of_nonneg_left
      (integral_sq_increment_le hM (ht (Nat.zero_le n)) (hM2 _) (hM2 _)) (sq_nonneg K))

theorem tendsto_integral_sq_grid_transform [IsFiniteMeasure μ]
    {ι : Type*} [Preorder ι] {F : Filtration ι mΩ}
    {M : ℕ → ι → Ω → ℝ} (hM : ∀ k, Martingale (M k) F μ)
    (hM2 : ∀ k t, MemLp (M k t) 2 μ) (t : ℕ → ℕ → ι)
    (ht : ∀ k, Monotone (t k)) (N : ℕ → ℕ) {T : ι}
    (hterminal : ∀ k, t k (N k) = T) (H : ℕ → ℕ → Ω → ℝ)
    (hH : ∀ k i, StronglyMeasurable[F (t k i)] (H k i))
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ k i, ∀ᵐ ω ∂μ, |H k i ω| ≤ K)
    (hlim : Tendsto (fun k => ∫ ω, M k T ω ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (∑ i ∈ Finset.range (N k),
      H k i ω * (M k (t k (i + 1)) ω - M k (t k i) ω)) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun k => integral_nonneg (fun ω => sq_nonneg _))
    (fun k => ?_) (by simpa using hlim.const_mul (K ^ 2))
  simpa only [hterminal k] using
    integral_sq_grid_transform_le_terminal (hM k) (hM2 k) (t k) (ht k)
      (H k) (hH k) hK (hbound k) (N k)

end Problem367.MartingaleTransformL2

end

end OAI
