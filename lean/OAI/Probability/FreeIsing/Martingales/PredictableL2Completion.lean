import OAI.Probability.FreeIsing.Brownian.SimpleIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

namespace Problem367.PredictableL2

theorem summable_of_orthogonal_sq
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2) : Summable f := by
  let V : ι → Submodule ℝ E := fun i => Submodule.span ℝ {f i}
  have hV : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) := by
    apply OrthogonalFamily.of_pairwise
    intro i j hij
    change (V i) ⟂ (V j)
    simpa only [V, Submodule.isOrtho_span, Set.mem_singleton_iff,
      forall_eq] using horth hij
  let x : (i : ι) → V i := fun i => ⟨f i, Submodule.mem_span_singleton_self (f i)⟩
  exact (hV.summable_iff_norm_sq_summable x).mpr hsum

theorem norm_tsum_sq_of_orthogonal
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : ι → E)
    (horth : Pairwise fun i j => inner ℝ (f i) (f j) = 0)
    (hsum : Summable fun i => ‖f i‖ ^ 2) :
    ‖∑' i, f i‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  classical
  have hf := summable_of_orthogonal_sq f horth hsum
  have hfinite (s : Finset ι) : ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_eq_single i]
    · exact real_inner_self_eq_norm_sq (f i)
    · intro j hj hji
      exact horth hji
    · exact fun h => (h hi).elim
  have hn := (hf.hasSum.norm).pow 2
  simp_rw [hfinite] at hn
  exact tendsto_nhds_unique hn hsum.hasSum

theorem inner_toLp {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ ω, f ω * g ω ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω hfω hgω
  simp only [hfω, hgω, Real.inner_apply]

theorem norm_toLp_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ ω, f ω ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  simp only [sq]

theorem toLp_finsetSum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ) (s : Finset ι) :
    (memLp_finsetSum s (fun i _ => hf i)).toLp (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, (hf i).toLp (f i) := by
  apply Lp.ext
  apply (MemLp.coeFn_toLp _).trans
  apply Filter.EventuallyEq.symm
  apply (Lp.coeFn_fun_finsetSum s (fun i => (hf i).toLp (f i))).trans
  have heq : ∀ᵐ ω ∂μ, ∀ i ∈ s, (hf i).toLp (f i) ω = f i ω :=
    (Filter.eventually_all_finite s.finite_toSet).mpr (fun i _ => (hf i).coeFn_toLp)
  filter_upwards [heq] with ω hω
  exact Finset.sum_congr rfl (fun i hi => hω i hi)

theorem exists_orthogonal_sum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (horth : Pairwise fun i j => ∫ ω, f i ω * f j ω ∂μ = 0)
    (henergy : Summable fun i => ∫ ω, f i ω ^ 2 ∂μ) :
    ∃ (Y : Ω → ℝ) (hY : MemLp Y 2 μ), Measurable Y ∧
      HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y) ∧
      (∫ ω, Y ω ^ 2 ∂μ) = ∑' i, ∫ ω, f i ω ^ 2 ∂μ := by
  let F : ι → Lp ℝ 2 μ := fun i => (hf i).toLp (f i)
  have hForth : Pairwise fun i j => inner ℝ (F i) (F j) = 0 := by
    intro i j hij
    exact (inner_toLp (hf i) (hf j)).trans (horth hij)
  have hFenergy : Summable fun i => ‖F i‖ ^ 2 := by
    simpa only [F, norm_toLp_sq] using henergy
  have hFsum := summable_of_orthogonal_sq F hForth hFenergy
  let Y : Lp ℝ 2 μ := ∑' i, F i
  refine ⟨Y, (Lp.memLp Y), (Lp.stronglyMeasurable Y).measurable, ?_, ?_⟩
  · simpa only [Lp.toLp_coeFn] using hFsum.hasSum
  · rw [← norm_toLp_sq (Lp.memLp Y), Lp.toLp_coeFn]
    exact (norm_tsum_sq_of_orthogonal F hForth hFenergy).trans
      (by simp only [F, norm_toLp_sq])

theorem orthogonal_sum_unique
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y))
    (hZsum : HasSum (fun i => (hf i).toLp (f i)) (hZ.toLp Z)) :
    Y =ᵐ[μ] Z :=
  (hY.toLp_eq_toLp_iff hZ).mp (hYsum.unique hZsum)

theorem tendsto_integral_sq_error_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    Tendsto (fun s : Finset ι => ∫ ω, ((∑ i ∈ s, f i ω) - Y ω) ^ 2 ∂μ)
      atTop (𝓝 0) := by
  have h := ((hYsum.sub_const (hY.toLp Y)).norm).pow 2
  change Tendsto _ atTop _ at h
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
  convert h using 1
  funext s
  calc
    _ = ‖((memLp_finsetSum s (fun i _ => hf i)).sub hY).toLp
        ((fun ω => ∑ i ∈ s, f i ω) - Y)‖ ^ 2 :=
      (norm_toLp_sq ((memLp_finsetSum s (fun i _ => hf i)).sub hY)).symm
    _ = _ := by
      change ‖(memLp_finsetSum s (fun i _ => hf i)).toLp
        (fun ω => ∑ i ∈ s, f i ω) - hY.toLp Y‖ ^ 2 = _
      rw [toLp_finsetSum]

theorem hasSum_integral_mul_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y Z : Ω → ℝ} (hY : MemLp Y 2 μ) (hZ : MemLp Z 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y)) :
    HasSum (fun i => ∫ ω, Z ω * f i ω ∂μ) (∫ ω, Z ω * Y ω ∂μ) := by
  have h := hYsum.mapL (innerSL ℝ (hZ.toLp Z))
  change HasSum (fun i => inner ℝ (hZ.toLp Z) ((hf i).toLp (f i)))
    (inner ℝ (hZ.toLp Z) (hY.toLp Y)) at h
  simpa only [inner_toLp] using h

theorem integral_eq_zero_of_hasSum
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (f : ι → Ω → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    {Y : Ω → ℝ} (hY : MemLp Y 2 μ)
    (hYsum : HasSum (fun i => (hf i).toLp (f i)) (hY.toLp Y))
    (hcenter : ∀ i, ∫ ω, f i ω ∂μ = 0) : ∫ ω, Y ω ∂μ = 0 := by
  have h := hasSum_integral_mul_of_hasSum f hf hY
    (memLp_const (1 : ℝ)) hYsum
  simp only [one_mul, hcenter] at h
  exact h.unique hasSum_zero

section Predictable

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (ℱ : Filtration ℕ mΩ) (H D : ℕ → Ω → ℝ) (v : ℕ → ℝ)
    (hH : ∀ i, StronglyMeasurable[ℱ i] (H i))
    (hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i))
    (hD2 : ∀ i, MemLp (D i) 2 μ)
    (hHD : ∀ i, MemLp (fun ω => H i ω * D i ω) 2 μ)
    (hzero : ∀ i, μ[D i | ℱ i] =ᵐ[μ] 0)
    (hvar : ∀ i, μ[(fun ω => D i ω ^ 2) | ℱ i] =ᵐ[μ] fun _ => v i)

include hH hD hD2 hzero hvar in

theorem exists_predictable_sum
    (henergy : Summable fun i => v i * ∫ ω, H i ω ^ 2 ∂μ) :
    ∃ (Y : Ω → ℝ) (hY : MemLp Y 2 μ), Measurable Y ∧
      HasSum (fun i => (hHD i).toLp (fun ω => H i ω * D i ω)) (hY.toLp Y) ∧
      (∫ ω, Y ω ^ 2 ∂μ) = ∑' i, v i * ∫ ω, H i ω ^ 2 ∂μ := by
  have horth : Pairwise fun i j =>
      ∫ ω, (H i ω * D i ω) * (H j ω * D j ω) ∂μ = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · exact SimpleIntegral.predictable_increments_orthogonal ℱ H D hH hD
        (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hij
    · simpa only [mul_comm] using
        SimpleIntegral.predictable_increments_orthogonal ℱ H D hH hD
          (fun i => (hD2 i).integrable (by norm_num)) hHD hzero hji
  have hsecond (i : ℕ) :
      (∫ ω, (H i ω * D i ω) ^ 2 ∂μ) = v i * ∫ ω, H i ω ^ 2 ∂μ :=
    SimpleIntegral.integral_sq_mul_of_condExp_sq (ℱ.le i) (hH i)
      (hD2 i).integrable_sq (hHD i).integrable_sq (hvar i)
  obtain ⟨Y, hY, hmY, hsY, hiY⟩ := exists_orthogonal_sum
    (fun i ω => H i ω * D i ω) hHD horth (by simpa only [hsecond] using henergy)
  exact ⟨Y, hY, hmY, hsY, by simpa only [hsecond] using hiY⟩

end Predictable

theorem exists_preBrownian_predictable_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hm : ∀ t, StronglyMeasurable (B t))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[Filtration.natural B hm (t i)] (H i))
    (hH2 : ∀ i, MemLp (H i) 2 P)
    (henergy : Summable fun i =>
      ((t (i + 1) : ℝ) - (t i : ℝ)) * ∫ ω, H i ω ^ 2 ∂P) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ MemLp Y 2 P ∧
      (∫ ω, Y ω ∂P) = 0 ∧
      (∫ ω, Y ω ^ 2 ∂P) =
        ∑' i, ((t (i + 1) : ℝ) - (t i : ℝ)) * ∫ ω, H i ω ^ 2 ∂P ∧
      Tendsto (fun s : Finset ℕ => ∫ ω,
        ((∑ i ∈ s, H i ω * (B (t (i + 1)) ω - B (t i) ω)) - Y ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let ℱ : Filtration ℕ mΩ :=
    ⟨fun i => Filtration.natural B hm (t i),
      fun _ _ hij => (Filtration.natural B hm).mono (ht hij),
      fun i => (Filtration.natural B hm).le (t i)⟩
  let D : ℕ → Ω → ℝ := fun i ω => B (t (i + 1)) ω - B (t i) ω
  have hD : ∀ i, StronglyMeasurable[ℱ (i + 1)] (D i) := by
    intro i
    exact (Filtration.stronglyAdapted_natural hm (t (i + 1))).sub
      ((Filtration.stronglyAdapted_natural hm (t i)).mono
        ((Filtration.natural B hm).mono (ht (Nat.le_succ i))))
  have hD2 : ∀ i, MemLp (D i) 2 P := by
    intro i
    exact (hB.isGaussianProcess.hasGaussianLaw_eval (t (i + 1))).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval (t i)).memLp_two
  have hHD : ∀ i, MemLp (fun ω => H i ω * D i ω) 2 P := fun i =>
    preBrownian_predictable_mul_memLp_two hB hm (ht (Nat.le_succ i)) (hH i) (hH2 i)
  have hz : ∀ i, P[D i | ℱ i] =ᵐ[P] 0 := fun i =>
    preBrownian_increment_condExp_zero hB hm (ht (Nat.le_succ i))
  obtain ⟨Y, hY, hmY, hsY, hiY⟩ := exists_predictable_sum ℱ H D
    (fun i => (t (i + 1) : ℝ) - (t i : ℝ)) hH hD hD2 hHD hz
    (fun i => preBrownian_increment_sq_condExp hB hm (ht (Nat.le_succ i))) henergy
  refine ⟨Y, hmY, hY, ?_, hiY, ?_⟩
  · apply integral_eq_zero_of_hasSum (fun i ω => H i ω * D i ω) hHD hY hsY
    intro i
    exact SimpleIntegral.integral_mul_eq_zero_of_condExp_eq_zero (ℱ.le i) (hH i)
      ((hD2 i).integrable (by norm_num)) ((hHD i).integrable (by norm_num)) (hz i)
  · exact tendsto_integral_sq_error_of_hasSum (fun i ω => H i ω * D i ω) hHD hY hsY

end Problem367.PredictableL2

end

end OAI
