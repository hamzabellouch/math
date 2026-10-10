import OAI.Probability.FreeIsing.Brownian.RowComparisonConstruction

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.PredictableL2

theorem exists_centered_terminal_meanSquare_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (F : Filtration ℝ≥0 mΩ) (T : ℝ≥0) (X : ℕ → Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (htX : ∀ n, AEStronglyMeasurable[F T] (X n) P)
    (hzX : ∀ n, (∫ ω, X n ω ∂P) = 0)
    (hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, (X n ω - X k ω) ^ 2 ∂P) < ε) :
    ∃ Y : Ω → ℝ, Measurable Y ∧ AEStronglyMeasurable[F T] Y P ∧
      MemLp Y 2 P ∧ (∫ ω, Y ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, X n ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Y ω ^ 2 ∂P)) := by
  have hC : CauchySeq (fun n => (hX n).toLp (X n)) := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hc (ε ^ 2) (sq_pos_of_pos hε)
    refine ⟨N, fun n hn k hk => ?_⟩
    have heq : dist ((hX n).toLp (X n)) ((hX k).toLp (X k)) ^ 2 =
        ∫ ω, (X n ω - X k ω) ^ 2 ∂P := by
      rw [dist_eq_norm]
      exact norm_toLp_sq ((hX n).sub (hX k))
    have hsq := hN n hn k hk
    rw [← heq] at hsq
    nlinarith [dist_nonneg (x := (hX n).toLp (X n)) (y := (hX k).toLp (X k))]
  obtain ⟨Z, hZ⟩ := cauchySeq_tendsto_of_complete hC
  let Y : Ω → ℝ := Z
  have hY : MemLp Y 2 P := Lp.memLp Z
  have hlim : Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (hY.toLp Y)) := by
    simpa only [Y, Lp.toLp_coeFn] using hZ
  have htY : AEStronglyMeasurable[F T] Y P := by
    apply (isClosed_aestronglyMeasurable (F.le T)).mem_of_tendsto hZ
    exact Eventually.of_forall fun n => (htX n).congr (hX n).coeFn_toLp.symm
  refine ⟨Y, (Lp.stronglyMeasurable Z).measurable, htY, hY, ?_, ?_, ?_⟩
  · have h := (tendsto_const_nhds (x := (memLp_const (1 : ℝ)).toLp
        (fun _ : Ω => (1 : ℝ)))).inner (𝕜 := ℝ) hlim
    simp only [inner_toLp, one_mul, hzX] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  · have h := (hlim.sub (tendsto_const_nhds (x := hY.toLp Y))).norm.pow 2
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at h
    have heq (n : ℕ) : (∫ ω, (X n ω - Y ω) ^ 2 ∂P) =
        ‖(hX n).toLp (X n) - hY.toLp Y‖ ^ 2 :=
      (norm_toLp_sq ((hX n).sub hY)).symm
    simpa only [heq] using h
  · simpa only [norm_toLp_sq] using hlim.norm.pow 2

end Problem367.PredictableL2

namespace Problem367.BrownianArrayFiltration

theorem exists_integral_limit_of_row_energy_cauchy
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ℕ → ι → ℝ≥0 → Ω → ℝ)
    (hH : ∀ n a, StronglyAdapted F (H n a))
    (hcH : ∀ n a, ∀ᵐ ω ∂P, Continuous (fun t => H n a t ω))
    (C : ℕ → ι → ℝ) (hC : ∀ n a, 0 ≤ C n a)
    (hbH : ∀ n a, ∀ᵐ ω ∂P, ∀ t, |H n a t ω| ≤ C n a)
    (T : ℝ≥0)
    (he : ∀ n, Summable fun a => ∫ t in (0 : ℝ)..(T : ℝ),
      ∫ ω, H n a t.toNNReal ω ^ 2 ∂P)
    (hCauchy : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, (H n a t.toNNReal ω - H k a t.toNNReal ω) ^ 2 ∂P) < ε) :
    ∃ (I : ℕ → ι → Ω → ℝ) (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ),
      (∀ n a, MemLp (I n a) 2 P) ∧
      (∀ n a, Tendsto (fun k => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H n a) T k ω - I n a ω) ^ 2 ∂P)
          atTop (𝓝 0)) ∧
      (∀ n, Measurable (Y n)) ∧
      (∀ n, AEStronglyMeasurable[F T] (Y n) P) ∧
      (∀ n, MemLp (Y n) 2 P) ∧
      (∀ n, (∫ ω, Y n ω ∂P) = 0) ∧
      (∀ n, (∫ ω, Y n ω ^ 2 ∂P) =
        ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H n a t.toNNReal ω ^ 2 ∂P) ∧
      (∀ n, Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ a ∈ s, I n a ω) - Y n ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      (∀ n k, (∫ ω, (Y n ω - Y k ω) ^ 2 ∂P) =
        ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ ω, (H n a t.toNNReal ω - H k a t.toNNReal ω) ^ 2 ∂P) ∧
      Measurable Z ∧ AEStronglyMeasurable[F T] Z P ∧ MemLp Z 2 P ∧
      (∫ ω, Z ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0) ∧
      Tendsto (fun n => ∑' a, ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ ω, H n a t.toNNReal ω ^ 2 ∂P) atTop (𝓝 (∫ ω, Z ω ^ 2 ∂P)) := by
  have hex (n : ℕ) := exists_infinite_integral hB hAd hind hcross
    (H n) (hH n) (hcH n) (C n) (hC n) (hbH n) T (he n)
  choose I Y hI haI hmY htY hY hzY heY hsY using hex
  have hpair (n k : ℕ) := infinite_row_difference_isometry_of_row_energies
    hB hAd hind (H n) (H k) (hH n) (hH k) (hcH n) (hcH k)
    (C n) (C k) (hC n) (hC k) (hbH n) (hbH k) T (he n) (he k)
    hcross (hI n) (hI k) (haI n) (haI k) (hY n) (hY k) (hsY n) (hsY k)
  have hc : ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∀ k ≥ N,
      (∫ ω, (Y n ω - Y k ω) ^ 2 ∂P) < ε := by
    simpa only [hpair] using hCauchy
  obtain ⟨Z, hmZ, htZ, hZ, hzZ, haZ, heZ⟩ :=
    PredictableL2.exists_centered_terminal_meanSquare_limit F T Y hY htY hzY hc
  refine ⟨I, Y, Z, hI, haI, hmY, htY, hY, hzY, heY, hsY, hpair,
    hmZ, htZ, hZ, hzZ, haZ, ?_⟩
  simpa only [heY] using heZ

end Problem367.BrownianArrayFiltration

end

end OAI
