import OAI.Probability.FreeIsing.Brownian.ArrayIntegralCompletion

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators

namespace Problem367.BrownianArrayFiltration

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ι → ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

theorem coordinate_increment_indep_past {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (a : ι) :
    Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance)
      (F s) P := by
  have hm : Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω => B a t ω - B a s ω) :=
    (measurable_pi_apply a).comp (show Measurable[
      MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance]
      (fun ω a => B a t ω - B a s ω) from measurable_iff_comap_le.mpr le_rfl)
  exact indep_of_indep_of_le_left hind hm.comap_le

theorem coefficients_indep_increments {s t : ℝ≥0}
    (hind : Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    {H : ι → Ω → ℝ} (hH : ∀ a, StronglyMeasurable[F s] (H a)) :
    IndepFun (fun ω a => H a ω) (fun ω a => B a t ω - B a s ω) P := by
  have hm : Measurable[F s] (fun ω a => H a ω) := by
    let : MeasurableSpace Ω := F s
    exact Measurable.of_eval fun a => (hH a).measurable
  exact indep_of_indep_of_le_left hind.symm hm.comap_le

theorem grid_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 P) :
    Pairwise fun p q : ι × ℕ => ∫ ω,
      (H p.1 p.2 ω * (B p.1 (t (p.2 + 1)) ω - B p.1 (t p.2) ω)) *
      (H q.1 q.2 ω * (B q.1 (t (q.2 + 1)) ω - B q.1 (t q.2) ω)) ∂P = 0 := by
  let G : Filtration ℕ mΩ :=
    ⟨fun k => F (t k), fun _ _ h => F.mono (ht h), fun k => F.le (t k)⟩
  let D : ι → ℕ → Ω → ℝ := fun a k ω => B a (t (k + 1)) ω - B a (t k) ω
  have hD2 (a : ι) (k : ℕ) : MemLp (D a k) 2 P :=
    ((hB a).isGaussianProcess.hasGaussianLaw_eval (t (k + 1))).memLp_two.sub
      ((hB a).isGaussianProcess.hasGaussianLaw_eval (t k)).memLp_two
  have hi (k : ℕ) : IndepFun (fun ω a => H a k ω) (fun ω a => D a k ω) P :=
    coefficients_indep_increments (hind _ _ (ht (Nat.le_succ k))) (fun a => hH a k)
  have hHD (a : ι) (k : ℕ) : MemLp (fun ω => H a k ω * D a k ω) 2 P :=
    PredictableL2.memLp_two_mul_of_indep
      ((hi k).comp (measurable_pi_apply a) (measurable_pi_apply a)) (hH2 a k) (hD2 a k)
  have hz (a : ι) (k : ℕ) : (∫ ω, D a k ω ∂P) = 0 := by
    change (∫ ω, B a (t (k + 1)) ω - B a (t k) ω ∂P) = 0
    rw [integral_sub ((hB a).integrable_eval _) ((hB a).integrable_eval _),
      (hB a).integral_eval, (hB a).integral_eval, sub_self]
  have hnoise (k : ℕ) : Pairwise fun a b => ∫ ω, D a k ω * D b k ω ∂P = 0 := by
    intro a b hab
    have heq := (hcross _ _ (ht (Nat.le_succ k)) hab).integral_fun_mul_eq_mul_integral
      (hD2 a k).aestronglyMeasurable (hD2 b k).aestronglyMeasurable
    change (∫ ω, D a k ω * D b k ω ∂P) =
      (∫ ω, D a k ω ∂P) * ∫ ω, D b k ω ∂P at heq
    simpa only [hz, zero_mul] using heq
  apply SimpleIntegral.predictable_array_increments_orthogonal G H D hH
  · intro a k
    exact (hAd a (t (k + 1))).sub
      ((hAd a (t k)).mono (F.mono (ht (Nat.le_succ k))))
  · exact fun a k => (hD2 a k).integrable (by norm_num)
  · exact hHD
  · intro a k
    exact BrownianFiltration.increment_condExp_zero (hB a) (hAd a)
      (coordinate_increment_indep_past (hind _ _ (ht (Nat.le_succ k))) a)
  · intro k
    exact PredictableL2.weighted_array_orthogonal (hi k) (fun a => hH2 a k)
      (fun a => hD2 a k) (hnoise k)

theorem grid_sums_orthogonal [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : ι → ℕ → Ω → ℝ)
    (hH : ∀ a k, StronglyMeasurable[F (t k)] (H a k))
    (hH2 : ∀ a k, MemLp (H a k) 2 P)
    {a b : ι} (hab : a ≠ b) (u v : Finset ℕ) :
    (∫ ω, (∑ k ∈ u, H a k ω * (B a (t (k + 1)) ω - B a (t k) ω)) *
      (∑ k ∈ v, H b k ω * (B b (t (k + 1)) ω - B b (t k) ω)) ∂P) = 0 := by
  have hHD (a : ι) (k : ℕ) : MemLp
      (fun ω => H a k ω * (B a (t (k + 1)) ω - B a (t k) ω)) 2 P :=
    BrownianFiltration.predictable_mul_memLp_two (hB a)
      (coordinate_increment_indep_past (hind _ _ (ht (Nat.le_succ k))) a)
      (hH a k) (hH2 a k)
  apply SimpleIntegral.integral_mul_sums_eq_zero
    (fun k ω => H a k ω * (B a (t (k + 1)) ω - B a (t k) ω))
    (fun k ω => H b k ω * (B b (t (k + 1)) ω - B b (t k) ω))
    (hHD a) (hHD b) _ u v
  intro k l
  exact grid_orthogonal hB hAd hind hcross t ht H hH hH2
    (show (a, k) ≠ (b, l) from fun h => hab (congrArg Prod.fst h))

theorem exists_channel_integrals [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a) (T : ℝ≥0) :
    ∃ I : ι → Ω → ℝ,
      (∀ a, MemLp (I a) 2 P) ∧
      (∀ a, StronglyMeasurable (I a)) ∧
      (∀ a, AEStronglyMeasurable[F T] (I a) P) ∧
      (∀ a, (∫ ω, I a ω ∂P) = 0) ∧
      (∀ a, (∫ ω, I a ω ^ 2 ∂P) =
        ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P) ∧
      (Pairwise fun a b => ∫ ω, I a ω * I b ω ∂P = 0) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  have hi (a : ι) (s t : ℝ≥0) (hst : s ≤ t) :
      Indep (MeasurableSpace.comap (fun ω => B a t ω - B a s ω) inferInstance) (F s) P :=
    coordinate_increment_indep_past (hind s t hst) a
  have hmH (a : ι) (t : ℝ≥0) : AEStronglyMeasurable (H a t) P :=
    ((hH a t).mono (F.le t)).aestronglyMeasurable
  have hH2 (a : ι) (t : ℝ≥0) : MemLp (H a t) 2 P := by
    apply MemLp.of_bound (hmH a t) (C a)
    filter_upwards [hb a] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hex (a : ι) := BrownianFiltrationGrid.exists_uniformSumLp_limit
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T
    (fun _ hε => MeanSquareContinuity.uniform_integral_sq_sub_le
      (hmH a) (hc a) (hC a) (hb a) T hε)
  choose I hI using hex
  have hprop (a : ι) := BrownianFiltrationGrid.uniformSumLp_limit_terminal_centered
    (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)
  refine ⟨fun a => I a, fun a => Lp.memLp (I a), fun a => Lp.stronglyMeasurable (I a),
    fun a => (hprop a).1, fun a => (hprop a).2, ?_, ?_, ?_⟩
  · intro a
    exact BrownianFiltrationGrid.uniformSumLp_limit_isometry
      (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) (hc a) (hC a) (hb a) T (hI a)
  · intro a b hab
    have hlim := (hI a).inner (𝕜 := ℝ) (hI b)
    have hz (n : ℕ) : inner ℝ
        (BrownianFiltrationGrid.uniformSumLp (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T n)
        (BrownianFiltrationGrid.uniformSumLp (hB b) (hAd b) (hi b) (H b) (hH b) (hH2 b) T n) = 0 := by
      rw [BrownianFiltrationGrid.uniformSumLp, BrownianFiltrationGrid.uniformSumLp,
        PredictableL2.inner_toLp]
      exact grid_sums_orthogonal hB hAd hind hcross
        (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
        (fun a k => H a (BrownianGrid.uniformGrid T n k))
        (fun a k => hH a _) (fun a k => hH2 a _) hab (Finset.range n) (Finset.range n)
    have heq : inner ℝ (I a) (I b) = 0 :=
      tendsto_nhds_unique hlim (by simpa only [hz] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
    rw [L2.inner_def] at heq
    simpa only [Real.inner_apply] using heq
  · intro a
    exact BrownianFiltrationGrid.integral_sq_error_tendsto_of_Lp_tendsto
      (hB a) (hAd a) (hi a) (H a) (hH a) (hH2 a) T (hI a)

theorem exists_infinite_integral [IsProbabilityMeasure P]
    (hB : ∀ a, IsPreBrownianReal (B a) P)
    (hAd : ∀ a, StronglyAdapted F (B a))
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω a => B a t ω - B a s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun a b =>
      IndepFun (fun ω => B a t ω - B a s ω) (fun ω => B b t ω - B b s ω) P)
    (H : ι → ℝ≥0 → Ω → ℝ) (hH : ∀ a, StronglyAdapted F (H a))
    (hc : ∀ a, ∀ᵐ ω ∂P, Continuous (fun t => H a t ω))
    (C : ι → ℝ) (hC : ∀ a, 0 ≤ C a)
    (hb : ∀ a, ∀ᵐ ω ∂P, ∀ t, |H a t ω| ≤ C a) (T : ℝ≥0)
    (henergy : Summable fun a =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P) :
    ∃ (I : ι → Ω → ℝ) (Y : Ω → ℝ),
      (∀ a, MemLp (I a) 2 P) ∧
      (∀ a, Tendsto (fun n => ∫ ω,
        (BrownianGrid.uniformSum (B a) (H a) T n ω - I a ω) ^ 2 ∂P) atTop (𝓝 0)) ∧
      Measurable Y ∧ AEStronglyMeasurable[F T] Y P ∧ MemLp Y 2 P ∧
      (∫ ω, Y ω ∂P) = 0 ∧
      (∫ ω, Y ω ^ 2 ∂P) =
        ∑' a, ∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, H a t.toNNReal ω ^ 2 ∂P ∧
      Tendsto (fun s : Finset ι => ∫ ω,
        ((∑ a ∈ s, I a ω) - Y ω) ^ 2 ∂P) atTop (𝓝 0) := by
  obtain ⟨I, hI2, _, hIterm, hz, hiso, horth, happrox⟩ :=
    exists_channel_integrals hB hAd hind hcross H hH hc C hC hb T
  obtain ⟨Y, hY, hmY, hsY, heY⟩ := PredictableL2.exists_orthogonal_sum I hI2 horth
    (by simpa only [hiso] using henergy)
  have hsumterm (s : Finset ι) :
      AEStronglyMeasurable[F T] (fun ω => ∑ a ∈ s, I a ω) P := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (stronglyMeasurable_const.aestronglyMeasurable :
          AEStronglyMeasurable[F T] (fun _ : Ω => (0 : ℝ)) P)
    | @insert a s has ih =>
        simpa only [Finset.sum_insert has, Pi.add_def] using (hIterm a).add ih
  have htermLp : AEStronglyMeasurable[F T] (hY.toLp Y : Ω → ℝ) P := by
    apply (isClosed_aestronglyMeasurable (F.le T)).mem_of_tendsto hsY
    apply Filter.Eventually.of_forall
    intro s
    change AEStronglyMeasurable[F T] (↑(∑ a ∈ s, (hI2 a).toLp (I a)) : Ω → ℝ) P
    rw [← PredictableL2.toLp_finsetSum I hI2 s]
    exact (hsumterm s).congr (MemLp.coeFn_toLp _).symm
  have hterminal : AEStronglyMeasurable[F T] Y P := htermLp.congr hY.coeFn_toLp
  refine ⟨I, Y, hI2, happrox, hmY, hterminal, hY, ?_, ?_, ?_⟩
  · exact PredictableL2.integral_eq_zero_of_hasSum I hI2 hY hsY hz
  · simpa only [hiso] using heY
  · exact PredictableL2.tendsto_integral_sq_error_of_hasSum I hI2 hY hsY

end Problem367.BrownianArrayFiltration

end

end OAI
