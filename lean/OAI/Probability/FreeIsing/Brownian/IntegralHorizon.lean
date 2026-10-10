import OAI.Probability.FreeIsing.Brownian.StoppedIsometry
import OAI.Probability.FreeIsing.Estimates.ContinuousHorizonGluing

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

omit mΩ in
theorem uniformGrid_nat_horizon {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (k i : ℕ) :
    BrownianGrid.uniformGrid (N : ℝ≥0) (N * k) i =
      BrownianGrid.uniformGrid (M : ℝ≥0) (M * k) i := by
  have hN0 : (N : ℝ≥0) ≠ 0 := by exact_mod_cast hN.ne'
  have hM0 : (M : ℝ≥0) ≠ 0 := by exact_mod_cast hM.ne'
  simp only [BrownianGrid.uniformGrid, Nat.cast_mul]
  by_cases hk : k = 0
  · simp [hk]
  · have hk0 : (k : ℝ≥0) ≠ 0 := by exact_mod_cast hk
    field_simp

omit mΩ in
theorem stoppedUniformSum_nat_horizon_le (B H : ℝ≥0 → Ω → ℝ)
    {N M : ℕ} (hN : 0 < N) (hNM : N ≤ M) {k : ℕ} (hk : 0 < k)
    {t : ℝ≥0} (ht : t ≤ (N : ℝ≥0)) :
    stoppedUniformSum B H N (N * k) t = stoppedUniformSum B H M (M * k) t := by
  have hM : 0 < M := hN.trans_le hNM
  have hg : BrownianGrid.uniformGrid (M : ℝ≥0) (M * k) =
      BrownianGrid.uniformGrid (N : ℝ≥0) (N * k) := by
    funext i
    exact uniformGrid_nat_horizon hM hN k i
  funext ω
  simp only [stoppedUniformSum, hg]
  apply Finset.sum_subset (Finset.range_mono (Nat.mul_le_mul_right k hNM))
  intro i hi hni
  have hindex : N * k ≤ i := Nat.le_of_not_gt (fun h => hni (Finset.mem_range.mpr h))
  have hta : t ≤ BrownianGrid.uniformGrid (N : ℝ≥0) (N * k) i := by
    apply ht.trans
    calc
      (N : ℝ≥0) = BrownianGrid.uniformGrid (N : ℝ≥0) (N * k) (N * k) :=
        (BrownianGrid.uniformGrid_end _ (Nat.mul_pos hN hk)).symm
      _ ≤ _ := BrownianGrid.uniformGrid_mono (N : ℝ≥0) (N * k) hindex
  have htb : t ≤ BrownianGrid.uniformGrid (N : ℝ≥0) (N * k) (i + 1) :=
    hta.trans (BrownianGrid.uniformGrid_mono _ _ (Nat.le_succ i))
  simp only [StoppedSimpleIntegral.intervalSum, min_eq_left hta, min_eq_left htb,
    sub_self, mul_zero]

omit mΩ in
theorem stoppedUniformSum_nat_horizon (B H : ℝ≥0 → Ω → ℝ)
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) {k : ℕ} (hk : 0 < k)
    {t : ℝ≥0} (htN : t ≤ (N : ℝ≥0)) (htM : t ≤ (M : ℝ≥0)) :
    stoppedUniformSum B H N (N * k) t = stoppedUniformSum B H M (M * k) t := by
  rcases le_total N M with hNM | hMN
  · exact stoppedUniformSum_nat_horizon_le B H hN hNM hk htN
  · exact (stoppedUniformSum_nat_horizon_le B H hM hMN hk htM).symm

theorem ae_eq_of_nat_horizon_meanSquare_limits
    (B H : ℝ≥0 → Ω → ℝ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    {t : ℝ≥0} (htN : t ≤ (N : ℝ≥0)) (htM : t ≤ (M : ℝ≥0))
    (hS2 : ∀ n, MemLp (stoppedUniformSum B H N n t) 2 P)
    {I J : Ω → ℝ} (hI : MemLp I 2 P) (hJ : MemLp J 2 P)
    (hlimI : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H N n t ω - I ω) ^ 2 ∂P) atTop (𝓝 0))
    (hlimJ : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H M n t ω - J ω) ^ 2 ∂P) atTop (𝓝 0)) :
    I =ᵐ[P] J := by
  have hsub (K : ℕ) (hK : 0 < K) :
      Tendsto (fun n : ℕ => K * (n + 1)) atTop atTop := by
    apply tendsto_atTop_mono (fun n => ?_) tendsto_id
    calc
      n ≤ n + 1 := Nat.le_succ n
      _ = 1 * (n + 1) := (one_mul _).symm
      _ ≤ K * (n + 1) := Nat.mul_le_mul_right _ hK
  apply BrownianGrid.ae_eq_of_mean_square_limits
    (fun n => hS2 (N * (n + 1))) hI hJ (hlimI.comp (hsub N hN))
  have hlim := hlimJ.comp (hsub M hM)
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only [Function.comp_def]
  rw [stoppedUniformSum_nat_horizon B H hN hM (Nat.succ_pos n) htN htM]

theorem exists_global_of_compatible_integer_martingales
    {F : Filtration ℝ≥0 mΩ} (L : ℕ → ℝ≥0 → Ω → ℝ)
    (hp : ∀ n, IsStronglyPredictable F (L n))
    (hM : ∀ n, Martingale (L n) F P)
    (hcont : ∀ n, ∀ᵐ ω ∂P, Continuous (fun t => L n t ω))
    (hcompat : ∀ (n m : ℕ) (t : ℝ≥0),
      t ≤ ((n + 1 : ℕ) : ℝ≥0) → t ≤ ((m + 1 : ℕ) : ℝ≥0) →
      L n t =ᵐ[P] L m t) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
      ∀ (n : ℕ) (t : ℝ≥0), t ≤ ((n + 1 : ℕ) : ℝ≥0) → I t =ᵐ[P] L n t := by
  have hlocal (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => L n t ω) (Iic (n : ℝ≥0)) :=
    (hcont n).mono (fun ω hω => hω.continuousOn)
  have hcompat' (n m : ℕ) (t : ℝ≥0) (hn : t ≤ (n : ℝ≥0)) (hm : t ≤ (m : ℝ≥0)) :
      L n t =ᵐ[P] L m t :=
    hcompat n m t (hn.trans (by exact_mod_cast Nat.le_succ n))
      (hm.trans (by exact_mod_cast Nat.le_succ m))
  let I := ContinuousHorizonGluing.glue L
  have hIp : IsStronglyPredictable F I :=
    ContinuousHorizonGluing.glue_isStronglyPredictable hp
  have hIc : ∀ᵐ ω ∂P, Continuous (fun t => I t ω) :=
    ContinuousHorizonGluing.ae_continuous_glue hlocal hcompat'
  have hIL (n : ℕ) (t : ℝ≥0) (ht : t ≤ ((n + 1 : ℕ) : ℝ≥0)) :
      I t =ᵐ[P] L n t := by
    obtain ⟨m, hm⟩ := exists_nat_ge t
    have heq : I t =ᵐ[P] L m t := by
      filter_upwards [ContinuousHorizonGluing.ae_all_glue_eq hlocal hcompat'] with ω hω
      exact hω m t hm
    exact heq.trans (hcompat m n t (hm.trans (by exact_mod_cast Nat.le_succ m)) ht)
  have hIM : Martingale I F P := by
    refine ⟨hIp.stronglyAdapted, fun s t hst => ?_⟩
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have ht : t ≤ ((n + 1 : ℕ) : ℝ≥0) := hn.trans (by exact_mod_cast Nat.le_succ n)
    exact (condExp_congr_ae (hIL n t ht)).trans
      (((hM n).condExp_ae_eq hst).trans (hIL n s (hst.trans ht)).symm)
  exact ⟨I, hIp, hIM, hIc, hIL⟩

theorem exists_global_continuous_uniform_integral
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hBc : ∀ᵐ ω ∂P, Continuous (fun t => B t ω))
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable F I ∧ Martingale I F P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => I t ω)) ∧
      (∀ t, MemLp (I t) 2 P) ∧ I 0 =ᵐ[P] 0 ∧
      (∀ t, (∫ ω, I t ω ∂P) = 0) ∧
      (∀ t, (∫ ω, (I t ω) ^ 2 ∂P) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ ω, (H s.toNNReal ω) ^ 2 ∂P) ∧
      (∀ (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ ω,
          (stoppedUniformSum B H N n t ω - I t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hS2 (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
      MemLp (stoppedUniformSum B H T n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H (BrownianGrid.uniformGrid T n i)) (fun i => hH _) (fun i => hH2 _)
      (Finset.range n) t
  have hex (n : ℕ) := exists_continuous_stopped_uniform_integral_isometry
    hB hAd hind hBc hH hc hC hb ((n + 1 : ℕ) : ℝ≥0)
  choose L hp hM hcont h2 hzero hmean hstop hiso hlim using hex
  have hcompat (n m : ℕ) (t : ℝ≥0)
      (hn : t ≤ ((n + 1 : ℕ) : ℝ≥0)) (hm : t ≤ ((m + 1 : ℕ) : ℝ≥0)) :
      L n t =ᵐ[P] L m t :=
    ae_eq_of_nat_horizon_meanSquare_limits (P := P) B H
      (N := n + 1) (M := m + 1) (Nat.succ_pos n) (Nat.succ_pos m)
      (t := t) hn hm (fun k => hS2 ((n + 1 : ℕ) : ℝ≥0) k t)
      (I := L n t) (J := L m t) (h2 n t) (h2 m t) (hlim n t) (hlim m t)
  obtain ⟨I, hIp, hIM, hIc, hIL⟩ :=
    exists_global_of_compatible_integer_martingales L hp hM hcont hcompat
  have hI2 (t : ℝ≥0) : MemLp (I t) 2 P := by
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (h2 n t).ae_eq (hIL n t (hn.trans (by exact_mod_cast Nat.le_succ n))).symm
  refine ⟨I, hIp, hIM, hIc, hI2,
    (hIL 0 0 (by simp)).trans (hzero 0), ?_, ?_, ?_⟩
  · intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact (integral_congr_ae (hIL n t (hn.trans (by exact_mod_cast Nat.le_succ n)))).trans
      (hmean n t)
  · intro t
    obtain ⟨n, hn⟩ := exists_nat_ge t
    have ht : t ≤ ((n + 1 : ℕ) : ℝ≥0) := hn.trans (by exact_mod_cast Nat.le_succ n)
    calc
      (∫ ω, I t ω ^ 2 ∂P) = ∫ ω, L n t ω ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hIL n t ht] with ω hω
        rw [hω]
      _ = _ := by simpa only [min_eq_left ht] using hiso n t
  · intro N hN t ht
    have hNs : N - 1 + 1 = N := Nat.sub_add_cancel hN
    have ht' : t ≤ ((N - 1 + 1 : ℕ) : ℝ≥0) := by simpa only [hNs] using ht
    have happrox := hlim (N - 1) t
    simp only [hNs] at happrox
    apply happrox.congr'
    apply Filter.Eventually.of_forall
    intro n
    apply integral_congr_ae
    filter_upwards [hIL (N - 1) t ht'] with ω hω
    rw [hω]

end Problem367.BrownianIntegralProcess

end

end OAI
