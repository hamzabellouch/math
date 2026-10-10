import OAI.Probability.FreeIsing.Brownian.ContinuousIntegral
import OAI.Probability.FreeIsing.Stochastic.IntegralAssociativityLimit

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*}

theorem stopped_sum_at_grid (B : ℝ≥0 → Ω → ℝ)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (H : ℕ → Ω → ℝ)
    {n j : ℕ} (hj : j ≤ n) :
    (fun ω => ∑ i ∈ Finset.range n,
      StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) (τ j) ω) =
      BrownianGrid.integralSum B τ H j := by
  funext ω
  calc
    _ = ∑ i ∈ Finset.range j,
        StoppedSimpleIntegral.intervalSum B (H i) (τ i) (τ (i + 1)) (τ j) ω := by
      symm
      apply Finset.sum_subset (Finset.range_mono hj)
      intro i hi hij
      have hji : j ≤ i := by simpa only [Finset.mem_range, not_lt] using hij
      simp only [StoppedSimpleIntegral.intervalSum, min_eq_left (hτ hji),
        min_eq_left (hτ (hji.trans (Nat.le_succ i))), sub_self, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      have hij : i + 1 ≤ j := Finset.mem_range.mp hi
      simp only [StoppedSimpleIntegral.intervalSum,
        min_eq_right (hτ hij), min_eq_right (hτ (Nat.le_of_succ_le hij))]

theorem stoppedUniformSum_at_grid (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) {n j : ℕ} (hj : j ≤ n) :
    stoppedUniformSum B H T n (BrownianGrid.uniformGrid T n j) =
      BrownianGrid.integralSum B (BrownianGrid.uniformGrid T n)
        (fun i => H (BrownianGrid.uniformGrid T n i)) j :=
  stopped_sum_at_grid B _ (BrownianGrid.uniformGrid_mono T n) _ hj

end Problem367.BrownianIntegralProcess

namespace Problem367.BrownianContinuousAssociativity

open BrownianGrid BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B H K : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}

def mixedSum (B H K : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n k : ℕ) : Ω → ℝ :=
  integralSum B (uniformGrid T (n * k))
    (fun i ω => K (uniformGrid T n (i / k)) ω * H (uniformGrid T (n * k) i) ω)
    (n * k)

theorem mixedSum_difference_bound
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) {ε : ℝ}
    (happrox : ∀ i < n * k,
      (∫ ω, (K (uniformGrid T n (i / k)) ω -
        K (uniformGrid T (n * k) i) ω) ^ 2 ∂P) ≤ ε) :
    (∫ ω, (mixedSum B H K T n k ω -
      uniformSum B (fun t ω => K t ω * H t ω) T (n * k) ω) ^ 2 ∂P) ≤
        (T : ℝ) * (C ^ 2 * ε) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    exact hω t
  have hK2 (t : ℝ≥0) : MemLp (K t) 2 P := by
    apply MemLp.of_bound ((hK t).mono (F.le t)).aestronglyMeasurable D
    filter_upwards [hbK] with ω hω
    exact hω t
  have hKH2 (s t : ℝ≥0) : MemLp (fun ω => K s ω * H t ω) 2 P :=
    memLp_compose_of_bounded (hH2 t) (hK2 s).aestronglyMeasurable
      (hbK.mono (fun ω hω => hω s))
  have hbound := composed_integralSum_difference_bound hB hAd hind
    (uniformGrid T (n * k)) (uniformGrid_mono T (n * k))
    (fun i => H (uniformGrid T (n * k) i))
    (fun j => K (uniformGrid T n j))
    (fun i ω => K (uniformGrid T (n * k) i) ω * H (uniformGrid T (n * k) i) ω)
    hk (fun i => hH _) (fun j => by rw [uniformGrid_refine T hn hk]; exact hK _)
    (fun i => (hK _).mul (hH _)) (fun i => hKH2 _ _) (fun i => hKH2 _ _)
    n (ε := C ^ 2 * ε) ?_
  · simpa only [integralSum_compose_refined B _ _ _ n hk, uniformGrid_end T (Nat.mul_pos hn hk),
      uniformGrid_zero, NNReal.coe_zero, sub_zero, mixedSum, uniformSum] using hbound
  · intro i hi
    let s := uniformGrid T n (i / k)
    let t := uniformGrid T (n * k) i
    calc
      _ ≤ ∫ ω, C ^ 2 * (K s ω - K t ω) ^ 2 ∂P := by
        apply integral_mono_ae ((hKH2 s t).sub (hKH2 t t)).integrable_sq
          (((hK2 s).sub (hK2 t)).integrable_sq.const_mul (C ^ 2))
        filter_upwards [hbH] with ω hω
        have hs : H t ω ^ 2 ≤ C ^ 2 := by
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC).mpr (hω t)
        calc
          _ = H t ω ^ 2 * (K s ω - K t ω) ^ 2 := by simp only [Pi.sub_apply]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hs (sq_nonneg _)
      _ = C ^ 2 * ∫ ω, (K s ω - K t ω) ^ 2 ∂P := integral_const_mul _ _
      _ ≤ C ^ 2 * ε := mul_le_mul_of_nonneg_left (happrox i hi) (sq_nonneg C)

theorem mixedSum_difference_tendsto
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (mixedSum B H K T (n + 1) (n + 1) ω -
      uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1)) ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε / ((T : ℝ) * C ^ 2 + 1)
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hmod⟩ := MeanSquareContinuity.uniform_integral_sq_sub_le
    (fun t => ((hK t).mono (F.le t)).aestronglyMeasurable) hcK hD hbK T hη
  have hwidth : Tendsto (fun n : ℕ => (T : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := (hwidth.eventually (gt_mem_nhds hδ)).exists_forall_of_atTop
  refine ⟨N, ?_⟩
  intro n hn
  have hmesh : (T : ℝ) / ((n + 1 : ℕ) : ℝ) ≤ δ :=
    (hN (n + 1) (hn.trans (Nat.le_succ n))).le
  have hbound := mixedSum_difference_bound hB hAd hind hH hK hC hD hbH hbK T
    (Nat.succ_pos n) (Nat.succ_pos n) (ε := η) (fun i hi => hmod _ _
      (uniformGrid_floor_le T (Nat.succ_pos n) (Nat.succ_pos n) i)
      (uniformGrid_le_horizon T (Nat.mul_pos (Nat.succ_pos n) (Nat.succ_pos n)) hi.le)
      ((uniformGrid_floor_sub_le T (Nat.succ_pos n) (Nat.succ_pos n) i).trans hmesh))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg (fun ω => sq_nonneg _))]
  apply hbound.trans_lt
  dsimp [η]
  have hp : 0 < (T : ℝ) * C ^ 2 + 1 := by positivity
  rw [← mul_assoc, ← mul_div_assoc]
  apply (div_lt_iff₀ hp).mpr
  nlinarith

omit mΩ in
theorem uniformSum_stoppedUniformSum_eq_mixedSum
    (B H K : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) {n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) :
    uniformSum (stoppedUniformSum B H T (n * k)) K T n =
      mixedSum B H K T n k := by
  have hp (j : ℕ) (hj : j ≤ n) :
      stoppedUniformSum B H T (n * k) (uniformGrid T n j) =
        integralSum B (uniformGrid T (n * k))
          (fun i => H (uniformGrid T (n * k) i)) (j * k) := by
    rw [← uniformGrid_refine T hn hk j]
    exact stoppedUniformSum_at_grid B H T (Nat.mul_le_mul_right k hj)
  funext ω
  dsimp only [mixedSum]
  rw [← integralSum_compose_refined B (uniformGrid T (n * k))
    (fun i => H (uniformGrid T (n * k) i)) (fun j => K (uniformGrid T n j)) n hk]
  unfold uniformSum integralSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i + 1 ≤ n := Finset.mem_range.mp hi
  rw [hp (i + 1) hin, hp i (Nat.le_of_succ_le hin)]
  rfl

theorem uniformSum_memLp {M : ℝ≥0 → Ω → ℝ}
    (hM2 : ∀ t, MemLp (M t) 2 P) (hK : StronglyAdapted F K)
    {D : ℝ} (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) (n : ℕ) : MemLp (uniformSum M K T n) 2 P := by
  exact SimpleIntegral.coarseTransform_memLp (fun j => K (uniformGrid T n j))
    (fun j => ((hK _).mono (F.le _)).aestronglyMeasurable) (fun _ => D)
    (fun j => hbK.mono (fun ω hω => hω _)) (fun j => hM2 _) n

theorem mixedSum_outer_difference_tendsto
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - M T ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (mixedSum B H K T (n + 1) (n + 1) ω -
      uniformSum M K T (n + 1) ω) ^ 2 ∂P) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hbH] with ω hω
    exact hω t
  let I (n : ℕ) := stoppedUniformSum B H T ((n + 1) * (n + 1))
  have hI2 (n : ℕ) (t : ℝ≥0) : MemLp (I n t) 2 P :=
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun i => hH2 _) _ t
  have hIM (n : ℕ) : Martingale (I n) F P := by
    apply BrownianFiltration.stopped_predictable_sum_martingale hB hAd hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun _ => C) (fun i => ?_) _
    filter_upwards [hbH] with ω hω
    exact hω _
  have hcofinal : Tendsto (fun n : ℕ => (n + 1) * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn => hn.trans ((Nat.le_succ n).trans (Nat.le_mul_self _))⟩
  have hterminal : Tendsto (fun n => ∫ ω, (I n T ω - M T ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
    simpa only [I, stoppedUniformSum_terminal, Function.comp_def] using hlim.comp hcofinal
  have herr := MartingaleTransformL2.tendsto_integral_sq_grid_transform
    (fun n => (hIM n).sub hM) (fun n t => (hI2 n t).sub (hM2 t))
    (fun n => uniformGrid T (n + 1)) (fun n => uniformGrid_mono T (n + 1))
    (fun n => n + 1) (fun n => uniformGrid_end T (Nat.succ_pos n))
    (fun n j => K (uniformGrid T (n + 1) j)) (fun n j => hK _) hD
    (fun n j => hbK.mono (fun ω hω => hω _)) hterminal
  refine herr.congr (fun n => ?_)
  rw [← uniformSum_stoppedUniformSum_eq_mixedSum B H K T
    (Nat.succ_pos n) (Nat.succ_pos n)]
  congr 1
  funext ω
  simp only [uniformSum, integralSum, Pi.sub_apply, I]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem mixedSum_memLp
    (hB : IsPreBrownianReal B P)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    {C D : ℝ} (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    (T : ℝ≥0) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    MemLp (mixedSum B H K T n k) 2 P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  rw [← uniformSum_stoppedUniformSum_eq_mixedSum B H K T hn hk]
  exact uniformSum_memLp (fun t =>
    BrownianFiltration.stopped_predictable_sum_memLp_two hB hind _
      (uniformGrid_mono T _) _ (fun i => hH _) (fun i => hH2 _) _ t) hK hbK T n

theorem uniformSum_associativity
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - M T ω) ^ 2 ∂P) atTop (𝓝 0))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZlim : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * H t ω) T n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (uniformSum M K T n ω - Z ω) ^ 2 ∂P)
      atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P :=
    MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
      (hbH.mono (fun ω hω => hω t))
  have hKH2 (t : ℝ≥0) : MemLp (fun ω => K t ω * H t ω) 2 P :=
    memLp_compose_of_bounded (hH2 t)
      ((hK t).mono (F.le t)).aestronglyMeasurable (hbK.mono (fun ω hω => hω t))
  have hproduct2 (n : ℕ) :
      MemLp (uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1))) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp hB hAd hind _
      (fun t => (hK t).mul (hH t)) hKH2 T _
  have hmixed2 (n : ℕ) : MemLp (mixedSum B H K T (n + 1) (n + 1)) 2 P :=
    mixedSum_memLp hB hind hH hK hbH hbK T (Nat.succ_pos n) (Nat.succ_pos n)
  have hcofinal : Tendsto (fun n : ℕ => (n + 1) * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    exact eventually_atTop.mpr ⟨b, fun n hn =>
      hn.trans ((Nat.le_succ n).trans (Nat.le_mul_self _))⟩
  have hproduct := hZlim.comp hcofinal
  have hclose := mixedSum_difference_tendsto hB hAd hind hH hK hcK hC hD hbH hbK T
  have hclose' : Tendsto (fun n => ∫ ω,
      (uniformSum B (fun t ω => K t ω * H t ω) T ((n + 1) * (n + 1)) ω -
        mixedSum B H K T (n + 1) (n + 1) ω) ^ 2 ∂P) atTop (𝓝 0) := by
    refine hclose.congr (fun n => ?_)
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by ring)
  have hmixed := SimpleIntegral.meanSquare_limit_of_close hproduct2 hmixed2 hZ hclose' hproduct
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact SimpleIntegral.meanSquare_limit_of_close hmixed2
    (fun n => uniformSum_memLp hM2 hK hbK T (n + 1)) hZ
    (mixedSum_outer_difference_tendsto hB hAd hind hH hK hD hbH hbK hM hM2 T hlim)
    hmixed

theorem exists_terminal_associative_integral
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hK : StronglyAdapted F K)
    (hcH : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    (hcK : ∀ᵐ ω ∂P, Continuous (fun t => K t ω))
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hbH : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hbK : ∀ᵐ ω ∂P, ∀ t, |K t ω| ≤ D)
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M F P)
    (hM2 : ∀ t, MemLp (M t) 2 P) (T : ℝ≥0)
    (hlim : Tendsto (fun n => ∫ ω,
      (uniformSum B H T n ω - M T ω) ^ 2 ∂P) atTop (𝓝 0)) :
    ∃ Z : Ω → ℝ, StronglyMeasurable[F T] Z ∧ MemLp Z 2 P ∧
      (∫ ω, Z ω ∂P) = 0 ∧
      Tendsto (fun n => ∫ ω,
        (uniformSum B (fun t ω => K t ω * H t ω) T n ω - Z ω) ^ 2 ∂P)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ ω, (uniformSum M K T n ω - Z ω) ^ 2 ∂P)
        atTop (𝓝 0) := by
  have hKH : StronglyAdapted F (fun t ω => K t ω * H t ω) :=
    fun t => (hK t).mul (hH t)
  have hcKH : ∀ᵐ ω ∂P, Continuous (fun t => K t ω * H t ω) := by
    filter_upwards [hcK, hcH] with ω hKω hHω
    exact hKω.mul hHω
  have hbKH : ∀ᵐ ω ∂P, ∀ t, |K t ω * H t ω| ≤ D * C := by
    filter_upwards [hbK, hbH] with ω hKω hHω
    intro t
    rw [abs_mul]
    exact mul_le_mul (hKω t) (hHω t) (abs_nonneg _) hD
  obtain ⟨Z, hZm, hZ2, hZ0, hZlim⟩ :=
    BrownianFiltrationGrid.exists_terminal_uniform_integral_of_bounded_continuous
      hB hAd hind _ hKH hcKH (mul_nonneg hD hC) hbKH T
  exact ⟨Z, hZm, hZ2, hZ0, hZlim,
    uniformSum_associativity hB hAd hind hH hK hcK hC hD hbH hbK hM hM2 T hlim hZ2 hZlim⟩

end Problem367.BrownianContinuousAssociativity

end

end OAI
