import OAI.Probability.FreeIsing.Brownian.FiltrationIntegralProperties
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianIntegral

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem meanSquare_condExp_sub_le [IsFiniteMeasure P]
    (m : MeasurableSpace Ω) {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    (∫ ω, (P[X | m] ω - P[Y | m] ω) ^ 2 ∂P) ≤
      ∫ ω, (X ω - Y ω) ^ 2 ∂P := by
  have hsub := condExp_sub (hX.integrable (by norm_num))
    (hY.integrable (by norm_num)) m
  calc
    _ = ∫ ω, (P[X - Y | m] ω) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hsub] with ω hω
      change P[X - Y | m] ω = P[X | m] ω - P[Y | m] ω at hω
      rw [hω]
    _ ≤ _ := by
      have hbound := integral_norm_condExp_rpow_le (m := m)
        (by norm_num : (1 : ℝ) ≤ 2)
        (f := X - Y) (by
          simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply] using
            (hX.sub hY).integrable_sq)
      simpa only [Real.rpow_two, Real.norm_eq_abs, sq_abs, Pi.sub_apply] using hbound

theorem finite_stoppedSum_eq_condExp [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hB : Martingale B F P) (s : Finset ℕ) (a b : ℕ → ℝ≥0)
    (H : ℕ → Ω → ℝ) (hab : ∀ i ∈ s, a i ≤ b i)
    (hH : ∀ i ∈ s, StronglyMeasurable[F (a i)] (H i))
    (C : ℕ → ℝ) (hb : ∀ i ∈ s, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) (t : ℝ≥0) :
    P[(fun ω => ∑ i ∈ s, H i ω * (B (b i) ω - B (a i) ω)) | F t] =ᵐ[P]
      fun ω => ∑ i ∈ s, StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω := by
  have hint (i : ℕ) (hi : i ∈ s) :
      Integrable (fun ω => H i ω * (B (b i) ω - B (a i) ω)) P :=
    ((hB.integrable (b i)).sub (hB.integrable (a i))).bdd_mul
      ((hH i hi).mono (F.le (a i))).aestronglyMeasurable (hb i hi)
  have hsum := condExp_finsetSum hint (F t)
  have hsumFun : (∑ i ∈ s, fun ω => H i ω * (B (b i) ω - B (a i) ω)) =
      (fun ω => ∑ i ∈ s, H i ω * (B (b i) ω - B (a i) ω)) := by
    funext ω
    simp only [Finset.sum_apply]
  rw [hsumFun] at hsum
  have heach : ∀ᵐ ω ∂P, ∀ i ∈ s,
      P[(fun ω => H i ω * (B (b i) ω - B (a i) ω)) | F t] ω =
        StoppedSimpleIntegral.intervalSum B (H i) (a i) (b i) t ω :=
    s.eventually_all.mpr (fun i hi =>
      StoppedSimpleIntegral.intervalSum_eq_condExp_terminal hB (hab i hi) (hH i hi) (hb i hi) t)
  filter_upwards [hsum, heach] with ω hsum heach
  simp only [Finset.sum_apply] at hsum
  rw [hsum]
  exact Finset.sum_congr rfl (fun i hi => heach i hi)

def stoppedUniformSum (B H : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, StoppedSimpleIntegral.intervalSum B
    (H (BrownianGrid.uniformGrid T n i)) (BrownianGrid.uniformGrid T n i)
    (BrownianGrid.uniformGrid T n (i + 1)) t ω

theorem stoppedUniformSum_eq_condExp
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) {C : ℝ}
    (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    P[BrownianGrid.uniformSum B H T n | F t] =ᵐ[P] stoppedUniformSum B H T n t := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply finite_stoppedSum_eq_condExp (BrownianFiltration.martingale_of_independent_past hB hAd hind)
    (Finset.range n) (BrownianGrid.uniformGrid T n)
    (fun i => BrownianGrid.uniformGrid T n (i + 1))
    (fun i => H (BrownianGrid.uniformGrid T n i))
    (fun i _ => BrownianGrid.uniformGrid_mono T n (Nat.le_succ i))
    (fun i _ => hH _) (fun _ => C)
  intro i hi
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs] using hω (BrownianGrid.uniformGrid T n i)

theorem exists_stopped_uniform_integral_process
    {B H : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C) (T : ℝ≥0) :
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M F P ∧
      (∀ t, MemLp (M t) 2 P) ∧
      (∀ t, (∫ ω, M t ω ∂P) = 0) ∧
      (∀ t, T ≤ t → M t = M T) ∧
      (∫ ω, (M T ω) ^ 2 ∂P) =
        (∫ t in (0 : ℝ)..(T : ℝ), ∫ ω, (H t.toNNReal ω) ^ 2 ∂P) ∧
      (∀ t, Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H T n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨I, hIm, hI2, hIzero, hIiso, hIlim⟩ :=
    BrownianFiltrationGrid.exists_terminal_uniform_integral_isometry
      hB hAd hind H hH hc hC hb T
  let M : ℝ≥0 → Ω → ℝ := fun t => P[I | F t]
  have hIint : Integrable I P := hI2.integrable (by norm_num)
  have hafter (t : ℝ≥0) (ht : T ≤ t) : M t = I :=
    condExp_of_stronglyMeasurable (F.le t) (hIm.mono (F.mono ht)) hIint
  have hH2 (t : ℝ≥0) : MemLp (H t) 2 P := by
    apply MemLp.of_bound ((hH t).mono (F.le t)).aestronglyMeasurable C
    filter_upwards [hb] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  refine ⟨M, martingale_condExp I F P, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    exact hI2.condExp (by norm_num)
  · intro t
    exact (integral_condExp (F.le t)).trans hIzero
  · intro t ht
    exact (hafter t ht).trans (hafter T le_rfl).symm
  · rw [hafter T le_rfl]
    exact hIiso
  · intro t
    apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) ?_ hIlim
    intro n
    calc
      _ = ∫ ω, (P[BrownianGrid.uniformSum B H T n | F t] ω - P[I | F t] ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [stoppedUniformSum_eq_condExp hB hAd hind hH hb T n t] with ω hω
        change (stoppedUniformSum B H T n t ω - P[I | F t] ω) ^ 2 = _
        rw [hω]
      _ ≤ _ := meanSquare_condExp_sub_le (F t)
        (BrownianFiltrationGrid.uniformSum_memLp hB hAd hind H hH hH2 T n) hI2

end Problem367.BrownianIntegralProcess

end

end OAI
