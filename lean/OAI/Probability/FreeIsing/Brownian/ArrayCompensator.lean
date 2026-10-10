import OAI.Probability.FreeIsing.Brownian.ArrayFiltrationIntegral
import OAI.Probability.FreeIsing.Brownian.IntegralProcess
import OAI.Probability.FreeIsing.Estimates.CompensatedSquareLimit
import OAI.Probability.FreeIsing.Stochastic.SelectedCompensator
import OAI.Probability.FreeIsing.Stochastic.StoppedBrownianArraySquare

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.BrownianArrayCompensator

variable {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Fintype ι]
  {P : Measure Ω} [IsProbabilityMeasure P] {F : Filtration ℝ≥0 mΩ}

theorem compensatedSquare_of_terminal_meanSquare
    {B H : ι → ℝ≥0 → Ω → ℝ} {M : ℝ≥0 → Ω → ℝ}
    (hB : ∀ j, IsPreBrownianReal (B j) P)
    (hAd : ∀ j, StronglyAdapted F (B j))
    (hpast : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω j => B j t ω - B j s ω) inferInstance) (F s) P)
    (hcross : ∀ s t, s ≤ t → Pairwise fun j k =>
      IndepFun (fun ω => B j t ω - B j s ω) (fun ω => B k t ω - B k s ω) P)
    (hH : ∀ j, StronglyAdapted F (H j))
    (hc : ∀ j, ∀ᵐ ω ∂P, Continuous (fun t => H j t ω))
    (C : ι → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hb : ∀ j, ∀ᵐ ω ∂P, ∀ t, |H j t ω| ≤ C j)
    (hM : Martingale M F P) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ T, Tendsto (fun n : ℕ => ∫ ω,
      ((∑ j, BrownianGrid.uniformSum (B j) (H j) T n ω) - M T ω) ^ 2 ∂P)
        atTop (𝓝 0)) :
    Martingale (fun t ω => M t ω ^ 2 -
      ∑ j, SelectedCompensator.selected (H j) t t ω) F P := by
  classical
  have hi (j : ι) (s t : ℝ≥0) (hst : s ≤ t) :=
    BrownianArrayFiltration.coordinate_increment_indep_past (hpast s t hst) j
  have hH2 (j : ι) (t : ℝ≥0) : MemLp (H j t) 2 P := by
    apply MemLp.of_bound (hH j).stronglyMeasurable.aestronglyMeasurable (C j)
    filter_upwards [hb j] with ω hω
    simpa only [Real.norm_eq_abs] using hω t
  have hU2 (T : ℝ≥0) (n : ℕ) (j : ι) :
      MemLp (BrownianGrid.uniformSum (B j) (H j) T n) 2 P :=
    BrownianFiltrationGrid.uniformSum_memLp (hB j) (hAd j) (hi j)
      (H j) (hH j) (hH2 j) T n
  have hQ : StronglyAdapted F (fun t ω =>
      ∑ j, SelectedCompensator.selected (H j) t t ω) := by
    intro t
    exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      SelectedCompensator.selected_stronglyAdapted (hH j) t t
  refine ⟨fun t => ((hM.stronglyAdapted t).pow 2).sub (hQ t), ?_⟩
  intro s T hsT
  let U (n : ℕ) : Ω → ℝ := fun ω =>
    ∑ j, BrownianGrid.uniformSum (B j) (H j) T n ω
  let X (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, BrownianIntegralProcess.stoppedUniformSum (B j) (H j) T n t ω
  let A (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, SelectedCompensator.squareSum (H j) T n t ω
  let Y (t : ℝ≥0) : Ω → ℝ := P[M T | F t]
  let Q (t : ℝ≥0) (ω : Ω) : ℝ :=
    ∑ j, SelectedCompensator.selected (H j) T t ω
  have hu2 (n : ℕ) : MemLp (U n) 2 P :=
    memLp_finsetSum _ fun j _ => hU2 T n j
  have hx2 (n : ℕ) (t : ℝ≥0) : MemLp (X n t) 2 P := by
    apply memLp_finsetSum
    intro j hj
    exact BrownianFiltration.stopped_predictable_sum_memLp_two (hB j) (hi j)
      (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun i => H j (BrownianGrid.uniformGrid T n i)) (fun i => hH j _)
      (fun i => hH2 j _) (Finset.range n) t
  have ha (n : ℕ) (t : ℝ≥0) : Integrable (A n t) P :=
    integrable_finsetSum _ fun j _ =>
      (SelectedCompensator.squareSum_memLp (hH j) (hC j) (hb j) T t n 1).integrable le_rfl
  have hq (t : ℝ≥0) : Integrable (Q t) P :=
    integrable_finsetSum _ fun j _ =>
      (SelectedCompensator.selected_memLp (hH j) (hc j) (hC j) (hb j) T t 1).integrable le_rfl
  have hy2 (t : ℝ≥0) : MemLp (Y t) 2 P := (hM2 T).condExp (by norm_num)
  have hce (n : ℕ) (t : ℝ≥0) : P[U n | F t] =ᵐ[P] X n t := by
    have hsum := condExp_finsetSum (s := Finset.univ)
      (fun j _ => (hU2 T n j).integrable (by norm_num)) (F t)
    have heach : ∀ᵐ ω ∂P, ∀ j,
        P[BrownianGrid.uniformSum (B j) (H j) T n | F t] ω =
          BrownianIntegralProcess.stoppedUniformSum (B j) (H j) T n t ω :=
      ae_all_iff.mpr fun j => BrownianIntegralProcess.stoppedUniformSum_eq_condExp
        (hB j) (hAd j) (hi j) (hH j) (hb j) T n t
    have hsumFun : (∑ j, BrownianGrid.uniformSum (B j) (H j) T n) = U n := by
      funext ω
      simp only [U, Finset.sum_apply]
    rw [hsumFun] at hsum
    filter_upwards [hsum, heach] with ω hω he
    simp only [Finset.sum_apply] at hω
    exact hω.trans (Finset.sum_congr rfl (fun j _ => he j))
  have hxlim (t : ℝ≥0) : Tendsto (fun n => ∫ ω,
      (X n t ω - Y t ω) ^ 2 ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg (fun ω => sq_nonneg _)) ?_ (hlim T)
    intro n
    calc
      _ = ∫ ω, (P[U n | F t] ω - P[M T | F t] ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hce n t] with ω hω
        exact congrArg (fun z => (z - Y t ω) ^ 2) hω.symm
      _ ≤ _ := BrownianIntegralProcess.meanSquare_condExp_sub_le (F t) (hu2 n) (hM2 T)
  have hfinite (n : ℕ) : Martingale (fun t ω => (X n t ω) ^ 2 - A n t ω) F P := by
    have hh := StoppedBrownianArraySquare.stopped_brownian_array_square_martingale
      B hB hAd hpast hcross (BrownianGrid.uniformGrid T n) (BrownianGrid.uniformGrid_mono T n)
      (fun j i => H j (BrownianGrid.uniformGrid T n i)) (fun j i => hH j _)
      (fun j _ => C j)
      (fun j i => (hb j).mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω _))
      Finset.univ n
    simpa only [X, A, BrownianIntegralProcess.stoppedUniformSum,
      SelectedCompensator.squareSum, mul_comm] using hh
  have halim (t : ℝ≥0) : Tendsto (fun n => eLpNorm (A n t - Q t) 1 P) atTop (𝓝 0) := by
    have hl := tendsto_finsetSum Finset.univ (fun j _ =>
      SelectedCompensator.tendsto_squareSum_L1_selected
        (fun r => (hH j).stronglyMeasurable.aestronglyMeasurable)
        (hc j) (hC j) (hb j) T t)
    simp only [Finset.sum_const_zero] at hl
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hl (fun _ => bot_le)
    intro n
    change eLpNorm (A n t - Q t) 1 P ≤ ∑ j,
      eLpNorm (SelectedCompensator.squareSum (H j) T n t - SelectedCompensator.selected (H j) T t) 1 P
    have heq : A n t - Q t = ∑ j,
        (SelectedCompensator.squareSum (H j) T n t - SelectedCompensator.selected (H j) T t) := by
      funext ω
      simp only [A, Q, Pi.sub_apply, Finset.sum_apply, Finset.sum_sub_distrib]
    rw [heq]
    exact eLpNorm_sum_le le_rfl
  have hcomp := CompensatedSquareLimit.martingale_compensatedSquare_of_limits
    hx2 ha hfinite (martingale_condExp (M T) F P).stronglyAdapted hy2
    (fun t => Finset.stronglyMeasurable_fun_sum _ fun j _ =>
      SelectedCompensator.selected_stronglyAdapted (hH j) T t) hq
    (fun t => CompensatedSquareLimit.tendsto_eLpNorm_two_of_meanSquare
      (fun n => hx2 n t) (hy2 t) (hxlim t)) halim
  have heq (r : ℝ≥0) (hr : r ≤ T) :
      (fun ω => (Y r ω) ^ 2 - Q r ω) =ᵐ[P]
        (fun ω => M r ω ^ 2 - ∑ j, SelectedCompensator.selected (H j) r r ω) := by
    have hcAll : ∀ᵐ ω ∂P, ∀ j, Continuous (fun t => H j t ω) := ae_all_iff.mpr hc
    filter_upwards [hM.condExp_ae_eq hr, hcAll] with ω hω hcω
    change (P[M T | F r] ω) ^ 2 - _ = _
    rw [hω]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    simp only [SelectedCompensator.selected_eq_integral_of_continuous (hcω j),
      min_self, min_eq_left (show (r : ℝ) ≤ T from hr)]
  exact (condExp_congr_ae (heq T le_rfl).symm).trans
    ((hcomp.condExp_ae_eq hsT).trans (heq s hsT))

end Problem367.BrownianArrayCompensator

end

end OAI
