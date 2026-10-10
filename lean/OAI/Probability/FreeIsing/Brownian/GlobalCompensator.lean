import OAI.Probability.FreeIsing.Brownian.IntegralCompensator

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace Problem367.BrownianIntegralProcess

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

def globalCompensator (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  SelectedCompensator.selected H t t ω

theorem globalCompensator_stronglyAdapted {F : Filtration ℝ≥0 mΩ}
    {H : ℝ≥0 → Ω → ℝ} (hH : StronglyAdapted F H) :
    StronglyAdapted F (globalCompensator H) :=
  fun t => SelectedCompensator.selected_stronglyAdapted hH t t

theorem ae_globalCompensator_eq_integral {H : ℝ≥0 → Ω → ℝ}
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω)) :
    ∀ᵐ ω ∂P, ∀ t, globalCompensator H t ω =
      ∫ s in (0 : ℝ)..(t : ℝ), (H s.toNNReal ω) ^ 2 := by
  filter_upwards [hc] with ω hω
  intro t
  simpa only [globalCompensator, min_self] using
    SelectedCompensator.selected_eq_integral_of_continuous hω t t

omit mΩ in
theorem stoppedUniformSum_min_horizon (B H : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (t : ℝ≥0) :
    stoppedUniformSum B H T n (min t T) = stoppedUniformSum B H T n t := by
  funext ω
  unfold stoppedUniformSum
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hn : 0 < n := (Nat.zero_le i).trans_lt hin
  have ha := BrownianGrid.uniformGrid_le_horizon T hn hin.le
  have hb := BrownianGrid.uniformGrid_le_horizon T hn (Nat.succ_le_of_lt hin)
  simp only [StoppedSimpleIntegral.intervalSum, min_assoc, min_eq_right ha, min_eq_right hb]

theorem global_compensatedSquare_of_integer_stopped_limits
    {B H M : ℝ≥0 → Ω → ℝ} {F : Filtration ℝ≥0 mΩ}
    (hB : IsPreBrownianReal B P) (hAd : StronglyAdapted F B)
    (hind : ∀ s t, s ≤ t → Indep
      (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) (F s) P)
    (hH : StronglyAdapted F H) (hc : ∀ᵐ ω ∂P, Continuous (fun t => H t ω))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂P, ∀ t, |H t ω| ≤ C)
    (hM : StronglyAdapted F M) (hM2 : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ N : ℕ, 0 < N → ∀ t : ℝ≥0, t ≤ N →
      Tendsto (fun n => ∫ ω,
        (stoppedUniformSum B H N n t ω - M t ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Martingale (fun t ω => (M t ω) ^ 2 - globalCompensator H t ω) F P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine ⟨fun t => ((hM t).pow 2).sub (globalCompensator_stronglyAdapted hH t), ?_⟩
  intro s t hst
  obtain ⟨N, htN⟩ := exists_nat_gt (t : ℝ)
  have hN : 0 < N := by exact_mod_cast (t.coe_nonneg.trans_lt htN)
  have htN' : t ≤ (N : ℝ≥0) := by exact_mod_cast htN.le
  have hsN : s ≤ (N : ℝ≥0) := hst.trans htN'
  let L : ℝ≥0 → Ω → ℝ := fun r => M (min r N)
  have hL : StronglyAdapted F L := fun r =>
    (hM (min r N)).mono (F.mono (min_le_left _ _))
  have hL2 (r : ℝ≥0) : MemLp (L r) 2 P := hM2 (min r N)
  have hLlim (r : ℝ≥0) : Tendsto (fun n => ∫ ω,
      (stoppedUniformSum B H N n r ω - L r ω) ^ 2 ∂P) atTop (𝓝 0) := by
    simpa only [stoppedUniformSum_min_horizon, L] using
      hlim N hN (min r N) (min_le_right _ _)
  have hcomp := stopped_uniform_limit_compensatedSquare hB hAd hind hH hc hC hb N hL hL2 hLlim
  have heq (r : ℝ≥0) (hr : r ≤ N) :
      (fun ω => (L r ω) ^ 2 - SelectedCompensator.selected H N r ω) =ᵐ[P]
        (fun ω => (M r ω) ^ 2 - globalCompensator H r ω) := by
    filter_upwards [hc] with ω hω
    have hrR : (r : ℝ) ≤ (N : ℝ) := by exact_mod_cast hr
    simp only [L, min_eq_left hr, globalCompensator,
      SelectedCompensator.selected_eq_integral_of_continuous hω, NNReal.coe_natCast, min_self, min_eq_left hrR]
  exact (condExp_congr_ae (heq t htN').symm).trans
    ((hcomp.condExp_ae_eq hst).trans (heq s hsN))

end Problem367.BrownianIntegralProcess

end

end OAI
