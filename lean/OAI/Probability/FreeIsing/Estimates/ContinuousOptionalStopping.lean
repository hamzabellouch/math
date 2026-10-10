import Mathlib
import OAI.Probability.FreeIsing.Estimates.RoundedStoppingTimes

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.ContinuousOptionalStopping

theorem countable_range_const {Ω α : Type*} (a : α) :
    (range (fun _ : Ω => a)).Countable := by
  apply (countable_singleton a).mono
  rintro x ⟨ω, rfl⟩
  exact mem_singleton a

theorem countable_range_min {Ω α : Type*} [LinearOrder α] {f g : Ω → α}
    (hf : (range f).Countable) (hg : (range g).Countable) :
    (range (fun ω => min (f ω) (g ω))).Countable := by
  apply (hf.union hg).mono
  rintro x ⟨ω, rfl⟩
  rcases le_total (f ω) (g ω) with h | h
  · exact Or.inl ⟨ω, min_eq_left h |>.symm⟩
  · exact Or.inr ⟨ω, min_eq_right h |>.symm⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
  {F : Filtration ℝ≥0 mΩ} {M : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

theorem integrable_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    Integrable (stoppedValue M τ) μ := by
  exact integrable_condExp.congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount).symm

theorem integral_stoppedValue_of_countable
    (hM : Martingale M F μ) (hτ : IsStoppingTime F τ)
    (hcount : (range τ).Countable) {T : ℝ≥0} (hT : ∀ ω, τ ω ≤ T) :
    (∫ ω, stoppedValue M τ ω ∂μ) = ∫ ω, M T ω ∂μ := by
  rw [integral_congr_ae
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hT hcount)]
  exact integral_condExp hτ.measurableSpace_le

theorem martingale_stoppedProcess_of_countable
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hτ : IsStoppingTime F τ) (hcount : (range τ).Countable) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    exact integrable_stoppedValue_of_countable hM ((isStoppingTime_const F t).min hτ)
      (countable_range_min (countable_range_const _) hcount) (fun _ => min_le_left _ _)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  classical
  let ν : Ω → WithTop ℝ≥0 := Aᶜ.piecewise (fun _ => s) (fun _ => t)
  have hν : IsStoppingTime F ν := isStoppingTime_piecewise_const hst hA.compl
  have hνcount : (range ν).Countable := by
    apply (Set.to_countable ({(s : WithTop ℝ≥0), (t : WithTop ℝ≥0)} : Set (WithTop ℝ≥0))).mono
    rintro value ⟨sample, rfl⟩
    change ν sample = (s : WithTop ℝ≥0) ∨ ν sample = (t : WithTop ℝ≥0)
    by_cases hsample : sample ∈ A
    · right
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_true_eq_false, ite_false]
    · left
      simp only [ν, Set.piecewise, mem_compl_iff, hsample, not_false_eq_true, ite_true]
  have hνle (ω : Ω) : ν ω ≤ t := by
    by_cases hω : ω ∈ A
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_true_eq_false, ite_false]
      exact le_rfl
    · simp only [ν, Set.piecewise, mem_compl_iff, hω, not_false_eq_true, ite_true]
      exact WithTop.coe_le_coe.mpr hst
  let π : Ω → WithTop ℝ≥0 := fun ω => min (ν ω) (τ ω)
  have hπ := hν.min hτ
  have hπcount := countable_range_min hνcount hcount
  have hmeanπ := integral_stoppedValue_of_countable hM hπ hπcount
    (fun ω => (min_le_left _ _).trans (hνle ω))
  have hmeans := integral_stoppedValue_of_countable hM ((isStoppingTime_const F s).min hτ)
    (countable_range_min (countable_range_const _) hcount)
    (fun ω => (min_le_left _ _).trans (WithTop.coe_le_coe.mpr hst))
  have hpiece : stoppedValue M π =
      A.piecewise (stoppedProcess M τ t) (stoppedProcess M τ s) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [π, ν, Set.piecewise, hω, stoppedValue, stoppedProcess]
  change (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, M t ω ∂μ at hmeanπ
  have hmean : (∫ ω, stoppedValue M π ω ∂μ) = ∫ ω, stoppedProcess M τ s ω ∂μ :=
    hmeanπ.trans hmeans.symm
  rw [hpiece, integral_piecewise (F.le s A hA) (hint t).integrableOn
    (hint s).integrableOn] at hmean
  have hsplit := integral_add_compl (F.le s A hA) (hint s)
  linarith

theorem martingale_stoppedProcess_of_approximation
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (stoppedProcess M τ) F μ := by
  have had := hprog.stronglyAdapted_stoppedProcess hτ
  have hMn (n : ℕ) : Martingale (stoppedProcess M (τn n)) F μ :=
    martingale_stoppedProcess_of_countable hM hprog (hτn n) (hcount n)
  have hbound (T : ℝ≥0) (g : Ω → ℝ)
      (hg : ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
      (σ : Ω → WithTop ℝ≥0) :
      ∀ᵐ ω ∂μ, ‖stoppedProcess M σ T ω‖ ≤ g ω := by
    filter_upwards [hg] with ω hω
    exact hω _ (WithTop.untopA_le (min_le_left _ _))
  have hint (t : ℝ≥0) : Integrable (stoppedProcess M τ t) μ := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    exact hg.mono' ((had t).mono (F.le t)).aestronglyMeasurable (hbound t g hgb τ)
  have hlim (t : ℝ≥0) (A : Set Ω) :
      Tendsto (fun n => ∫ ω in A, stoppedProcess M (τn n) t ω ∂μ) atTop
        (𝓝 (∫ ω in A, stoppedProcess M τ t ω ∂μ)) := by
    obtain ⟨g, hg, hgb⟩ := hdom t
    apply tendsto_integral_of_dominated_convergence g
      (fun n => ((hMn n).integrable t).aestronglyMeasurable.restrict) hg.restrict
      (fun n => ae_restrict_of_ae (hbound t g hgb (τn n)))
    filter_upwards [ae_restrict_of_ae hc] with ω hcω
    exact (hcω.tendsto _).comp (htime ω t)
  refine ⟨had, ?_⟩
  intro s t hst
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun A hA _ => (hint s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA hAfin
  exact tendsto_nhds_unique (hlim s A)
    (Filter.Tendsto.congr (fun n => ((hMn n).setIntegral_eq hst hA).symm) (hlim t A))

theorem martingale_stoppedProcess_of_approximation_bounded
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) {C : ℝ}
    (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (stoppedProcess M τ) F μ := by
  apply martingale_stoppedProcess_of_approximation hM hprog hc _ hτ τn hτn hcount htime
  intro T
  exact ⟨fun _ => C, integrable_const C, hb.mono (fun ω hω t _ => hω t)⟩

theorem martingale_stopped_compensatedSquare_of_approximation
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hcomp : Martingale (fun t ω => (M t ω)^2 - A t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)
    (hτ : IsStoppingTime F τ) (τn : ℕ → Ω → WithTop ℝ≥0)
    (hτn : ∀ n, IsStoppingTime F (τn n))
    (hcount : ∀ n, (range (τn n)).Countable)
    (htime : ∀ (ω : Ω) (t : ℝ≥0), Tendsto
      (fun n => (min (t : WithTop ℝ≥0) (τn n ω)).untopA) atTop
      (𝓝 ((min (t : WithTop ℝ≥0) (τ ω)).untopA))) :
    Martingale (fun t ω => (stoppedProcess M τ t ω)^2 - stoppedProcess A τ t ω) F μ := by
  have hprog : IsStronglyProgressive F (fun t ω => (M t ω)^2 - A t ω) := by
    intro t
    exact ((hprogM t).pow 2).sub (hprogA t)
  have hc : ∀ᵐ ω ∂μ, Continuous (fun t => (M t ω)^2 - A t ω) := by
    filter_upwards [hcM, hcA] with ω hm ha
    exact (hm.pow 2).sub ha
  apply martingale_stoppedProcess_of_approximation hcomp hprog hc _ hτ τn hτn hcount htime
  intro T
  refine ⟨fun ω => C^2 + A T ω, (integrable_const _).add (hAint T), ?_⟩
  filter_upwards [hb, hA0, hAmono] with ω hbw hA0w hAmonow
  intro t ht
  have hMsq : (M t ω)^2 ≤ C^2 := by
    have := (sq_le_sq₀ (abs_nonneg (M t ω)) hC).mpr (hbw t)
    simpa only [sq_abs] using this
  calc
    |(M t ω)^2 - A t ω| ≤ |(M t ω)^2| + |A t ω| := abs_sub _ _
    _ = (M t ω)^2 + A t ω := by rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (hA0w t)]
    _ ≤ C^2 + A T ω := add_le_add hMsq (hAmonow ht)

theorem martingale_stoppedProcess_of_continuous_dominated
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hdom : ∀ T : ℝ≥0, ∃ g : Ω → ℝ, Integrable g μ ∧
      ∀ᵐ ω ∂μ, ∀ t ≤ T, |M t ω| ≤ g ω)
    (hτ : IsStoppingTime F τ) : Martingale (stoppedProcess M τ) F μ := by
  obtain ⟨τn, hτn, hcount, htime⟩ :=
    RoundedStoppingTimes.exists_countable_range_approximation hτ
  exact martingale_stoppedProcess_of_approximation hM hprog hc hdom hτ τn hτn hcount htime

theorem martingale_stoppedProcess_of_continuous_bounded
    (hM : Martingale M F μ) (hprog : IsStronglyProgressive F M)
    (hc : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω)) {C : ℝ}
    (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hτ : IsStoppingTime F τ) : Martingale (stoppedProcess M τ) F μ := by
  apply martingale_stoppedProcess_of_continuous_dominated hM hprog hc _ hτ
  intro T
  exact ⟨fun _ => C, integrable_const C, hb.mono (fun ω hω t _ => hω t)⟩

theorem martingale_stopped_compensatedSquare
    {A : ℝ≥0 → Ω → ℝ} {C : ℝ}
    (hcomp : Martingale (fun t ω => (M t ω)^2 - A t ω) F μ)
    (hprogM : IsStronglyProgressive F M) (hprogA : IsStronglyProgressive F A)
    (hcM : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    (hcA : ∀ᵐ ω ∂μ, Continuous (fun t => A t ω))
    (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, ∀ t, |M t ω| ≤ C)
    (hA0 : ∀ᵐ ω ∂μ, ∀ t, 0 ≤ A t ω)
    (hAmono : ∀ᵐ ω ∂μ, Monotone (fun t => A t ω))
    (hAint : ∀ t, Integrable (A t) μ)
    (hτ : IsStoppingTime F τ) :
    Martingale (fun t ω => (stoppedProcess M τ t ω)^2 - stoppedProcess A τ t ω) F μ := by
  obtain ⟨τn, hτn, hcount, htime⟩ :=
    RoundedStoppingTimes.exists_countable_range_approximation hτ
  exact martingale_stopped_compensatedSquare_of_approximation hcomp hprogM hprogA hcM hcA
    hC hb hA0 hAmono hAint hτ τn hτn hcount htime

end Problem367.ContinuousOptionalStopping

end

end OAI
