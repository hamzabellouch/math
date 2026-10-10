import OAI.Probability.SLE.Mass.MassCompensatorEndpoint
import OAI.Probability.SLE.Mass.MassCompensatorSelection

namespace OAI

/-! Recovery of a continuous finite mass path from its discrete
predictable increments, with the paper's growing dyadic horizon. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

def meshMassIncrement (A : ℝ≥0 → Ω → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  A (compensatorMeshTime n (i+1)) ω-A (compensatorMeshTime n i) ω

def meshMassCompensator (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ)
    (n j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, condExp (ℱ n i) P (meshMassIncrement A n i) ω

omit [IsProbabilityMeasure P] in
lemma meshMassIncrement_memLp
    (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ) (hL : MemLp L 2 P)
    (hA : ∀ t, Measurable (A t))
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧ ∀ t, A t ω ≤ L ω)
    (n i : ℕ) : MemLp (meshMassIncrement A n i) 2 P := by
  apply hL.mono' (((hA _).sub (hA _)).aestronglyMeasurable)
  filter_upwards [hp] with ω hω
  have hn : 0 ≤ meshMassIncrement A n i ω :=
    sub_nonneg.mpr (hω.1 (compensatorMeshTime_mono n (Nat.le_succ i)))
  have hz : 0 ≤ A (compensatorMeshTime n i) ω := by
    rw [← hω.2.1]
    exact hω.1 (show 0 ≤ _ from zero_le)
  simp only [Pi.sub_apply]
  change 0 ≤ A (compensatorMeshTime n (i+1)) ω-A (compensatorMeshTime n i) ω at hn
  rw [Real.norm_of_nonneg hn]
  linarith [hω.2.2 (compensatorMeshTime n (i+1))]

omit [IsProbabilityMeasure P] in
lemma meshMassCompensator_decomposition
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ) (n j : ℕ) (ω : Ω) :
    meshMassCompensator P ℱ A n j ω =
      A (compensatorMeshTime n j) ω-A 0 ω-
        centeredMassPartialSum P (ℱ n) (meshMassIncrement A n) j ω := by
  unfold centeredMassPartialSum meshMassCompensator
  rw [Finset.sum_sub_distrib]
  have he : (∑ i ∈ Finset.range j, meshMassIncrement A n i ω) =
      A (compensatorMeshTime n j) ω-A 0 ω := by
    simp only [meshMassIncrement]
    rw [Finset.sum_range_sub (fun i => A (compensatorMeshTime n i) ω) j,compensatorMeshTime_zero]
  rw [he]
  ring

theorem meshMassCentered_selected_tendstoInMeasure
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ)
    (hA : ∀ t, Measurable (A t))
    (hgrid : ∀ n i, StronglyMeasurable[ℱ n i] (A (compensatorMeshTime n i)))
    (hL : MemLp L 2 P)
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧
      Continuous (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop (𝓝 (L ω)) ∧
      ∀ t, A t ω ≤ L ω)
    (J : ℕ → Ω → ℕ) (hJ : ∀ n ω, J n ω ≤ n*2^n) :
    TendstoInMeasure P
      (fun n ω => centeredMassPartialSum P (ℱ n) (meshMassIncrement A n) (J n ω) ω)
      atTop 0 := by
  apply centeredMassPartialSum_selected_tendstoInMeasure P ℱ (meshMassIncrement A)
    (fun n i => meshMassIncrement_memLp P A L hL hA
      (hp.mono (fun ω hω => ⟨hω.1,hω.2.1,hω.2.2.2.2⟩)) n i)
    (fun n i => (hgrid n (i+1)).sub ((hgrid n i).mono (ℱ n |>.mono (Nat.le_succ i))))
    (fun n => n*2^n) J hJ
  exact compensatorQuadraticError_mean_tendsto_zero P A L hA hL.integrable_sq hp

omit [IsProbabilityMeasure P] in
lemma meshMassCompensator_selected_measurable
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (J : Ω → ℕ) (hJ : Measurable J) :
    Measurable (fun ω => meshMassCompensator P ℱ A n (J ω) ω) := by
  have hjoint : Measurable (fun z : ℕ × Ω => meshMassCompensator P ℱ A n z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro j
    change Measurable (fun ω => ∑ i ∈ Finset.range j, condExp (ℱ n i) P (meshMassIncrement A n i) ω)
    apply Finset.measurable_sum
    intro i _
    exact stronglyMeasurable_condExp.measurable.le (ℱ n |>.le i)
  exact hjoint.comp (hJ.prodMk measurable_id)

/-- Any measurable choice of endpoints where the sampled mass has its
pathwise limit recovers that same mass from the predictable increments. -/
theorem meshMassCompensator_selected_tendstoInMeasure
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ) (L V : Ω → ℝ)
    (hA : ∀ t, Measurable (A t))
    (hgrid : ∀ n i, StronglyMeasurable[ℱ n i] (A (compensatorMeshTime n i)))
    (hL : MemLp L 2 P)
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧
      Continuous (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop (𝓝 (L ω)) ∧
      ∀ t, A t ω ≤ L ω)
    (J : ℕ → Ω → ℕ) (hJm : ∀ n, Measurable (J n))
    (hJ : ∀ n ω, J n ω ≤ n*2^n)
    (hJV : ∀ᵐ ω ∂P, Tendsto (fun n => A (compensatorMeshTime n (J n ω)) ω)
      atTop (𝓝 (V ω))) :
    TendstoInMeasure P (fun n ω => meshMassCompensator P ℱ A n (J n ω) ω) atTop V := by
  have hZ := meshMassCentered_selected_tendstoInMeasure P ℱ A L hA hgrid hL hp J hJ
  apply (exists_seq_tendstoInMeasure_atTop_iff
    (fun n => (meshMassCompensator_selected_measurable P ℱ A n (J n) (hJm n)).aestronglyMeasurable)).mpr
  intro ns hns
  obtain ⟨ms,hms,hlim⟩ := (hZ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hp,hJV,hlim] with ω hω hV hZω
  have ht := (hV.comp (hns.tendsto_atTop.comp hms.tendsto_atTop)).sub hZω
  simp only [Pi.zero_apply,sub_zero,Function.comp_def] at ht
  convert ht using 1
  funext n
  rw [meshMassCompensator_decomposition,hω.2.1,sub_zero]

/-- The exact last-full-cell convention, including an infinite endpoint,
recovers the stopped mass in probability. -/
theorem meshMassCompensator_stopped_tendstoInMeasure
    (ℱ : ℕ → Filtration ℕ mΩ) (A : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ)
    (hA : ∀ t, Measurable (A t))
    (hgrid : ∀ n i, StronglyMeasurable[ℱ n i] (A (compensatorMeshTime n i)))
    (hL : MemLp L 2 P)
    (hp : ∀ᵐ ω ∂P, Monotone (fun t => A t ω) ∧ A 0 ω=0 ∧
      Continuous (fun t => A t ω) ∧ Tendsto (fun t => A t ω) atTop (𝓝 (L ω)) ∧
      ∀ t, A t ω ≤ L ω)
    (T : Ω → ℝ≥0∞) (hT : Measurable T) :
    TendstoInMeasure P
      (fun n ω => meshMassCompensator P ℱ A n (compensatorStopIndex n (T ω)) ω)
      atTop (fun ω => massAtExtendedTime (fun t => A t ω) (L ω) (T ω)) := by
  apply meshMassCompensator_selected_tendstoInMeasure P ℱ A L _ hA hgrid hL hp
    (fun n ω => compensatorStopIndex n (T ω))
    (fun n => compensatorStopIndex_measurable T hT n)
    (fun n ω => compensatorStopIndex_le n (T ω))
  filter_upwards [hp] with ω hω
  exact massAt_compensatorEndpoint_tendsto (fun t => A t ω) (L ω)
    hω.2.2.1 hω.2.2.2.1 (T ω)

end SLEExactGauge

end

end OAI
