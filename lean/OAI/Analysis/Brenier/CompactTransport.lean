import OAI.Analysis.Brenier.CompactMeasure
import OAI.Analysis.Brenier.Wasserstein

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

/-- A coupling inherits almost-everywhere support from each marginal. -/
theorem IsCoupling.ae_mem {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∀ᵐ p ∂π, p.1 ∈ K ∧ p.2 ∈ Y := by
  have hμae : ∀ᵐ x ∂μ, x ∈ K := by
    rw [ae_iff]
    exact hμ
  have hνae : ∀ᵐ y ∂ν, y ∈ Y := by
    rw [ae_iff]
    exact hν
  have hfst : ∀ᵐ p ∂π, p.1 ∈ K := by
    apply ae_of_ae_map measurable_fst.aemeasurable
    simpa only [hπ.2.1] using hμae
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ Y := by
    apply ae_of_ae_map measurable_snd.aemeasurable
    simpa only [hπ.2.2] using hνae
  exact hfst.and hsnd

/-- Finite second cost for a coupling whose two marginals have compact support. -/
theorem IsCoupling.integrable_sqDist_of_compact {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π := by
  let : IsProbabilityMeasure π := hπ.1
  obtain ⟨R, hR, hRK⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨S, hS, hSY⟩ := hY.isBounded.exists_pos_norm_le
  have hmeas : AEStronglyMeasurable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) π :=
    ((continuous_fst.sub continuous_snd).norm.pow 2).aestronglyMeasurable
  apply (integrable_const ((R + S) ^ 2)).mono' hmeas
  filter_upwards [hπ.ae_mem hμ hν] with p hp
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans (add_le_add (hRK _ hp.1) (hSY _ hp.2))) 2

/-- On compact marginal supports every coupling has finite ENNReal quadratic cost. -/
theorem IsCoupling.quadraticPlanCost_ne_top_of_compact {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)}
    (hπ : IsCoupling μ ν π) (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    quadraticPlanCost π ≠ ∞ := by
  have hi := hπ.integrable_sqDist_of_compact hK hY hμ hν
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => sq_nonneg ‖p.1 - p.2‖))).2 hi

/-- An explicit uniform cost bound from bounds on the marginal supports. -/
theorem IsCoupling.quadraticPlanCost_le_of_norm_le {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} {K Y : Set (E d)} {R S : ℝ}
    (hπ : IsCoupling μ ν π) (hμ : IsSupported μ K) (hν : IsSupported ν Y)
    (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hY : ∀ y ∈ Y, ‖y‖ ≤ S) :
    quadraticPlanCost π ≤ ENNReal.ofReal ((R + S) ^ 2) := by
  let : IsProbabilityMeasure π := hπ.1
  calc
    quadraticPlanCost π ≤ ∫⁻ _ : E d × E d, ENNReal.ofReal ((R + S) ^ 2) ∂π := by
      apply lintegral_mono_ae
      filter_upwards [hπ.ae_mem hμ hν] with p hp
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (norm_nonneg _) ((norm_sub_le _ _).trans
        (add_le_add (hK _ hp.1) (hY _ hp.2))) 2
    _ = ENNReal.ofReal ((R + S) ^ 2) := by simp

end Problem358

end

noncomputable section
open MeasureTheory
open scoped Topology

namespace Problem358

section MeasurableSpaces
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- The closed set of probability measures with two specified marginals. -/
def probabilityCouplings (μ : ProbabilityMeasure X) (ν : ProbabilityMeasure Y) :
    Set (ProbabilityMeasure (X × Y)) :=
  {π | π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

theorem probabilityCouplings_nonempty (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : (probabilityCouplings μ ν).Nonempty := by
  let π : ProbabilityMeasure (X × Y) :=
    ⟨(μ : Measure X).prod (ν : Measure Y), inferInstance⟩
  refine ⟨π, ?_, ?_⟩
  · apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.fst ((μ : Measure X).prod (ν : Measure Y)) = μ
    simp
  · apply ProbabilityMeasure.toMeasure_injective
    change Measure.map Prod.snd ((μ : Measure X).prod (ν : Measure Y)) = ν
    simp

end MeasurableSpaces

section MetricSpaces
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [SecondCountableTopology Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

theorem isClosed_probabilityCouplings (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : IsClosed (probabilityCouplings μ ν) :=
  (isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const).inter
    (isClosed_eq (ProbabilityMeasure.continuous_map continuous_snd) continuous_const)

end MetricSpaces

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [CompactSpace X] [CompactSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]

theorem isCompact_probabilityCouplings (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) : IsCompact (probabilityCouplings μ ν) :=
  (isClosed_probabilityCouplings μ ν).isCompact

/-- Every continuous real cost attains its minimum over compact-space probability couplings. -/
theorem exists_probabilityCoupling_minimizer (μ : ProbabilityMeasure X)
    (ν : ProbabilityMeasure Y) (c : X × Y → ℝ) (hc : Continuous c) :
    ∃ π ∈ probabilityCouplings μ ν,
      ∀ η ∈ probabilityCouplings μ ν,
        (∫ p, c p ∂(π : Measure (X × Y))) ≤ ∫ p, c p ∂(η : Measure (X × Y)) := by
  have hcost : Continuous (fun π : ProbabilityMeasure (X × Y) =>
      ∫ p, c p ∂(π : Measure (X × Y))) :=
    ProbabilityMeasure.continuous_integral_continuousMap (⟨c, hc⟩ : ContinuousMap (X × Y) ℝ)
  exact (isCompact_probabilityCouplings μ ν).exists_isMinOn
    (probabilityCouplings_nonempty μ ν) hcost.continuousOn

/-- Unbundled continuous-cost minimization, for direct use with measure-valued plans. -/
theorem exists_compact_coupling_minimizer (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (c : X × Y → ℝ) (hc : Continuous c) :
    ∃ π : Measure (X × Y), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧ Measure.map Prod.snd π = ν ∧
      ∀ η : Measure (X × Y), IsProbabilityMeasure η →
        Measure.map Prod.fst η = μ → Measure.map Prod.snd η = ν →
        (∫ p, c p ∂π) ≤ ∫ p, c p ∂η := by
  let μp : ProbabilityMeasure X := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure Y := ⟨ν, inferInstance⟩
  obtain ⟨π, hπ, hmin⟩ := exists_probabilityCoupling_minimizer μp νp c hc
  refine ⟨π, inferInstance, ?_, ?_, ?_⟩
  · exact congrArg (fun p : ProbabilityMeasure X => (p : Measure X)) hπ.1
  · exact congrArg (fun p : ProbabilityMeasure Y => (p : Measure Y)) hπ.2
  · intro η hη hfst hsnd
    exact hmin ⟨η, hη⟩
      ⟨ProbabilityMeasure.toMeasure_injective hfst,
        ProbabilityMeasure.toMeasure_injective hsnd⟩

end Problem358

end

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Problem358

/-- Fixed compact support determines a compact set of probability measures. -/
theorem isCompact_probability_supported {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {K : Set X} (hK : IsCompact K) :
    IsCompact {μ : ProbabilityMeasure X | (μ : Measure X) Kᶜ = 0} := by
  have h := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (K := fun _ : ℕ => K) (u := fun _ : ℕ => (0 : ℝ≥0))
    tendsto_const_nhds (fun _ => hK) (Or.inl inferInstance)
  simpa only [Set.mem_ofPred_eq, le_zero_iff, forall_const,
    ProbabilityMeasure.null_iff_toMeasure_null] using h

/-- Couplings of supported marginals are concentrated on the product of their supports. -/
theorem probabilityCouplings_ae_mem_prod {d : ℕ}
    {μ ν : ProbabilityMeasure (E d)} {K Y : Set (E d)}
    (hμ : (μ : Measure (E d)) Kᶜ = 0) (hν : (ν : Measure (E d)) Yᶜ = 0)
    {π : ProbabilityMeasure (E d × E d)} (hπ : π ∈ probabilityCouplings μ ν) :
    ∀ᵐ p ∂(π : Measure (E d × E d)), p ∈ K ×ˢ Y := by
  have hfst : Measure.map Prod.fst (π : Measure (E d × E d)) = μ :=
    congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) hπ.1
  have hsnd : Measure.map Prod.snd (π : Measure (E d × E d)) = ν :=
    congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) hπ.2
  have hμae : ∀ᵐ x ∂(μ : Measure (E d)), x ∈ K := ae_iff.mpr hμ
  have hνae : ∀ᵐ x ∂(ν : Measure (E d)), x ∈ Y := ae_iff.mpr hν
  have ha := ae_of_ae_map measurable_fst.aemeasurable (hfst.symm ▸ hμae)
  have hb := ae_of_ae_map measurable_snd.aemeasurable (hsnd.symm ▸ hνae)
  filter_upwards [ha, hb] with p hp hq
  exact ⟨hp, hq⟩

/-- Compactly supported marginals have a compact set of couplings in the weak topology. -/
theorem isCompact_probabilityCouplings_of_supported {d : ℕ}
    {μ ν : ProbabilityMeasure (E d)} {K Y : Set (E d)}
    (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : (μ : Measure (E d)) Kᶜ = 0) (hν : (ν : Measure (E d)) Yᶜ = 0) :
    IsCompact (probabilityCouplings μ ν) := by
  apply (isCompact_probability_supported (hK.prod hY)).of_isClosed_subset
    (isClosed_probabilityCouplings μ ν)
  intro π hπ
  exact ae_iff.mp (probabilityCouplings_ae_mem_prod hμ hν hπ)

/-- A conveniently clipped quadratic cost, bounded and continuous on the full product space. -/
def boundedQuadraticCost (d : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    BoundedContinuousFunction (E d × E d) ℝ where
  toFun p := min M (‖p.1 - p.2‖ ^ 2)
  continuous_toFun := by fun_prop
  map_bounded' := by
    refine ⟨2 * M, fun p q => ?_⟩
    have hp : 0 ≤ min M (‖p.1 - p.2‖ ^ 2) := le_min hM (sq_nonneg _)
    have hq : 0 ≤ min M (‖q.1 - q.2‖ ^ 2) := le_min hM (sq_nonneg _)
    calc
      dist (min M (‖p.1 - p.2‖ ^ 2)) (min M (‖q.1 - q.2‖ ^ 2))
          ≤ |min M (‖p.1 - p.2‖ ^ 2)| + |min M (‖q.1 - q.2‖ ^ 2)| := by
            simpa only [Real.dist_eq, sub_zero, zero_sub, abs_neg] using
              abs_sub_le (min M (‖p.1 - p.2‖ ^ 2)) 0 (min M (‖q.1 - q.2‖ ^ 2))
      _ ≤ M + M := by
        rw [abs_of_nonneg hp, abs_of_nonneg hq]
        exact add_le_add (min_le_left _ _) (min_le_left _ _)
      _ = 2 * M := by ring

/-- Compactly supported probabilities have a minimizing quadratic transport plan. -/
theorem exists_quadraticOptimalPlan_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧
      quadraticPlanCost π ≠ ∞ ∧
      ∀ η : Measure (E d × E d), IsCoupling μ ν η →
        quadraticPlanCost π ≤ quadraticPlanCost η := by
  let μp : ProbabilityMeasure (E d) := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure (E d) := ⟨ν, inferInstance⟩
  obtain ⟨B, hB⟩ := (hK.prod hY).exists_bound_of_continuousOn
    (show ContinuousOn (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2) (K ×ˢ Y) by fun_prop)
  let M := max B 0
  let c := boundedQuadraticCost d M (le_max_right B 0)
  have heq (π : ProbabilityMeasure (E d × E d))
      (hπ : π ∈ probabilityCouplings μp νp) :
      ∀ᵐ p ∂(π : Measure (E d × E d)), c p = ‖p.1 - p.2‖ ^ 2 := by
    filter_upwards [probabilityCouplings_ae_mem_prod
      (μ := μp) (ν := νp) (K := K) (Y := Y) hμ hν hπ] with p hp
    have hbp : ‖p.1 - p.2‖ ^ 2 ≤ B := by
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hB p hp
    exact min_eq_right (hbp.trans (le_max_left B 0))
  have hcost (π : ProbabilityMeasure (E d × E d))
      (hπ : π ∈ probabilityCouplings μp νp) :
      quadraticPlanCost (π : Measure (E d × E d)) =
        ENNReal.ofReal (∫ p, c p ∂(π : Measure (E d × E d))) := by
    have hc : Integrable (fun p : E d × E d => ‖p.1 - p.2‖ ^ 2)
        (π : Measure (E d × E d)) :=
      (c.integrable (μ := (π : Measure (E d × E d)))).congr (heq π hπ)
    rw [quadraticPlanCost_eq_ofReal_integral hc]
    congr 1
    exact integral_congr_ae (Filter.EventuallyEq.symm (heq π hπ))
  have hcompact := isCompact_probabilityCouplings_of_supported
    (μ := μp) (ν := νp) hK hY hμ hν
  have hccont : Continuous (fun π : ProbabilityMeasure (E d × E d) =>
      ∫ p, c p ∂(π : Measure (E d × E d))) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction c
  obtain ⟨π, hπ, hmin⟩ := hcompact.exists_isMinOn
    (probabilityCouplings_nonempty μp νp) hccont.continuousOn
  refine ⟨π, ⟨inferInstance, ?_, ?_⟩, ?_, ?_⟩
  · exact congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) hπ.1
  · exact congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) hπ.2
  · rw [hcost π hπ]
    exact ENNReal.ofReal_ne_top
  · intro η hη
    let ηp : ProbabilityMeasure (E d × E d) := ⟨η, hη.1⟩
    have hηp : ηp ∈ probabilityCouplings μp νp :=
      ⟨ProbabilityMeasure.toMeasure_injective hη.2.1,
        ProbabilityMeasure.toMeasure_injective hη.2.2⟩
    change quadraticPlanCost (π : Measure (E d × E d)) ≤
      quadraticPlanCost (ηp : Measure (E d × E d))
    rw [hcost π hπ, hcost ηp hηp]
    exact ENNReal.ofReal_le_ofReal (hmin hηp)

/-- In particular, a finite-cost plan is available for any compactly supported probabilities. -/
theorem exists_finite_cost_coupling_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞ := by
  obtain ⟨π, hπ, hfinite, _⟩ :=
    exists_quadraticOptimalPlan_of_compact_support μ ν hK hY hμ hν
  exact ⟨π, hπ, hfinite⟩

end Problem358

end

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open Filter
open scoped Topology

namespace Problem358

/-- The infimum in the exact Wasserstein definition is attained for compact supports. -/
theorem wasserstein2_attained_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞ ∧
      wasserstein2 μ ν = Real.sqrt (quadraticPlanCost π).toReal := by
  obtain ⟨π, hπ, hfin, hopt⟩ :=
    exists_quadraticOptimalPlan_of_compact_support μ ν hK hY hμ hν
  exact ⟨π, hπ, hfin, wasserstein2_eq_of_minimizing_coupling hπ hopt⟩

/-- Zero distance separates compactly supported probabilities. -/
theorem wasserstein2_eq_zero_iff_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    wasserstein2 μ ν = 0 ↔ μ = ν := by
  constructor
  · exact measure_eq_of_wasserstein2_eq_zero
      (exists_finite_cost_coupling_of_compact_support μ ν hK hY hμ hν)
  · rintro rfl
    exact wasserstein2_self μ

/-- Distinct compactly supported probabilities have strictly positive distance. -/
theorem wasserstein2_pos_iff_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y) :
    0 < wasserstein2 μ ν ↔ μ ≠ ν := by
  rw [lt_iff_le_and_ne, and_iff_right (wasserstein2_nonneg μ ν), ne_comm]
  exact not_congr (wasserstein2_eq_zero_iff_of_compact_support μ ν hK hY hμ hν)

/-- Compact support discharges both the finite-cost and integrability hypotheses
in the Lipschitz testing inequality. -/
theorem integral_test_le_wasserstein2_of_compact_support {d : ℕ}
    (μ ν : Measure (E d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {K Y : Set (E d)} (hK : IsCompact K) (hY : IsCompact Y)
    (hμ : IsSupported μ K) (hν : IsSupported ν Y)
    {L : ℝ≥0} {f : E d → ℝ} (hf : LipschitzWith L f) :
    |(∫ x, f x ∂μ) - ∫ y, f y ∂ν| ≤ L * wasserstein2 μ ν := by
  exact integral_test_le_wasserstein2
    (exists_finite_cost_coupling_of_compact_support μ ν hK hY hμ hν) hf
    (hμ.integrable_continuousOn hK hf.continuous.continuousOn)
    (hν.integrable_continuousOn hY hf.continuous.continuousOn)

/-- On compact supports, Wasserstein convergence implies weak convergence without
an additional finite-cost hypothesis; the compact supports may vary with the index. -/
theorem tendsto_probabilityMeasure_of_compact_wasserstein2_tendsto_zero
    {d : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure (E d)} {ν : ProbabilityMeasure (E d)}
    {Ks : ι → Set (E d)} {Y : Set (E d)}
    (hKs : ∀ i, IsCompact (Ks i)) (hY : IsCompact Y)
    (hμs : ∀ i, IsSupported (μs i : Measure (E d)) (Ks i))
    (hν : IsSupported (ν : Measure (E d)) Y)
    (hW : Tendsto (fun i => wasserstein2 (μs i : Measure (E d)) (ν : Measure (E d)))
      l (𝓝 0)) : Tendsto μs l (𝓝 ν) := by
  exact tendsto_probabilityMeasure_of_wasserstein2_tendsto_zero
    (fun i => exists_finite_cost_coupling_of_compact_support
      (μs i : Measure (E d)) (ν : Measure (E d)) (hKs i) hY (hμs i) hν) hW

end Problem358

end

end OAI
