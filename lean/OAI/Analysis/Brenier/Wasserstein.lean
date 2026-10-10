import OAI.Analysis.Brenier.Optimality

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Problem358

variable {d : ℕ}

/-- The real-valued transport distance is nonnegative. -/
theorem wasserstein2_nonneg (μ ν : Measure (E d)) :
    0 ≤ wasserstein2 μ ν :=
  Real.sqrt_nonneg _

/-- Any finite-cost coupling supplies an upper bound for the transport distance. -/
theorem wasserstein2_le_of_coupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hfin : quadraticPlanCost π ≠ ∞) :
    wasserstein2 μ ν ≤ Real.sqrt (quadraticPlanCost π).toReal := by
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono hfin
  exact sInf_le ⟨π, hπ, rfl⟩

/-- A coupling which minimizes the extended cost computes the defined distance. -/
theorem wasserstein2_eq_of_minimizing_coupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hmin : ∀ π', IsCoupling μ ν π' → quadraticPlanCost π ≤ quadraticPlanCost π') :
    wasserstein2 μ ν = Real.sqrt (quadraticPlanCost π).toReal := by
  have hinf : sInf {r : ℝ≥0∞ | ∃ π' : Measure (E d × E d),
      IsCoupling μ ν π' ∧ quadraticPlanCost π' = r} = quadraticPlanCost π := by
    apply le_antisymm
    · exact sInf_le ⟨π, hπ, rfl⟩
    · apply le_sInf
      rintro r ⟨π', hπ', rfl⟩
      exact hmin π' hπ'
  unfold wasserstein2
  rw [hinf]

private theorem swap_isCoupling {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π) :
    IsCoupling ν μ (π.map Prod.swap) := by
  have : IsProbabilityMeasure π := hπ.1
  refine ⟨inferInstance, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst measurable_swap]
    exact hπ.2.2
  · rw [Measure.map_map measurable_snd measurable_swap]
    exact hπ.2.1

/-- Swapping both variables in a plan preserves quadratic cost. -/
theorem quadraticPlanCost_swap (π : Measure (E d × E d)) :
    quadraticPlanCost (π.map Prod.swap) = quadraticPlanCost π := by
  unfold quadraticPlanCost
  rw [lintegral_map (by fun_prop) measurable_swap]
  congr 1
  funext p
  dsimp only [Prod.swap]
  rw [norm_sub_rev]

/-- The transport distance is symmetric, including for arbitrary input measures. -/
theorem wasserstein2_symm (μ ν : Measure (E d)) :
    wasserstein2 μ ν = wasserstein2 ν μ := by
  have hset : {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π = r} =
      {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
      IsCoupling ν μ π ∧ quadraticPlanCost π = r} := by
    ext r
    constructor
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨π.map Prod.swap, swap_isCoupling hπ, quadraticPlanCost_swap π⟩
    · rintro ⟨π, hπ, rfl⟩
      exact ⟨π.map Prod.swap, swap_isCoupling hπ, quadraticPlanCost_swap π⟩
  unfold wasserstein2
  rw [hset]

/-- Every probability measure has zero distance from itself. -/
theorem wasserstein2_self (μ : Measure (E d)) [IsProbabilityMeasure μ] :
    wasserstein2 μ μ = 0 := by
  let π : Measure (E d × E d) := μ.map (fun x => (x, x))
  have hmeas : Measurable (fun x : E d => (x, x)) := measurable_id.prodMk measurable_id
  have hπ : IsCoupling μ μ π := by
    refine ⟨inferInstance, ?_, ?_⟩
    · change (μ.map (fun x => (x, x))).map Prod.fst = μ
      rw [Measure.map_map measurable_fst hmeas]
      exact Measure.map_id
    · change (μ.map (fun x => (x, x))).map Prod.snd = μ
      rw [Measure.map_map measurable_snd hmeas]
      exact Measure.map_id
  have hcost : quadraticPlanCost π = 0 := by
    unfold quadraticPlanCost π
    rw [lintegral_map (by fun_prop) hmeas]
    simp
  apply le_antisymm
  · have h := wasserstein2_le_of_coupling hπ (by rw [hcost]; exact ENNReal.zero_ne_top)
    simpa [hcost] using h
  · exact wasserstein2_nonneg μ μ

/-- The infimum defining `wasserstein2` can be approximated by finite-cost plans.
This does not require existence of an optimal coupling. -/
theorem exists_coupling_sqrt_cost_lt {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {ε : ℝ} (hε : 0 < ε) :
    ∃ π : Measure (E d × E d), IsCoupling μ ν π ∧
      quadraticPlanCost π ≠ ∞ ∧
      Real.sqrt (quadraticPlanCost π).toReal < wasserstein2 μ ν + ε := by
  let c : ℝ≥0∞ := sInf {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
    IsCoupling μ ν π ∧ quadraticPlanCost π = r}
  have hcfinite : c ≠ ∞ :=
    ne_top_of_le_ne_top hfinite (sInf_le ⟨π₀, hπ₀, rfl⟩)
  have hc : c < ENNReal.ofReal ((wasserstein2 μ ν + ε) ^ 2) := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt hcfinite).2
    change c.toReal < (Real.sqrt c.toReal + ε) ^ 2
    have hsqrt := Real.sq_sqrt (ENNReal.toReal_nonneg (a := c))
    have hnonneg := Real.sqrt_nonneg c.toReal
    nlinarith
  obtain ⟨r, ⟨π, hπ, hcost⟩, hr⟩ := sInf_lt_iff.mp hc
  have hlt : quadraticPlanCost π < ENNReal.ofReal ((wasserstein2 μ ν + ε) ^ 2) := by
    rwa [hcost]
  refine ⟨π, hπ, hlt.ne_top, ?_⟩
  apply (Real.sqrt_lt' (add_pos_of_nonneg_of_pos (wasserstein2_nonneg μ ν) hε)).2
  exact ENNReal.toReal_lt_of_lt_ofReal hlt

end Problem358

namespace Problem358

/-- A single Euclidean coordinate is dominated by the Euclidean norm. -/
lemma coordinate_sq_le_norm_sq {d : ℕ} (x : E d) (j : Fin d) :
    (x j) ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := PiLp.norm_apply_le x j
  have hsq := pow_le_pow_left₀ (norm_nonneg (x j)) h 2
  simpa only [Real.norm_eq_abs, sq_abs] using hsq

/-- If the source coordinate vanishes, displacement controls the target coordinate. -/
lemma coordinate_sq_le_displacement_sq {d : ℕ} (x y : E d) (j : Fin d)
    (hx : x j = 0) :
    (y j) ^ 2 ≤ ‖x - y‖ ^ 2 := by
  simpa [hx] using coordinate_sq_le_norm_sq (x - y) j

/-- Every coupling pays at least the target coordinate second moment when the
source is concentrated on the zero coordinate hyperplane. -/
lemma coordinate_moment_le_quadraticPlanCost {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π) :
    (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) ≤ quadraticPlanCost π := by
  have hsource : ∀ᵐ p ∂π, p.1 j = 0 := by
    have hμ' : ∀ᵐ x ∂Measure.map Prod.fst π, x j = 0 := by
      simpa only [hπ.2.1] using hμ
    exact ae_of_ae_map measurable_fst.aemeasurable hμ'
  rw [← hπ.2.2, lintegral_map (by fun_prop) measurable_snd]
  apply lintegral_mono_ae
  filter_upwards [hsource] with p hp
  exact ENNReal.ofReal_le_ofReal (coordinate_sq_le_displacement_sq p.1 p.2 j hp)

/-- The same lower bound passes to the infimum of all coupling costs. -/
lemma coordinate_moment_le_sInf_cost {d : ℕ}
    {μ ν : Measure (E d)} (j : Fin d) (hμ : ∀ᵐ x ∂μ, x j = 0) :
    (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) ≤
      sInf {r : ℝ≥0∞ | ∃ π : Measure (E d × E d),
        IsCoupling μ ν π ∧ quadraticPlanCost π = r} := by
  apply le_sInf
  rintro r ⟨π, hπ, rfl⟩
  exact coordinate_moment_le_quadraticPlanCost j hμ hπ

/-- A finite-cost coupling makes the coordinate-moment bound valid after taking
`toReal` and square roots. The finiteness hypothesis is essential because
`ENNReal.toReal ∞ = 0`. -/
lemma sqrt_coordinate_moment_le_wasserstein2 {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hfinite : quadraticPlanCost π < ∞) :
    Real.sqrt (ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν)) ≤
      wasserstein2 μ ν := by
  unfold wasserstein2
  apply Real.sqrt_le_sqrt
  apply ENNReal.toReal_mono _ (coordinate_moment_le_sInf_cost j hμ)
  apply ne_of_lt
  refine lt_of_le_of_lt ?_ hfinite
  exact sInf_le ⟨π, hπ, rfl⟩

/-- A coupling attaining the coordinate lower bound computes the Wasserstein
quantity exactly; in particular this applies to the central-atom matching plan. -/
lemma wasserstein2_eq_sqrt_coordinate_moment {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hcost : quadraticPlanCost π = ∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :
    wasserstein2 μ ν =
      Real.sqrt (ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν)) := by
  unfold wasserstein2
  congr 2
  apply le_antisymm
  · exact sInf_le ⟨π, hπ, hcost⟩
  · exact coordinate_moment_le_sInf_cost j hμ

/-- A positive target coordinate moment separates the measures in Wasserstein
quantity whenever a finite-cost coupling exists. -/
lemma wasserstein2_pos_of_coordinate_moment_pos {d : ℕ}
    {μ ν : Measure (E d)} {π : Measure (E d × E d)} (j : Fin d)
    (hμ : ∀ᵐ x ∂μ, x j = 0) (hπ : IsCoupling μ ν π)
    (hfinite : quadraticPlanCost π < ∞)
    (hpos : 0 < ∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :
    0 < wasserstein2 μ ν := by
  have hmfinite : (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) < ∞ :=
    lt_of_le_of_lt (coordinate_moment_le_quadraticPlanCost j hμ hπ) hfinite
  have hmpos : 0 < ENNReal.toReal (∫⁻ y, ENNReal.ofReal ((y j) ^ 2) ∂ν) :=
    ENNReal.toReal_pos hpos.ne' hmfinite.ne
  exact lt_of_lt_of_le (Real.sqrt_pos.2 hmpos)
    (sqrt_coordinate_moment_le_wasserstein2 j hμ hπ hfinite)

end Problem358

end

noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace Problem358

/-- The second-moment inequality for a real random variable on a probability space. -/
theorem testing_integral_sq_le {X : Type*} [MeasurableSpace X]
    {ρ : Measure X} [IsProbabilityMeasure ρ] {f : X → ℝ} (hf : MemLp f 2 ρ) :
    (∫ x, f x ∂ρ) ^ 2 ≤ ∫ x, (f x) ^ 2 ∂ρ := by
  have h := ProbabilityTheory.variance_nonneg f ρ
  rw [ProbabilityTheory.variance_eq_sub hf] at h
  exact sub_nonneg.mp h

/-- A finite-cost coupling controls the difference of Lipschitz test integrals. -/
theorem integral_test_le_sqrt_cost {d : ℕ} {μ ν : Measure (E d)}
    {π : Measure (E d × E d)} (hπ : IsCoupling μ ν π)
    (hc : quadraticPlanCost π ≠ ∞) {L : ℝ≥0} {f : E d → ℝ}
    (hf : LipschitzWith L f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    |(∫ x, f x ∂μ) - ∫ y, f y ∂ν| ≤
      L * Real.sqrt (quadraticPlanCost π).toReal := by
  let : IsProbabilityMeasure π := hπ.1
  have hd2 := integrable_sqdist_of_cost_ne_top hc
  have hdLp : MemLp (fun p : E d × E d => ‖p.1 - p.2‖) 2 π :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mpr hd2
  have hd : Integrable (fun p : E d × E d => ‖p.1 - p.2‖) π :=
    hdLp.integrable (by norm_num)
  have hmean : (∫ p : E d × E d, ‖p.1 - p.2‖ ∂π) ≤
      Real.sqrt (quadraticPlanCost π).toReal := by
    have hsq := testing_integral_sq_le hdLp
    rw [quadraticPlanCost_eq_ofReal_integral hd2, ENNReal.toReal_ofReal
      (integral_nonneg fun p => sq_nonneg _)]
    exact Real.le_sqrt_of_sq_le hsq
  have hdiff : Integrable (fun p : E d × E d => f p.1 - f p.2) π := by
    simpa only [sub_eq_add_neg, Pi.neg_apply] using dual_integrable_sum hπ hfμ hfν.neg
  have heq : (∫ p : E d × E d, f p.1 - f p.2 ∂π) =
      (∫ x, f x ∂μ) - ∫ y, f y ∂ν := by
    simpa only [sub_eq_add_neg, Pi.neg_apply, integral_neg] using dual_integral_sum hπ hfμ hfν.neg
  rw [← heq, ← Real.norm_eq_abs]
  calc
    ‖∫ p : E d × E d, f p.1 - f p.2 ∂π‖ ≤
        ∫ p : E d × E d, ‖f p.1 - f p.2‖ ∂π := norm_integral_le_integral_norm _
    _ ≤ ∫ p : E d × E d, (L : ℝ) * ‖p.1 - p.2‖ ∂π :=
      integral_mono hdiff.norm (hd.const_mul _) (fun p => by
        simpa only [dist_eq_norm] using hf.dist_le_mul p.1 p.2)
    _ = (L : ℝ) * ∫ p : E d × E d, ‖p.1 - p.2‖ ∂π := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hmean L.coe_nonneg

/-- A nonnegative square-root lower bound passes to the infimum of extended costs. -/
theorem testing_sqrt_sInf_bound (S : Set ℝ≥0∞)
    (hfinite : ∃ r ∈ S, r ≠ ∞) {D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L)
    (hbound : ∀ r ∈ S, r ≠ ∞ → D ≤ L * Real.sqrt r.toReal) :
    D ≤ L * Real.sqrt (sInf S).toReal := by
  obtain ⟨r₀, hr₀, hfin₀⟩ := hfinite
  by_cases hzero : L = 0
  · simpa only [hzero, zero_mul] using hbound r₀ hr₀ hfin₀
  have hLpos : 0 < L := lt_of_le_of_ne hL (Ne.symm hzero)
  have hSfinite : sInf S ≠ ∞ :=
    (lt_of_le_of_lt (sInf_le hr₀) (lt_top_iff_ne_top.mpr hfin₀)).ne
  have hlower : ENNReal.ofReal ((D / L) ^ 2) ≤ sInf S := by
    apply le_sInf
    intro r hr
    by_cases hrTop : r = ∞
    · simp only [hrTop, le_top]
    have hdiv : D / L ≤ Real.sqrt r.toReal :=
      (div_le_iff₀ hLpos).mpr (by simpa only [mul_comm] using hbound r hr hrTop)
    apply ENNReal.ofReal_le_of_le_toReal
    exact (Real.le_sqrt (div_nonneg hD hL) ENNReal.toReal_nonneg).mp hdiv
  have hsq : (D / L) ^ 2 ≤ (sInf S).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hSfinite).mp hlower
  have h := (div_le_iff₀ hLpos).mp (Real.le_sqrt_of_sq_le hsq)
  simpa only [mul_comm] using h

/-- Lipschitz testing is controlled by the problem's Wasserstein distance whenever a
finite-cost coupling exists. Compact support is not required in this interface. -/
theorem integral_test_le_wasserstein2 {d : ℕ} {μ ν : Measure (E d)}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    {L : ℝ≥0} {f : E d → ℝ} (hf : LipschitzWith L f)
    (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    |(∫ x, f x ∂μ) - ∫ y, f y ∂ν| ≤ L * wasserstein2 μ ν := by
  unfold wasserstein2
  refine testing_sqrt_sInf_bound _ ?_ (abs_nonneg _) L.coe_nonneg ?_
  · obtain ⟨π, hπ, hc⟩ := hfinite
    exact ⟨quadraticPlanCost π, ⟨π, hπ, rfl⟩, hc⟩
  · intro r hr hfin
    obtain ⟨π, hπ, rfl⟩ := hr
    exact integral_test_le_sqrt_cost hπ hfin hf hfμ hfν

/-- A zero-Wasserstein pair agrees on every integrable Lipschitz test. -/
theorem integral_test_eq_of_wasserstein2_eq_zero {d : ℕ} {μ ν : Measure (E d)}
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hzero : wasserstein2 μ ν = 0) {L : ℝ≥0} {f : E d → ℝ}
    (hf : LipschitzWith L f) (hfμ : Integrable f μ) (hfν : Integrable f ν) :
    (∫ x, f x ∂μ) = ∫ y, f y ∂ν := by
  have h := integral_test_le_wasserstein2 hfinite hf hfμ hfν
  rw [hzero, mul_zero] at h
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))

/-- Wasserstein convergence with finite-cost couplings implies weak convergence. -/
theorem tendsto_probabilityMeasure_of_wasserstein2_tendsto_zero
    {d : ℕ} {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure (E d)} {ν : ProbabilityMeasure (E d)}
    (hfinite : ∀ i, ∃ π : Measure (E d × E d),
      IsCoupling (μs i : Measure (E d)) (ν : Measure (E d)) π ∧ quadraticPlanCost π ≠ ∞)
    (hW : Tendsto (fun i => wasserstein2 (μs i : Measure (E d)) (ν : Measure (E d))) l (𝓝 0)) :
    Tendsto μs l (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro f hb hLip
  obtain ⟨L, hf⟩ := hLip
  let g : BoundedContinuousFunction (E d) ℝ :=
    { toFun := f
      continuous_toFun := hf.continuous
      map_bounded' := hb }
  have hfμ (i : ι) : Integrable f (μs i : Measure (E d)) := g.integrable (μ := (μs i : Measure (E d)))
  have hfν : Integrable f (ν : Measure (E d)) := g.integrable (μ := (ν : Measure (E d)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun i => (L : ℝ) *
    wasserstein2 (μs i : Measure (E d)) (ν : Measure (E d)))
    (fun _ => norm_nonneg _) (fun i => ?_) ?_
  · simpa only [Real.norm_eq_abs] using
      integral_test_le_wasserstein2 (hfinite i) hf (hfμ i) hfν
  · simpa only [mul_zero] using hW.const_mul (L : ℝ)

/-- Finite-cost probability measures at zero Wasserstein distance are equal. -/
theorem measure_eq_of_wasserstein2_eq_zero {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞)
    (hzero : wasserstein2 μ ν = 0) : μ = ν := by
  let μp : ProbabilityMeasure (E d) := ⟨μ, inferInstance⟩
  let νp : ProbabilityMeasure (E d) := ⟨ν, inferInstance⟩
  have hconv : Tendsto (fun _ : ℕ => μp) atTop (𝓝 νp) := by
    apply tendsto_probabilityMeasure_of_wasserstein2_tendsto_zero (fun _ => hfinite)
    change Tendsto (fun _ : ℕ => wasserstein2 μ ν) atTop (𝓝 0)
    simpa only [hzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  have heq : μp = νp := tendsto_nhds_unique tendsto_const_nhds hconv
  exact congrArg (fun p : ProbabilityMeasure (E d) => (p : Measure (E d))) heq

/-- Distinct probabilities with a finite-cost coupling have positive Wasserstein distance. -/
theorem wasserstein2_pos_of_ne_of_finite_coupling {d : ℕ} {μ ν : Measure (E d)}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hfinite : ∃ π : Measure (E d × E d),
      IsCoupling μ ν π ∧ quadraticPlanCost π ≠ ∞) (hne : μ ≠ ν) :
    0 < wasserstein2 μ ν := by
  apply lt_of_le_of_ne (Real.sqrt_nonneg _)
  intro hzero
  exact hne (measure_eq_of_wasserstein2_eq_zero hfinite hzero.symm)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Problem358

variable {d : ℕ}

/-- A continuous nondecreasing function of root cost commutes with the transport
infimum for purposes of universal lower estimates. No minimizing plan is required. -/
theorem le_of_le_all_coupling_sqrt_cost {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {F : ℝ → ℝ}
    (hmono : MonotoneOn F (Set.Ici 0))
    (hcont : ContinuousAt F (wasserstein2 μ ν)) {a : ℝ}
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ → a ≤ F (Real.sqrt (quadraticPlanCost π).toReal)) :
    a ≤ F (wasserstein2 μ ν) := by
  have hlim : Tendsto (fun ε : ℝ => F (wasserstein2 μ ν + ε))
      (𝓝[>] 0) (𝓝 (F (wasserstein2 μ ν))) := by
    apply hcont.tendsto.comp
    simpa using (tendsto_const_nhds.add
      (tendsto_id.mono_left nhdsWithin_le_nhds) :
      Tendsto (fun ε : ℝ => wasserstein2 μ ν + ε) (𝓝[>] 0)
        (𝓝 (wasserstein2 μ ν + 0)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  obtain ⟨π, hπ, hfin, hlt⟩ := exists_coupling_sqrt_cost_lt hπ₀ hfinite hε
  exact (hbound π hπ hfin).trans (hmono (Real.sqrt_nonneg _)
    (add_nonneg (wasserstein2_nonneg μ ν) hε.le) hlt.le)

/-- Power-type estimates valid for every finite-cost coupling descend to the
exact transport distance, including at zero distance. -/
theorem le_mul_rpow_wasserstein2_of_coupling_bound {μ ν : Measure (E d)}
    {π₀ : Measure (E d × E d)} (hπ₀ : IsCoupling μ ν π₀)
    (hfinite : quadraticPlanCost π₀ ≠ ∞) {a C α : ℝ}
    (hC : 0 ≤ C) (hα : 0 ≤ α)
    (hbound : ∀ π : Measure (E d × E d), IsCoupling μ ν π →
      quadraticPlanCost π ≠ ∞ →
      a ≤ C * Real.rpow (Real.sqrt (quadraticPlanCost π).toReal) α) :
    a ≤ C * Real.rpow (wasserstein2 μ ν) α := by
  apply le_of_le_all_coupling_sqrt_cost hπ₀ hfinite (F := fun x => C * x ^ α)
  · intro x hx y hy hxy
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx hxy hα) hC
  · exact (continuous_const.mul (Real.continuous_rpow_const hα)).continuousAt
  · exact hbound

end Problem358

end

end OAI
