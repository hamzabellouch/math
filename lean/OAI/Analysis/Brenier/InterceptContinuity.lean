import OAI.Analysis.Brenier.FixedMass

namespace OAI

/-! Compactness and uniqueness imply continuous dependence of minimizers.
No differentiability or inverse-function theorem is used. -/

noncomputable section
open Set Filter
open scoped Topology

namespace Problem358.CompactArgmin

variable {P C I : Type*} [TopologicalSpace P] [TopologicalSpace C]

/-- A compactly constrained family of minimizers converges to the unique minimizer
of the limiting continuous objective. The feasible set may be noncompact. -/
theorem tendsto_of_unique_minimizer {l : Filter I} {p : I → P} {p₀ : P}
    {c : I → C} {c₀ : C} {S K : Set C} {F : P × C → ℝ}
    (hK : IsCompact K) (hS : IsClosed S) (hF : Continuous F)
    (hp : Tendsto p l (𝓝 p₀)) (hbounded : ∀ᶠ i in l, c i ∈ K)
    (hfeasible : ∀ᶠ i in l, c i ∈ S)
    (hmin : ∀ᶠ i in l, ∀ z ∈ S, F (p i, c i) ≤ F (p i, z))
    (hunique : ∀ z ∈ S, IsMinOn (fun w => F (p₀, w)) S z → z = c₀) :
    Tendsto c l (𝓝 c₀) := by
  apply hK.tendsto_nhds_of_unique_mapClusterPt hbounded
  intro z _ hz
  obtain ⟨U, hUl, hUz⟩ := mapClusterPt_iff_ultrafilter.mp hz
  have hzS : z ∈ S := hS.mem_of_tendsto hUz (hUl hfeasible)
  apply hunique z hzS
  intro w hw
  have hleft : Tendsto (fun i => F (p i, c i)) (U : Filter I) (𝓝 (F (p₀, z))) :=
    hF.continuousAt.tendsto.comp ((hp.mono_left hUl).prodMk_nhds hUz)
  have hright : Tendsto (fun i => F (p i, w)) (U : Filter I) (𝓝 (F (p₀, w))) :=
    hF.continuousAt.tendsto.comp ((hp.mono_left hUl).prodMk_nhds tendsto_const_nhds)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [hUl hmin] with i hi
  exact hi w hw

/-- Local compact bounds and uniqueness give continuity of an arbitrary selected minimizer. -/
theorem continuousAt_unique_minimizer {c : P → C} {p : P}
    {S K : Set C} {F : P × C → ℝ}
    (hK : IsCompact K) (hS : IsClosed S) (hF : Continuous F)
    (hbounded : ∀ᶠ q in 𝓝 p, c q ∈ K)
    (hfeasible : ∀ᶠ q in 𝓝 p, c q ∈ S)
    (hmin : ∀ᶠ q in 𝓝 p, ∀ z ∈ S, F (q, c q) ≤ F (q, z))
    (hunique : ∀ z ∈ S, IsMinOn (fun w => F (p, w)) S z → z = c p) :
    ContinuousAt c p :=
  tendsto_of_unique_minimizer hK hS hF tendsto_id hbounded hfeasible hmin hunique

end Problem358.CompactArgmin

end

noncomputable section
open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Finite affine maxima depend jointly continuously on sites, intercepts, and source points. -/
theorem continuous_joint_potential {d : ℕ} :
    Continuous (fun p : ((ι → E d) × (ι → ℝ)) × E d =>
      potential p.1.1 p.1.2 p.2) := by
  have h : Continuous (Finset.univ.sup' Finset.univ_nonempty
      (fun i (p : ((ι → E d) × (ι → ℝ)) × E d) => ⟪p.2, p.1.1 i⟫ + p.1.2 i)) := by
    apply Continuous.finset_sup'
    intro i _
    fun_prop
  convert h using 1
  funext p
  simp only [potential, Finset.sup'_apply]

/-- The integrated finite affine objective is jointly continuous in all sites and intercepts. -/
theorem continuous_uniform_integral_potential {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hne : (interior K).Nonempty) :
    Continuous (fun p : (ι → E d) × (ι → ℝ) =>
      ∫ x, potential p.1 p.2 x ∂uniformMeasure K) := by
  let := UniformSource.probability hK hne
  have h := continuous_parametric_integral_of_continuous
    (μ := uniformMeasure K)
    (f := fun (p : (ι → E d) × (ι → ℝ)) (x : E d) => potential p.1 p.2 x)
    (continuous_joint_potential (ι := ι) (d := d)) hK
  rwa [Measure.restrict_eq_self_of_ae_mem (UniformSource.ae_mem hK.measurableSet)] at h

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory Filter
open scoped RealInnerProductSpace BigOperators Topology

namespace Problem358.MaxPotential

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Any normalized minimizing intercept selection depends continuously on the sites
at every injective configuration. This needs neither moving-cell derivatives nor IFT. -/
theorem continuousAt_uniform_intercept_selection {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (c : (ι → E d) → ι → ℝ)
    (hc0 : ∀ y, ∑ i, m i * c y i = 0)
    (hcmin : ∀ y (a : ι → ℝ), (∑ i, m i * a i) = 0 →
      (∫ x, potential y (c y) x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K)
    (y : ι → E d) (hy : Function.Injective y) : ContinuousAt c y := by
  let := UniformSource.probability hK hne
  let L : NNReal := ⟨‖y‖ + 1, by positivity⟩
  let B : ℝ := 2 * (L : ℝ) * ∫ x, ‖x‖ ∂uniformMeasure K
  let S : Set (ι → ℝ) := {a | ∑ i, m i * a i = 0}
  let J : Set (ι → ℝ) := Set.Icc (fun i => -B / m i) (fun _ => B)
  have hS : IsClosed S := isClosed_eq (by fun_prop) continuous_const
  have hJ : IsCompact J := isCompact_Icc
  have hnorm : ∀ᶠ z : ι → E d in 𝓝 y, ‖z‖ < (L : ℝ) := by
    exact continuous_norm.continuousAt.eventually_lt continuousAt_const (by change ‖y‖ < ‖y‖ + 1; linarith)
  have hbounded : ∀ᶠ z in 𝓝 y, c z ∈ J := by
    filter_upwards [hnorm] with z hz
    apply minimizer_mem_box (uniformMeasure K) z (c z) m L
      (fun i => (norm_le_pi_norm z i).trans hz.le) hm hsum (hc0 z)
      (UniformSource.integrable_norm hK)
    exact hcmin z 0 (by simp)
  apply CompactArgmin.continuousAt_unique_minimizer hJ hS
    (continuous_uniform_integral_potential (ι := ι) hK hne) hbounded
    (Filter.Eventually.of_forall hc0) (Filter.Eventually.of_forall hcmin)
  intro a ha hamin
  exact uniform_normalized_minimizer_unique hK hconv hne y hy m hm hsum
    a (c y) ha (hc0 y) hamin (hcmin y)

/-- A globally defined normalized minimizer selection exists, and is continuous
on the open set of pairwise distinct sites. -/
theorem exists_continuous_uniform_intercept_selection {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    ∃ c : (ι → E d) → ι → ℝ,
      (∀ y, ∑ i, m i * c y i = 0) ∧
      (∀ y (a : ι → ℝ), (∑ i, m i * a i) = 0 →
        (∫ x, potential y (c y) x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K) ∧
      ContinuousOn c {y | Function.Injective y} := by
  classical
  let := UniformSource.probability hK hne
  have hex : ∀ y : ι → E d, ∃ c : ι → ℝ,
      (∑ i, m i * c i) = 0 ∧
      ∀ a : ι → ℝ, (∑ i, m i * a i) = 0 →
        (∫ x, potential y c x ∂uniformMeasure K) ≤ ∫ x, potential y a x ∂uniformMeasure K := by
    intro y
    obtain ⟨c, hc0, hcmin⟩ := exists_minimum_objective (uniformMeasure K) y m hm hsum
      ‖y‖₊ (fun i => norm_le_pi_norm y i) (UniformSource.integrable_norm hK)
    refine ⟨c, hc0, ?_⟩
    intro a ha
    simpa only [objective, hc0, ha, sub_zero] using hcmin a ha
  choose c hc0 hcmin using hex
  refine ⟨c, hc0, hcmin, ?_⟩
  intro y hy
  exact (continuousAt_uniform_intercept_selection hK hconv hne m hm hsum c hc0 hcmin y hy).continuousWithinAt

end Problem358.MaxPotential

end

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology

namespace Problem358.FixedMassIntercepts

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- Distinct finite site configurations form an open subset of the ambient coordinate space. -/
theorem isOpen_injective_sites : IsOpen {y : ι → E d | Function.Injective y} := by
  have heq : {y : ι → E d | Function.Injective y} =
      ⋂ i : ι, ⋂ j : ι, {y | i ≠ j → y i ≠ y j} := by
    ext y
    simp only [mem_ofPred_eq, mem_iInter]
    exact Function.injective_iff_pairwise_ne
  rw [heq]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  by_cases hij : i = j
  · simp [hij]
  · have hset : {y : ι → E d | i ≠ j → y i ≠ y j} =
        {y : ι → E d | y i = y j}ᶜ := by
      ext y
      simp [hij]
    rw [hset]
    exact (isClosed_eq (show Continuous (fun y : ι → E d => y i) from continuous_apply i)
      (show Continuous (fun y : ι → E d => y j) from continuous_apply j)).isOpen_compl

variable [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual prescribed intercepts minimize the integrated affine potential. -/
theorem intercepts_minimize {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) (a : ι → ℝ)
    (ha : ∑ i, m i * a i = 0) :
    (∫ x, MaxPotential.potential y (intercepts hK hconv hne m hm hsum y) x
      ∂uniformMeasure K) ≤ ∫ x, MaxPotential.potential y a x ∂uniformMeasure K := by
  let := UniformSource.probability hK hne
  let c := intercepts hK hconv hne m hm hsum y
  obtain ⟨k, hk, _, hmax⟩ := exists_measurable_argmax
    (fun i (x : E d) => ⟪x, y i⟫ + (c : ι → ℝ) i)
    (fun i => ((continuous_id.inner continuous_const).add continuous_const).measurable)
  apply MaxPotential.isMin_of_cell_masses (uniformMeasure K) y c m k c.property
    (fun i => hk (measurableSet_singleton i)) (Eventually.of_forall hmax)
    _ _ a ha
  · intro i
    exact (masses_eq_selector hK.measurableSet y hy c k hmax i).symm.trans
      (congrFun (intercepts_spec hK hconv hne m hm hsum y hy) i)
  · intro b
    exact UniformSource.integrable_continuousOn hK
      (MaxPotential.continuous_potential y b).continuousOn

/-- Canonical closed-cell intercepts are continuous at every distinct-site configuration.
This compactness argument is independent of the moving-boundary C1 theorem. -/
theorem continuousAt_intercepts_coe {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : Function.Injective y) :
    ContinuousAt (fun z => (intercepts hK hconv hne m hm hsum z : ι → ℝ)) y := by
  obtain ⟨b, hb0, hbmin, hbcont⟩ :=
    MaxPotential.exists_continuous_uniform_intercept_selection hK hconv hne m hm hsum
  have heq : ∀ z : ι → E d, Function.Injective z →
      (intercepts hK hconv hne m hm hsum z : ι → ℝ) = b z := by
    intro z hz
    apply MaxPotential.uniform_normalized_minimizer_unique hK hconv hne z hz m hm hsum
      _ _ (intercepts hK hconv hne m hm hsum z).property (hb0 z)
    · exact intercepts_minimize hK hconv hne m hm hsum z hz
    · exact hbmin z
  have h_nhds : {z : ι → E d | Function.Injective z} ∈ 𝓝 y :=
    isOpen_injective_sites.mem_nhds hy
  apply (hbcont.continuousAt h_nhds).congr_of_eventuallyEq
  filter_upwards [h_nhds] with z hz
  exact heq z hz

/-- On repeated-site configurations the chosen extension is exactly zero. -/
theorem intercepts_eq_zero_of_not_injective {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1)
    (y : ι → E d) (hy : ¬Function.Injective y) :
    intercepts hK hconv hne m hm hsum y = 0 := by
  simp only [intercepts, dite_eq_right hy]

/-- The actual normalized intercept choice is globally Borel measurable, including
at repeated-site configurations, where its value was explicitly set to zero. -/
theorem measurable_intercepts_coe {K : Set (E d)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : (interior K).Nonempty)
    (m : ι → ℝ) (hm : ∀ i, 0 < m i) (hsum : ∑ i, m i = 1) :
    Measurable (fun y => (intercepts hK hconv hne m hm hsum y : ι → ℝ)) := by
  classical
  let c : (ι → E d) → ι → ℝ := fun y => intercepts hK hconv hne m hm hsum y
  have hc : ContinuousOn c {y | Function.Injective y} := fun y hy =>
    (continuousAt_intercepts_coe hK hconv hne m hm hsum y hy).continuousWithinAt
  have hmeas := hc.measurable_piecewise (continuous_const.continuousOn :
    ContinuousOn (fun _ : ι → E d => (0 : ι → ℝ)) {y | Function.Injective y}ᶜ)
    isOpen_injective_sites.measurableSet
  have heq : ({y : ι → E d | Function.Injective y}.piecewise c (fun _ => 0)) = c := by
    funext y
    by_cases hy : Function.Injective y
    · simp only [piecewise, mem_ofPred_eq, ite_eq_left hy]
    · simp only [piecewise, mem_ofPred_eq, ite_eq_right hy]
      symm
      exact congrArg Subtype.val (intercepts_eq_zero_of_not_injective hK hconv hne m hm hsum y hy)
  rwa [heq] at hmeas

end Problem358.FixedMassIntercepts

end

end OAI
