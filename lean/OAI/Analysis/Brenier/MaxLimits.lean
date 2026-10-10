import OAI.Analysis.Brenier.Argmax
import OAI.Analysis.Brenier.ConvexOptimality
import OAI.Analysis.Brenier.MapLimits
import OAI.Analysis.Brenier.Potential
import OAI.Analysis.Brenier.Uniform

namespace OAI

noncomputable section

open Filter

namespace Problem358

/-- A maximizer among finitely many convergent scores is eventually a maximizer
of the limiting scores. Only membership in the limiting maximizing set is asserted;
ties among the limiting scores need not be resolved consistently. -/
theorem eventually_limiting_maximizer
    {ι β : Type*} [Finite ι] {l : Filter β}
    {score : β → ι → ℝ} {limitScore : ι → ℝ} {pick : β → ι}
    (hscore : ∀ i, Tendsto (fun n => score n i) l (nhds (limitScore i)))
    (hpick : ∀ᶠ n in l, ∀ i, score n i ≤ score n (pick n)) :
    ∀ᶠ n in l, ∀ i, limitScore i ≤ limitScore (pick n) := by
  have hpair : ∀ i j, ∀ᶠ n in l,
      limitScore j < limitScore i → score n j < score n i := by
    intro i j
    by_cases hij : limitScore j < limitScore i
    · exact ((hscore j).eventually_lt (hscore i) hij).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => (hij hn).elim
  have hall : ∀ᶠ n in l, ∀ i j,
      limitScore j < limitScore i → score n j < score n i := by
    simpa only [eventually_all] using hpair
  filter_upwards [hpick, hall] with n hn halln
  intro i
  by_contra h
  exact (not_lt_of_ge (hn i)) (halln i (pick n) (lt_of_not_ge h))

/-- Finite active-value convergence, allowing different active indices at every
parameter and repeated limiting slopes. This is the endpoint argument for finite
maxima of moving affine functions. -/
theorem tendsto_value_of_finite_maximizer
    {ι β X : Type*} [Finite ι] [TopologicalSpace X] {l : Filter β}
    {score : β → ι → ℝ} {limitScore : ι → ℝ} {pick : β → ι}
    {value : β → ι → X} {limitValue : ι → X} {x : X}
    (hscore : ∀ i, Tendsto (fun n => score n i) l (nhds (limitScore i)))
    (hpick : ∀ᶠ n in l, ∀ i, score n i ≤ score n (pick n))
    (hvalue : ∀ i, Tendsto (fun n => value n i) l (nhds (limitValue i)))
    (hactive : ∀ i, (∀ j, limitScore j ≤ limitScore i) → limitValue i = x) :
    Tendsto (fun n => value n (pick n)) l (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  have hlim := eventually_limiting_maximizer hscore hpick
  have hi : ∀ i, ∀ᶠ n in l,
      (∀ j, limitScore j ≤ limitScore i) → value n i ∈ U := by
    intro i
    by_cases hmax : ∀ j, limitScore j ≤ limitScore i
    · have ht : Tendsto (fun n => value n i) l (nhds x) := by
        simpa only [hactive i hmax] using hvalue i
      exact (ht.eventually hU).mono fun n hn _ => hn
    · exact Eventually.of_forall fun n hn => (hmax hn).elim
  have hall : ∀ᶠ n in l, ∀ i,
      (∀ j, limitScore j ≤ limitScore i) → value n i ∈ U :=
    eventually_all.mpr hi
  filter_upwards [hlim, hall] with n hn hval
  exact hval (pick n) hn

/-- If equal maximal scores force equal values, some limiting maximizing value
is the limit, without requiring the maximizing index to be unique. -/
theorem exists_tendsto_value_of_finite_maximizer
    {ι β X : Type*} [Finite ι] [Nonempty ι] [TopologicalSpace X]
    {l : Filter β} {score : β → ι → ℝ} {limitScore : ι → ℝ}
    {pick : β → ι} {value : β → ι → X} {limitValue : ι → X}
    (hscore : ∀ i, Tendsto (fun n => score n i) l (nhds (limitScore i)))
    (hpick : ∀ᶠ n in l, ∀ i, score n i ≤ score n (pick n))
    (hvalue : ∀ i, Tendsto (fun n => value n i) l (nhds (limitValue i)))
    (hties : ∀ i j, limitScore i = limitScore j → limitValue i = limitValue j) :
    ∃ i, (∀ j, limitScore j ≤ limitScore i) ∧
      Tendsto (fun n => value n (pick n)) l (nhds (limitValue i)) := by
  obtain ⟨i, hi⟩ := Finite.exists_max limitScore
  refine ⟨i, hi, tendsto_value_of_finite_maximizer hscore hpick hvalue ?_⟩
  intro j hj
  exact hties j i (le_antisymm (hi j) (hj i))

/-- Endpoint convergence of the active slopes of affine maxima. The source point
is fixed; a.e. applications remove the finite union of limiting tie hyperplanes. -/
theorem tendsto_affine_active_slope
    {ι β V : Type*} [Finite ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {l : Filter β} {site : β → ι → V} {limitSite : ι → V}
    {offset : β → ι → ℝ} {limitOffset : ι → ℝ} {pick : β → ι}
    {point target : V}
    (hsite : ∀ i, Tendsto (fun n => site n i) l (nhds (limitSite i)))
    (hoffset : ∀ i, Tendsto (fun n => offset n i) l (nhds (limitOffset i)))
    (hpick : ∀ᶠ n in l, ∀ i,
      inner ℝ point (site n i) + offset n i ≤
        inner ℝ point (site n (pick n)) + offset n (pick n))
    (hactive : ∀ i, (∀ j,
      inner ℝ point (limitSite j) + limitOffset j ≤
        inner ℝ point (limitSite i) + limitOffset i) → limitSite i = target) :
    Tendsto (fun n => site n (pick n)) l (nhds target) := by
  apply tendsto_value_of_finite_maximizer (score := fun n i =>
    inner ℝ point (site n i) + offset n i)
    (limitScore := fun i => inner ℝ point (limitSite i) + limitOffset i)
    _ hpick hsite hactive
  intro i
  exact (tendsto_const_nhds.inner (hsite i)).add (hoffset i)

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology
open scoped BoundedContinuousFunction
open scoped BigOperators ENNReal

namespace Problem358

/-- Almost-everywhere active-slope convergence, without distinctness of the limiting
sites. The finite union of limiting affine tie hyperplanes is removed here. -/
theorem ae_tendsto_selected_affine_slopes
    {d : ℕ} {ι β : Type*} [Fintype ι] {l : Filter β}
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {y : β → ι → E d} {y₀ : ι → E d}
    {c : β → ι → ℝ} {c₀ : ι → ℝ}
    {pick : β → E d → ι} {pick₀ : E d → ι}
    (hy : ∀ i, Tendsto (fun n => y n i) l (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) l (𝓝 (c₀ i)))
    (hpick : ∀ᵐ x ∂ρ, ∀ᶠ n in l, ∀ i,
      inner ℝ x (y n i) + c n i ≤ inner ℝ x (y n (pick n x)) + c n (pick n x))
    (hpick₀ : ∀ᵐ x ∂ρ, ∀ i,
      inner ℝ x (y₀ i) + c₀ i ≤ inner ℝ x (y₀ (pick₀ x)) + c₀ (pick₀ x)) :
    ∀ᵐ x ∂ρ, Tendsto (fun n => y n (pick n x)) l (𝓝 (y₀ (pick₀ x))) := by
  filter_upwards [hρ.ae_le (ae_affine_tie_implies_slopes_eq volume y₀ c₀),
    hpick, hpick₀] with x hx hxn hx₀
  apply tendsto_affine_active_slope hy hc hxn
  intro i hi
  exact hx i (pick₀ x) (le_antisymm (hx₀ i) (hi (pick₀ x)))

/-- The same endpoint statement for maps specified by active-slope certificates.
No convergence of active indices, and no injectivity of limiting sites, is required. -/
theorem ae_tendsto_affine_maximizer_maps
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} (hρ : ρ ≪ volume)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hT : ∀ n, ∀ᵐ x ∂ρ, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hT₀ : ∀ᵐ x ∂ρ, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) :
    ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)) := by
  classical
  have hAll : ∀ᵐ x ∂ρ, ∀ n, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i :=
    ae_all_iff.mpr hT
  filter_upwards [hρ.ae_le (ae_affine_tie_implies_slopes_eq volume y₀ c₀),
    hAll, hT₀] with x hx hxn hx₀
  choose pick hpick hmax using hxn
  obtain ⟨i₀, hi₀, hmax₀⟩ := hx₀
  have ht := tendsto_affine_active_slope hy hc
    (Eventually.of_forall hmax)
    (target := y₀ i₀) (fun i hi => hx i i₀ (le_antisymm (hmax₀ i) (hi i₀)))
  simpa only [← hpick, ← hi₀] using ht

/-- Coefficient convergence also gives L² convergence for any finite absolutely
continuous source. A common compact slope range follows from convergence of the
finite family; boundedness of the source itself is not needed. -/
theorem tendsto_mapL2Dist_affine_maximizer_maps
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ] (hρ : ρ ≪ volume)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hT : ∀ n, ∀ᵐ x ∂ρ, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hT₀ : ∀ᵐ x ∂ρ, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) :
    Tendsto (fun n => mapL2Dist ρ (T n) T₀) atTop (𝓝 0) := by
  have hyPi : Tendsto y atTop (𝓝 y₀) := tendsto_pi_nhds.mpr hy
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto y hyPi).exists_norm_le
  apply CompactIntegrability.tendsto_mapL2Dist_of_ae_tendsto hTm hT₀m
    (isCompact_closedBall (0 : E d) (max R 0)) _
    (ae_tendsto_affine_maximizer_maps hρ hy hc hT hT₀)
  intro n
  filter_upwards [hT n] with x hx
  obtain ⟨i, hi, _⟩ := hx
  rw [hi, Metric.mem_closedBall, dist_zero_right]
  exact (norm_le_pi_norm (y n) i).trans ((hR _ ⟨n, rfl⟩).trans (le_max_left _ _))

/-- Identification of an endpoint law carried by a fixed finite index measure.
Different limiting indices may have the same site; their masses are automatically merged
by the pushforward, so no endpoint injectivity is needed. -/
theorem map_eq_of_finite_site_law_limit
    {d : ℕ} {ι : Type*} [Fintype ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ]
    {η : Measure ι} [IsFiniteMeasure η]
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)))
    (hpush : ∀ n, Measure.map (T n) ρ = Measure.map (y n) η) :
    Measure.map T₀ ρ = Measure.map y₀ η := by
  apply map_eq_of_ae_tendsto_and_test_tendsto hTm hT₀m hlim
  intro f
  have heq (n : ℕ) : (∫ x, f (T n x) ∂ρ) = ∫ i, f (y n i) ∂η := by
    rw [← integral_map (hTm n).aemeasurable f.continuous.measurable.aestronglyMeasurable,
      hpush n, integral_map (measurable_of_countable (y n)).aemeasurable
        f.continuous.measurable.aestronglyMeasurable]
  have htarget : (∫ z, f z ∂Measure.map y₀ η) = ∫ i, f (y₀ i) ∂η :=
    integral_map (measurable_of_countable y₀).aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  simp_rw [heq, htarget]
  exact tendsto_integral_boundedContinuous_comp_ae
    (fun n => measurable_of_countable (y n)) (ae_of_all _ hy) f

/-- Explicit atomic form of endpoint-law identification. Repeated endpoint sites are
allowed, so this applies at both ends of an optimal finite atomic motion. -/
theorem map_eq_atomic_of_finite_site_limit
    {d : ℕ} {ι : Type*} [Fintype ι]
    {ρ : Measure (E d)} [IsFiniteMeasure ρ]
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {T : ℕ → E d → E d} {T₀ : E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hTm : ∀ n, Measurable (T n)) (hT₀m : Measurable T₀)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x)))
    (hpush : ∀ n, Measure.map (T n) ρ = ∑ i, w i • Measure.dirac (y n i)) :
    Measure.map T₀ ρ = ∑ i, w i • Measure.dirac (y₀ i) := by
  classical
  let : MeasurableSpace ι := ⊤
  let η : Measure ι := ∑ i, w i • Measure.dirac i
  have : IsProbabilityMeasure η := by
    constructor
    simpa [η] using hw
  have hmap (z : ι → E d) : Measure.map z η = ∑ i, w i • Measure.dirac (z i) := by
    dsimp [η]
    rw [Measure.map_finset_sum' (measurable_of_countable z).aemeasurable]
    simp only [Measure.map_smul _ (measurable_of_countable z).aemeasurable,
      Measure.map_dirac]
  rw [← hmap y₀]
  apply map_eq_of_finite_site_law_limit hy hTm hT₀m hlim
  intro n
  rw [hmap, hpush]

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal NNReal

namespace Problem358

/-- A finite-affine selected map is plan-uniquely optimal on a uniform convex source
even when the slopes are repeated. The supporting-potential certificate avoids any
choice of a merged presentation. -/
theorem isUniqueQuadraticOptimalMap_uniform_of_finite_affine_repeated
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} [IsFiniteMeasure (uniformMeasure K)]
    (hK : IsCompact K) (hne : K.Nonempty) (hconv : Convex ℝ K)
    (y : ι → E d) (c : ι → ℝ) {T : E d → E d} (hT : Measurable T)
    (hactive : ∀ᵐ x ∂uniformMeasure K, ∃ i, T x = y i ∧
      ∀ j, inner ℝ x (y j) + c j ≤ inner ℝ x (y i) + c i) :
    IsUniqueQuadraticOptimalMap (uniformMeasure K)
      (Measure.map T (uniformMeasure K)) T := by
  have hY : IsCompact (Set.range y) := (Set.finite_range y).isCompact
  obtain ⟨R, hR⟩ := hY.isBounded.exists_norm_le
  let L : ℝ≥0 := ⟨max R 0, le_max_right _ _⟩
  have hL (i : ι) : ‖y i‖ ≤ L :=
    (hR _ ⟨i, rfl⟩).trans (le_max_left _ _)
  have hsupport : IsSupported (Measure.map T (uniformMeasure K)) (Set.range y) := by
    apply ae_iff.mp
    apply (ae_map_iff hT.aemeasurable hY.measurableSet).mpr
    filter_upwards [hactive] with x hx
    obtain ⟨i, hi, _⟩ := hx
    exact ⟨i, hi.symm⟩
  apply isUniqueQuadraticOptimalMap_uniform_of_supporting_potential
    hK hne hconv hY hsupport
    (MaxPotential.lipschitzWith_potential y c L hL).lipschitzOnWith hT rfl
  filter_upwards [hactive] with x hx
  obtain ⟨i, hi, hmax⟩ := hx
  intro z _
  rw [hi]
  exact MaxPotential.supporting_inequality y c x z i hmax

/-- Coefficient limits at an endpoint of a fixed-mass finite affine motion produce
an actual measurable endpoint map, its exact atomic law, plan-unique optimality,
and both almost-everywhere and L² convergence. Endpoint slopes may coincide. -/
theorem exists_unique_optimal_finite_affine_endpoint
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {y : ℕ → ι → E d} {y₀ : ι → E d}
    {c : ℕ → ι → ℝ} {c₀ : ι → ℝ} {T : ℕ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, Tendsto (fun n => y n i) atTop (𝓝 (y₀ i)))
    (hc : ∀ i, Tendsto (fun n => c n i) atTop (𝓝 (c₀ i)))
    (hTm : ∀ n, Measurable (T n))
    (hT : ∀ n, ∀ᵐ x ∂uniformMeasure K, ∃ i, T n x = y n i ∧
      ∀ j, inner ℝ x (y n j) + c n j ≤ inner ℝ x (y n i) + c n i)
    (hpush : ∀ n, Measure.map (T n) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y n i)) :
    ∃ T₀ : E d → E d,
      (∀ x, ∃ i, T₀ x = y₀ i ∧
        ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y₀ i)) T₀ ∧
      (∀ᵐ x ∂uniformMeasure K, Tendsto (fun n => T n x) atTop (𝓝 (T₀ x))) ∧
      Tendsto (fun n => mapL2Dist (uniformMeasure K) (T n) T₀) atTop (𝓝 0) := by
  let : IsProbabilityMeasure (uniformMeasure K) := UniformSource.probability hK hinterior
  obtain ⟨T₀, hT₀m, hselected⟩ := exists_measurable_affine_maximizer y₀ c₀
  have hactive : ∀ x, ∃ i, T₀ x = y₀ i ∧
      ∀ j, inner ℝ x (y₀ j) + c₀ j ≤ inner ℝ x (y₀ i) + c₀ i := by
    intro x
    simpa only [real_inner_comm] using hselected x
  have hac : uniformMeasure K ≪ (volume : Measure (E d)) :=
    Measure.absolutelyContinuous_restrict.smul_left _
  have hlim := ae_tendsto_affine_maximizer_maps hac hy hc hT (ae_of_all _ hactive)
  have hlaw := map_eq_atomic_of_finite_site_limit w hw hy hTm hT₀m hlim hpush
  have hopt := isUniqueQuadraticOptimalMap_uniform_of_finite_affine_repeated
    hK (hinterior.mono interior_subset) hconv y₀ c₀ hT₀m (ae_of_all _ hactive)
  rw [hlaw] at hopt
  exact ⟨T₀, hactive, hopt, hlim,
    tendsto_mapL2Dist_affine_maximizer_maps hac hy hc hTm hT₀m hT (ae_of_all _ hactive)⟩

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Problem358

/-- A boundary value of a continuous finite-affine family has the prescribed
atomic law and a plan-uniquely optimal selected map. Only the coefficient limits
within the parameter set are needed, and limiting sites may coincide. -/
theorem exists_unique_optimal_finite_affine_boundary
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {S : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ closure S)
    {y : ℝ → ι → E d} {c : ℝ → ι → ℝ}
    {T : ℝ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, ContinuousWithinAt (fun t => y t i) S t₀)
    (hc : ∀ i, ContinuousWithinAt (fun t => c t i) S t₀)
    (hTm : ∀ t ∈ S, Measurable (T t))
    (hT : ∀ t ∈ S, ∀ᵐ x ∂uniformMeasure K, ∃ i, T t x = y t i ∧
      ∀ j, inner ℝ x (y t j) + c t j ≤ inner ℝ x (y t i) + c t i)
    (hpush : ∀ t ∈ S, Measure.map (T t) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y t i)) :
    ∃ T₀ : E d → E d,
      (∀ x, ∃ i, T₀ x = y t₀ i ∧
        ∀ j, inner ℝ x (y t₀ j) + c t₀ j ≤ inner ℝ x (y t₀ i) + c t₀ i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y t₀ i)) T₀ := by
  obtain ⟨s, hs, hlim⟩ := mem_closure_iff_seq_limit.mp ht₀
  have hwithin : Tendsto s atTop (𝓝[S] t₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hs⟩
  obtain ⟨T₀, hactive, hopt, _, _⟩ :=
    exists_unique_optimal_finite_affine_endpoint hK hconv hinterior w hw
      (fun i => (hy i).tendsto.comp hwithin)
      (fun i => (hc i).tendsto.comp hwithin)
      (fun n => hTm (s n) (hs n))
      (fun n => hT (s n) (hs n))
      (fun n => hpush (s n) (hs n))
  exact ⟨T₀, hactive, hopt⟩

/-- Continuous coefficients on a closed time interval and the fixed-mass law
on its interior produce both exact endpoint maps. No injectivity or cell-mass
condition is required at either endpoint. -/
theorem exists_unique_optimal_finite_affine_path_endpoints
    {d : ℕ} {ι : Type*} [Fintype ι] [Nonempty ι]
    {K : Set (E d)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hinterior : (interior K).Nonempty)
    {a b : ℝ} (hab : a < b)
    {y : ℝ → ι → E d} {c : ℝ → ι → ℝ}
    {T : ℝ → E d → E d}
    (w : ι → ℝ≥0∞) (hw : ∑ i, w i = 1)
    (hy : ∀ i, ContinuousOn (fun t => y t i) (Set.Icc a b))
    (hc : ∀ i, ContinuousOn (fun t => c t i) (Set.Icc a b))
    (hTm : ∀ t ∈ Set.Ioo a b, Measurable (T t))
    (hT : ∀ t ∈ Set.Ioo a b, ∀ᵐ x ∂uniformMeasure K, ∃ i,
      T t x = y t i ∧ ∀ j,
        inner ℝ x (y t j) + c t j ≤ inner ℝ x (y t i) + c t i)
    (hpush : ∀ t ∈ Set.Ioo a b, Measure.map (T t) (uniformMeasure K) =
      ∑ i, w i • Measure.dirac (y t i)) :
    ∃ Ta Tb : E d → E d,
      (∀ x, ∃ i, Ta x = y a i ∧
        ∀ j, inner ℝ x (y a j) + c a j ≤ inner ℝ x (y a i) + c a i) ∧
      (∀ x, ∃ i, Tb x = y b i ∧
        ∀ j, inner ℝ x (y b j) + c b j ≤ inner ℝ x (y b i) + c b i) ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y a i)) Ta ∧
      IsUniqueQuadraticOptimalMap (uniformMeasure K)
        (∑ i, w i • Measure.dirac (y b i)) Tb := by
  have ha : a ∈ Set.Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Set.Icc a b := ⟨hab.le, le_rfl⟩
  have hclosure : closure (Set.Ioo a b) = Set.Icc a b := closure_Ioo hab.ne
  obtain ⟨Ta, hTa, hoptA⟩ :=
    exists_unique_optimal_finite_affine_boundary hK hconv hinterior
      (hclosure.symm ▸ ha) w hw
      (fun i => (hy i a ha).mono Set.Ioo_subset_Icc_self)
      (fun i => (hc i a ha).mono Set.Ioo_subset_Icc_self) hTm hT hpush
  obtain ⟨Tb, hTb, hoptB⟩ :=
    exists_unique_optimal_finite_affine_boundary hK hconv hinterior
      (hclosure.symm ▸ hb) w hw
      (fun i => (hy i b hb).mono Set.Ioo_subset_Icc_self)
      (fun i => (hc i b hb).mono Set.Ioo_subset_Icc_self) hTm hT hpush
  exact ⟨Ta, Tb, hTa, hTb, hoptA, hoptB⟩

end Problem358

end

end OAI
