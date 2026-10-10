import OAI.Analysis.Brenier.MapDistance

namespace OAI

section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Problem358

/-- Bounded continuous tests commute with almost-everywhere limits of measurable
maps on a finite measure space. No uniform bound on the maps themselves is needed. -/
theorem tendsto_integral_boundedContinuous_comp_ae
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {Tn : ℕ → X → Y} {T : X → Y}
    (hTn : ∀ n, Measurable (Tn n))
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (f : Y →ᵇ ℝ) :
    Tendsto (fun n => ∫ x, f (Tn n x) ∂ρ) atTop
      (𝓝 (∫ x, f (T x) ∂ρ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
  · intro n
    exact (f.continuous.measurable.comp (hTn n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall fun x => f.norm_coe_le_norm (Tn n x)
  · filter_upwards [hlim] with x hx
    exact f.continuous.continuousAt.tendsto.comp hx

/-- A candidate almost-everywhere limit has the prescribed target law whenever
the approximating laws converge against bounded continuous functions. -/
theorem map_eq_of_ae_tendsto_and_test_tendsto
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [HasOuterApproxClosed Y]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {ν : Measure Y} [IsFiniteMeasure ν]
    {Tn : ℕ → X → Y} {T : X → Y}
    (hTn : ∀ n, Measurable (Tn n)) (hT : Measurable T)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (htest : ∀ f : Y →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f (Tn n x) ∂ρ) atTop (𝓝 (∫ y, f y ∂ν))) :
    Measure.map T ρ = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map hT.aemeasurable f.continuous.measurable.aestronglyMeasurable]
  exact tendsto_nhds_unique (tendsto_integral_boundedContinuous_comp_ae hTn hlim f) (htest f)

/-- Closed support constraints survive almost-everywhere limits. -/
theorem ae_mem_of_closed_of_ae_tendsto
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    {ρ : Measure X} {Tn : ℕ → X → Y} {T : X → Y} {K : Set Y}
    (hK : IsClosed K) (hmem : ∀ n, ∀ᵐ x ∂ρ, Tn n x ∈ K)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x))) :
    ∀ᵐ x ∂ρ, T x ∈ K := by
  have hall : ∀ᵐ x ∂ρ, ∀ n, Tn n x ∈ K := ae_all_iff.mpr hmem
  filter_upwards [hall, hlim] with x hx htx
  exact hK.mem_of_tendsto htx (Filter.Eventually.of_forall hx)

/-- The limit of maps to quantized target laws has the original target law.
This is the law-identification step in finite-target approximation. -/
theorem map_eq_of_ae_tendsto_quantized
    {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [HasOuterApproxClosed Y]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {ν : Measure Y} [IsFiniteMeasure ν]
    {Tn : ℕ → X → Y} {T : X → Y} {Qn : ℕ → Y → Y}
    (hTn : ∀ n, Measurable (Tn n)) (hT : Measurable T)
    (hQn : ∀ n, Measurable (Qn n))
    (hpush : ∀ n, Measure.map (Tn n) ρ = Measure.map (Qn n) ν)
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (hQlim : ∀ᵐ y ∂ν, Tendsto (fun n => Qn n y) atTop (𝓝 y)) :
    Measure.map T ρ = ν := by
  apply map_eq_of_ae_tendsto_and_test_tendsto hTn hT hlim
  intro f
  have heq : ∀ n, (∫ x, f (Tn n x) ∂ρ) = ∫ y, f (Qn n y) ∂ν := by
    intro n
    rw [← integral_map (hTn n).aemeasurable f.continuous.measurable.aestronglyMeasurable,
      hpush n, integral_map (hQn n).aemeasurable f.continuous.measurable.aestronglyMeasurable]
  simp_rw [heq]
  exact tendsto_integral_boundedContinuous_comp_ae hQn hQlim f

/-- Almost-everywhere convergence gives convergence against bounded continuous tests. -/
theorem tendsto_integral_boundedContinuous_comp_of_ae
    {X V : Type*} [MeasurableSpace X] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V]
    {ρ : Measure X} [IsFiniteMeasure ρ]
    {Tn : ℕ → X → V} {T : X → V} (hTn : ∀ n, Measurable (Tn n))
    (hlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (f : BoundedContinuousFunction V ℝ) :
    Tendsto (fun n => ∫ x, f (Tn n x) ∂ρ) atTop (𝓝 (∫ x, f (T x) ∂ρ)) :=
  tendsto_integral_boundedContinuous_comp_ae hTn hlim f

/-- Almost-everywhere limits with convergent approximating laws have the prescribed pushforward. -/
theorem map_eq_of_ae_limits
    {X V : Type*} [MeasurableSpace X] [TopologicalSpace V]
    [MeasurableSpace V] [BorelSpace V] [HasOuterApproxClosed V]
    {ρ : Measure X} {μ : Measure V} [IsFiniteMeasure ρ] [IsFiniteMeasure μ]
    {Tn : ℕ → X → V} {T : X → V} {Qn : ℕ → V → V}
    (hTn : ∀ n, Measurable (Tn n)) (hT : Measurable T)
    (hQn : ∀ n, Measurable (Qn n))
    (hTlim : ∀ᵐ x ∂ρ, Tendsto (fun n => Tn n x) atTop (𝓝 (T x)))
    (hQlim : ∀ᵐ y ∂μ, Tendsto (fun n => Qn n y) atTop (𝓝 y))
    (hpush : ∀ n, Measure.map (Tn n) ρ = Measure.map (Qn n) μ) :
    Measure.map T ρ = μ :=
  map_eq_of_ae_tendsto_quantized hTn hT hQn hpush hTlim hQlim

end Problem358

end

noncomputable section
open Filter MeasureTheory
open scoped Topology

namespace Problem358

/-- Almost-everywhere existence of a pointwise limit with an arbitrary extra
property can be realized by one measurable function. No measurability of the
extra property is required. -/
theorem exists_measurable_limit_with_property
    {α β : Type*} [MeasurableSpace α] [MetricSpace β]
    [MeasurableSpace β] [BorelSpace β] [Nonempty β]
    {ρ : Measure α} {f : ℕ → α → β} {P : α → β → Prop}
    (hmeas : ∀ n, AEMeasurable (f n) ρ)
    (hex : ∀ᵐ x ∂ρ, ∃ y, Tendsto (fun n => f n x) atTop (𝓝 y) ∧ P x y) :
    ∃ g : α → β, Measurable g ∧ ∀ᵐ x ∂ρ,
      Tendsto (fun n => f n x) atTop (𝓝 (g x)) ∧ P x (g x) := by
  classical
  let Q : α → β → Prop := fun x y =>
    Tendsto (fun n => f n x) atTop (𝓝 y) ∧ P x y
  let g : α → β := fun x =>
    if h : ∃ y, Q x y then Classical.choose h else Classical.arbitrary β
  have hgprop : ∀ᵐ x ∂ρ, Q x (g x) := by
    filter_upwards [hex] with x hx
    dsimp only [g]
    rw [dite_eq_left hx]
    exact Classical.choose_spec hx
  have hgmeas : AEMeasurable g ρ :=
    aemeasurable_of_tendsto_metrizable_ae atTop hmeas (hgprop.mono fun x hx => hx.1)
  refine ⟨hgmeas.mk g, hgmeas.measurable_mk, ?_⟩
  filter_upwards [hgprop, hgmeas.ae_eq_mk] with x hx heq
  exact heq ▸ hx

end Problem358

end

noncomputable section

open MeasureTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Problem358

variable {d : ℕ} {ρ ν : Measure (E d)}

/-- An L² limit has the target law when the approximating laws come from maps converging to
identity on that target. -/
theorem map_eq_of_mapL2Dist_limit [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {T Q : ℕ → E d → E d} {S : E d → E d}
    (hT : ∀ n, Measurable (T n)) (hQ : ∀ n, Measurable (Q n))
    (hS : Measurable S) (hTmem : ∀ n, MemLp (T n) 2 ρ) (hSmem : MemLp S 2 ρ)
    (hTlim : Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0))
    (hQlim : ∀ᵐ y ∂ν, Tendsto (fun n => Q n y) atTop (𝓝 y))
    (hmap : ∀ n, Measure.map (T n) ρ = Measure.map (Q n) ν) :
    Measure.map S ρ = ν := by
  obtain ⟨ns, hns, hlim⟩ :=
    exists_subseq_tendsto_ae_of_mapL2Dist_tendsto_zero hTmem hSmem hTlim
  apply map_eq_of_ae_limits (fun n => hT (ns n)) hS (fun n => hQ (ns n)) hlim
    _ (fun n => hmap (ns n))
  filter_upwards [hQlim] with y hy
  exact hy.comp hns.tendsto_atTop

/-- Completeness and target-law identification combined, without an optimality assertion. -/
theorem exists_map_of_approximating_mapL2_cauchy [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    {T Q : ℕ → E d → E d}
    (hT : ∀ n, Measurable (T n)) (hQ : ∀ n, Measurable (Q n))
    (hTmem : ∀ n, MemLp (T n) 2 ρ)
    (hC : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      mapL2Dist ρ (T m) (T n) < ε)
    (hQlim : ∀ᵐ y ∂ν, Tendsto (fun n => Q n y) atTop (𝓝 y))
    (hmap : ∀ n, Measure.map (T n) ρ = Measure.map (Q n) ν) :
    ∃ S : E d → E d, Measurable S ∧ MemLp S 2 ρ ∧ Measure.map S ρ = ν ∧
      Tendsto (fun n => mapL2Dist ρ (T n) S) atTop (𝓝 0) := by
  obtain ⟨S, hS, hSmem, hlim⟩ := exists_mapL2Dist_limit hTmem hC
  exact ⟨S, hS, hSmem, map_eq_of_mapL2Dist_limit hT hQ hS hTmem hSmem hlim hQlim hmap,
    hlim⟩

end Problem358

end

end OAI
