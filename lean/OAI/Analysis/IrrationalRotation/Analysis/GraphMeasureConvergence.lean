import Mathlib
import OAI.Analysis.IrrationalRotation.Analysis.DensityMeasureConvergence
import OAI.Analysis.IrrationalRotation.Analysis.UniformAbsoluteContinuityLimits

namespace OAI

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

namespace Invariant233.GraphMeasureConvergence

variable {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem tendsto_integral_sub_graph
    (ν : ℕ → FiniteMeasure (X × Y)) (g : X → Y) (hg : Continuous g)
    (M : ℝ) (hM : ∀ᶠ n in atTop, (ν n : Measure (X × Y)).real univ ≤ M)
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (f : (X × Y) →ᵇ ℝ) :
    Tendsto (fun n => (∫ z, f z ∂(ν n : Measure (X × Y))) -
      ∫ z, f (z.1, g z.1) ∂(ν n : Measure (X × Y))) atTop (𝓝 0) := by
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  let G : C(X × Y, X × Y) :=
    ⟨fun z => (z.1, g z.1), continuous_fst.prodMk (hg.comp continuous_fst)⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hη : 0 < ε / (2 * B) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / (2 * B)) hη
  filter_upwards [hM, hnear δ hδ] with n hn hclose
  have hpoint : ∀ᵐ z ∂(ν n : Measure (X × Y)),
      ‖f z - f (z.1, g z.1)‖ ≤ ε / (2 * B) := by
    filter_upwards [hclose] with z hz
    have hd : dist z (z.1, g z.1) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hz
    simpa only [dist_eq_norm] using (hδf hd).le
  have hfg : Integrable (fun z : X × Y => f (z.1, g z.1))
      (ν n : Measure (X × Y)) := (f.compContinuous G).integrable _
  rw [dist_zero_right, ← integral_sub (f.integrable _) hfg]
  calc
    ‖∫ z, f z - f (z.1, g z.1) ∂(ν n : Measure (X × Y))‖ ≤
        (ε / (2 * B)) * (ν n : Measure (X × Y)).real univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ ≤ (ε / (2 * B)) * B := by
      apply mul_le_mul_of_nonneg_left _ hη.le
      exact hn.trans (by dsimp [B]; linarith [le_abs_self M])
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem tendsto_graph_of_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x, g x)))) := by
  have hmass : Tendsto (fun n => (ν n : Measure (X × Y)).real univ)
      atTop (𝓝 ((μ : Measure X).real univ)) := by
    have h := NNReal.continuous_coe.continuousAt.tendsto.comp hfirst.mass
    simpa only [Function.comp_def, FiniteMeasure.measureReal_eq_coe_coeFn,
      FiniteMeasure.mass, FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,
      Set.preimage_univ] using h
  let M := (μ : Measure X).real univ + 1
  have hM : ∀ᶠ n in atTop, (ν n : Measure (X × Y)).real univ ≤ M :=
    (hmass.eventually_lt_const (by dsimp [M]; linarith)).mono (fun _ h => h.le)
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let G : C(X, X × Y) := ⟨fun x => (x, g x), continuous_id.prodMk hg⟩
  have hgraph := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfirst
    (f.compContinuous G)
  have heq : ∀ n, (∫ x, (f.compContinuous G) x ∂((ν n).map Prod.fst : Measure X)) =
      ∫ z, f (z.1, g z.1) ∂(ν n : Measure (X × Y)) := by
    intro n
    exact integral_map measurable_fst.aemeasurable
      ((f.compContinuous G).continuous.measurable.aestronglyMeasurable)
  simp_rw [heq] at hgraph
  have hlim := (tendsto_integral_sub_graph ν g hg M hM hnear f).add hgraph
  have hmap : (∫ z, f z ∂(μ.map (fun x => (x, g x)) : Measure (X × Y))) =
      ∫ x, (f.compContinuous G) x ∂(μ : Measure X) :=
    integral_map (continuous_id.prodMk hg).measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  rw [hmap]
  simpa only [sub_add_cancel, zero_add] using hlim

theorem tendsto_restrict_of_compl_mass_tendsto_zero
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : ℕ → FiniteMeasure Z) (μ : FiniteMeasure Z)
    (hν : Tendsto ν atTop (𝓝 μ)) (s : ℕ → Set Z)
    (hs : ∀ n, MeasurableSet (s n))
    (hremoved : Tendsto (fun n => (ν n : Measure Z).real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (s n)) atTop (𝓝 μ) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hdiff : Tendsto (fun n => (∫ z, f z ∂(ν n : Measure Z)) -
      ∫ z in s n, f z ∂(ν n : Measure Z)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => norm_integral_sub_setIntegral_le
        (Eventually.of_forall fun z => f.norm_coe_le_norm z) (hs n) (f.integrable _))
    simpa only [zero_mul] using hremoved.mul_const ‖f‖
  have htest := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f
  simpa only [sub_sub_cancel, sub_zero, FiniteMeasure.restrict_measure_eq] using htest.sub hdiff

theorem tendsto_trimmed_graph_of_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (s : ℕ → Set (X × Y)) (hs : ∀ n, MeasurableSet (s n))
    (hremoved : Tendsto (fun n => (ν n : Measure (X × Y)).real (s n)ᶜ)
      atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (s n)) atTop
      (𝓝 (μ.map (fun x => (x, g x)))) :=
  tendsto_restrict_of_compl_mass_tendsto_zero ν _
    (tendsto_graph_of_first_marginal ν μ g hg hfirst hnear) s hs hremoved

theorem tendsto_graph_of_first_marginal_of_dist_le
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hnear : ∀ n, ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) ≤ ε n) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x, g x)))) := by
  apply tendsto_graph_of_first_marginal ν μ g hg hfirst
  intro δ hδ
  filter_upwards [hε.eventually_lt_const hδ] with n hn
  exact (hnear n).mono (fun _ hz => hz.trans_lt hn)

theorem tendsto_graph_of_first_density_L2
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    [IsProbabilityMeasure (μ : Measure X)]
    (g : X → Y) (hg : Continuous g) (ρ : ℕ → X → ℝ)
    (hρ : ∀ n, MemLp (ρ n) 2 (μ : Measure X))
    (hnonneg : ∀ n, 0 ≤ᵐ[(μ : Measure X)] ρ n)
    (hfirst : ∀ n, ((ν n).map Prod.fst : Measure X) =
      (μ : Measure X).withDensity (fun x => ENNReal.ofReal (ρ n x)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x => ρ n x - 1) 2 (μ : Measure X))
      atTop (𝓝 0))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x, g x)))) :=
  tendsto_graph_of_first_marginal ν μ g hg
    (tendsto_of_density_L2 μ (fun n => (ν n).map Prod.fst) ρ hρ hnonneg hfirst hL2) hnear

theorem tendsto_trimmed_graph_of_uniform_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (huac : UniformlyAbsolutelyContinuous (μ : Measure X)
      (fun n => (ν n : Measure (X × Y)).map Prod.fst))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hbase : Tendsto (fun n => (μ : Measure X).real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (Prod.fst ⁻¹' s n)) atTop
      (𝓝 (μ.map (fun x => (x, g x)))) := by
  apply tendsto_trimmed_graph_of_first_marginal ν μ g hg hfirst hnear
    (fun n => Prod.fst ⁻¹' s n) (fun n => (hs n).preimage measurable_fst)
  have h := huac.tendsto_real_apply_of_base_real_tendsto_zero
    (fun n => (s n)ᶜ) (fun n => (hs n).compl) hbase
  have heq (n : ℕ) : ((ν n : Measure (X × Y)).map Prod.fst).real (s n)ᶜ =
      (ν n : Measure (X × Y)).real (Prod.fst ⁻¹' s n)ᶜ := by
    rw [map_measureReal_apply measurable_fst (hs n).compl]
    rfl
  simpa only [heq] using h

end Invariant233.GraphMeasureConvergence

end OAI
