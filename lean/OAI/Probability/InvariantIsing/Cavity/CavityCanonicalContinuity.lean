import OAI.Probability.InvariantIsing.Cavity.CavityCanonicalLabels

namespace OAI

/-! Recalculating the canonical covariance after an L1 path
approximation changes every covariance endpoint uniformly. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace InvariantIsing

lemma cavityCanonicalCoordinate_uniform_of_L1 {m : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0))
    (a : Fin m) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |cavityCanonicalCoordinate ρ eig hρ hρsum (q n) a t -
        cavityCanonicalCoordinate ρ eig hρ hρsum p a t| < ε := by
  intro ε hε
  have huc := isCompact_Icc.uniformContinuousOn_of_continuous
    (continuousOn_projectedResolventDerivative ρ eig hρ hρsum a (c := 1))
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc (ε / 2) (by positivity)
  filter_upwards [hL.eventually (Iio_mem_nhds hδ)] with n hn
  have hden (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      |spectralPathDensity ρ eig hρ hρsum (q n) a r -
        spectralPathDensity ρ eig hρ hρsum p a r| < ε / 2 := by
    apply hmod (deficit (q n) r) (deficit_mem_unit (q n) hr)
      (deficit p r) (deficit_mem_unit p hr)
    exact (abs_deficit_sub_path_le (q n) p r).trans_lt hn
  intro t
  let c := Set.projIcc 0 1 zero_le_one t
  have hiq := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum (q n) a c.property
  have hip := spectralPathDensity_intervalIntegrable ρ eig hρ hρsum p a c.property
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (c : ℝ)) (C := ε / 2)
    (f := fun r => spectralPathDensity ρ eig hρ hρsum (q n) a r -
      spectralPathDensity ρ eig hρ hρsum p a r) (fun r hr => by
        rw [uIoc_of_le c.property.1] at hr
        exact (hden r ⟨hr.1.le, hr.2.trans c.property.2⟩).le)
  change |(∫ r in 0..(c : ℝ), spectralPathDensity ρ eig hρ hρsum (q n) a r) -
    ∫ r in 0..(c : ℝ), spectralPathDensity ρ eig hρ hρsum p a r| < ε
  rw [← intervalIntegral.integral_sub hiq hip]
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg c.property.1] at hb
  have hc : ε / 2 * (c : ℝ) ≤ ε / 2 := by nlinarith [c.property.2]
  exact (hb.trans hc).trans_lt (by linarith)

lemma cavity_spectralGroupDiagonal_tendsto_of_L1 {m : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hρsum : ∑ a, ρ a = 1)
    (p : OverlapPath) (q : ℕ → OverlapPath)
    (hL : Tendsto (fun n => ∫ s, |q n s - p s| ∂pathMeasure) atTop (𝓝 0)) (a : Fin m) :
    Tendsto (fun n => spectralGroupDiagonal ρ eig hρ hρsum (q n) a) atTop
      (𝓝 (spectralGroupDiagonal ρ eig hρ hρsum p a)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [cavityCanonicalCoordinate_uniform_of_L1 ρ eig hρ hρsum p q hL a ε hε] with n hn
  simpa only [Real.dist_eq, cavityCanonicalCoordinate, spectralGroupDiagonal,
    Set.projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)] using hn 1

end InvariantIsing

end

end OAI
