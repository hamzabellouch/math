import OAI.Analysis.Mahler.SourceRegularFlux

namespace OAI

open Set MeasureTheory Filter MahlerStokes
open scoped Topology
namespace Mahler
noncomputable section
variable {k N m : ℕ} {U : Set (ComplexEuclidean (k+1))}
  {f : Fin N → ComplexEuclidean (k+1) → ℂ} {G : Fin N → MvPolynomial (Fin (k+1)) ℂ}

/-- Small balls really lie in the source sublevel eventually; this is
derived from the isolated zero and local continuity, not assumed. -/
theorem source_eventually_ball_subset_sublevel (h : MassHypotheses (k+1) N m U f G)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ r in 𝓝[>] (0 : ℝ), coordClosedBall ((2*k+1)+1) r ⊆
      regularSublevel ((sourceCoordinates k) ⁻¹' U) (fun x => tau f (sourceCoordinates k x)) R := by
  have hc : ContinuousOn (tau f) U := fun z hz => (h.contDiffAt_tau hz 0).continuousAt.continuousWithinAt
  have hD : IsOpen (U ∩ {z | tau f z < R}) := hc.isOpen_inter_preimage h.open_domain isOpen_Iio
  have hf0 : ∀ j, f j 0 = 0 := (h.isolated_zero 0 h.zero_mem).2 rfl
  have ht0 : tau f 0 = 0 := by simp [tau, hf0]
  obtain ⟨δ, hδ, hsub⟩ := Metric.isOpen_iff.mp hD 0 ⟨h.zero_mem, by simpa [ht0] using hR⟩
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  intro x hx
  have hs : ‖sourceCoordinates k x‖^2 ≤ r^2 := by
    rw [norm_sourceCoordinates_sq]
    exact hx
  have hn : ‖sourceCoordinates k x‖ < δ :=
    ((sq_le_sq₀ (norm_nonneg _) hr.1.le).mp hs).trans_lt hr.2
  exact hsub (by simpa using hn)

/-- A limit L of outward Stokes sphere flux
gives a regular-level mass bound R^n L.
No Stokes identity, positivity, or ball-inclusion premise remains. -/
theorem source_regular_mass_lower_of_flux_limit (h : MassHypotheses (k+1) N m U f G)
    {R L : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (hreg : ∀ z ∈ U, tau f z = R → fderiv ℝ (tau f) z ≠ 0)
    (hlimit : Tendsto
      (fun r => sphereFlux r (sourceCoordinateForm (sourceCoordinates k) (logTau f) k))
      (𝓝[>] (0 : ℝ)) (𝓝 L)) :
    R^(k+1) * L ≤ ∫ z in U ∩ {z | tau f z < R}, massDensity f z := by
  have hle : L ≤ (R⁻¹)^(k+1) * (∫ z in U ∩ {z | tau f z < R}, massDensity f z) := by
    apply le_of_tendsto hlimit
    filter_upwards [source_eventually_ball_subset_sublevel h hR, self_mem_nhdsWithin] with r hB hr
    exact source_regular_flux_le_mass h hR hR1 hreg hr hB
  have hmul := mul_le_mul_of_nonneg_left hle (pow_nonneg hR.le (k+1))
  simpa only [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hR.ne', one_pow, one_mul] using hmul

end
end Mahler

end OAI
