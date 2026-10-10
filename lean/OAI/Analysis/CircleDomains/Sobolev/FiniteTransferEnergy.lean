import OAI.Analysis.CircleDomains.Sobolev.CoordinateEstimates
import OAI.Analysis.CircleDomains.Modulus.ActualWedgeCost

namespace OAI

/-!
# Common-width selection with actual transferred energy bounds

After the geometric disk construction, one sufficiently late width gives
smooth filled coordinates, a metric retaining the spherical background,
and both the total and localized energy estimates. The cost is measured
only on the original domain. Periodic and masked coordinates are treated
separately from this real-coordinate analytic assembly.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Analytic assembly for a finite family of real coordinates. The
geometric filling premise is eventual in width, so it is met at the same
width that gives the cost estimate. -/
theorem exists_filled_spherical_transfer_at_good_width
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsCompact Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (v : ℝ → Fin n → (ℝ × ℝ) → ℝ) (u : Fin n → (ℝ × ℝ) → ℝ)
    (hu : ∀ i, MemLp (planarGradient (u i)) 2 (volume.restrict G))
    (hretain : ∀ δ, ∀ᶠ x in 𝓝ˢ K, ∀ i, v δ i x = u i x)
    {h : ℝ} (hh : 0 < h)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → ℝ,
      IsFilledCoordinateFamily D Ω (v δ) F)
    (hvi : ∀ k, IntegrableOn
      (fun z => 2 * coordinateWedges (natCoordinateFamily (v (staircaseWidth h k))) n z) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop,
      (∫ z in G \ K, 2 * coordinateWedges (natCoordinateFamily (v (staircaseWidth h k))) n z) < ε)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → ℝ) (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsFilledCoordinateFamily D Ω (v (staircaseWidth h k)) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i ∈ range n, ∫ z in Q \ K, gradientEnergy (natCoordinateFamily F i) g z) < ε ∧
      ∀ (i : ℕ), i < n → ∀ (E : Set (ℝ × ℝ)), MeasurableSet E → E ⊆ K →
        (∫ z in Q \ E, gradientEnergy (natCoordinateFamily F i) g z) <
          (∫ z in G \ E, gradientEnergy (natCoordinateFamily u i)
            (fun z => sphericalMetricFactor z • 1) z) + ε := by
  obtain ⟨k, F, hk, hcost, hF⟩ :=
    exists_good_width_filled_coordinates D Ω v hh hfill _ hgood k₀
  obtain ⟨R, g, hR, hg, hPD, hmetric, hfar, henergy⟩ :=
    hF.exists_spherical_metric_of_original_cost hD hΩ hQ hQΩ hK hG hcover (hvi k) hcost
  have hFcore : ∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z := by
    filter_upwards [hF.eventuallyEq_near_set hD hKD, hretain (staircaseWidth h k)] with z hz hvz i
    exact (hz i).trans (hvz i)
  have hFs := contDiffOn_natCoordinateFamily hF.1
  refine ⟨k, F, R, g, hk, hF, hFcore, hR, hg, hPD, hmetric, hfar, ?_, ?_⟩
  · rw [← integral_coordinateGram_eq_sum hΩ hQ hQΩ _ hFs n hg.continuous hPD]
    exact henergy
  · intro i hi E hE hEK
    apply localized_coordinate_energy_lt hΩ hQ hQΩ hG hK (fun _ hz => hKG hz.2)
      (natCoordinateFamily F) (natCoordinateFamily u) hFs ?_ ?_
      hg.continuous hPD hmetric henergy hi hE hEK
    · intro j hj
      simpa only [IntegrableOn, natCoordinateFamily, dite_eq_left hj] using
        integrable_gradientEnergy_spherical_of_memLp (hu ⟨j, hj⟩)
    · filter_upwards [hFcore] with z hz j hj
      simpa only [natCoordinateFamily, dite_eq_left hj] using hz ⟨j, hj⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
