import OAI.Analysis.CircleDomains.Topology.CircleCutoffFillings

namespace OAI

/-!
# Analytic transfer of circle coordinates on the full completion

One sufficiently small good width gives simultaneous smooth fillings,
core agreement, a common spherical-background metric, and total and
localized energy bounds on the entire cofinite completed domain.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_circle_transfer_at_good_width
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (v : ℝ → Fin n → (ℝ × ℝ) → UnitAddCircle)
    (u : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hu : ∀ i, MemLp (circleGradient (u i)) 2 (volume.restrict G))
    (hretain : ∀ δ, ∀ᶠ x in 𝓝ˢ K, ∀ i, v δ i x = u i x)
    {h : ℝ} (hh : 0 < h)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsFilledCircleFamily D Ω (v δ) F)
    (hvi : ∀ k, IntegrableOn
      (fun z => 2 * circleWedges (v (staircaseWidth h k)) z) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop,
      (∫ z in G \ K, 2 * circleWedges (v (staircaseWidth h k)) z) < ε)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsFilledCircleFamily D Ω (v (staircaseWidth h k)) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in Q \ K, fieldEnergy (circleGradient (F i)) g z) < ε ∧
      ∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in Q \ E, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in G \ E, fieldEnergy (circleGradient (u i))
            (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hwidth : Tendsto (staircaseWidth h) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨staircaseWidth_tendsto_zero h,
      Filter.Eventually.of_forall (staircaseWidth_pos hh)⟩
  obtain ⟨k, hkcost, hlate, F, hF⟩ :=
    (hgood.and_eventually ((eventually_ge_atTop k₀).and (hwidth.eventually hfill))).exists
  have hcore : ∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z := by
    apply eventually_nhdsSet_iff_forall.mpr
    intro z hz
    apply eventually_all.mpr
    intro i
    have hvu := (hretain (staircaseWidth h k)).filter_mono (nhds_le_nhdsSet hz)
    filter_upwards [hF.eventuallyEq_outside hD (hKD z hz) i, hvu] with x hx hxu
    exact hx.trans (hxu i)
  obtain ⟨R₀, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  obtain ⟨R, g, hR, hg, hPD, hmetric, hfar, henergy⟩ :=
    hF.exists_spherical_metric_of_original_cost hD hΩ hQc (fun z hz => hQΩ hz.1) hK hG
      (fun z hz => hcover hz.1) (hvi k) hkcost
  have hsum : (∑ i : Fin n, ∫ z in Q \ K, fieldEnergy (circleGradient (F i)) g z) < ε := by
    simpa only [htail] using henergy
  refine ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, ?_⟩
  intro i E hE hEK
  have hsingle : (∫ z in Q \ K, fieldEnergy (circleGradient (F i)) g z) < ε := by
    apply lt_of_le_of_lt _ hsum
    exact single_le_sum
      (f := fun j : Fin n => ∫ z in Q \ K, fieldEnergy (circleGradient (F j)) g z)
      (fun j _ => integral_nonneg fun z => covectorEnergy_nonneg _ (hPD z)) (mem_univ i)
  apply localized_circle_energy_lt hΩ hQ hQΩ hG hK hKc hKG (hF.1 i) (hu i)
    (hcore.mono fun _ hz => hz i) hg.continuous hPD hmetric hsingle hE hEK

end CircleDomainRigidity.FiniteTransfer

end

end OAI
