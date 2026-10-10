import OAI.Analysis.CircleDomains.Rigidity.MaskedFilledEnergy

namespace OAI

/-!
# Full masked analytic transfer at one good width

A single width gives simultaneous circle fillings and one metric, with
both total tail energy and localized estimates on each actual mask.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_masked_circle_transfer_at_good_width
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hcover : Q ⊆ G ∪ ⋃ i, D i) (hKD : ∀ x ∈ K, ∀ i, x ∉ D i)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (v : ℝ → Fin n → (ℝ × ℝ) → UnitAddCircle)
    (u : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hu : ∀ i, MemLp (circleGradient (u i)) 2 (volume.restrict (G ∩ M i)))
    (hretain : ∀ δ, ∀ᶠ x in 𝓝ˢ K, ∀ i, v δ i x = u i x)
    {h : ℝ} (hh : 0 < h)
    (hfill : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∃ F : Fin n → (ℝ × ℝ) → UnitAddCircle,
      IsMaskedFilledCircleFamily D Ω M (v δ) F)
    (hvi : ∀ k, IntegrableOn
      (fun z => 2 * maskedCircleWedges M (v (staircaseWidth h k)) z) (G \ K))
    {ε : ℝ} (hgood : ∃ᶠ k in atTop,
      (∫ z in G \ K, 2 * maskedCircleWedges M (v (staircaseWidth h k)) z) < ε)
    (k₀ : ℕ) :
    ∃ (k : ℕ) (F : Fin n → (ℝ × ℝ) → UnitAddCircle)
      (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric),
      k₀ ≤ k ∧ IsMaskedFilledCircleFamily D Ω M (v (staircaseWidth h k)) F ∧
      (∀ᶠ z in 𝓝ˢ K, ∀ i, F i z = u i z) ∧
      0 < R ∧ ContDiff ℝ ∞ g ∧ (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε ∧
      ∀ i : Fin n, ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in (Q \ E) ∩ M i, fieldEnergy (circleGradient (F i)) g z) <
          (∫ z in (G \ E) ∩ M i, fieldEnergy (circleGradient (u i))
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
    filter_upwards [hF.2.eventuallyEq_outside hD (hKD z hz) i, hvu] with x hx hxu
    exact hx.trans (hxu i)
  obtain ⟨R, g, hR, hg, hPD, hmetric, hfar, hsum⟩ :=
    hF.exists_spherical_metric_of_original_cost hD hΩ hQ hK hKc htail hG hM hboundary
      hcover (hvi k) hkcost
  refine ⟨k, F, R, g, hlate, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, ?_⟩
  intro i E hE hEK
  have hsingle : (∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (F i)) g z) < ε := by
    apply lt_of_le_of_lt _ hsum
    exact single_le_sum
      (f := fun j : Fin n => ∫ z in (Q \ K) ∩ M j, fieldEnergy (circleGradient (F j)) g z)
      (fun j _ => integral_nonneg fun z => covectorEnergy_nonneg _ (hPD z)) (mem_univ i)
  exact localized_masked_circle_energy_lt hΩ hQ hG hK hKc htail hKG (hM i) (hboundary i)
    (hF.1 i) (hu i) (hcore.mono fun _ hz => hz i) hg.continuous hPD hmetric hsingle hE hEK

end CircleDomainRigidity.FiniteTransfer

end

end OAI
