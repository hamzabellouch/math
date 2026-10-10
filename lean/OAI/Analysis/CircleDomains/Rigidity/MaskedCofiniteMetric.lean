import OAI.Analysis.CircleDomains.Rigidity.MaskedCircleMetric
import OAI.Analysis.CircleDomains.Transfer.CoreGeometry

namespace OAI

/-!
# Masked circle energy on a completion containing infinity

Only the closure of the tail needs smooth coordinate branches. This
allows every mask boundary to stay inside the retained core, while the
whole completed region may be unbounded in the finite chart.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem exists_spherical_metric_for_masked_cofinite_circles
    {n : ℕ} {Ω Q K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K)
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i)))
    {ε : ℝ} (hbudget : (∫ z in Q \ K, 2 * maskedCircleWedges M f z) < ε) :
    ∃ (R : ℝ) (g : (ℝ × ℝ) → PlanarMetric), 0 < R ∧ ContDiff ℝ ∞ g ∧
      (∀ z, (g z).PosDef) ∧
      (∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) ∧
      (∀ z ∉ Metric.closedBall 0 R, g z = sphericalMetricFactor z • 1) ∧
      (∑ i : Fin n, ∫ z in (Q \ K) ∩ M i, fieldEnergy (circleGradient (f i)) g z) < ε := by
  have hC : IsCompact (Q ∩ closure Kᶜ) :=
    hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right
  have heq : (Q ∩ closure Kᶜ) \ K = Q \ K := by
    ext z
    constructor
    · exact fun hz => ⟨hz.1.1, hz.2⟩
    · exact fun hz => ⟨⟨hz.1, subset_closure hz.2⟩, hz.2⟩
  obtain ⟨R, g, hR, hg, hPD, hcore, hfar, henergy⟩ :=
    exists_spherical_metric_for_masked_circles hΩ hC htail hK M hM hboundary f hf
      (heq.symm ▸ hbudget)
  exact ⟨R, g, hR, hg, hPD, hcore, hfar, by simpa only [heq] using henergy⟩

/-- Mask boundaries retained strictly inside the core cannot meet its
tail closure. The finite union may therefore be removed from the smooth
coordinate neighborhood used by the metric theorem. -/
theorem tail_avoids_mask_boundaries
    {n : ℕ} {Q K Ω : Set (ℝ × ℝ)}
    (hQΩ : Q ⊆ Ω) (M : Fin n → Set (ℝ × ℝ))
    (hboundary : ∀ i, frontier (M i) ⊆ interior K) :
    Q ∩ closure Kᶜ ⊆ Ω \ ⋃ i, frontier (M i) := by
  intro z hz
  refine ⟨hQΩ hz.1, ?_⟩
  intro h
  obtain ⟨i, hi⟩ := mem_iUnion.mp h
  have hnot : z ∉ interior K := by
    simpa only [closure_compl, mem_compl_iff] using hz.2
  exact hnot (hboundary i hi)

end CircleDomainRigidity.FiniteTransfer

end

end OAI
