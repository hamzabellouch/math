import OAI.Analysis.CircleDomains.Sobolev.FiniteTransferEnergy
import OAI.Analysis.CircleDomains.Transfer.CoreGeometry

namespace OAI

/-!
# Energy transfer on a completed region containing infinity

The completed region is unbounded in a finite chart. Its tail outside the
retained core lies in one compact piece. Local agreement on the core and
the original finite energy give integrability on the entire completed
region, and hence the full localized estimate.
-/

open Set Filter MeasureTheory Finset
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem gradientEnergy_eq_spherical_on_core
    {K : Set (ℝ × ℝ)} {f u : (ℝ × ℝ) → ℝ}
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {z : ℝ × ℝ} (hz : z ∈ K) :
    gradientEnergy f g z = gradientEnergy u (fun z => sphericalMetricFactor z • 1) z := by
  have heq := (hretain.filter_mono (nhds_le_nhdsSet hz)).fderiv_eq (𝕜 := ℝ)
  simp only [gradientEnergy, planarGradient, heq, hmetric.self_of_nhdsSet z hz]

theorem integrableOn_gradientEnergy_with_cofinite_core
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    {f u : (ℝ × ℝ) → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    (hu : IntegrableOn (gradientEnergy u (fun z => sphericalMetricFactor z • 1)) G)
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (gradientEnergy f g) Q := by
  obtain ⟨R, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  have ht : IntegrableOn (gradientEnergy f g) (Q \ K) := by
    rw [htail]
    exact (integrableOn_gradientEnergy hΩ hQc (fun z hz => hQΩ hz.1) hf hg hPD).mono_set sdiff_subset
  have hc : IntegrableOn (gradientEnergy f g) (Q ∩ K) := by
    apply (hu.mono_set (fun z hz => hKG hz.2)).congr
    filter_upwards [ae_restrict_mem (hQ.measurableSet.inter hK.measurableSet)] with z hz
    exact (gradientEnergy_eq_spherical_on_core hretain hmetric hz.2).symm
  simpa only [inter_union_sdiff] using hc.union ht

theorem localized_coordinate_energy_lt_with_cofinite_core
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
    (f u : ℕ → (ℝ × ℝ) → ℝ) (hf : ∀ i, ContDiffOn ℝ ∞ (f i) Ω)
    {n : ℕ} (hu : ∀ i < n, IntegrableOn
      (gradientEnergy (u i) (fun z => sphericalMetricFactor z • 1)) G)
    (hretain : ∀ᶠ z in 𝓝ˢ K, ∀ i < n, f i z = u i z)
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {ε : ℝ} (henergy : (∫ z in Q \ K, matrixEnergy (coordinateGram f n z) (g z)) < ε)
    {i : ℕ} (hi : i < n) {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ z in Q \ E, gradientEnergy (f i) g z) <
      (∫ z in G \ E, gradientEnergy (u i) (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have heq : f i =ᶠ[𝓝ˢ K] u i := hretain.mono (fun _ hz => hz i hi)
  obtain ⟨R, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  have hT : IntegrableOn (fun z => matrixEnergy (coordinateGram f n z) (g z)) (Q \ K) := by
    rw [htail]
    exact (integrableOn_coordinateGram_energy hΩ hQc (fun z hz => hQΩ hz.1) f hf n hg hPD).mono_set
      sdiff_subset
  apply localized_energy_lt_source hQ.measurableSet hG hK.measurableSet hE hEK
    (fun z hz => hKG hz.2)
    (integrableOn_gradientEnergy_with_cofinite_core hΩ hQ hQΩ hK hKc hKG (hf i) (hu i hi)
      heq hg hPD hmetric) (hu i hi) hT
    (fun z _ => gradientEnergy_nonneg _ (fun w => Matrix.PosDef.one.smul
      (sphericalMetricFactor_pos w)) z)
    (fun z hz => gradientEnergy_eq_spherical_on_core heq hmetric hz.2)
    (fun z _ => gradientEnergy_le_coordinateGram f hi hPD z) henergy

/-- The common-width analytic transfer applies to the entire completed
region, including its unbounded chart part, whenever the core retains
infinity. -/
theorem exists_cofinite_transfer_at_good_width
    {I : Type*} [Fintype I] {n : ℕ}
    (D : I → Set (ℝ × ℝ)) (hD : ∀ i, IsOpen (D i))
    {Ω Q G K : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q) (hQΩ : Q ⊆ Ω)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ)) (hKG : K ⊆ G)
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
      ∀ i : ℕ, i < n → ∀ E : Set (ℝ × ℝ), MeasurableSet E → E ⊆ K →
        (∫ z in Q \ E, gradientEnergy (natCoordinateFamily F i) g z) <
          (∫ z in G \ E, gradientEnergy (natCoordinateFamily u i)
            (fun z => sphericalMetricFactor z • 1) z) + ε := by
  obtain ⟨R₀, _, hQc, htail⟩ := exists_compact_tail_piece hQ hKc
  obtain ⟨k, F, R, g, hk, hF, hcore, hR, hg, hPD, hmetric, hfar, hsum, _⟩ :=
    exists_filled_spherical_transfer_at_good_width D hD hΩ hQc (fun z hz => hQΩ hz.1)
      hG hK hKG (fun z hz => hcover hz.1) hKD v u hu hretain hh hfill hvi hgood k₀
  have hFs := contDiffOn_natCoordinateFamily hF.1
  have henergy : (∫ z in Q \ K, matrixEnergy (coordinateGram (natCoordinateFamily F) n z) (g z)) < ε := by
    rw [htail, integral_coordinateGram_eq_sum hΩ hQc (fun z hz => hQΩ hz.1) _ hFs n hg.continuous hPD]
    exact hsum
  refine ⟨k, F, R, g, hk, hF, hcore, hR, hg, hPD, hmetric, hfar, ?_, ?_⟩
  · simpa only [htail] using hsum
  · intro i hi E hE hEK
    apply localized_coordinate_energy_lt_with_cofinite_core hΩ hQ hQΩ hG hK hKc hKG
      (natCoordinateFamily F) (natCoordinateFamily u) hFs ?_ ?_
      hg.continuous hPD hmetric henergy hi hE hEK
    · intro j hj
      simpa only [IntegrableOn, natCoordinateFamily, dite_eq_left hj] using
        integrable_gradientEnergy_spherical_of_memLp (hu ⟨j, hj⟩)
    · filter_upwards [hcore] with z hz j hj
      simpa only [natCoordinateFamily, dite_eq_left hj] using hz ⟨j, hj⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
