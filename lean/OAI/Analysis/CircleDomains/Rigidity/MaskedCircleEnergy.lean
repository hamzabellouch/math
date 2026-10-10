import OAI.Analysis.CircleDomains.Rigidity.MaskedCofiniteMetric
import OAI.Analysis.CircleDomains.Rigidity.MaskTopology
import OAI.Analysis.CircleDomains.Sobolev.CircleFilledEnergy

namespace OAI

/-!
# Localized energy on the actual coordinate masks

The retained core contains the mask boundaries. Smoothness on the
compact tail and original masked L² data suffice for whole-domain
integrability and comparison after deleting any measurable part of the
core. No extension across a mask boundary is required.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem continuousOn_maskedCircleWedges_off_boundaries
    {n : ℕ} {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (M : Fin n → Set (ℝ × ℝ)) (hM : ∀ i, IsClosed (M i))
    (f : Fin n → (ℝ × ℝ) → UnitAddCircle)
    (hf : ∀ i, SmoothCircleOn (f i) (Ω ∩ interior (M i))) :
    ContinuousOn (maskedCircleWedges M f) (Ω \ ⋃ i, frontier (M i)) := by
  have hclosed : IsClosed (⋃ i, frontier (M i)) := isClosed_iUnion_of_finite (fun _ => isClosed_frontier)
  have hc := continuousOn_circleWedges (hΩ.sdiff hclosed)
    (fun i => maskCircleMap (M i) (f i)) (smoothCircleOn_masks_off_boundaries M hM f hf)
  apply hc.congr
  intro z hz
  exact (circleWedges_maskCircleMap_eq M hM f
    (fun i hi => hz.2 (mem_iUnion.mpr ⟨i, hi⟩))).symm

theorem integrableOn_masked_circle_energy_tail
    {Ω Q K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hKc : IsCompact (closure Kᶜ)) (htail : Q ∩ closure Kᶜ ⊆ Ω)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    {g : (ℝ × ℝ) → PlanarMetric} (hg : Continuous g) (hPD : ∀ z, (g z).PosDef) :
    IntegrableOn (fieldEnergy (circleGradient f) g) ((Q \ K) ∩ M) := by
  have hC : IsCompact ((Q ∩ closure Kᶜ) ∩ M) :=
    (hKc.of_isClosed_subset (hQ.inter isClosed_closure) inter_subset_right).inter_right hM
  have hCΩ : (Q ∩ closure Kᶜ) ∩ M ⊆ Ω ∩ interior M := by
    intro z hz
    refine ⟨htail hz.1, (mem_interior_iff_notMem_frontier hz.2).mpr ?_⟩
    intro hb
    have hn : z ∉ interior K := by
      simpa only [closure_compl, mem_compl_iff] using hz.1.2
    exact hn (hboundary hb)
  have hc := continuousOn_fieldEnergy
    (contDiffOn_circleGradient (hΩ.inter isOpen_interior) hf).continuousOn hg hPD
  exact ((hc.mono hCΩ).integrableOn_compact hC).mono_set
    (fun z hz => ⟨⟨hz.1.1, subset_closure hz.1.2⟩, hz.2⟩)

theorem integrableOn_masked_circle_energy
    {Ω Q G K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    (hu : MemLp (circleGradient u) 2 (volume.restrict (G ∩ M)))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1) :
    IntegrableOn (fieldEnergy (circleGradient f) g) (Q ∩ M) := by
  have ht : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) \ K) := by
    have heq : (Q ∩ M) \ K = (Q \ K) ∩ M := by ext z; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [heq]
    exact integrableOn_masked_circle_energy_tail hΩ hQ hKc htail hM hboundary hf hg hPD
  have hsource : IntegrableOn (fieldEnergy (circleGradient u)
      (fun z => sphericalMetricFactor z • 1)) (G ∩ M) :=
    integrable_fieldEnergy_spherical_of_memLp hu
  have hc : IntegrableOn (fieldEnergy (circleGradient f) g) ((Q ∩ M) ∩ K) := by
    apply (hsource.mono_set
      (fun z hz => ⟨hKG hz.2, hz.1.2⟩)).congr
    filter_upwards [ae_restrict_mem ((hQ.measurableSet.inter hM.measurableSet).inter hK.measurableSet)] with z hz
    have hgrad := circleGradient_congr_of_eventuallyEq
      (hretain.filter_mono (nhds_le_nhdsSet hz.2))
    simp only [fieldEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]
  simpa only [inter_union_sdiff] using hc.union ht

theorem localized_masked_circle_energy_lt
    {Ω Q G K M : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hQ : IsClosed Q)
    (hG : MeasurableSet G) (hK : IsClosed K) (hKc : IsCompact (closure Kᶜ))
    (htail : Q ∩ closure Kᶜ ⊆ Ω) (hKG : K ⊆ G)
    (hM : IsClosed M) (hboundary : frontier M ⊆ interior K)
    {f u : (ℝ × ℝ) → UnitAddCircle} (hf : SmoothCircleOn f (Ω ∩ interior M))
    (hu : MemLp (circleGradient u) 2 (volume.restrict (G ∩ M)))
    (hretain : f =ᶠ[𝓝ˢ K] u) {g : (ℝ × ℝ) → PlanarMetric}
    (hg : Continuous g) (hPD : ∀ z, (g z).PosDef)
    (hmetric : ∀ᶠ z in 𝓝ˢ K, g z = sphericalMetricFactor z • 1)
    {ε : ℝ} (henergy : (∫ z in (Q \ K) ∩ M, fieldEnergy (circleGradient f) g z) < ε)
    {E : Set (ℝ × ℝ)} (hE : MeasurableSet E) (hEK : E ⊆ K) :
    (∫ z in (Q \ E) ∩ M, fieldEnergy (circleGradient f) g z) <
      (∫ z in (G \ E) ∩ M, fieldEnergy (circleGradient u)
        (fun z => sphericalMetricFactor z • 1) z) + ε := by
  have hswap (S A : Set (ℝ × ℝ)) : (S ∩ M) \ A = (S \ A) ∩ M := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff]
    tauto
  have hi := integrableOn_masked_circle_energy hΩ hQ hK hKc htail hKG hM hboundary
    hf hu hretain hg hPD hmetric
  have hu' := integrable_fieldEnergy_spherical_of_memLp hu
  have ht := hi.mono_set (s := (Q ∩ M) \ K) Set.sdiff_subset
  have he : (∫ z in (Q ∩ M) \ K, fieldEnergy (circleGradient f) g z) < ε := by
    simpa only [hswap] using henergy
  have hresult := localized_energy_lt_source
    (hQ.measurableSet.inter hM.measurableSet) (hG.inter hM.measurableSet) hK.measurableSet hE hEK
    (fun z hz => ⟨hKG hz.2, hz.1.2⟩) hi hu' ht
    (fun z _ => covectorEnergy_nonneg _ (Matrix.PosDef.one.smul (sphericalMetricFactor_pos z)))
    (T := fieldEnergy (circleGradient f) g) ?_ (fun _ _ => le_rfl) he
  · simpa only [hswap] using hresult
  · intro z hz
    have hgrad := circleGradient_congr_of_eventuallyEq
      (hretain.filter_mono (nhds_le_nhdsSet hz.2))
    simp only [fieldEnergy, hgrad, hmetric.self_of_nhdsSet z hz.2]

end CircleDomainRigidity.FiniteTransfer

end

end OAI
