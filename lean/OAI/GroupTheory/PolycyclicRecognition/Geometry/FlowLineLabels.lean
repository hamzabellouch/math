import OAI.GroupTheory.PolycyclicRecognition.Geometry.CompactFlowSegments
import OAI.GroupTheory.PolycyclicRecognition.Algebra.JointDirectionLabels

namespace OAI

/-! # Fubini turns joint flow-label agreement into agreement on lines -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory MeasureTheory.Measure Set Filter

theorem ae_flowLine_pair_relation
    {G V L : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (μ : Measure G) [SFinite μ] (Exp : V → G) (v : V) (U : Set G)
    (label : G → L) (R : L → L → Prop)
    (hR : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      R (label (z.2 * Exp (z.1.1 • v))) (label (z.2 * Exp (z.1.2 • v))))
    (T : ℝ) :
    ∀ᵐ g ∂μ, (∀ a ∈ Icc 0 T, g * Exp (a • v) ∈ U) →
      ∀ᵐ s ∂volume.restrict (Icc 0 T), ∀ᵐ t ∂volume.restrict (Icc 0 T),
        R (label (g * Exp (s • v))) (label (g * Exp (t • v))) := by
  have hglobal := ae_imp_of_ae_restrict hR
  have hswap := (Measure.measurePreserving_swap (μ := μ) (ν := pairTimeMeasure)).quasiMeasurePreserving.ae
    hglobal
  filter_upwards [ae_ae_of_ae_prod hswap] with g hg
  intro hstay
  change ∀ᵐ p ∂(volume.prod volume),
    (p, g) ∈ flowSegmentDomain U Exp v →
      R (label (g * Exp (p.1 • v))) (label (g * Exp (p.2 • v))) at hg
  filter_upwards [ae_restrict_of_ae (ae_ae_of_ae_prod hg), ae_restrict_mem measurableSet_Icc]
    with s hs hsmem
  filter_upwards [ae_restrict_of_ae hs, ae_restrict_mem measurableSet_Icc] with t ht htmem
  apply ht
  intro r hr
  apply hstay
  have hm := (convex_Icc (0 : ℝ) T) hsmem htmem
    (sub_nonneg.mpr hr.2) hr.1 (show (1 - r) + r = 1 by ring)
  simpa only [smul_eq_mul] using hm

end PolycyclicRecognition

end

end OAI
