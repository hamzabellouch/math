import OAI.GroupTheory.PolycyclicRecognition.Geometry.FlowLineLabels
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineProfileLines

namespace OAI

/-! # Actual affine restrictions along almost every horizontal line -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem ae_affine_flowLine_of_joint_derivative_agreement
    {G V W I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] (Exp : V → G) (hExp0 : Exp 0 = 1)
    (v : V) (U : Set G) (f q : G → W)
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {T : ℝ} (hT : 0 ≤ T) {C : ℝ≥0}
    (hlip : ∀ g, (∀ t ∈ Icc 0 T, g * Exp (t • v) ∈ U) →
      LipschitzOnWith C (fun t => f (g * Exp (t • v))) (Icc 0 T))
    (hderiv : ∀ᵐ g ∂μ, (∀ t ∈ Icc 0 T, g * Exp (t • v) ∈ U) →
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        HasDerivAt (fun s => f (g * Exp (s • v))) (q (g * Exp (t • v))) t)
    (hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v))) :
    ∀ᵐ g ∂μ, (∀ t ∈ Icc 0 T, g * Exp (t • v) ∈ U) →
      ∃ u : W, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u := by
  filter_upwards [hderiv, ae_flowLine_pair_relation μ Exp v U q Eq hpair T] with g hd hp
  intro hstay
  obtain ⟨u, hu⟩ := exists_affine_of_lipschitz_pairwise_derivative α hsep hT
    (hlip g hstay) (hd hstay) (hp hstay)
  exact ⟨u, fun t ht => by simpa only [zero_smul, hExp0, mul_one] using hu t ht⟩

end PolycyclicRecognition

end

end OAI
