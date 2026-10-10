import OAI.GroupTheory.PolycyclicRecognition.Geometry.ContinuousFlowAffinity

namespace OAI

/-! # Finite derivative labels give finite, locally constant flow slopes -/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped NNReal

theorem ae_affine_flowLine_mem_of_joint_derivative_agreement
    {G V W I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] (Exp : V → G) (hExp0 : Exp 0 = 1)
    (v : V) (U : Set G) (f q : G → W)
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {T : ℝ} (hT : 0 < T) {C : ℝ≥0}
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t => f (g * Exp (t • v))) (Icc 0 T))
    (hderiv : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        HasDerivAt (fun s => f (g * Exp (s • v))) (q (g * Exp (t • v))) t)
    (hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)))
    {E : Set W} (hq : ∀ g ∈ U, q g ∈ E) :
    ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∃ u ∈ E, ∀ t ∈ Icc 0 T, f (g * Exp (t • v)) = f g + t • u := by
  filter_upwards [hderiv, ae_flowLine_pair_relation μ Exp v U q Eq hpair T] with g hd hp
  intro hstay
  have hqline : ∀ᵐ t ∂volume.restrict (Icc 0 T), q (g * Exp (t • v)) ∈ E := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hq _ (hstay t ht)
  obtain ⟨u, huE, hu⟩ := exists_affine_mem_of_lipschitz_pairwise_derivative α hsep hT
    (hlip g hstay) (hd hstay) (hp hstay) hqline
  exact ⟨u, huE, fun t ht => by simpa only [zero_smul, hExp0, mul_one] using hu t ht⟩

theorem finite_flowLine_slopes
    {G V W I : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [MeasurableSpace G] [OpensMeasurableSpace G]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure G) [SFinite μ] [μ.IsOpenPosMeasure]
    (Exp : V → G) (hExp : Continuous Exp) (hExp0 : Exp 0 = 1)
    (v : V) (U : Set G) (hU : IsOpen U) (f q : G → W) (hf : ContinuousOn f U)
    (α : I → W →L[ℝ] ℝ) (hsep : ∀ w : W, (∀ i, α i w = 0) → w = 0)
    {T : ℝ} (hT : 0 < T) {C : ℝ≥0}
    (hlip : ∀ g ∈ flowLineBase U Exp v T,
      LipschitzOnWith C (fun t => f (g * Exp (t • v))) (Icc 0 T))
    (hderiv : ∀ᵐ g ∂μ, g ∈ flowLineBase U Exp v T →
      ∀ᵐ t ∂volume.restrict (Icc 0 T),
        HasDerivAt (fun s => f (g * Exp (s • v))) (q (g * Exp (t • v))) t)
    (hpair : ∀ᵐ z ∂(pairTimeMeasure.prod μ).restrict (flowSegmentDomain U Exp v),
      q (z.2 * Exp (z.1.1 • v)) = q (z.2 * Exp (z.1.2 • v)))
    {E : Set W} (hE : E.Finite) (hq : ∀ g ∈ U, q g ∈ E) :
    (∀ g ∈ flowLineBase U Exp v T, ∀ t ∈ Icc 0 T,
      f (g * Exp (t • v)) = f g + t • flowLineSlope f Exp v T g) ∧
    MapsTo (flowLineSlope f Exp v T) (flowLineBase U Exp v T) E := by
  have hae := ae_affine_flowLine_mem_of_joint_derivative_agreement μ Exp hExp0 v U f q
    α hsep hT hlip hderiv hpair hq
  refine ⟨flowLine_affinity_of_ae μ hU hExp hExp0 hT hf ?_,
    flowLineSlope_mem_of_ae μ hU hExp hExp0 hT hf hE.isClosed hae⟩
  filter_upwards [hae] with g hg hbase
  obtain ⟨u, _, hu⟩ := hg hbase
  exact ⟨u, hu⟩

end PolycyclicRecognition

end

end OAI
