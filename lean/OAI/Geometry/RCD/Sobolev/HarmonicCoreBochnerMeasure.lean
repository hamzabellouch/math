import OAI.Geometry.RCD.Coordinates.RegularCoreHessianBound

namespace OAI

/-! # The actual full Bochner measure of a locally harmonic regular function -/

open Set Filter MeasureTheory Metric
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.harmonic_core_bochner_measure {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n)
    (f : compactLaplacianCore (hausdorff n X) hX.quadratic univ)
    (qf : Lp ℝ 2 (hausdorff n X))
    (hqf : IsWeakLaplacian (hausdorff n X) hX.quadratic f.val qf)
    (p : X) {R : ℝ} (hR : 0 < R)
    (hq0 : qf =ᵐ[(hausdorff n X).restrict (ball p R)] fun _ => 0) :
    ∃ (F : SobolevSpace (hausdorff n X) hX.quadratic) (σ : Measure X) (hσ : IsFiniteMeasure σ),
      letI := hσ;
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic F =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic f.val f.val) ∧
      IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) F
        (bochnerGramSource (hausdorff n X) hX.quadratic K f.val f.val 0 0 σ.toSignedMeasure) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hz : SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) =ᵐ[μ] fun _ => (0:ℝ) := by
    simpa only [map_zero] using! (Lp.coeFn_zero ℝ 2 μ)
  have hzb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) x|≤(0:ℝ≥0) := by
    filter_upwards [hz] with x hx
    simp only [hx,abs_zero,NNReal.coe_zero,le_refl]
  have hs : qf =ᵐ[μ.restrict (ball p R)] SobolevSpace.toLp μ Q (0 : SobolevSpace μ Q) :=
    hq0.trans (Filter.EventuallyEq.symm (ae_restrict_of_ae hz))
  obtain ⟨F,_FG,_GG,σ,hσ,hF,_hFG,_hGG,hsource,_hbound⟩ :=
    hX.regular_core_directional_hessian hn f f p hR (S := (∅ : Set X)) isCompact_empty
      (empty_subset _) 0 0 qf qf hqf hqf 0 0 hzb hzb hs hs
  exact ⟨F,σ,hσ,hF,hsource⟩

end RegularPointCoordinates

end

end OAI
