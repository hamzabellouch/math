import OAI.Geometry.RCD.Coordinates.CurvedRegularShiftedHessian

namespace OAI

/-! # Nonnegativity of the shifted full-source density on any interior compact ball -/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_regular_shifted_density_nonneg {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n) (hK : K≤0)
    (w dw G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : IsWeakLaplacian (hausdorff n X) hX.quadratic w
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic dw))
    (W : X → ℝ) (L A B : ℝ≥0) (hW : LipschitzWith L W)
    (hwr : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] W)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x|≤A)
    (hB : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x|≤B)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic w w)
    (p : X) {r R : ℝ} (hR : 0<R) (hrR : r<R) (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p R) G
      (bochnerGramSource (hausdorff n X) hX.quadratic K w w dw dw σ.toSignedMeasure)) :
    ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      0≤(σ.rnDeriv (hausdorff n X) x).toReal-
        2*SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x+(n:ℝ) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  obtain ⟨Cχ,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn p hR
  obtain ⟨f,df,hf,hfr,hdf⟩ := bounded_regular_localization μ Q w
    (SobolevSpace.toLp μ Q dw) hw W hW hwr A hA χ
  have hF : SobolevSpace.toLp μ Q G =ᵐ[μ.restrict (ball p R)] localGamma μ Q f.val f.val := by
    filter_upwards [ae_restrict_of_ae hG,localGamma_pair_congr_ae μ Q hfr hfr] with x hx hy
    exact hx.trans hy.symm
  have hs : IsMeasureLaplacianOn μ Q (ball p R) G
      (bochnerGramSource μ Q K f.val f.val dw dw σ.toSignedMeasure) :=
    IsMeasureLaplacianOn.bochner_congr μ Q measurableSet_ball K σ.toSignedMeasure hfr.symm hσ
  obtain ⟨-,-,-,-,hdim,-⟩ := hX.regular_core_weak_hessian_on_measure hn
    (hX.scalarBochner_nonpositive K n hn hK p) f f p hR
    (isCompact_closedBall p r) (closedBall_subset_ball hrR) dw df hf B hB hdf le_rfl G σ hF hs
  have hn0 : 0<(n:ℝ) := by exact_mod_cast (show 0<n by omega)
  filter_upwards [hdim] with x hx
  have hpos : 0≤(n:ℝ)*((σ.rnDeriv μ x).toReal-2*SobolevSpace.toLp μ Q dw x+n) := by
    nlinarith only [hx,sq_nonneg (SobolevSpace.toLp μ Q dw x-(n:ℝ))]
  exact (mul_nonneg_iff_of_pos_left hn0).mp hpos

end RegularPointCoordinates

end

end OAI
