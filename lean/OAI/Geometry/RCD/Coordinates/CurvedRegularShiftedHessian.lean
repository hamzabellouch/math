import OAI.Geometry.RCD.Coordinates.RegularCoreWeakMeasure
import OAI.Geometry.RCD.Coordinates.BoundedRegularLocalization
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Sobolev.HessianActionLocality
import OAI.Geometry.RCD.Sobolev.BochnerSourceLocality
import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction

namespace OAI

/-! # The shifted diagonal Hessian estimate for the prescribed full source -/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_regular_shifted_hessian_curved {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2 ≤ n) (hK : K ≤ 0)
    (w dw G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : IsWeakLaplacian (hausdorff n X) hX.quadratic w
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic dw))
    (W : X → ℝ) (L A B : ℝ≥0) (hW : LipschitzWith L W)
    (hwr : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] W)
    (hA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ A)
    (hB : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x| ≤ B)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic w w)
    (p : X) {r : ℝ} (hr : 0 < r) (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) G
      (bochnerGramSource (hausdorff n X) hX.quadratic K w w dw dw σ.toSignedMeasure))
    (g : SobolevSpace (hausdorff n X) hX.quadratic) (dg : Lp ℝ 2 (hausdorff n X))
    (hdg : IsWeakLaplacian (hausdorff n X) hX.quadratic g dg)
    (V : X → ℝ) (M C : ℝ≥0) (hV : LipschitzWith M V)
    (hgr : SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] V)
    (hC : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic g x| ≤ C) :
    ∃ FG GG : SobolevSpace (hausdorff n X) hX.quadratic,
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic FG
        =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic w g) ∧
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic GG
        =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic g g) ∧
      (∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
        0 ≤ (σ.rnDeriv (hausdorff n X) x).toReal-
          2*SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x+(n:ℝ)) ∧
      (∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
        (localHessianAction (hausdorff n X) hX.quadratic w g g FG FG GG x-
          localGamma (hausdorff n X) hX.quadratic g g x)^2 ≤
        ((σ.rnDeriv (hausdorff n X) x).toReal-
          2*SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x+(n:ℝ))*
            (localGamma (hausdorff n X) hX.quadratic g g x)^2) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  have hsub : closedBall p r ⊆ ball p (2*r) := closedBall_subset_ball (by linarith)
  obtain ⟨Cχ,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn p (by positivity : 0 < 2*r)
  obtain ⟨f,df,hf,hfr,hdf⟩ := bounded_regular_localization μ Q w
    (SobolevSpace.toLp μ Q dw) hw W hW hwr A hA χ
  obtain ⟨v,-,-,hvr,-⟩ := bounded_regular_localization μ Q g dg hdg V hV hgr C hC χ
  have hF : SobolevSpace.toLp μ Q G =ᵐ[μ.restrict (ball p (2*r))] localGamma μ Q f.val f.val := by
    filter_upwards [ae_restrict_of_ae hG,localGamma_pair_congr_ae μ Q hfr hfr] with x hx hy
    exact hx.trans hy.symm
  have hs : IsMeasureLaplacianOn μ Q (ball p (2*r)) G
      (bochnerGramSource μ Q K f.val f.val dw dw σ.toSignedMeasure) :=
    IsMeasureLaplacianOn.bochner_congr μ Q measurableSet_ball K σ.toSignedMeasure (EventuallyEq.symm hfr) hσ
  obtain ⟨FG,GG,hFG,hGG,hdim,hbound⟩ := hX.regular_core_weak_hessian_on_measure hn
    (hX.scalarBochner_nonpositive K n hn hK p) f v p (by positivity : 0 < 2*r)
    (isCompact_closedBall p r) hsub dw df hf B hB hdf le_rfl G σ hF hs
  have hfΩ := ae_restrict_of_ae_restrict_of_subset hsub hfr
  have hgΩ := ae_restrict_of_ae_restrict_of_subset hsub hvr
  have hFG' := EventuallyEq.trans (ae_restrict_of_ae hFG) (localGamma_pair_congr_ae μ Q hfΩ hgΩ)
  have hGG' := EventuallyEq.trans (ae_restrict_of_ae hGG) (localGamma_pair_congr_ae μ Q hgΩ hgΩ)
  have hh := localHessianAction_congr μ Q (f := f.val) (f' := w) (u := v.val) (u' := g)
    (v := v.val) (v' := g) (fu := FG) (fv := FG) (uv := GG)
    hfΩ hgΩ hgΩ EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl
  refine ⟨FG,GG,hFG',hGG',?_,?_⟩
  · have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
    filter_upwards [hdim] with x hx
    have hpos : 0 ≤ (n:ℝ)*((σ.rnDeriv μ x).toReal-2*SobolevSpace.toLp μ Q dw x+n) := by
      nlinarith only [hx,sq_nonneg (SobolevSpace.toLp μ Q dw x-(n:ℝ))]
    exact (mul_nonneg_iff_of_pos_left hn0).mp hpos
  · have hb1 := hbound 1
    filter_upwards [hb1,hh,localGamma_pair_congr_ae μ Q hgΩ hgΩ] with x hx hy hz
    simp only [one_mul,one_pow,mul_one] at hx
    change (localHessianAction μ Q f.val v.val v.val FG FG GG x-localGamma μ Q v.val v.val x)^2 ≤
      ((σ.rnDeriv μ x).toReal-2*SobolevSpace.toLp μ Q dw x+(n:ℝ))*(localGamma μ Q v.val v.val x)^2 at hx
    rwa [hy,hz] at hx

end RegularPointCoordinates

end

end OAI
