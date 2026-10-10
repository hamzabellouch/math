import OAI.Geometry.RCD.Coordinates.RegularCoreMixedHessian
import OAI.Geometry.RCD.Sobolev.BochnerSourceLocality
import OAI.Geometry.RCD.Coordinates.BoundedRegularLocalization
import OAI.Geometry.RCD.Sobolev.GoodCutoffFromResolvent
import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # Mixed Hessian domination by a prescribed full Bochner measure

Localizing the potential and directions preserves the original measure,
so quantitative mass estimates survive the compact-core reduction.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.bounded_regular_prescribed_hessian {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) [(hausdorff n X).Regular] (hn : 2≤n)
    (hscalar : ScalarDimensionalBochner (hausdorff n X) hX.quadratic K n)
    (w dw : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : IsWeakLaplacian (hausdorff n X) hX.quadratic w
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic dw))
    (W : X → ℝ) {L A B : ℝ≥0} (hW : LipschitzWith L W)
    (hwr : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] W)
    (hwA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x|≤A)
    (hdB : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x|≤B)
    (G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic w w)
    (p : X) {r : ℝ} (hr : 0<r) (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) G
      (bochnerGramSource (hausdorff n X) hX.quadratic K w w dw dw σ.toSignedMeasure)) :
      ∀ (g : SobolevSpace (hausdorff n X) hX.quadratic) (q : Lp ℝ 2 (hausdorff n X)),
      IsWeakLaplacian (hausdorff n X) hX.quadratic g q →
      ∀ (V : X → ℝ) (M C : ℝ≥0), LipschitzWith M V →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic g =ᵐ[hausdorff n X] V) →
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic g x|≤C) →
      ∀ (h : SobolevSpace (hausdorff n X) hX.quadratic) (e : Lp ℝ 2 (hausdorff n X)),
      IsWeakLaplacian (hausdorff n X) hX.quadratic h e →
      ∀ (Z : X → ℝ) (N D : ℝ≥0), LipschitzWith N Z →
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic h =ᵐ[hausdorff n X] Z) →
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic h x| ≤ D) →
      ∃ WG WH GH : SobolevSpace (hausdorff n X) hX.quadratic,
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic WG
          =ᵐ[(hausdorff n X).restrict (closedBall p r)]
            localGamma (hausdorff n X) hX.quadratic w g) ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic WH
          =ᵐ[(hausdorff n X).restrict (closedBall p r)]
            localGamma (hausdorff n X) hX.quadratic w h) ∧
        (SobolevSpace.toLp (hausdorff n X) hX.quadratic GH
          =ᵐ[(hausdorff n X).restrict (closedBall p r)]
            localGamma (hausdorff n X) hX.quadratic g h) ∧
        ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
          (localHessianAction (hausdorff n X) hX.quadratic w g h WG WH GH x)^2 ≤
            (σ.rnDeriv (hausdorff n X) x).toReal*
              localGamma (hausdorff n X) hX.quadratic g g x*
              localGamma (hausdorff n X) hX.quadratic h h x := by
  let m := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded m hX.finiteOnBounded
  have h2r : 0<2*r := by positivity
  have hsub : closedBall p r⊆ball p (2*r) := closedBall_subset_ball (by linarith)
  obtain ⟨Cχ,-,⟨χ⟩⟩ := hX.goodCutoff_exists hn p h2r
  obtain ⟨f,df,hf,hfr,hdf⟩ := bounded_regular_localization m Q w
    (SobolevSpace.toLp m Q dw) hw W hW hwr A hwA χ
  have hfΩ := ae_restrict_of_ae_restrict_of_subset hsub hfr
  intro g q hg V M C hV hgr hgC h e he Z N D hZ hhr hhD
  obtain ⟨v,dv,hv,hvr,-⟩ := bounded_regular_localization m Q g q hg V hV hgr C hgC χ
  obtain ⟨z,dz,hz,hzr,-⟩ := bounded_regular_localization m Q h e he Z hZ hhr D hhD χ
  let u : Fin 3 → compactLaplacianCore m Q univ := ![f,v,z]
  let U := sobolevColumnMap m Q (fun i => (u i).val)
  let E (i : Fin 3) : Euclidean 3 := EuclideanSpace.single i 1
  have h0 : U (E 0) = f.val := by simpa [u,E] using sobolevColumnMap_single m Q (fun i => (u i).val) 0
  have h1 : U (E 1) = v.val := by simpa [u,E] using sobolevColumnMap_single m Q (fun i => (u i).val) 1
  have h2 : U (E 2) = z.val := by simpa [u,E] using sobolevColumnMap_single m Q (fun i => (u i).val) 2
  have hqU : IsWeakLaplacian m Q (U (E 0)) df := by rw [h0]; exact hf
  have hF0 : SobolevSpace.toLp m Q G =ᵐ[m.restrict (ball p (2*r))]
      localGamma m Q (U (E 0)) (U (E 0)) := by
    rw [h0]
    filter_upwards [ae_restrict_of_ae hG,localGamma_pair_congr_ae m Q hfr hfr] with x hx hy
    exact hx.trans hy.symm
  have hlapU : IsMeasureLaplacianOn m Q (ball p (2*r)) G
      (bochnerGramSource m Q K (U (E 0)) (U (E 0)) dw dw σ.toSignedMeasure) := by
    rw [h0]
    exact IsMeasureLaplacianOn.bochner_congr m Q measurableSet_ball K σ.toSignedMeasure hfr.symm hσ
  obtain ⟨H,_hsym,hH,_hdim,hbound⟩ := hX.regular_core_mixed_hessian_on_measure hn hscalar u
    p h2r (isCompact_closedBall p r) hsub (E 0) dw df hqU B hdB hdf le_rfl G σ hF0 hlapU
  let WG := H (E 0) (E 1)
  let WH := H (E 0) (E 2)
  let GH := H (E 1) (E 2)
  have hWG : SobolevSpace.toLp m Q WG =ᵐ[m] localGamma m Q f.val v.val := by
    have hh := hH (E 0) (E 1)
    change SobolevSpace.toLp m Q WG =ᵐ[m] localGamma m Q (U (E 0)) (U (E 1)) at hh
    simpa only [h0,h1] using hh
  have hWH : SobolevSpace.toLp m Q WH =ᵐ[m] localGamma m Q f.val z.val := by
    have hh := hH (E 0) (E 2)
    change SobolevSpace.toLp m Q WH =ᵐ[m] localGamma m Q (U (E 0)) (U (E 2)) at hh
    simpa only [h0,h2] using hh
  have hGH : SobolevSpace.toLp m Q GH =ᵐ[m] localGamma m Q v.val z.val := by
    have hh := hH (E 1) (E 2)
    change SobolevSpace.toLp m Q GH =ᵐ[m] localGamma m Q (U (E 1)) (U (E 2)) at hh
    simpa only [h1,h2] using hh
  have hgΩ := ae_restrict_of_ae_restrict_of_subset hsub hvr
  have hhΩ := ae_restrict_of_ae_restrict_of_subset hsub hzr
  have hb := hbound 0 (E 1) (E 2)
  change ∀ᵐ x ∂m.restrict (closedBall p r),
    (localHessianAction m Q (U (E 0)) (U (E 1)) (U (E 2)) WG WH GH x -
      0*localGamma m Q (U (E 1)) (U (E 2)) x)^2 ≤
      ((σ.rnDeriv m x).toReal-2*0*SobolevSpace.toLp m Q dw x+(n:ℝ)*0^2)*
        localGamma m Q (U (E 1)) (U (E 1)) x*localGamma m Q (U (E 2)) (U (E 2)) x at hb
  simp only [h0,h1,h2,zero_mul,mul_zero,sub_zero,zero_pow (by decide : (2:ℕ) ≠ 0),add_zero] at hb
  refine ⟨WG,WH,GH,?_,?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hWG,localGamma_pair_congr_ae m Q hfΩ hgΩ] with x hx hy
    exact hx.trans hy
  · filter_upwards [ae_restrict_of_ae hWH,localGamma_pair_congr_ae m Q hfΩ hhΩ] with x hx hy
    exact hx.trans hy
  · filter_upwards [ae_restrict_of_ae hGH,localGamma_pair_congr_ae m Q hgΩ hhΩ] with x hx hy
    exact hx.trans hy
  · have hHlocal : localHessianAction m Q f.val v.val z.val WG WH GH
        =ᵐ[m.restrict (closedBall p r)] localHessianAction m Q w g h WG WH GH :=
      localHessianAction_congr m Q hfΩ hgΩ hhΩ
        (EventuallyEq.refl _ _) (EventuallyEq.refl _ _) (EventuallyEq.refl _ _)
    filter_upwards [hb,hHlocal,localGamma_pair_congr_ae m Q hgΩ hgΩ,
      localGamma_pair_congr_ae m Q hhΩ hhΩ] with x hx hh hg hz
    rwa [hh,hg,hz] at hx

end RegularPointCoordinates

end

end OAI
