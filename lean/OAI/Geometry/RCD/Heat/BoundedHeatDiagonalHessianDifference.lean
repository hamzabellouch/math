import OAI.Geometry.RCD.Heat.BoundedHeatMixedHessianVanishing
import OAI.Geometry.RCD.Sobolev.HessianDifferencePolarization
import OAI.Geometry.RCD.Sobolev.HessianActionLocality

namespace OAI

/-! # Diagonal Hessian stability along bounded regular directions

Two actual regular directions with vanishing weighted gradient difference
have the same limiting diagonal Hessian action against a fixed heat test.
The conclusion is independent of the chosen local Gram representatives.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem bounded_heat_diagonal_hessian_difference (hK : K ≤ 0)
    (f : Lp ℝ 2 (hausdorff n X)) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A) {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    (u v : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (du dv : ℕ → Lp ℝ 2 (hausdorff n X))
    (hdu : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (u k) (du k))
    (hdv : ∀ k, IsWeakLaplacian (hausdorff n X) hX.quadratic (v k) (dv k))
    (U V : ℕ → X → ℝ) (L M B C : ℕ → ℝ≥0)
    (hU : ∀ k, LipschitzWith (L k) (U k)) (hV : ∀ k, LipschitzWith (M k) (V k))
    (hu : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) =ᵐ[hausdorff n X] U k)
    (hv : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) =ᵐ[hausdorff n X] V k)
    (huB : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (u k) x| ≤ B k)
    (hvC : ∀ k, ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic (v k) x| ≤ C k)
    {P : ℝ} (hP : 0 ≤ P)
    (hgu : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (u k) (u k) x ≤ P)
    (hgv : ∀ k, ∀ᵐ x ∂(hausdorff n X).restrict (closedBall p r),
      localGamma (hausdorff n X) hX.quadratic (v k) (v k) x ≤ P)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (hzero : ∀ x ∉ closedBall p r, φ x = 0)
    (henergy : Tendsto (fun k => weightedGamma (hausdorff n X) hX.quadratic
      (fun x => (φ x)^2) (u k-v k) (u k-v k)) atTop (𝓝 0))
    (WU WV UU VV : ℕ → SobolevSpace (hausdorff n X) hX.quadratic)
    (hWU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (u k))
    (hWV : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (WV k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)]
        localGamma (hausdorff n X) hX.quadratic (heatSobolev (hausdorff n X) hX.quadratic a ha f) (v k))
    (hUU : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (UU k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (u k) (u k))
    (hVV : ∀ k, SobolevSpace.toLp (hausdorff n X) hX.quadratic (VV k)
      =ᵐ[(hausdorff n X).restrict (closedBall p r)] localGamma (hausdorff n X) hX.quadratic (v k) (v k)) :
    let m := hausdorff n X
    let q := hX.quadratic
    let w := heatSobolev m q a ha f
    Tendsto (fun k => ∫ x in closedBall p r, |φ x*(
      localHessianAction m q w (u k) (u k) (WU k) (WU k) (UU k) x-
      localHessianAction m q w (v k) (v k) (WV k) (WV k) (VV k) x)| ∂m) atTop (𝓝 0) := by
  intro m q w
  have hdsub (k : ℕ) : IsWeakLaplacian m q (u k-v k) (du k-dv k) := by
    simpa only [neg_one_smul,sub_eq_add_neg] using (hdu k).add m q ((hdv k).smul m q (-1))
  have hsub (k : ℕ) : SobolevSpace.toLp m q (u k-v k) =ᵐ[m] fun x => U k x-V k x := by
    simp only [map_sub]
    filter_upwards [Lp.coeFn_sub (SobolevSpace.toLp m q (u k)) (SobolevSpace.toLp m q (v k)),hu k,hv k]
      with x he h1 h2
    simp only [he,Pi.sub_apply]
    exact congrArg₂ (·-·) h1 h2
  have hadd (k : ℕ) : SobolevSpace.toLp m q (u k+v k) =ᵐ[m] fun x => U k x+V k x := by
    simp only [map_add]
    filter_upwards [Lp.coeFn_add (SobolevSpace.toLp m q (u k)) (SobolevSpace.toLp m q (v k)),hu k,hv k]
      with x he h1 h2
    simp only [he,Pi.add_apply]
    exact congrArg₂ (·+·) h1 h2
  have hsubB (k : ℕ) : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (u k-v k) x| ≤ B k+C k := by
    simp only [map_sub]
    filter_upwards [Lp.coeFn_sub (SobolevSpace.toLp m q (u k)) (SobolevSpace.toLp m q (v k)),huB k,hvC k]
      with x he h1 h2
    simpa only [he,Pi.sub_apply,NNReal.coe_add] using (abs_sub _ _).trans (add_le_add h1 h2)
  have haddB (k : ℕ) : ∀ᵐ x ∂m, |SobolevSpace.toLp m q (u k+v k) x| ≤ B k+C k := by
    simp only [map_add]
    filter_upwards [Lp.coeFn_add (SobolevSpace.toLp m q (u k)) (SobolevSpace.toLp m q (v k)),huB k,hvC k]
      with x he h1 h2
    simpa only [he,Pi.add_apply,NNReal.coe_add] using (abs_add_le _ _).trans (add_le_add h1 h2)
  have hb (k : ℕ) := localGamma_sum_difference_bound m q (u k) (v k) (hgu k) (hgv k)
  obtain ⟨G,H,J,hG,hH,hJ,hlim⟩ := hX.bounded_heat_mixed_hessian_vanishes hn p hK f A hf ha hr
    (fun k => u k-v k) (fun k => u k+v k) (fun k => du k-dv k) (fun k => du k+dv k)
    hdsub (fun k => (hdu k).add m q (hdv k))
    (fun k x => U k x-V k x) (fun k x => U k x+V k x)
    (fun k => L k+M k) (fun k => L k+M k) (fun k => B k+C k) (fun k => B k+C k)
    (fun k => (hU k).sub (hV k)) (fun k => (hU k).add (hV k)) hsub hadd hsubB haddB
    (mul_nonneg (by norm_num) hP) (mul_nonneg (by norm_num) hP)
    (fun k => (hb k).1) (fun k => (hb k).2) φ hφ D hD hzero henergy
  apply hlim.congr'
  refine Eventually.of_forall fun k => ?_
  apply integral_congr_ae
  have hminus : SobolevSpace.toLp m q (WU k-WV k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q w (u k-v k) := by
    simp only [map_sub]
    filter_upwards [hWU k,hWV k,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp m q (WU k)) (SobolevSpace.toLp m q (WV k))),
      ae_restrict_of_ae (localGamma_sub_right m q w (u k) (v k))] with x h1 h2 h3 h4
    simp only [h3,Pi.sub_apply,h4]
    exact congrArg₂ (·-·) h1 h2
  have hplus : SobolevSpace.toLp m q (WU k+WV k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q w (u k+v k) := by
    simp only [map_add]
    filter_upwards [hWU k,hWV k,
      ae_restrict_of_ae (Lp.coeFn_add (SobolevSpace.toLp m q (WU k)) (SobolevSpace.toLp m q (WV k))),
      ae_restrict_of_ae (localGamma_add_right m q w (u k) (v k))] with x h1 h2 h3 h4
    simp only [h3,Pi.add_apply,h4]
    exact congrArg₂ (·+·) h1 h2
  have hcross := localGamma_difference_sum_rep m q (u k) (v k) (UU k) (VV k) (hUU k) (hVV k)
  have he : localHessianAction m q w (u k-v k) (u k+v k) (WU k-WV k) (WU k+WV k) (UU k-VV k)
      =ᵐ[m.restrict (closedBall p r)] localHessianAction m q w (u k-v k) (u k+v k) (G k) (H k) (J k) :=
    localHessianAction_congr m q EventuallyEq.rfl EventuallyEq.rfl EventuallyEq.rfl
      (hminus.trans (hG k).symm) (hplus.trans (hH k).symm) (hcross.trans (hJ k).symm)
  filter_upwards [he,ae_restrict_of_ae (localHessianAction_diagonal_difference m q w
    (u k) (v k) (WU k) (WV k) (UU k) (VV k))] with x he hp
  rw [← he,← hp]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
