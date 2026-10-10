import OAI.Geometry.RCD.Heat.CanonicalHeatHessian
import OAI.Geometry.RCD.Coordinates.BoundedRegularPrescribedHessian
import OAI.Geometry.RCD.Sobolev.ScalarBochnerConstruction
import OAI.Geometry.RCD.Sobolev.HessianL1MassBound

namespace OAI

/-! # The canonical Hessian mass bound with nonpositive curvature -/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X)
  [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn in
theorem curved_canonical_hessian_young_bound (hK : K ≤ 0)
    (w dw G : SobolevSpace (hausdorff n X) hX.quadratic)
    (hw : IsWeakLaplacian (hausdorff n X) hX.quadratic w
      (SobolevSpace.toLp (hausdorff n X) hX.quadratic dw))
    (W : X → ℝ) (Lw Aw Bw : ℝ≥0) (hW : LipschitzWith Lw W)
    (hwr : SobolevSpace.toLp (hausdorff n X) hX.quadratic w =ᵐ[hausdorff n X] W)
    (hwA : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ Aw)
    (hdB : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x| ≤ Bw)
    (hG : SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
      localGamma (hausdorff n X) hX.quadratic w w)
    {r : ℝ} (hr : 0 < r) (σ : Measure X) [IsFiniteMeasure σ]
    (hσ : IsMeasureLaplacianOn (hausdorff n X) hX.quadratic (ball p (2*r)) G
      (bochnerGramSource (hausdorff n X) hX.quadratic K w w dw dw σ.toSignedMeasure))
    (v : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ) (Lv Av : ℝ≥0)
    (hV : LipschitzWith Lv V) (hVc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hJ : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic w v p r φ J)
    {a : ℝ} (ha : 0 < a) :
    4*a*(∫ x in closedBall p r, |J x| ∂hausdorff n X) ≤
      4*a^2*(hausdorff n X).real (closedBall p r)+((D:ℝ)*((Lv:ℝ)*Real.exp |K|)^2)^2*σ.real (closedBall p r) := by
  let m := hausdorff n X
  let q := hX.quadratic
  obtain ⟨u,du,U,M,_P,hu,hdu,hU,hur,huA,_hP,_hgu,_hconv⟩ :=
    hX.compact_lipschitz_heat_directions hn p v V Lv Av hV hVc hv hAv
  have hgu (k : ℕ) : ∀ᵐ x ∂m, localGamma m q (u k) (u k) x ≤ ((Lv:ℝ)*Real.exp |K|)^2 := by
    have ht : 0 < 1/((k:ℝ)+1) := by positivity
    have hg := hX.heat_compact_slope_bdd K n hn hV hVc p (SobolevSpace.toLp m q v)
      hv.symm (1/((k:ℝ)+1)) ht
    have he : u k=heatSobolev m q (1/((k:ℝ)+1)) ht (SobolevSpace.toLp m q v) := by
      rw [hu k]
      simp only [heatH1,dite_eq_left ht]
      rfl
    rw [he]
    filter_upwards [hg,localGamma_self m q _,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg m q _)] with x hx hs h0
    rw [hs]
    have ht1 : 1/((k:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity : 0 < (k:ℝ)+1)).mpr
      have hk : (0:ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    have hexp : -K*(1/((k:ℝ)+1)) ≤ |K| := by
      calc
        _ ≤ |K| *(1/((k:ℝ)+1)) := mul_le_mul_of_nonneg_right (neg_le_abs K) ht.le
        _ ≤ |K| := by simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 (abs_nonneg K)
    have hlarge : (Lv:ℝ)*Real.exp (-K*(1/((k:ℝ)+1))) ≤ (Lv:ℝ)*Real.exp |K| :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) Lv.coe_nonneg
    exact pow_le_pow_left₀ h0 (hx.trans hlarge) 2
  obtain ⟨A,B,hA,hB,hlim⟩ := hJ
  have hAr (k : ℕ) : SobolevSpace.toLp m q (A k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q w (u k) := by simpa only [hu k] using hA k
  have hBr (k : ℕ) : SobolevSpace.toLp m q (B k) =ᵐ[m.restrict (closedBall p r)]
      localGamma m q (u k) (u k) := by simpa only [hu k] using hB k
  let F k x := φ x*localHessianAction m q w (u k) (u k) (A k) (A k) (B k) x
  have hF (k : ℕ) : Integrable (F k) (m.restrict (closedBall p r)) :=
    ((localHessianAction_integrable m q w (u k) (u k) (A k) (A k) (B k)).bdd_mul hφ
      (hD.mono fun x hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  apply L1_limit_radon_young_bound m σ (isCompact_closedBall p r).measure_lt_top.ne
    F hF J (by simpa only [F,hu] using hlim) ((D:ℝ)*((Lv:ℝ)*Real.exp |K|)^2) _ ha
  intro k
  obtain ⟨A',B',C',hA',hB',hC',hh⟩ := hX.bounded_regular_prescribed_hessian hn
    (hX.scalarBochner_nonpositive K n hn hK p) w dw hw W hW hwr hwA hdB G hG p hr σ hσ
    (u k) (du k) (hdu k) (U k) (M k) Av (hU k) (hur k) (huA k)
    (u k) (du k) (hdu k) (U k) (M k) Av (hU k) (hur k) (huA k)
  have he := localHessianAction_congr_of_grams m q w (u k) (u k) (u k) (u k)
    (A k) A' (A k) B' (B k) C' EventuallyEq.rfl EventuallyEq.rfl
    (hAr k) hA' (hAr k) hB' (hBr k) hC'
  filter_upwards [he,hh,ae_restrict_of_ae (hgu k),ae_restrict_of_ae hD,
    ae_restrict_of_ae (localGamma_self m q (u k))] with x he hh hg hφx hself
  have h0 : 0 ≤ localGamma m q (u k) (u k) x := by rw [hself]; positivity
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hg 2)
    (ENNReal.toReal_nonneg (a := σ.rnDeriv m x))
  have hH : (localHessianAction m q w (u k) (u k) (A k) (A k) (B k) x)^2 ≤
      (σ.rnDeriv m x).toReal*(((Lv:ℝ)*Real.exp |K|)^2)^2 := by
    rw [he]
    exact hh.trans (by simpa only [pow_two,mul_assoc] using hsq)
  have hφsq : (φ x)^2 ≤ (D:ℝ)^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (φ x)) hφx 2
  dsimp only [F]
  calc
    _ = (φ x)^2*(localHessianAction m q w (u k) (u k) (A k) (A k) (B k) x)^2 := mul_pow _ _ _
    _ ≤ (φ x)^2*((σ.rnDeriv m x).toReal*(((Lv:ℝ)*Real.exp |K|)^2)^2) :=
      mul_le_mul_of_nonneg_left hH (sq_nonneg _)
    _ ≤ (D:ℝ)^2*((σ.rnDeriv m x).toReal*(((Lv:ℝ)*Real.exp |K|)^2)^2) :=
      mul_le_mul_of_nonneg_right hφsq (mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
    _ = _ := by ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
