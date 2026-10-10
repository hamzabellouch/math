import OAI.Geometry.RCD.Coordinates.CurvedRegularShiftedHessian
import OAI.Geometry.RCD.Heat.HeatCompactUniform
import OAI.Geometry.RCD.Heat.CanonicalHeatHessian
import OAI.Geometry.RCD.Harmonic.GramL1Continuity
import OAI.Geometry.RCD.Sobolev.L1DifferenceLimit

namespace OAI

/-! # Shifted density controls the canonical Hessian error with curvature -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.canonical_shifted_hessian_young_curved {K : ℝ} {n : ℕ}
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
    (v : SobolevSpace (hausdorff n X) hX.quadratic) (V : X → ℝ) (Lv Av : ℝ≥0)
    (hV : LipschitzWith Lv V) (hVc : HasCompactSupport V)
    (hv : SobolevSpace.toLp (hausdorff n X) hX.quadratic v =ᵐ[hausdorff n X] V)
    (hAv : ∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic v x| ≤ Av)
    (φ : X → ℝ) (hφ : AEStronglyMeasurable φ (hausdorff n X)) (D : ℝ≥0)
    (hD : ∀ᵐ x ∂hausdorff n X, |φ x| ≤ D)
    (J : Lp ℝ 1 ((hausdorff n X).restrict (closedBall p r)))
    (hJ : IsCanonicalHeatHessian (hausdorff n X) hX.quadratic w v p r φ J) (a : ℝ) :
    4*a*(∫ x in closedBall p r, |J x-φ x*localGamma (hausdorff n X) hX.quadratic v v x|
      ∂hausdorff n X) ≤ 4*a^2*(hausdorff n X).real (closedBall p r)+
        ((D:ℝ)*((Lv:ℝ)*Real.exp |K|)^2)^2*(∫ x in closedBall p r,
          (σ.rnDeriv (hausdorff n X) x).toReal-
            2*SobolevSpace.toLp (hausdorff n X) hX.quadratic dw x+(n:ℝ) ∂hausdorff n X) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let := hX.separable
  let := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let S := closedBall p r
  let : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.mpr (isCompact_closedBall p r).measure_lt_top.ne
  obtain ⟨u,du,U,M,-,hu,hdu,hU,hur,huA,-,-,hconv⟩ :=
    hX.compact_lipschitz_heat_directions hn p v V Lv Av hV hVc hv hAv
  have hgu (k : ℕ) : ∀ᵐ x ∂μ, localGamma μ Q (u k) (u k) x ≤ ((Lv:ℝ)*Real.exp |K|)^2 := by
    have ht : 0 < 1/((k:ℝ)+1) := by positivity
    have ht1 : 1/((k:ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith [Nat.cast_nonneg (α := ℝ) k]
    have hg := hX.heat_compact_uniform_slope hn hV hVc p
      (SobolevSpace.toLp μ Q v) hv.symm ht ht1
    have he : u k=heatSobolev μ Q (1/((k:ℝ)+1)) ht (SobolevSpace.toLp μ Q v) := by
      rw [hu k]
      simp only [heatH1,dite_eq_left ht]
      rfl
    rw [he]
    filter_upwards [hg,localGamma_self μ Q _,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q _)] with x hx hs h0
    rw [hs]
    exact pow_le_pow_left₀ h0 hx 2
  obtain ⟨FG,GG,hFG,hGG,hlim⟩ := hJ
  have hFGr k : SobolevSpace.toLp μ Q (FG k) =ᵐ[μ.restrict S] localGamma μ Q w (u k) := by
    simpa only [hu k] using hFG k
  have hGGr k : SobolevSpace.toLp μ Q (GG k) =ᵐ[μ.restrict S] localGamma μ Q (u k) (u k) := by
    simpa only [hu k] using hGG k
  let F k x := φ x*localHessianAction μ Q w (u k) (u k) (FG k) (FG k) (GG k) x
  let H k x := φ x*localGamma μ Q (u k) (u k) x
  have hF k : Integrable (F k) (μ.restrict S) :=
    ((localHessianAction_integrable μ Q w (u k) (u k) (FG k) (FG k) (GG k)).bdd_mul hφ
      (hD.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  have hH k : Integrable (H k) (μ.restrict S) :=
    ((localGamma_memL1 μ Q (u k) (u k)).bdd_mul hφ
      (hD.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  have hI : Integrable (fun x => φ x*localGamma μ Q v v x) (μ.restrict S) :=
    ((localGamma_memL1 μ Q v v).bdd_mul hφ
      (hD.mono fun _ hx => by simpa only [Real.norm_eq_abs] using hx)).integrableOn
  let I := hI.toL1 (fun x => φ x*localGamma μ Q v v x)
  have hIr : I =ᵐ[μ.restrict S] fun x => φ x*localGamma μ Q v v x := hI.coeFn_toL1
  have hHl : Tendsto (fun k => ∫ x in S, |H k x-I x| ∂μ) atTop (𝓝 0) := by
    have heq k : (∫ x in S, |H k x-I x| ∂μ)=
        ∫ x in S, |φ x*(localGamma μ Q (u k) (u k) x-localGamma μ Q v v x)| ∂μ := by
      apply integral_congr_ae
      filter_upwards [hIr] with x hx
      simp only [H,hx,mul_sub]
    simpa only [heq] using weighted_gram_L1_tendsto μ Q (Ω := S) u v hconv φ hφ D hD
  let c x := (σ.rnDeriv μ x).toReal-2*SobolevSpace.toLp μ Q dw x+(n:ℝ)
  have hc : Integrable c (μ.restrict S) :=
    ((Measure.integrableOn_toReal_rnDeriv (μ := σ) (ν := μ) (measure_ne_top σ S)).sub
      (((Lp.memLp (SobolevSpace.toLp μ Q dw)).restrict S).integrable (by norm_num) |>.const_mul 2)).add
        (integrable_const (n:ℝ))
  have hb (k : ℕ) : ∀ᵐ x ∂μ.restrict S, (F k x-H k x)^2 ≤ ((D:ℝ)*((Lv:ℝ)*Real.exp |K|)^2)^2*c x := by
    obtain ⟨A',B',hA',hB',hc0,hbound⟩ := hX.bounded_regular_shifted_hessian_curved hn hK w dw G hw W L A B hW hwr hA hB hG
      p hr σ hσ (u k) (du k) (hdu k) (U k) (M k) Av (hU k) (hur k) (huA k)
    have hsame := localHessianAction_congr_of_grams μ Q w (u k) (u k) (u k) (u k)
      (FG k) A' (FG k) A' (GG k) B' EventuallyEq.rfl EventuallyEq.rfl
      (hFGr k) hA' (hFGr k) hA' (hGGr k) hB'
    filter_upwards [hbound,hc0,hsame,ae_restrict_of_ae (hgu k),ae_restrict_of_ae hD,
      ae_restrict_of_ae (localGamma_self μ Q (u k))] with x hx hc0 he hg hφx hself
    rw [← he] at hx
    have h0 : 0 ≤ localGamma μ Q (u k) (u k) x := by rw [hself]; positivity
    have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hg 2) hc0
    have hφsq : (φ x)^2 ≤ (D:ℝ)^2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (φ x)) hφx 2
    change (φ x*localHessianAction μ Q w (u k) (u k) (FG k) (FG k) (GG k) x-
      φ x*localGamma μ Q (u k) (u k) x)^2 ≤ _
    rw [← mul_sub,mul_pow]
    calc
      _ ≤ (φ x)^2*(c x*(((Lv:ℝ)*Real.exp |K|)^2)^2) := mul_le_mul_of_nonneg_left (hx.trans hsq) (sq_nonneg _)
      _ ≤ (D:ℝ)^2*(c x*(((Lv:ℝ)*Real.exp |K|)^2)^2) := mul_le_mul_of_nonneg_right hφsq (mul_nonneg hc0 (sq_nonneg _))
      _ = _ := by ring
  have hfinal := L1_difference_density_young_bound (μ.restrict S) F H hF hH J I
    (by simpa only [F,hu] using hlim) hHl c hc ((D:ℝ)*((Lv:ℝ)*Real.exp |K|)^2) a hb
  have heq : (∫ x in S, |J x-I x| ∂μ) = ∫ x in S, |J x-φ x*localGamma μ Q v v x| ∂μ := by
    apply integral_congr_ae
    filter_upwards [hIr] with x hx
    rw [hx]
  simpa only [heq,measureReal_restrict_apply_univ] using hfinal

end RegularPointCoordinates

end

end OAI
