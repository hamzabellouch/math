import Mathlib
import OAI.Analysis.RCDHeat.GeometricSlopeOptimization

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: DimensionalCompactWeightedGradient, DimensionalWeightedGradient, CoefficientLimit, HeatGeneratorComposition, DimensionalHeatBochner. -/



namespace RegularPointCoordinates

section

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_compact_weighted_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    {φ : X → ℝ} {L : ℝ≥0} (hφ : LipschitzWith L φ) (hs : HasCompactSupport φ)
    (p : X) (f G w : Lp ℝ 2 (hausdorff n X))
    (hf : φ =ᵐ[hausdorff n X] f) (hG : IsSlopeMajorant (hausdorff n X) φ G)
    (N : ℝ) (hN : (n:ℝ) ≤ N)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht f) x)^2 ∂hausdorff n X) +
      heatDimensionCoefficient K N t * (∫ x, w x *
        (heatGeneratorAt (hausdorff n X) hX.quadratic t f x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*(G x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨R,hR⟩ := hs.isCompact.isBounded.subset_closedBall p
  have hsupp (x : X) (hx : R < dist p x) : φ x = 0 := by
    by_contra hh
    have h := hR (subset_tsupport φ hh)
    simp only [mem_closedBall,dist_comm] at h
    linarith
  let hm := localSlope_sq_compact_memLp μ hφ p R hsupp
  let H := hm.toLp (fun x => (localSlope φ x).toReal^2)
  have hH : ⇑H =ᵐ[μ] fun x => (localSlope φ x).toReal^2 := hm.coeFn_toLp
  have hHi : Integrable H μ :=
    (localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq.congr hH.symm
  obtain ⟨V,hV,heV,hgrad⟩ := hX.heat_lipschitz_gradient_compact K n hn hφ p R hsupp f H hf hH.symm ht.le
  have hdim := hX.dimensional_local_gradient K n hn hφ p R hsupp f H hf hH.symm N hN ht V hV.continuous heV
  have hPH := heatAt_integrable μ hX.quadratic t H hHi
  have hVsq : Integrable (fun x => (localSlope V x).toReal^2) μ := by
    apply (hPH.const_mul (Real.exp (-2*K*t))).mono'
      ((localSlope_measurable hV.continuous).ennreal_toReal.pow_const 2).aestronglyMeasurable
    filter_upwards [hgrad] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ((localSlope V x).toReal))] using hx
  have hVm : MemLp (fun x => (localSlope V x).toReal) 2 μ :=
    (memLp_two_iff_integrable_sq ((localSlope_measurable hV.continuous).ennreal_toReal.aestronglyMeasurable)).mpr hVsq
  let S := SobolevSpace.minimalSlope μ hX.quadratic (heatSobolev μ hX.quadratic t ht f)
  have hSle := SobolevSpace.minimalSlope_le_localSlope μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f) hV heV hVm
  have hS0 := (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hX.quadratic
    (heatSobolev μ hX.quadratic t ht f))
  have hw0 := (Lp.coeFn_nonneg _).mpr hw
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hPw0 := (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hX.quadratic t w hw)
  have hpair : (∫ x, w x*heatAt μ hX.quadratic t H x ∂μ) =
      ∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ := by
    have he := heatAt_inner μ hX.quadratic t w H
    simp only [L2.inner_def,Real.inner_apply] at he
    rw [← he]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    rw [hx]
  let d := heatDimensionCoefficient K N t
  let Z := heatGeneratorAt μ hX.quadratic t f
  have hiS := (Lp.memLp S).integrable_sq.bdd_mul (Lp.aestronglyMeasurable w) hwb
  have hiZ := (Lp.memLp Z).integrable_sq.bdd_mul (Lp.aestronglyMeasurable w) hwb
  calc
    (∫ x, w x*(S x)^2 ∂μ)+d*(∫ x, w x*(Z x)^2 ∂μ) =
        ∫ x, w x*(S x)^2+d*(w x*(Z x)^2) ∂μ := by
      rw [integral_add hiS (hiZ.const_mul d), integral_const_mul]
    _ ≤ ∫ x, w x*(Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x) ∂μ := by
      apply integral_mono_ae (hiS.add (hiZ.const_mul d))
        ((hPH.const_mul _).bdd_mul (Lp.aestronglyMeasurable w) hwb)
      filter_upwards [hw0,hS0,hSle,hdim] with x hw hs hsle hg
      have hsq := pow_le_pow_left₀ hs hsle 2
      have hsum : (S x)^2+d*(Z x)^2 ≤ Real.exp (-2*K*t)*heatAt μ hX.quadratic t H x := by
        exact (add_le_add hsq le_rfl).trans hg
      have hh := mul_le_mul_of_nonneg_left hsum hw
      dsimp only [Pi.add_apply]
      nlinarith only [hh]
    _ = Real.exp (-2*K*t)*(∫ x, heatAt μ hX.quadratic t w x*(localSlope φ x).toReal^2 ∂μ) := by
      simp_rw [mul_left_comm (w _) (Real.exp (-2*K*t))]
      rw [integral_const_mul,hpair]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      apply integral_mono_ae
        (((localSlope_toReal_memLp μ hφ (slopeEnergy_lt_top_of_lipschitz_hasCompactSupport μ hφ hs).ne).integrable_sq).bdd_mul
          (Lp.aestronglyMeasurable _) hPwb)
        ((Lp.memLp G).integrable_sq.bdd_mul (Lp.aestronglyMeasurable _) hPwb)
      filter_upwards [hPw0,hG] with x hw hG
      apply mul_le_mul_of_nonneg_left _ hw
      apply pow_le_pow_left₀ ENNReal.toReal_nonneg _ 2
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hG.2
      simpa only [ENNReal.toReal_ofReal hG.1] using hh


 
theorem NoncollapsedRCD.dimensional_weighted_gradient
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) (f : SobolevSpace (hausdorff n X) hX.quadratic)
    (w : Lp ℝ 2 (hausdorff n X)) (N : ℝ) (hN : (n:ℝ) ≤ N) (hw : 0 ≤ w) (C : ℝ≥0)
    (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    ∀ {t : ℝ} (ht : 0 < t),
      (∫ x, w x*(SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
        (heatSobolev (hausdorff n X) hX.quadratic t ht
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic f)) x)^2 ∂hausdorff n X) +
      heatDimensionCoefficient K N t * (∫ x, w x *
        (heatGeneratorAt (hausdorff n X) hX.quadratic t
          (SobolevSpace.toLp (hausdorff n X) hX.quadratic f) x)^2 ∂hausdorff n X) ≤
      Real.exp (-2*K*t)*(∫ x, heatAt (hausdorff n X) hX.quadratic t w x*
        (SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic f x)^2 ∂hausdorff n X) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  intro t ht
  obtain ⟨us,gs,Gs,hl,hs,ha,hm,hu,hG⟩ :=
    (SobolevSpace.minimalSlope_isRelaxed μ hX.quadratic f).compact_recovery μ p
  have hab (i : ℕ) := hX.dimensional_compact_weighted_gradient K n hn
    (hl i).choose_spec (hs i) p (us i) (Gs i) w (ha i).symm (hm i) N hN hw C hwC ht
  have hsf : Tendsto (fun i => heatSobolev μ hX.quadratic t ht (us i)) atTop
      (𝓝 (heatSobolev μ hX.quadratic t ht (SobolevSpace.toLp μ hX.quadratic f))) :=
    ((heatSobolevMap μ hX.quadratic t ht).continuous.tendsto _).comp hu
  have hsl := ((SobolevSpace.minimalSlope_lipschitz μ hX.quadratic).continuous.tendsto _).comp hsf
  have hwb : ∀ᵐ x ∂μ, ‖w x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hwC
  have hPwb : ∀ᵐ x ∂μ, ‖heatAt μ hX.quadratic t w x‖ ≤ (C:ℝ) := by
    simpa only [Real.norm_eq_abs] using heatAt_abs_le_const μ hX.quadratic t C w hwC
  have hleft := ((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w) hwb).tendsto _).comp hsl
  have hright := (((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable
    (heatAt μ hX.quadratic t w)) hPwb).tendsto _).comp hG).const_mul (Real.exp (-2*K*t))
  have hgen := ((heatGeneratorAt μ hX.quadratic t).continuous.tendsto _).comp hu
  have hextra := (((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable w) hwb).tendsto _).comp hgen).const_mul (heatDimensionCoefficient K N t)
  exact le_of_tendsto_of_tendsto (hleft.add hextra) hright (Eventually.of_forall hab)

end

 
section

 

open Set Filter MeasureTheory
open scoped Topology

theorem heatDimensionCoefficient_div_tendsto (K : ℝ) {N : ℝ} (hN : 0 < N) :
    Tendsto (fun r => heatDimensionCoefficient K N r / r) (𝓝[>] (0:ℝ)) (𝓝 (2/N)) := by
  have hc : Continuous (fun s : ℝ => Real.exp (-2*K*s)) := by fun_prop
  have hJ : HasDerivAt (fun r => heatKernelIntegral K 1 1 r) 1 0 := by
    simp_rw [heatKernelIntegral_one]
    simpa only [mul_zero,Real.exp_zero] using (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt)
  have hJ0 : heatKernelIntegral K 1 1 0 = 0 := by rw [heatKernelIntegral_one]; simp
  have hlim : Tendsto (fun r => heatKernelIntegral K 1 1 r/r) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    convert! hJ.tendsto_slope_zero_right using 1
    ext r
    simp only [zero_add,hJ0,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hexp : Tendsto (fun r : ℝ => Real.exp (-2*K*r)) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    convert! hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1; simp
  have h := (hexp.const_mul 2).div (hlim.const_mul N) (by simpa using hN.ne')
  have he : (fun r => heatDimensionCoefficient K N r/r) =ᶠ[𝓝[>] (0:ℝ)]
      (fun r => 2*Real.exp (-2*K*r)/(N*(heatKernelIntegral K 1 1 r/r))) := by
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    unfold heatDimensionCoefficient
    field_simp [hr.ne',hN.ne',(heatKernelIntegral_pos K hr).ne']
  apply Tendsto.congr' he.symm
  convert! h using 1; simp

end

 
section

 

open Set Filter MeasureTheory
open scoped Topology
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heatGeneratorAt_comp_heat {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (f : Lp ℝ 2 μ) :
    heatGeneratorAt μ hQ r (heatAt μ hQ t f) = heatGeneratorAt μ hQ (r+t) f := by
  have h1 := heatAt_hasDerivAt μ hQ r hr (heatAt μ hQ t f)
  have h2 := (heatAt_hasDerivAt μ hQ (r+t) (add_pos_of_pos_of_nonneg hr ht) f).scomp r
    ((hasDerivAt_id r).add_const t)
  simp only [one_smul] at h2
  have h3 : HasDerivAt (fun u => heatAt μ hQ u (heatAt μ hQ t f))
      (-heatGeneratorAt μ hQ (r+t) f) r := by
    apply h2.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with u hu
    change heatAt μ hQ u (heatAt μ hQ t f) = heatAt μ hQ (u+t) f
    rw [heatAt_add μ hQ u t hu.le ht,mul_apply_eq_comp]
  exact neg_injective (h1.unique h3)

theorem heatGeneratorAt_comp_heat_tendsto {t : ℝ} (ht : 0 < t) (f : Lp ℝ 2 μ) :
    Tendsto (fun r => heatGeneratorAt μ hQ r (heatAt μ hQ t f)) (𝓝[>] (0:ℝ))
      (𝓝 (heatGeneratorAt μ hQ t f)) := by
  have hu : Tendsto (fun r : ℝ => r+t) (𝓝[>] (0:ℝ)) (𝓝 t) := by
    simpa only [id_eq,zero_add] using ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun r : ℝ => r) (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ))).add_const t)
  have h := (heatGeneratorAt_continuousAt μ hQ f t ht).tendsto.comp hu
  apply Tendsto.congr' _ (by simpa only [zero_add] using h)
  filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
  exact (heatGeneratorAt_comp_heat μ hQ hr ht.le f).symm

end

 

 

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped Topology NNReal ENNReal
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem NoncollapsedRCD.dimensional_heat_weak_bochner
    (K : ℝ) (n : ℕ) (hn : 2 ≤ n) (hX : NoncollapsedRCD K n X)
    (p : X) (f w : Lp ℝ 2 (hausdorff n X))
    (N : ℝ) (hN : (n:ℝ) ≤ N)
    (hw : 0 ≤ w) (C : ℝ≥0) (hwC : ∀ᵐ x ∂hausdorff n X, |w x| ≤ C)
    (t s : ℝ) (ht : 0 < t) (hs : 0 < s) :
    letI : ProperSpace X := hX.proper K n hn
    letI : SeparableSpace X := hX.separable
    letI : IsLocallyFiniteMeasure (hausdorff n X) := locallyFinite_of_finiteOnBounded _ hX.finiteOnBounded
    let μ := hausdorff n X
    let F := heatSobolev μ hX.quadratic t ht f
    let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
      (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
    ∀ (H : Lp ℝ 2 μ), (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H →
      K*(∫ x, heatAt μ hX.quadratic s w x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)
        +weightedGamma μ hX.quadratic (heatAt μ hX.quadratic s w) F D
        +(1/N)*(∫ x, heatAt μ hX.quadratic s w x * (SobolevSpace.toLp μ hX.quadratic D x)^2 ∂μ) ≤
      (1/2:ℝ)*(∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*H x ∂μ) := by
  let : ProperSpace X := hX.proper K n hn
  let : SeparableSpace X := hX.separable
  let μ := hausdorff n X
  let : IsLocallyFiniteMeasure μ := locallyFinite_of_finiteOnBounded μ hX.finiteOnBounded
  let F := heatSobolev μ hX.quadratic t ht f
  let D := heatSobolevMap μ hX.quadratic (t/2) (half_pos ht)
    (-heatGeneratorAt μ hX.quadratic (t-t/2) f)
  dsimp only
  intro H hH
  change (fun x => (SobolevSpace.minimalSlope μ hX.quadratic F x)^2) =ᵐ[μ] H at hH
  let W := heatAt μ hX.quadratic s w
  have hW : 0 ≤ W := heatAt_nonneg μ hX.quadratic s w hw
  have hWC : ∀ᵐ x ∂μ, |W x| ≤ C := heatAt_abs_le_const μ hX.quadratic s C w hwC
  have hWb : ∀ᵐ x ∂μ, ‖W x‖ ≤ (C:ℝ) := by simpa only [Real.norm_eq_abs] using hWC
  let q (r : ℝ) := ∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic
    (heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r)) x)^2 ∂μ
  let b (r : ℝ) := Real.exp (-2*K*r)*inner ℝ (heatAt μ hX.quadratic (s+r) w) H
  let z (r : ℝ) := ∫ x, W x*(heatGeneratorAt μ hX.quadratic r
      (SobolevSpace.toLp μ hX.quadratic F) x)^2 ∂μ
  let Z := ∫ x, W x*(SobolevSpace.toLp μ hX.quadratic D x)^2 ∂μ
  have hN0 : 0 < N := by
    have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hD : SobolevSpace.toLp μ hX.quadratic D = -heatGeneratorAt μ hX.quadratic t f :=
    heatTail_deriv_toLp μ hX.quadratic (t/2) (half_pos ht) f t (by linarith)
  have hZe : (∫ x, W x*(heatGeneratorAt μ hX.quadratic t f x)^2 ∂μ) = Z := by
    dsimp only [Z]
    rw [hD]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_neg (heatGeneratorAt μ hX.quadratic t f)] with x hx
    simp only [hx,Pi.neg_apply,neg_sq]
  have hz : Tendsto z (𝓝[>] (0:ℝ)) (𝓝 Z) := by
    rw [←hZe]
    exact ((lp_weighted_square_continuous μ (Lp.aestronglyMeasurable W) hWb).tendsto _).comp
      (heatGeneratorAt_comp_heat_tendsto μ hX.quadratic ht f)
  have hF : heatTail μ hX.quadratic (t/2) (half_pos ht) f t = F :=
    heatTail_eq μ hX.quadratic (t/2) (half_pos ht) f t (by linarith)
  have hq : HasDerivAt q (2*weightedGamma μ hX.quadratic W F D) 0 := by
    have hd0 : HasDerivAt (heatTail μ hX.quadratic (t/2) (half_pos ht) f) D (t+0) := by
      simpa only [add_zero] using heatTail_hasDerivAt μ hX.quadratic (t/2) (half_pos ht) f t (by linarith)
    have hd := hd0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add t)
    simp only [one_smul] at hd
    have hh := weighted_gradient_hasDerivAt μ hX.quadratic (Lp.aestronglyMeasurable W) hWb hd
    simpa only [Function.comp_apply,add_zero,hF] using hh
  have hb : HasDerivAt b
      ((-2*K)*inner ℝ W H+inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H) 0 := by
    have hd0 : HasDerivAt (fun r => heatAt μ hX.quadratic r w)
        (-heatGeneratorAt μ hX.quadratic s w) (s+0) := by
      simpa only [add_zero] using heatAt_hasDerivAt μ hX.quadratic s hs w
    have hd := hd0.scomp 0 ((hasDerivAt_id (0:ℝ)).const_add s)
    simp only [one_smul] at hd
    have he := ((hasDerivAt_id (0:ℝ)).const_mul (-2*K)).exp
    convert! he.mul (hd.inner ℝ (hasDerivAt_const (0:ℝ) H)) using 1
    simp only [W,Function.comp_apply,id_eq,mul_zero,Real.exp_zero,one_mul,mul_one,add_zero,inner_zero_right,zero_add]
  have hq0 : q 0 = inner ℝ W H := by
    dsimp only [q]
    rw [add_zero,hF,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  have hb0 : b 0 = inner ℝ W H := by simp only [b,mul_zero,Real.exp_zero,one_mul,add_zero]; rfl
  have hab (r : ℝ) (hr : 0 < r) : q r + heatDimensionCoefficient K N r * z r ≤ b r := by
    have hh := hX.dimensional_weighted_gradient K n hn p F W N hN hW C hWC hr
    have heF : heatSobolev μ hX.quadratic r hr (SobolevSpace.toLp μ hX.quadratic F) =
        heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r) := by
      apply Subtype.ext
      change SobolevSpace.toLp μ hX.quadratic (heatSobolev μ hX.quadratic r hr (SobolevSpace.toLp μ hX.quadratic F)) =
        SobolevSpace.toLp μ hX.quadratic (heatTail μ hX.quadratic (t/2) (half_pos ht) f (t+r))
      rw [heatSobolev_toLp,heatTail_toLp μ hX.quadratic (t/2) (half_pos ht) f (t+r) (by linarith)]
      dsimp only [F]
      rw [heatSobolev_toLp,←mul_apply_eq_comp,←heatAt_add μ hX.quadratic r t hr.le ht.le,add_comm r t]
    have heW : heatAt μ hX.quadratic r W = heatAt μ hX.quadratic (s+r) w := by
      dsimp only [W]
      rw [←mul_apply_eq_comp,←heatAt_add μ hX.quadratic r s hr.le hs.le,add_comm r s]
    rw [heF,heW] at hh
    change q r + heatDimensionCoefficient K N r * z r ≤ Real.exp (-2*K*r)*(∫ x, heatAt μ hX.quadratic (s+r) w x*
      (SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) at hh
    convert hh using 1
    dsimp only [b]
    congr 1
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  have hder : 2*weightedGamma μ hX.quadratic W F D + (2/N)*Z ≤
      (-2*K)*inner ℝ W H+inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H := by
    apply le_of_tendsto_of_tendsto (hq.tendsto_slope_zero_right.add
      ((heatDimensionCoefficient_div_tendsto K hN0).mul hz)) hb.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [zero_add,smul_eq_mul,hq0,hb0]
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right (hab r hr) (inner ℝ W H)) (inv_nonneg.mpr hr.le)
    simp only [div_eq_mul_inv]
    nlinarith only [hh]
  have he : (∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ) = inner ℝ W H := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hH] with x hx
    simp only [Real.inner_apply,hx]
  change K*(∫ x, W x*(SobolevSpace.minimalSlope μ hX.quadratic F x)^2 ∂μ)+
    weightedGamma μ hX.quadratic W F D + (1/N)*Z ≤ _
  rw [he]
  have he' : (∫ x, (-heatGeneratorAt μ hX.quadratic s w) x*H x ∂μ) =
      inner ℝ (-heatGeneratorAt μ hX.quadratic s w) H := by simp only [L2.inner_def,Real.inner_apply]
  rw [he']
  simp only [div_eq_mul_inv] at hder ⊢
  nlinarith only [hder]


end RegularPointCoordinates

end OAI
