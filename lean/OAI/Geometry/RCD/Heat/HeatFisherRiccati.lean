import OAI.Geometry.RCD.Heat.HeatFisherDimensional
import OAI.Geometry.RCD.Heat.FisherSourceMoment
import OAI.Geometry.RCD.Sobolev.ShiftedSobolevProduct

namespace OAI

/-! # The dimensional scalar inequality along the actual heat interpolation

The mass and source moment are constant along the forward/backward heat
pairing. No probability normalization or nonzero-mass assumption is needed.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2≤n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p

theorem regularizedFisherInterpolation_riccati (hK : K≤0)
    (f w : Lp ℝ 2 (hausdorff n X)) (hf0 : 0≤f) (hw0 : 0≤w) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x|≤A) (hw : ∀ᵐ x ∂hausdorff n X, |w x|≤B)
    (hwi : Integrable w (hausdorff n X))
    {T t ε : ℝ} (ht : 0<t) (htT : t<T) (hε : 0<ε) :
    let μ := hausdorff n X
    let Q := hX.quadratic
    let M := ε*(∫ x, w x ∂μ)+inner ℝ w (heatAt μ Q T f)
    let D := inner ℝ w (-heatGeneratorAt μ Q T f)
    let I := regularizedFisherInterpolation μ Q f w ε T
    ∃ rate : ℝ, HasDerivAt I rate t ∧
      (2/(n:ℝ))*(D-I t)^2+2*K*M*I t≤M*rate := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  have hs : 0<T-t := sub_pos.mpr htT
  let u := heatSobolev μ Q (T-t) hs f
  let W := heatSobolev μ Q t ht w
  let d := heatSobolevMap μ Q t ht (-heatGeneratorAt μ Q (T-t) f)
  have hdval : SobolevSpace.toLp μ Q d = -heatGeneratorAt μ Q T f := by
    exact heatTail_deriv_toLp μ Q t ht f T htT
  have hu : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q u x := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q (T-t) f hf0)] with x hx
    simpa only [Pi.zero_apply,u,heatSobolev_toLp] using hx
  have huA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x|≤A := by
    simpa only [u,heatSobolev_toLp] using heatAt_abs_le_const μ Q (T-t) A f hf
  have hWB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q W x|≤B := by
    simpa only [W,heatSobolev_toLp] using heatAt_abs_le_const μ Q t B w hw
  have hW0 : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q W x := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ Q t w hw0)] with x hx
    simpa only [Pi.zero_apply,W,heatSobolev_toLp] using hx
  let R := ε • W+SobolevSpace.product μ Q u W A B
  have hRr := SobolevSpace.shifted_product_coe μ Q u W ε A B huA hWB
  change SobolevSpace.toLp μ Q R =ᵐ[μ] _ at hRr
  have hR0 : ∀ᵐ x ∂μ, 0≤SobolevSpace.toLp μ Q R x := by
    filter_upwards [hRr,hu,hW0] with x hr hx hy
    rw [hr]
    positivity
  let C : ℝ≥0 := (⟨ε,hε.le⟩+A)*B
  have hRC : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q R x|≤C := by
    filter_upwards [hRr,huA,hWB] with x hr hx hy
    rw [hr,abs_mul]
    exact mul_le_mul ((abs_add_le _ _).trans (add_le_add
      (by rw [abs_of_pos hε]) hx)) hy (abs_nonneg _) (add_nonneg hε.le A.coe_nonneg)
  obtain ⟨ℓ,S,H,_C,_L,_hS,_hH,_hℓ,_hL,_hb,hsource⟩ :=
    hX.heat_logarithm_sobolev_data hn p f hf0 A hf hs hε
  have hSactual : SobolevSpace.toLp μ Q S =ᵐ[μ]
      regularizedHeatLogSource μ Q f ε (T-t) hs := by
    have hv := hX.boundedHeat_represents hn p f ⟨A,hf⟩ (T-t) hs
    filter_upwards [hsource,hv] with x hx hy
    change heatAt μ Q (T-t) f x = _ at hy
    change SobolevSpace.toLp μ Q S x = _ at hx
    change SobolevSpace.toLp μ Q S x =
      (-heatGeneratorAt μ Q (T-t) f) x/(ε+heatAt μ Q (T-t) f x)-
        localGamma μ Q u u x/(ε+heatAt μ Q (T-t) f x)^2
    rw [hy]
    exact hx
  have hSr : SobolevSpace.toLp μ Q S =ᵐ[μ] fun x =>
      (-heatGeneratorAt μ Q (T-t) f) x/(ε+SobolevSpace.toLp μ Q u x)-
        localGamma μ Q u u x/(ε+SobolevSpace.toLp μ Q u x)^2 := by
    exact hSactual
  have hmass : ε*(∫ x, SobolevSpace.toLp μ Q W x ∂μ)+
      inner ℝ (SobolevSpace.toLp μ Q u) (SobolevSpace.toLp μ Q W) =
      ε*(∫ x, w x ∂μ)+inner ℝ w (heatAt μ Q T f) := by
    simp only [u,W,heatSobolev_toLp]
    rw [hX.conservative K n hn p w hw0 hwi t ht.le,real_inner_comm,
      heatAt_inner μ Q t,←mul_apply_eq_comp,←heatAt_add μ Q t (T-t) ht.le hs.le]
    rw [show t+(T-t)=T by ring]
  have hD : inner ℝ (SobolevSpace.toLp μ Q W) (-heatGeneratorAt μ Q (T-t) f)=
      inner ℝ w (-heatGeneratorAt μ Q T f) := by
    simp only [W,heatSobolev_toLp]
    rw [heatAt_inner]
    exact congrArg (inner ℝ w) hdval
  have hcs := fisher_source_moment_square μ (SobolevSpace.toLp μ Q u)
    (SobolevSpace.toLp μ Q W) (-heatGeneratorAt μ Q (T-t) f)
    (SobolevSpace.toLp μ Q S) (SobolevSpace.toLp μ Q R) (localGamma μ Q u u)
    hε hu (heatAt_integrable μ Q t w hwi) hR0 C hRC hRr hSr
  have hI : (∫ x, SobolevSpace.toLp μ Q W x*localGamma μ Q u u x /
      (ε+SobolevSpace.toLp μ Q u x) ∂μ)=regularizedFisherInterpolation μ Q f w ε T t := by
    simp only [u,W,heatSobolev_toLp,regularizedFisherInterpolation,dite_eq_left hs]
  have hsq : (∫ x, SobolevSpace.toLp μ Q R x*(SobolevSpace.toLp μ Q S x)^2 ∂μ)=
      ∫ x, heatAt μ Q t w x*(ε+heatAt μ Q (T-t) f x)*
        (regularizedHeatLogSource μ Q f ε (T-t) hs x)^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [hRr,hSactual] with x hr hx
    simp only [u,W,heatSobolev_toLp] at hr
    rw [hr,hx]
    ring
  rw [hI,hmass,hD,hsq] at hcs
  have hm := shifted_product_mass μ (SobolevSpace.toLp μ Q u) (SobolevSpace.toLp μ Q W)
    (SobolevSpace.toLp μ Q R) ε (heatAt_integrable μ Q t w hwi) hRr
  have hM0 : 0≤ε*(∫ x, w x ∂μ)+inner ℝ w (heatAt μ Q T f) := by
    rw [←hmass,←hm.2]
    exact integral_nonneg_of_ae hR0
  obtain ⟨rate,hrate,hbound⟩ :=
    hX.regularizedFisherInterpolation_dimensional hn p hK f w hf0 hw0 A B hf hw ht htT hε
  refine ⟨rate,hrate,?_⟩
  have hc := mul_le_mul_of_nonneg_left hcs (by positivity : 0≤2/(n:ℝ))
  have hd := mul_le_mul_of_nonneg_left hbound hM0
  nlinarith only [hc,hd]

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
