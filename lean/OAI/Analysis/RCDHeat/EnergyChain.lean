import Mathlib
import OAI.Analysis.RCDHeat.SlopeLevels

namespace OAI

/-! Cheeger energy, curvature-dimension transport and heat-flow estimates: EnergyChain, IntegralPotential, HeatPotential, HeatDissipation, RegularizedLog. -/



open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal NNReal
namespace RegularPointCoordinates
universe u
open Metric
open Metric
section EnergyChain
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

noncomputable def SobolevSpace.chainGradient (f : SobolevSpace μ hQ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) : Lp ℝ 2 μ :=
  lpMultiplier μ (boundedMultiplier μ (fun x => ψ (SobolevSpace.toLp μ hQ f x))
    ((hψ.measurable.comp (Lp.stronglyMeasurable (SobolevSpace.toLp μ hQ f)).measurable)) B
    (fun _ => hB _)) (SobolevSpace.minimalSlope μ hQ f)

 theorem SobolevSpace.chainGradient_coe (f : SobolevSpace μ hQ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    ∀ᵐ x ∂μ, SobolevSpace.chainGradient μ hQ f hψ B hB x =
      ψ (SobolevSpace.toLp μ hQ f x) * SobolevSpace.minimalSlope μ hQ f x := by
  unfold SobolevSpace.chainGradient
  filter_upwards [lpMultiplier_coe μ _ (SobolevSpace.minimalSlope μ hQ f),
    boundedMultiplier_coe μ (fun x => ψ (SobolevSpace.toLp μ hQ f x)) _ B (fun _ => hB _)]
    with x hm hb
  rw [hm, hb]

omit [BorelSpace X] in
 theorem SobolevSpace.comp_add (f : SobolevSpace μ hQ)
    {φ θ : ℝ → ℝ} {C D : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hθ : LipschitzWith D θ) (hθ0 : θ 0 = 0) :
    SobolevSpace.comp μ hQ (hφ.add hθ) (by simp only [hφ0, hθ0, add_zero]) f =
      SobolevSpace.comp μ hQ hφ hφ0 f + SobolevSpace.comp μ hQ hθ hθ0 f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [SobolevSpace.comp_coe μ hQ (hφ.add hθ) (by simp [hφ0, hθ0]) f,
    SobolevSpace.comp_coe μ hQ hφ hφ0 f, SobolevSpace.comp_coe μ hQ hθ hθ0 f,
    Lp.coeFn_add (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f))
      (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hθ hθ0 f))] with x ha hp ht hs
  change SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ (hφ.add hθ) (by simp [hφ0, hθ0]) f) x = _
  rw [ha]
  change _ = (SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) +
    SobolevSpace.toLp μ hQ (SobolevSpace.comp μ hQ hθ hθ0 f)) x
  rw [hs, Pi.add_apply, hp, ht]
  rfl

omit [BorelSpace X] in
 theorem SobolevSpace.comp_id (f : SobolevSpace μ hQ) :
    SobolevSpace.comp μ hQ LipschitzWith.id rfl f = f := by
  apply Subtype.ext
  exact Lp.ext (SobolevSpace.comp_coe μ hQ LipschitzWith.id rfl f)

 theorem SobolevSpace.chainGradient_const_add (f : SobolevSpace μ hQ)
    {ψ : ℝ → ℝ} (hψ : Continuous ψ) (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B)
    (hD : ∀ a, |1+ψ a| ≤ (1+B : ℝ≥0)) :
    SobolevSpace.chainGradient μ hQ f (hψ.const_add 1) (1+B) hD =
      SobolevSpace.minimalSlope μ hQ f + SobolevSpace.chainGradient μ hQ f hψ B hB := by
  apply Lp.ext
  filter_upwards [SobolevSpace.chainGradient_coe μ hQ f (hψ.const_add 1) (1+B) hD,
    SobolevSpace.chainGradient_coe μ hQ f hψ B hB,
    Lp.coeFn_add (SobolevSpace.minimalSlope μ hQ f) (SobolevSpace.chainGradient μ hQ f hψ B hB)]
    with x h1 h2 ha
  rw [h1, ha, Pi.add_apply, h2]
  ring

variable [ProperSpace X]

 theorem SobolevSpace.minimalSlope_comp_C1_eq_abs (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    SobolevSpace.minimalSlope μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) =
      |SobolevSpace.chainGradient μ hQ f hψ B hB| := by
  apply Lp.ext
  filter_upwards [SobolevSpace.minimalSlope_comp_C1 μ hQ f hφ hφ0 hψ hd B hB,
    SobolevSpace.chainGradient_coe μ hQ f hψ B hB,
    Lp.coeFn_abs (SobolevSpace.chainGradient μ hQ f hψ B hB),
    (Lp.coeFn_le _ _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ f), Lp.coeFn_zero ℝ 2 μ]
    with x hc hm ha hn hz
  rw [hz, Pi.zero_apply] at hn
  rw [hc, ha, hm, abs_mul, abs_of_nonneg hn]

 theorem SobolevSpace.chainGradient_norm_sq (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    ‖SobolevSpace.chainGradient μ hQ f hψ B hB‖^2 =
      2 * SobolevSpace.energy μ hQ (SobolevSpace.comp μ hQ hφ hφ0 f) := by
  rw [← SobolevSpace.minimalSlope_norm_sq, SobolevSpace.minimalSlope_comp_C1_eq_abs μ hQ f
    hφ hφ0 hψ hd B hB, norm_abs_eq_norm]

 

 theorem energyForm_comp_C1 (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    energyForm μ hQ f (SobolevSpace.comp μ hQ hφ hφ0 f) =
      inner ℝ (SobolevSpace.minimalSlope μ hQ f) (SobolevSpace.chainGradient μ hQ f hψ B hB) := by
  have hD (a : ℝ) : |1+ψ a| ≤ (1+B : ℝ≥0) := by
    simp only [NNReal.coe_add, NNReal.coe_one]
    calc
      |1+ψ a| ≤ |1|+|ψ a| := abs_add_le _ _
      _ ≤ 1+B := by rw [abs_one]; exact add_le_add_right (hB a) 1
  have he := SobolevSpace.chainGradient_norm_sq μ hQ f (LipschitzWith.id.add hφ)
    (by simp [hφ0]) (hψ.const_add 1) (fun a => (hasDerivAt_id a).add (hd a)) (1+B) hD
  rw [SobolevSpace.chainGradient_const_add μ hQ f hψ B hB hD,
    SobolevSpace.comp_add μ hQ f LipschitzWith.id rfl hφ hφ0, SobolevSpace.comp_id, norm_add_sq_real,
    SobolevSpace.minimalSlope_norm_sq,
    SobolevSpace.chainGradient_norm_sq μ hQ f hφ hφ0 hψ hd B hB] at he
  let g := SobolevSpace.comp μ hQ hφ hφ0 f
  have headd : 2 * SobolevSpace.energy μ hQ (f+g) =
      2 * SobolevSpace.energy μ hQ f + 2 * energyForm μ hQ f g + 2 * SobolevSpace.energy μ hQ g := by
    rw [← energyForm_self, energyForm_add_left, energyForm_comm μ hQ f (f+g),
      energyForm_add_left, energyForm_comm μ hQ g (f+g), energyForm_add_left,
      energyForm_self, energyForm_self, energyForm_comm μ hQ g f]
    ring
  change _ = 2 * SobolevSpace.energy μ hQ (f+g) at he
  rw [headd] at he
  linarith

 theorem energyForm_comp_C1_integral (f : SobolevSpace μ hQ)
    {φ ψ : ℝ → ℝ} {C : ℝ≥0} (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) :
    energyForm μ hQ f (SobolevSpace.comp μ hQ hφ hφ0 f) =
      ∫ x, ψ (SobolevSpace.toLp μ hQ f x) * SobolevSpace.minimalSlope μ hQ f x ^ 2 ∂μ := by
  rw [energyForm_comp_C1 μ hQ f hφ hφ0 hψ hd B hB, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [SobolevSpace.chainGradient_coe μ hQ f hψ B hB] with x hx
  rw [Real.inner_apply, hx]
  ring

end EnergyChain

section IntegralPotential

 
 theorem scalar_potential_remainder {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt F (φ a) a) (hφ : LipschitzWith C φ) (a b : ℝ) :
    |F b - F a - φ a * (b-a)| ≤ C * |b-a|^2 := by
  let R : ℝ → ℝ := fun x => F x - F a - φ a * (x-a)
  have hR (x : ℝ) : HasDerivAt R (φ x-φ a) x := by
    convert ((hd x).sub_const (F a)).sub (((hasDerivAt_id x).sub_const a).const_mul (φ a)) using 1 <;>
      first | rfl | simp
  have hb (x : ℝ) (hx : x ∈ Set.uIcc a b) : ‖φ x-φ a‖ ≤ C * |b-a| := by
    calc
      _ ≤ (C : ℝ) * dist x a := hφ.dist_le_mul x a
      _ ≤ (C : ℝ) * |b-a| := by
        apply mul_le_mul_of_nonneg_left _ C.coe_nonneg
        simpa only [Real.dist_eq, abs_sub_comm a] using Real.dist_left_le_of_mem_uIcc hx
  have hh := (convex_uIcc a b).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x _ => (hR x).hasDerivWithinAt) hb (left_mem_uIcc) (right_mem_uIcc)
  simpa only [R, sub_self, mul_zero, sub_zero, Real.norm_eq_abs, pow_two, mul_assoc] using hh

variable {X : Type u} [MeasurableSpace X] (μ : Measure X)

noncomputable def integralPotential (F : ℝ → ℝ) (f : Lp ℝ 2 μ) : ℝ := ∫ x, F (f x) ∂μ

 theorem integral_sq_Lp (f : Lp ℝ 2 μ) : ∫ x, (f x)^2 ∂μ = ‖f‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp only [Real.inner_apply, pow_two]

 theorem integralPotential_integrable {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ) :
    Integrable (fun x => F (f x)) μ := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  apply (((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul
    (C : ℝ)).mono' (hFc.comp_aestronglyMeasurable (Lp.stronglyMeasurable f).aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    simpa only [hF0, hφ0, sub_zero, zero_mul, Real.norm_eq_abs]
      using scalar_potential_remainder hd hφ 0 (f x)

 theorem integralPotential_remainder {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f g : Lp ℝ 2 μ) :
    |integralPotential μ F g - integralPotential μ F f - inner ℝ (hφ.compLp hφ0 f) (g-f)| ≤
      C * ‖g-f‖^2 := by
  have hfg := (Lp.memLp (hφ.compLp hφ0 f)).integrable_mul (Lp.memLp (g-f))
  have hf := integralPotential_integrable μ hd hF0 hφ hφ0 f
  have hg := integralPotential_integrable μ hd hF0 hφ hφ0 g
  have he : integralPotential μ F g - integralPotential μ F f - inner ℝ (hφ.compLp hφ0 f) (g-f) =
      ∫ x, F (g x) - F (f x) - (hφ.compLp hφ0 f x) * (g-f) x ∂μ := by
    unfold integralPotential
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    rw [← integral_sub hg hf]
    exact (integral_sub (hg.sub hf) hfg).symm
  rw [he]
  calc
    _ ≤ ∫ x, |F (g x)-F (f x)-(hφ.compLp hφ0 f x)*(g-f) x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (C : ℝ) * (g-f) x ^ 2 ∂μ := by
      apply integral_mono_ae ((hg.sub hf).sub hfg).abs
        (((Lp.memLp (g-f)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).const_mul
          (C : ℝ) |>.congr (Eventually.of_forall fun x => by dsimp only; rw [Real.norm_eq_abs, sq_abs]))
      filter_upwards [hφ.coeFn_compLp hφ0 f, Lp.coeFn_sub g f] with x hp hs
      dsimp only [Pi.sub_apply, Pi.mul_apply]
      rw [hp, hs, Pi.sub_apply]
      simpa only [sq_abs, Function.comp_apply] using scalar_potential_remainder hd hφ (f x) (g x)
    _ = _ := by rw [integral_const_mul, integral_sq_Lp]

 

 theorem integralPotential_hasFDerivAt {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hd : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ) :
    HasFDerivAt (integralPotential μ F) (innerSL ℝ (hφ.compLp hφ0 f)) f := by
  rw [hasFDerivAt_iff_tendsto]
  apply squeeze_zero (fun g => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
    (fun g => ?_) (show Tendsto (fun g : Lp ℝ 2 μ => (C : ℝ)*‖g-f‖) (𝓝 f) (𝓝 0) by
      have hc : Continuous (fun g : Lp ℝ 2 μ => (C : ℝ)*‖g-f‖) :=
        continuous_const.mul (continuous_id.sub continuous_const).norm
      simpa only [sub_self, norm_zero, mul_zero] using hc.tendsto f)
  have h := mul_le_mul_of_nonneg_left (integralPotential_remainder μ hd hF0 hφ hφ0 f g)
    (inv_nonneg.mpr (norm_nonneg (g-f)))
  have he : ‖g-f‖⁻¹ * ((C : ℝ)*‖g-f‖^2) = (C : ℝ)*‖g-f‖ := by
    by_cases hz : ‖g-f‖ = 0
    · simp [hz]
    · field_simp
  simpa only [Real.norm_eq_abs, innerSL_apply_apply, he] using h

end IntegralPotential

section HeatPotential
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 

 theorem heatAt_integralPotential_hasDerivAt {F φ ψ : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => integralPotential μ F (heatAt μ hQ s f))
      (-(∫ x, ψ (heatAt μ hQ t f x) *
        SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x ^ 2 ∂μ)) t := by
  have h := (integralPotential_hasFDerivAt μ hF hF0 hφ hφ0 (heatAt μ hQ t f)).comp_hasDerivAt t
    (heatAt_hasDerivAt μ hQ t ht f)
  simp only [innerSL_apply_apply, heatGeneratorAt_of_pos μ hQ t ht, inner_neg_right] at h
  have he := energyForm_comp_C1_integral μ hQ (heatSobolev μ hQ t ht f) hφ hφ0 hψ hd B hB
  rw [heatGenerator_form, heatSobolev_toLp] at he
  have hc : SobolevSpace.toLp μ hQ
      (SobolevSpace.comp μ hQ hφ hφ0 (heatSobolev μ hQ t ht f)) =
      hφ.compLp hφ0 (heatAt μ hQ t f) := by
    change hφ.compLp hφ0 (SobolevSpace.toLp μ hQ (heatSobolev μ hQ t ht f)) = _
    rw [heatSobolev_toLp]
  rw [hc, real_inner_comm] at he
  rw [he] at h
  convert h using 1
  rfl

end HeatPotential

section HeatDissipation
variable {X : Type u} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

 theorem heatGeneratorAt_continuousAt (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun s => heatGeneratorAt μ hQ s f) t := by
  have hc : Continuous (fun s => heatAt μ hQ (s-t/2) (heatGenerator μ hQ (t/2) (half_pos ht) f)) :=
    (heatAt_continuous μ hQ _).comp (continuous_id.sub continuous_const)
  apply hc.continuousAt.congr
  filter_upwards [Ioi_mem_nhds (show t/2 < t by linarith)] with s hs
  rw [heatGeneratorAt_of_pos μ hQ s ((half_pos ht).trans hs)]
  have he := heatGenerator_add μ hQ (s-t/2) (t/2) (sub_nonneg.mpr hs.le) (half_pos ht)
  simp only [sub_add_cancel] at he
  rw [he, mul_apply_eq_comp]

omit [MetricSpace X] [BorelSpace X] [ProperSpace X] [μ.Regular] in
 theorem integralPotential_continuous {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) : Continuous (integralPotential μ F) :=
  continuous_iff_continuousAt.mpr fun f =>
    (integralPotential_hasFDerivAt μ hF hF0 hφ hφ0 f).continuousAt

noncomputable def heatDissipation {φ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ) (t : ℝ) : ℝ :=
  inner ℝ (hφ.compLp hφ0 (heatAt μ hQ t f)) (heatGeneratorAt μ hQ t f)

 theorem heatDissipation_continuousOn {φ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0) (f : Lp ℝ 2 μ) :
    ContinuousOn (heatDissipation μ hQ hφ hφ0 f) (Ioi 0) := by
  intro t ht
  exact (((hφ.continuous_compLp hφ0).comp (heatAt_continuous μ hQ f)).continuousAt.inner
    (heatGeneratorAt_continuousAt μ hQ f t ht)).continuousWithinAt

 theorem heatAt_integralPotential_deriv_form {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => integralPotential μ F (heatAt μ hQ s f))
      (-heatDissipation μ hQ hφ hφ0 f t) t := by
  have h := (integralPotential_hasFDerivAt μ hF hF0 hφ hφ0 _).comp_hasDerivAt t
    (heatAt_hasDerivAt μ hQ t ht f)
  simp only [innerSL_apply_apply, inner_neg_right] at h
  convert h using 1 <;> rfl

 theorem heatDissipation_eq_integral {φ ψ : ℝ → ℝ} {C : ℝ≥0}
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B)
    (f : Lp ℝ 2 μ) (t : ℝ) (ht : 0 < t) :
    heatDissipation μ hQ hφ hφ0 f t = ∫ x, ψ (heatAt μ hQ t f x) *
      SobolevSpace.minimalSlope μ hQ (heatSobolev μ hQ t ht f) x ^ 2 ∂μ := by
  have he := energyForm_comp_C1_integral μ hQ (heatSobolev μ hQ t ht f)
    hφ hφ0 hψ hd B hB
  rw [heatGenerator_form, heatSobolev_toLp] at he
  unfold heatDissipation
  rw [heatGeneratorAt_of_pos μ hQ t ht, real_inner_comm]
  exact he

 theorem heatAt_integralPotential_dissipation {F φ : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (f : Lp ℝ 2 μ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ s in a..b, heatDissipation μ hQ hφ hφ0 f s) =
      integralPotential μ F (heatAt μ hQ a f) - integralPotential μ F (heatAt μ hQ b f) := by
  have hc := (heatDissipation_continuousOn μ hQ hφ hφ0 f).mono
    (show Icc a b ⊆ Ioi 0 from fun s hs => ha.trans_le hs.1)
  have hi := hc.intervalIntegrable_of_Icc (μ := volume) hab
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (hs : s ∈ uIcc a b) => heatAt_integralPotential_deriv_form μ hQ hF hF0 hφ hφ0 f s
      (ha.trans_le ((uIcc_of_le hab) ▸ hs).1)) hi.neg
  rw [intervalIntegral.integral_neg] at he
  linarith

 theorem heatAt_integralPotential_antitoneOn {F φ ψ : ℝ → ℝ} {C : ℝ≥0}
    (hF : ∀ a, HasDerivAt F (φ a) a) (hF0 : F 0 = 0)
    (hφ : LipschitzWith C φ) (hφ0 : φ 0 = 0)
    (hψ : Continuous ψ) (hd : ∀ a, HasDerivAt φ (ψ a) a)
    (B : ℝ≥0) (hB : ∀ a, |ψ a| ≤ B) (hψ0 : ∀ a, 0 ≤ ψ a)
    (f : Lp ℝ 2 μ) : AntitoneOn (fun t => integralPotential μ F (heatAt μ hQ t f)) (Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
    (((integralPotential_continuous μ hF hF0 hφ hφ0).comp (heatAt_continuous μ hQ f)).continuousOn)
    (fun t ht => (heatAt_integralPotential_deriv_form μ hQ hF hF0 hφ hφ0 f t
      (by simpa only [interior_Ici, mem_Ioi] using ht)).hasDerivWithinAt)
  intro t ht
  have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
  rw [heatDissipation_eq_integral μ hQ hφ hφ0 hψ hd B hB f t ht']
  exact neg_nonpos.mpr (integral_nonneg fun x => mul_nonneg (hψ0 _) (sq_nonneg _))

end HeatDissipation


noncomputable def regularizedLog (ε a : ℝ) : ℝ := Real.arsinh (a/ε)
noncomputable def regularizedReciprocal (ε a : ℝ) : ℝ := (Real.sqrt (1+(a/ε)^2))⁻¹/ε
noncomputable def regularizedEntropy (ε a : ℝ) : ℝ := ∫ s in (0 : ℝ)..a, regularizedLog ε s

 theorem regularizedLog_zero (ε : ℝ) : regularizedLog ε 0 = 0 := by
  simp only [regularizedLog, zero_div, Real.arsinh_zero]

 theorem regularizedLog_continuous (ε : ℝ) : Continuous (regularizedLog ε) :=
  Real.continuous_arsinh.comp (continuous_id.div_const ε)

 theorem regularizedLog_hasDerivAt (ε a : ℝ) :
    HasDerivAt (regularizedLog ε) (regularizedReciprocal ε a) a := by
  unfold regularizedLog regularizedReciprocal
  convert ((hasDerivAt_id a).div_const ε).arsinh using 1 <;>
    simp only [id_eq, smul_eq_mul, mul_one_div]

 theorem regularizedReciprocal_continuous (ε : ℝ) : Continuous (regularizedReciprocal ε) := by
  have hp (a : ℝ) : Real.sqrt (1+(a/ε)^2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  exact (((continuous_const.add ((continuous_id.div_const ε).pow 2)).sqrt).inv₀ hp).div_const ε

 theorem regularizedReciprocal_nonneg {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 ≤ regularizedReciprocal ε a := by unfold regularizedReciprocal; positivity

 theorem regularizedReciprocal_bound {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    |regularizedReciprocal ε a| ≤ ε⁻¹ := by
  rw [abs_of_nonneg (regularizedReciprocal_nonneg hε a)]
  dsimp only [regularizedReciprocal]
  have hh : 1 ≤ Real.sqrt (1+(a/ε)^2) := Real.one_le_sqrt.mpr (by linarith [sq_nonneg (a/ε)])
  have hi := inv_le_one_of_one_le₀ hh
  simpa only [one_div] using (div_le_div_of_nonneg_right hi hε.le)

 theorem regularizedLog_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith ⟨ε⁻¹, inv_nonneg.mpr hε.le⟩ (regularizedLog ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun a => (regularizedLog_hasDerivAt ε a).differentiableAt)
  intro a
  rw [(regularizedLog_hasDerivAt ε a).deriv]
  exact_mod_cast regularizedReciprocal_bound hε a

 theorem regularizedEntropy_zero (ε : ℝ) : regularizedEntropy ε 0 = 0 := by
  simp only [regularizedEntropy, intervalIntegral.integral_same]

 theorem regularizedEntropy_hasDerivAt (ε a : ℝ) :
    HasDerivAt (regularizedEntropy ε) (regularizedLog ε a) a :=
  intervalIntegral.integral_hasDerivAt_right
    ((regularizedLog_continuous ε).intervalIntegrable _ _)
    ((regularizedLog_continuous ε).stronglyMeasurableAtFilter volume _)
    (regularizedLog_continuous ε).continuousAt

 theorem regularizedEntropy_nonneg {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    0 ≤ regularizedEntropy ε a := by
  rcases le_total 0 a with ha | ha
  · apply intervalIntegral.integral_nonneg ha
    intro s hs
    exact Real.arsinh_nonneg_iff.mpr (div_nonneg hs.1 hε.le)
  · have hh : 0 ≤ ∫ s in a..(0 : ℝ), -regularizedLog ε s := by
      apply intervalIntegral.integral_nonneg ha
      intro s hs
      exact neg_nonneg.mpr (Real.arsinh_nonpos_iff.mpr (div_nonpos_of_nonpos_of_nonneg hs.2 hε.le))
    rw [intervalIntegral.integral_neg, ← intervalIntegral.integral_symm] at hh
    exact hh

end RegularPointCoordinates

end OAI
