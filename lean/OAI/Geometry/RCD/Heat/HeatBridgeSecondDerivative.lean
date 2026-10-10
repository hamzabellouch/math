import OAI.Geometry.RCD.Heat.HeatBridgePairingDerivative
import OAI.Geometry.RCD.Heat.HeatGeneratorSecondDerivative

namespace OAI

/-! # Exact second variation of bounded heat-bridge pairings

All derivatives are taken in L2 before the bounded multiplier is paired.
The coefficient contains the two actual iterated generators and the mixed
first-generator term. No spatial regularity of the bounded test is assumed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (Q : QuadraticCheegerEnergy μ)

def heatBridgeVariation (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) (T t : ℝ) : ℝ :=
  inner ℝ (heatAt μ Q t f) (lpMultiplier μ θ (heatGeneratorAt μ Q (T-t) g)) +
    inner ℝ (-heatGeneratorAt μ Q t f) (lpMultiplier μ θ (heatAt μ Q (T-t) g))

def heatBridgeSecondVariation (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) (T t : ℝ) : ℝ :=
  inner ℝ (heatAt μ Q t f) (lpMultiplier μ θ (heatSecondGeneratorAt μ Q (T-t) g)) -
    2*inner ℝ (heatGeneratorAt μ Q t f) (lpMultiplier μ θ (heatGeneratorAt μ Q (T-t) g)) +
    inner ℝ (heatSecondGeneratorAt μ Q t f) (lpMultiplier μ θ (heatAt μ Q (T-t) g))

theorem heatBridgeVariation_hasDerivAt (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (heatBridgeVariation μ Q θ f g T)
      (heatBridgeSecondVariation μ Q θ f g T t) t := by
  have hback := (heatAt_hasDerivAt μ Q (T-t) (sub_pos.mpr htT) g).scomp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have hback' : HasDerivAt (fun s => heatAt μ Q (T-s) g)
      (heatGeneratorAt μ Q (T-t) g) t := by
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hback
  have hbgen := (heatGeneratorAt_hasDerivAt_second μ Q g (sub_pos.mpr htT)).scomp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have hbgen' : HasDerivAt (fun s => heatGeneratorAt μ Q (T-s) g)
      (heatSecondGeneratorAt μ Q (T-t) g) t := by
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hbgen
  have hfront : HasDerivAt (fun s => -heatGeneratorAt μ Q s f)
      (heatSecondGeneratorAt μ Q t f) t := by
    simpa only [Pi.neg_apply,neg_neg] using! (heatGeneratorAt_hasDerivAt_second μ Q f ht).neg
  have h₁ := (heatAt_hasDerivAt μ Q t ht f).inner ℝ
    ((lpMultiplier μ θ).hasFDerivAt.comp_hasDerivAt t hbgen')
  have h₂ := hfront.inner ℝ ((lpMultiplier μ θ).hasFDerivAt.comp_hasDerivAt t hback')
  convert h₁.add h₂ using 1
  · rfl
  · simp only [heatBridgeSecondVariation,Function.comp_def,inner_neg_left]
    ring

variable {ker : ℝ → X → X → ℝ} (hk : IsContinuousHeatKernel μ Q ker)

theorem kernelHeat_bridge_pairing_hasDerivAt_variation
    (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) {T t : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ x, θ x*(kernelHeat μ Q hk s f x*
      kernelHeat μ Q hk (T-s) g x) ∂μ) (heatBridgeVariation μ Q θ f g T t) t := by
  have hb := (heatAt_hasDerivAt μ Q (T-t) (sub_pos.mpr htT) g).scomp t
    ((hasDerivAt_const t T).sub (hasDerivAt_id t))
  have hb' : HasDerivAt (fun s => heatAt μ Q (T-s) g)
      (heatGeneratorAt μ Q (T-t) g) t := by
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hb
  have hd := (heatAt_hasDerivAt μ Q t ht f).inner ℝ
    ((lpMultiplier μ θ).hasFDerivAt.comp_hasDerivAt t hb')
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with s hs
  exact (kernelHeat_weighted_pairing μ Q hk θ f g hs.1 (sub_pos.mpr hs.2)).symm

theorem kernelHeat_bridge_pairing_second_hasDerivAt
    (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ) {T t : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (deriv (fun s => ∫ x, θ x*(kernelHeat μ Q hk s f x*
      kernelHeat μ Q hk (T-s) g x) ∂μ)) (heatBridgeSecondVariation μ Q θ f g T t) t := by
  apply (heatBridgeVariation_hasDerivAt μ Q θ f g ht htT).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with s hs
  exact (kernelHeat_bridge_pairing_hasDerivAt_variation μ Q hk θ f g hs.1
    hs.2).deriv

end RegularPointCoordinates

end

end OAI
