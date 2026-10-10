import OAI.Geometry.RCD.Heat.KernelHeatSpatialSource

namespace OAI

/-! # Differentiating bounded tests of the forward/backward heat product

The derivative is taken in L² before pairing. No exchange of a pointwise
derivative with an improper spatial integral is needed.
-/

open Set Filter MeasureTheory
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)
  {p : ℝ → X → X → ℝ} (hp : IsContinuousHeatKernel μ hQ p)

theorem kernelHeat_weighted_pairing (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r) :
    inner ℝ (heatAt μ hQ s f) (lpMultiplier μ θ (heatAt μ hQ r g)) =
      ∫ x, θ x * (kernelHeat μ hQ hp s f x * kernelHeat μ hQ hp r g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpMultiplier_coe μ θ (heatAt μ hQ r g),
    kernelHeat_represents_L2 μ hQ hp hs f,kernelHeat_represents_L2 μ hQ hp hr g] with x hm hf hg
  simp only [Real.inner_apply,hm,← hf,← hg]
  ring

theorem kernelHeat_bridge_pairing_hasDerivAt (θ : Lp ℝ ∞ μ) (f g : Lp ℝ 2 μ)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun s => ∫ x, θ x * (kernelHeat μ hQ hp s f x *
        kernelHeat μ hQ hp (T-s) g x) ∂μ)
      (∫ x, θ x * (kernelHeatGeneratorSource μ hQ hp t f x *
          kernelHeat μ hQ hp (T-t) g x - kernelHeat μ hQ hp t f x *
          kernelHeatGeneratorSource μ hQ hp (T-t) g x) ∂μ) t := by
  let F := heatAt μ hQ t f
  let G := heatAt μ hQ (T-t) g
  let d := heatGeneratorAt μ hQ t f
  let e := heatGeneratorAt μ hQ (T-t) g
  have hback : HasDerivAt (fun s => heatAt μ hQ (T-s) g) e t := by
    have hh := (heatAt_hasDerivAt μ hQ (T-t) (sub_pos.mpr htT) g).scomp t
      ((hasDerivAt_const t T).sub (hasDerivAt_id t))
    simpa only [Function.comp_def,zero_sub,neg_smul,one_smul,neg_neg] using hh
  have hh := (heatAt_hasDerivAt μ hQ t ht f).inner ℝ
    ((lpMultiplier μ θ).hasFDerivAt.comp_hasDerivAt t hback)
  have hdiff : inner ℝ F (lpMultiplier μ θ e) + inner ℝ (-d) (lpMultiplier μ θ G) =
      ∫ x, θ x * (kernelHeatGeneratorSource μ hQ hp t f x *
          kernelHeat μ hQ hp (T-t) g x - kernelHeat μ hQ hp t f x *
          kernelHeatGeneratorSource μ hQ hp (T-t) g x) ∂μ := by
    have hi₁ := L2.integrable_inner (𝕜 := ℝ) F (lpMultiplier μ θ e)
    have hi₂ := L2.integrable_inner (𝕜 := ℝ) (-d) (lpMultiplier μ θ G)
    rw [L2.inner_def,L2.inner_def,← integral_add hi₁ hi₂]
    apply integral_congr_ae
    filter_upwards [lpMultiplier_coe μ θ G,lpMultiplier_coe μ θ e,Lp.coeFn_neg d,
      kernelHeat_represents_L2 μ hQ hp ht f,
      kernelHeat_represents_L2 μ hQ hp (sub_pos.mpr htT) g,
      kernelHeatGeneratorSource_represents μ hQ hp ht f,
      kernelHeatGeneratorSource_represents μ hQ hp (sub_pos.mpr htT) g] with x hm hn hd hf hg hdf hdg
    change kernelHeatGeneratorSource μ hQ hp t f x = -(d x) at hdf
    change kernelHeatGeneratorSource μ hQ hp (T-t) g x = -(e x) at hdg
    change kernelHeat μ hQ hp t f x = F x at hf
    change kernelHeat μ hQ hp (T-t) g x = G x at hg
    simp only [Real.inner_apply,hm,hn,hdf,hdg,hd,Pi.neg_apply,hf,hg]
    ring
  rw [← hdiff]
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht htT] with s hs
  exact (kernelHeat_weighted_pairing μ hQ hp θ f g hs.1 (sub_pos.mpr hs.2)).symm

end RegularPointCoordinates

end

end OAI
