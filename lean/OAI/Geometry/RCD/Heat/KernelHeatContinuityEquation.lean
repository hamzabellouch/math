import OAI.Geometry.RCD.Heat.HeatBridgePairingDerivative
import OAI.Geometry.RCD.Sobolev.WeakLaplacianFluxIdentity
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # The continuity equation for actual forward/backward heat factors

The common Sobolev factors work for every bounded Sobolev test.
The derivative of its density pairing is the exact antisymmetric flux.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal Topology
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem kernelHeat_continuity_equation {ker : ℝ → X → X → ℝ}
    (hk : IsContinuousHeatKernel (hausdorff n X) hX.quadratic ker)
    (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {T t : ℝ} (ht : 0 < t) (htT : t < T) :
    ∃ (u v : SobolevSpace (hausdorff n X) hX.quadratic),
      (kernelHeat (hausdorff n X) hX.quadratic hk t f =ᵐ[hausdorff n X]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic u) ∧
      (kernelHeat (hausdorff n X) hX.quadratic hk (T-t) g =ᵐ[hausdorff n X]
        SobolevSpace.toLp (hausdorff n X) hX.quadratic v) ∧
      ∀ (w : SobolevSpace (hausdorff n X) hX.quadratic) (C : ℝ≥0),
        (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic w x| ≤ C) →
        HasDerivAt (fun s => ∫ x, SobolevSpace.toLp (hausdorff n X) hX.quadratic w x *
          (kernelHeat (hausdorff n X) hX.quadratic hk s f x *
            kernelHeat (hausdorff n X) hX.quadratic hk (T-s) g x) ∂hausdorff n X)
          (∫ x, kernelHeat (hausdorff n X) hX.quadratic hk t f x *
            localGamma (hausdorff n X) hX.quadratic v w x -
            kernelHeat (hausdorff n X) hX.quadratic hk (T-t) g x *
            localGamma (hausdorff n X) hX.quadratic u w x ∂hausdorff n X) t := by
  let μ := hausdorff n X
  let hQ := hX.quadratic
  obtain ⟨u,d,hu,hd,hD⟩ := kernelHeat_spatial_source μ hQ hk f ht
  obtain ⟨v,e,hv,he,hE⟩ := kernelHeat_spatial_source μ hQ hk g (sub_pos.mpr htT)
  obtain ⟨_,hfB⟩ := hX.kernelHeat_bounded_regularity hn p hk f A hf t ht
  obtain ⟨_,hgB⟩ := hX.kernelHeat_bounded_regularity hn p hk g B hg (T-t) (sub_pos.mpr htT)
  have huB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x| ≤ A :=
    hu.mono fun x hx => hx ▸ hfB x
  have hvB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ v x| ≤ B :=
    hv.mono fun x hx => hx ▸ hgB x
  refine ⟨u,v,hu,hv,?_⟩
  intro w C hw
  let W := SobolevSpace.toLp μ hQ w
  have hW : MemLp W ∞ μ := memLp_top_of_bound (Lp.aestronglyMeasurable W) C
    (by simpa only [Real.norm_eq_abs] using hw)
  let θ := hW.toLp W
  have hθ : θ =ᵐ[μ] W := hW.coeFn_toLp
  have hder := kernelHeat_bridge_pairing_hasDerivAt μ hQ hk θ f g ht htT
  have hflux := weakLaplacian_product_flux μ hQ u v w d e hd he A B C huB hvB hw
  have hcoeff : (∫ x, θ x * (kernelHeatGeneratorSource μ hQ hk t f x *
      kernelHeat μ hQ hk (T-t) g x - kernelHeat μ hQ hk t f x *
      kernelHeatGeneratorSource μ hQ hk (T-t) g x) ∂μ) =
      ∫ x, kernelHeat μ hQ hk t f x * localGamma μ hQ v w x -
        kernelHeat μ hQ hk (T-t) g x * localGamma μ hQ u w x ∂μ := by
    calc
      _ = ∫ x, W x * (d x * SobolevSpace.toLp μ hQ v x -
          SobolevSpace.toLp μ hQ u x * e x) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hθ,hu,hv,hD,hE] with x hx hux hvx hdx hex
        rw [hx,hux,hvx,hdx,hex]
      _ = _ := hflux.trans (integral_congr_ae (by
        filter_upwards [hu,hv] with x hux hvx
        rw [hux,hvx]))
  rw [hcoeff] at hder
  apply hder.congr_of_eventuallyEq
  exact Eventually.of_forall fun s => integral_congr_ae (hθ.mono fun x hx =>
    congrArg (fun z : ℝ => z * (kernelHeat μ hQ hk s f x * kernelHeat μ hQ hk (T-s) g x)) hx.symm)

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
