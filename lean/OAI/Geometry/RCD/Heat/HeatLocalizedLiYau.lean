import OAI.Geometry.RCD.Heat.HeatLiYauParameter
import OAI.Geometry.RCD.Heat.LocalizedLiYauIntegral
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity

namespace OAI

/-! # The actual heat factors satisfy localized logarithmic energy control -/

open Set Filter MeasureTheory TopologicalSpace
open scoped NNReal ENNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

include hn p in
theorem heat_localized_liYau (hK : K ≤ 0) (α : ℝ) (hα : 1 < α)
    (f g : Lp ℝ 2 (hausdorff n X)) (A B : ℝ≥0) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hf : ∀ᵐ x ∂hausdorff n X, |f x| ≤ A)
    (hg : ∀ᵐ x ∂hausdorff n X, |g x| ≤ B)
    {s t : ℝ} (hs : 0 < s) (ht : 0 < t)
    (φ : X → ℝ) (hφ : Continuous φ) (hφs : HasCompactSupport φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hpos : ∀ x ∈ tsupport φ, 0 < kernelHeat (hausdorff n X) hX.quadratic
      (hX.canonicalHeatKernel_isContinuousHeatKernel hn p) s f x) :
    let m := hausdorff n X
    let Q := hX.quadratic
    let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
    let F := kernelHeat m Q hk s f
    let G := kernelHeat m Q hk t g
    let u := heatSobolev m Q s hs f
    (∫ x, φ x*(G x/F x)*localGamma m Q u u x ∂m) ≤
      α*(∫ x, φ x*G x*(-heatGeneratorAt m Q s f) x ∂m)+
      (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/s))*(∫ x, φ x*G x*F x ∂m) := by
  intro m Q hk F G u
  have hF := kernelHeat_represents_L2 m Q hk hs f
  have hG := kernelHeat_represents_L2 m Q hk ht g
  have hFc : Continuous F := kernelHeat_continuous m Q hk hs f
  have hGc : Continuous G := kernelHeat_continuous m Q hk ht g
  have hGmem : MemLp G 2 m := (memLp_congr_ae hG).mpr (Lp.memLp (heatAt m Q t g))
  have hFmem : MemLp F 2 m := (memLp_congr_ae hF).mpr (Lp.memLp (heatAt m Q s f))
  have hG0 : ∀ᵐ x ∂m, 0 ≤ G x := by
    filter_upwards [hG,(Lp.coeFn_nonneg _).mpr (heatAt_nonneg m Q t g hg0)] with x hx hg
    rw [show G x=heatAt m Q t g x from hx]
    exact hg
  have hpoint : ∀ᵐ x ∂m, localGamma m Q u u x ≤
      α*F x*(-heatGeneratorAt m Q s f) x+
        (((n:ℝ)*α^2/2)*(|K|/(α-1)+1/s))*(F x)^2 := by
    filter_upwards [hX.heat_liYau_parameter hn p hK α hα f hf0 A hf hs,hF] with x hx he
    rwa [← he] at hx
  exact localized_liYau_of_memLp m φ F G (localGamma m Q u u)
    (fun x => ((-heatGeneratorAt m Q s f : Lp ℝ 2 m) : X → ℝ) x)
    α _ hφ hφs hφ0 hFc hGc hpos hFmem hGmem
    (Lp.memLp (-heatGeneratorAt m Q s f)) hG0
    (Eventually.of_forall (hX.kernelHeat_bounded_regularity hn p hk g B hg t ht).2)
    (localGamma_memL1 m Q u u) hpoint

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
