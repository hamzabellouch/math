import OAI.Geometry.RCD.Heat.HeatGamma
import OAI.Geometry.RCD.Coordinates.KernelHeatBoundedRegularity
import OAI.Geometry.RCD.Sobolev.GammaL2Bound
import OAI.Geometry.RCD.Heat.CanonicalKernelConstruction

namespace OAI

/-! # Sobolev energy densities for the actual bounded heat factors

The initial L2 function need not have compact support or be Lipschitz.
The positive-time gradient bound and the existing Bochner estimate supply
the Sobolev representative of its squared gradient.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  [(hausdorff n X).Regular] (hn : 2 ≤ n) (p : X)

include hn p in
theorem heat_gram_of_gradient_bound (f : Lp ℝ 2 (hausdorff n X))
    {t : ℝ} (ht : 0 < t) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂hausdorff n X, SobolevSpace.minimalSlope (hausdorff n X) hX.quadratic
      (heatSobolev (hausdorff n X) hX.quadratic t ht f) x ≤ L) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) ∧
      (∀ᵐ x ∂hausdorff n X, |SobolevSpace.toLp (hausdorff n X) hX.quadratic G x| ≤ (L:ℝ)^2) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let F := heatSobolev μ Q t ht f
  have hm := localGamma_memLp_of_bounded_gradient μ Q F F L hL
  let H := hm.toLp _
  have hrep : H =ᵐ[μ] localGamma μ Q F F := hm.coeFn_toLp
  have hsq : (fun x => (SobolevSpace.minimalSlope μ Q F x)^2) =ᵐ[μ] H :=
    (localGamma_self μ Q F).symm.trans hrep.symm
  have hB : ∀ᵐ x ∂μ, |H x| ≤ (L:ℝ)^2 := by
    filter_upwards [hsq,hL,(Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ Q F)]
      with x hx hg h0
    rw [← hx,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 hg 2
  have hfin := hX.heat_gamma_finite_energy hn p f ht H (L^2) hsq (by simpa using hB)
  exact ⟨⟨H,hfin⟩,hrep,hB⟩

variable [SeparableSpace X] [IsLocallyFiniteMeasure (hausdorff n X)]

include hn p in
theorem bounded_heat_gram (f : Lp ℝ 2 (hausdorff n X)) (C : ℝ≥0)
    (hC : ∀ᵐ x ∂hausdorff n X, |f x| ≤ C) {t : ℝ} (ht : 0 < t) :
    ∃ G : SobolevSpace (hausdorff n X) hX.quadratic,
      SobolevSpace.toLp (hausdorff n X) hX.quadratic G =ᵐ[hausdorff n X]
        localGamma (hausdorff n X) hX.quadratic
          (heatSobolev (hausdorff n X) hX.quadratic t ht f)
          (heatSobolev (hausdorff n X) hX.quadratic t ht f) := by
  let μ := hausdorff n X
  let Q := hX.quadratic
  let hk := hX.canonicalHeatKernel_isContinuousHeatKernel hn p
  obtain ⟨hlip,-⟩ := hX.kernelHeat_bounded_regularity hn p hk f C hC t ht
  have hrep : SobolevSpace.toLp μ Q (heatSobolev μ Q t ht f) =ᵐ[μ]
      kernelHeat μ Q hk t f := by
    simpa only [heatSobolev_toLp] using (kernelHeat_represents_L2 μ Q hk ht f).symm
  have hgrad := SobolevSpace.minimalSlope_le_lipschitz μ Q
    (heatSobolev μ Q t ht f) hlip hrep
  obtain ⟨G,hG,-⟩ := hX.heat_gram_of_gradient_bound hn p f ht _ hgrad
  exact ⟨G,hG⟩

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
