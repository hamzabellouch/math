import OAI.Geometry.RCD.Coordinates.RegularDirichletCore
import OAI.Geometry.RCD.Sobolev.WeakLaplacianProduct
import OAI.Geometry.RCD.Sobolev.GoodLaplacianCutoff

namespace OAI

/-! # Compact regular localization retaining the full L² source

A bounded Lipschitz function with weak L² Laplacian is multiplied by an
actual good cutoff. On its plateau both the function and source agree
with the originals. No constant-source or source-gradient premise is used.
-/

open Set Filter Metric MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (hQ : QuadraticCheegerEnergy μ)

theorem bounded_regular_localization (u : SobolevSpace μ hQ) (d : Lp ℝ 2 μ)
    (hd : IsWeakLaplacian μ hQ u d) (v : X → ℝ) {L : ℝ≥0}
    (hv : LipschitzWith L v) (hu : SobolevSpace.toLp μ hQ u =ᵐ[μ] v)
    (A : ℝ≥0) (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ u x|≤A)
    {p : X} {r C : ℝ} (χ : GoodLaplacianCutoff μ hQ p r C) :
    ∃ (F : compactLaplacianCore μ hQ univ) (q : Lp ℝ 2 μ),
      IsWeakLaplacian μ hQ F.val q ∧
      SobolevSpace.toLp μ hQ F.val =ᵐ[μ.restrict (ball p r)] SobolevSpace.toLp μ hQ u ∧
      q =ᵐ[μ.restrict (ball p r)] d := by
  have hχb : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ hQ χ.sobolev x|≤(1:ℝ≥0) := by
    filter_upwards [χ.representative] with x hx
    rw [hx,abs_of_nonneg (χ.bounds x).1]
    exact (χ.bounds x).2
  have hχg := SobolevSpace.minimalSlope_le_lipschitz μ hQ χ.sobolev χ.lipschitz χ.representative
  have hΓ : ∀ᵐ x ∂μ, localGamma μ hQ χ.sobolev χ.sobolev x≤((C/r).toNNReal:ℝ)^2 := by
    filter_upwards [localGamma_self μ hQ χ.sobolev,hχg,
      (Lp.coeFn_nonneg _).mpr (SobolevSpace.minimalSlope_nonneg μ hQ χ.sobolev)] with x hx hg hn
    rw [hx]
    exact pow_le_pow_left₀ hn hg 2
  let F := SobolevSpace.product μ hQ u χ.sobolev A 1
  obtain ⟨q,hq,hqr⟩ := hd.product μ hQ u χ.sobolev d χ.laplacian χ.weak_laplacian
    A 1 (C/r).toNNReal hA hχb hΓ
  have hFr : SobolevSpace.toLp μ hQ F =ᵐ[μ] fun x => χ.weight x*v x := by
    filter_upwards [SobolevSpace.product_coe μ hQ u χ.sobolev A 1 hA hχb,hu,χ.representative] with x hx hy hz
    change SobolevSpace.toLp μ hQ (SobolevSpace.product μ hQ u χ.sobolev A 1) x = _
    rw [hx,hy,hz,mul_comm]
  obtain ⟨B,hB⟩ := lipschitz_mul_compact_cutoff χ.lipschitz hv (χ.hasCompactSupport μ hQ)
    (fun x => by rw [abs_of_nonneg (χ.bounds x).1]; exact (χ.bounds x).2)
  have hFc : F ∈ compactLaplacianCore μ hQ univ :=
    ⟨⟨_,B,hB,(χ.hasCompactSupport μ hQ).mul_right,subset_univ _,hFr⟩,q,hq⟩
  refine ⟨⟨F,hFc⟩,q,hq,?_,?_⟩
  · apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [hFr,hu] with x hx hy hball
    rw [hx,χ.one x hball,one_mul,hy]
  · apply (ae_restrict_iff' measurableSet_ball).mpr
    filter_upwards [hqr,χ.representative,χ.laplacian_locality,
      localGamma_zero_on_level μ hQ χ.sobolev u 1,
      localGamma_comm μ hQ u χ.sobolev] with x hx hχ hΔ hz hc hball
    have hχ1 := χ.one x hball
    have hΓ0 : localGamma μ hQ u χ.sobolev x=0 := hc.trans (hz (hχ.trans hχ1))
    rw [hx,hχ,hχ1,hΔ (Or.inl (by simpa only [mem_ball,dist_comm] using hball)),hΓ0]
    ring

end RegularPointCoordinates

end

end OAI
