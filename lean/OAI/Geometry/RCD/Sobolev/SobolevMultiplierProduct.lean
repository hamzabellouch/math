import OAI.Geometry.RCD.Sobolev.WeakLaplacianProduct

namespace OAI

/-! # The product Laplacian in bounded-multiplier form

This form keeps all three terms in the original L2 space, which permits
exact self-adjointness calculations for the heat-bridge second variation.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

omit [BorelSpace X] [ProperSpace X] in
theorem weakLaplacian_inner_comm (u v : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hu : IsWeakLaplacian μ Q u d) (hv : IsWeakLaplacian μ Q v e) :
    inner ℝ d (SobolevSpace.toLp μ Q v) = inner ℝ (SobolevSpace.toLp μ Q u) e := by
  have he := energyForm_comm μ Q u v
  rw [hu,hv] at he
  have hs : inner ℝ e (SobolevSpace.toLp μ Q u) = inner ℝ (SobolevSpace.toLp μ Q u) e :=
    real_inner_comm _ _
  rw [hs] at he
  linarith only [he]

omit [BorelSpace X] [ProperSpace X] in
theorem sobolev_product_toLp_multiplier (u v : SobolevSpace μ Q)
    (U : Lp ℝ ∞ μ) (hU : U =ᵐ[μ] SobolevSpace.toLp μ Q u) (A B : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B) :
    SobolevSpace.toLp μ Q (SobolevSpace.product μ Q u v A B) =
      lpMultiplier μ U (SobolevSpace.toLp μ Q v) := by
  apply Lp.ext
  filter_upwards [SobolevSpace.product_coe μ Q u v A B hA hB,
    lpMultiplier_coe μ U (SobolevSpace.toLp μ Q v),hU] with x hp hm hu
  rw [hp,hm,hu]

theorem weakLaplacian_product_multiplier
    (u v uv : SobolevSpace μ Q) (d e : Lp ℝ 2 μ)
    (hu : IsWeakLaplacian μ Q u d) (hv : IsWeakLaplacian μ Q v e)
    (U V : Lp ℝ ∞ μ)
    (hU : U =ᵐ[μ] SobolevSpace.toLp μ Q u)
    (hV : V =ᵐ[μ] SobolevSpace.toLp μ Q v)
    (hΓ : SobolevSpace.toLp μ Q uv =ᵐ[μ] localGamma μ Q u v)
    (A B L : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hL : ∀ᵐ x ∂μ, localGamma μ Q v v x ≤ (L:ℝ)^2) :
    IsWeakLaplacian μ Q (SobolevSpace.product μ Q u v A B)
      (lpMultiplier μ V d+lpMultiplier μ U e+(2:ℝ) • SobolevSpace.toLp μ Q uv) := by
  obtain ⟨q,hq,hrep⟩ := IsWeakLaplacian.product μ Q u v d e hu hv A B L hA hB hL
  have heq : q = lpMultiplier μ V d+lpMultiplier μ U e+(2:ℝ) • SobolevSpace.toLp μ Q uv := by
    apply Lp.ext
    filter_upwards [hrep,hU,hV,hΓ,lpMultiplier_coe μ V d,lpMultiplier_coe μ U e,
      Lp.coeFn_add (lpMultiplier μ V d) (lpMultiplier μ U e),
      Lp.coeFn_add (lpMultiplier μ V d+lpMultiplier μ U e) ((2:ℝ) • SobolevSpace.toLp μ Q uv),
      Lp.coeFn_smul (2:ℝ) (SobolevSpace.toLp μ Q uv)] with x hq hux hvx hΓx hd he hsum htotal hs
    rw [htotal]
    simp only [Pi.add_apply]
    rw [hsum,hs]
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [hd,he,hux,hvx,hΓx]
    exact hq
  rwa [heq] at hq

end RegularPointCoordinates

end

end OAI
