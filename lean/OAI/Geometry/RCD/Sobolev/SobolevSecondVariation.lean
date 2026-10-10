import OAI.Geometry.RCD.Sobolev.SobolevMultiplierProduct
import OAI.Geometry.RCD.Sobolev.HessianLaplacianPairing

namespace OAI

/-! # Exact Hessian cancellation in a twice differentiated heat product

The identity uses only weak Laplacians, bounded Sobolev product rules,
and three actual Sobolev Gram representatives. All terms are in L2.
-/

open Set Filter MeasureTheory
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (Q : QuadraticCheegerEnergy μ)

theorem sobolev_second_variation_hessian
    (u v w du dv dw uv wu wv : SobolevSpace μ Q)
    (d e q d₂ e₂ q₂ : Lp ℝ 2 μ)
    (hu : IsWeakLaplacian μ Q u d) (hv : IsWeakLaplacian μ Q v e)
    (hw : IsWeakLaplacian μ Q w q)
    (hdu : IsWeakLaplacian μ Q du d₂) (hdv : IsWeakLaplacian μ Q dv e₂)
    (hdw : IsWeakLaplacian μ Q dw q₂)
    (hduv : SobolevSpace.toLp μ Q du = d) (hdvv : SobolevSpace.toLp μ Q dv = e)
    (hdwv : SobolevSpace.toLp μ Q dw = q)
    (U V W : Lp ℝ ∞ μ)
    (hU : U =ᵐ[μ] SobolevSpace.toLp μ Q u)
    (hV : V =ᵐ[μ] SobolevSpace.toLp μ Q v)
    (hW : W =ᵐ[μ] SobolevSpace.toLp μ Q w)
    (huv : SobolevSpace.toLp μ Q uv =ᵐ[μ] localGamma μ Q u v)
    (hwu : SobolevSpace.toLp μ Q wu =ᵐ[μ] localGamma μ Q w u)
    (hwv : SobolevSpace.toLp μ Q wv =ᵐ[μ] localGamma μ Q w v)
    (A B C Lu Lv : ℝ≥0)
    (hA : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q u x| ≤ A)
    (hB : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q v x| ≤ B)
    (hC : ∀ᵐ x ∂μ, |SobolevSpace.toLp μ Q w x| ≤ C)
    (hLu : ∀ᵐ x ∂μ, localGamma μ Q u u x ≤ (Lu:ℝ)^2)
    (hLv : ∀ᵐ x ∂μ, localGamma μ Q v v x ≤ (Lv:ℝ)^2) :
    inner ℝ d₂ (lpMultiplier μ W (SobolevSpace.toLp μ Q v)) -
        2*inner ℝ d (lpMultiplier μ W e) +
        inner ℝ (SobolevSpace.toLp μ Q u) (lpMultiplier μ W e₂) =
      inner ℝ q₂ (SobolevSpace.toLp μ Q (SobolevSpace.product μ Q u v A B)) -
        4*(∫ x, localHessianAction μ Q w u v wu wv uv x ∂μ) := by
  let Puv := lpMultiplier μ V d+lpMultiplier μ U e+(2:ℝ) • SobolevSpace.toLp μ Q uv
  let Pwu := lpMultiplier μ U q+lpMultiplier μ W d+(2:ℝ) • SobolevSpace.toLp μ Q wu
  let Pwv := lpMultiplier μ V q+lpMultiplier μ W e+(2:ℝ) • SobolevSpace.toLp μ Q wv
  have hpUV : IsWeakLaplacian μ Q (SobolevSpace.product μ Q u v A B) Puv :=
    weakLaplacian_product_multiplier μ Q u v uv d e hu hv U V hU hV huv A B Lv hA hB hLv
  have hpWU : IsWeakLaplacian μ Q (SobolevSpace.product μ Q w u C A) Pwu :=
    weakLaplacian_product_multiplier μ Q w u wu q d hw hu W U hW hU hwu C A Lu hC hA hLu
  have hpWV : IsWeakLaplacian μ Q (SobolevSpace.product μ Q w v C B) Pwv :=
    weakLaplacian_product_multiplier μ Q w v wv q e hw hv W V hW hV hwv C B Lv hC hB hLv
  have hfirst : inner ℝ d₂ (lpMultiplier μ W (SobolevSpace.toLp μ Q v)) = inner ℝ d Pwv := by
    rw [← sobolev_product_toLp_multiplier μ Q w v W hW C B hC hB]
    simpa only [hduv] using weakLaplacian_inner_comm μ Q du
      (SobolevSpace.product μ Q w v C B) d₂ Pwv hdu hpWV
  have hlast : inner ℝ (SobolevSpace.toLp μ Q u) (lpMultiplier μ W e₂) = inner ℝ e Pwu := by
    rw [lpMultiplier_inner_symm,real_inner_comm,
      ← sobolev_product_toLp_multiplier μ Q w u W hW C A hC hA]
    simpa only [hdvv] using weakLaplacian_inner_comm μ Q dv
      (SobolevSpace.product μ Q w u C A) e₂ Pwu hdv hpWU
  have htarget : inner ℝ q₂ (SobolevSpace.toLp μ Q (SobolevSpace.product μ Q u v A B)) =
      inner ℝ q Puv := by
    simpa only [hdwv] using weakLaplacian_inner_comm μ Q dw
      (SobolevSpace.product μ Q u v A B) q₂ Puv hdw hpUV
  have hswap (Z : Lp ℝ ∞ μ) (a b : Lp ℝ 2 μ) :
      inner ℝ a (lpMultiplier μ Z b) = inner ℝ b (lpMultiplier μ Z a) := by
    rw [lpMultiplier_inner_symm,real_inner_comm]
  rw [hfirst,hlast,htarget,integral_hessian_laplacian_pairings μ Q w u v wu wv uv q d e hw hu hv]
  simp only [Puv,Pwu,Pwv,inner_add_right,real_inner_smul_right]
  rw [hswap V d q,hswap U e q,hswap W e d]
  ring

end RegularPointCoordinates

end

end OAI
