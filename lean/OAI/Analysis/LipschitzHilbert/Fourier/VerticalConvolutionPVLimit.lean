import OAI.Analysis.LipschitzHilbert.Estimates.ProductPVPointwiseBound
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValueBound
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalBinLpReconstruction
import OAI.Analysis.LipschitzHilbert.Fourier.SharpVerticalCommutator

namespace OAI

/-! Vertical convolution commutes with the limit of symmetric truncations
on Schwartz inputs. Domination comes from the global derivative bound and
does not use a full-frequency Hilbert estimate. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem verticalConvolution_shortSharp_tendsto (K : ℝ → ℂ)
    (hKm : Measurable K) (hKi : Integrable K) (u : (ℝ×ℝ) → ℝ)
    (hu : Measurable u) (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (R : ℝ) (hR : 0<R) (hRsmall : R≤1/4) (z : ℝ×ℝ) :
    Tendsto (fun n => verticalConvolution K
      (shortSlopeOperator (sharpTimeKernel (pvInnerRadius R n) R) u f) z)
      atTop (𝓝 (verticalConvolution K (productSlopePrincipalValue u R f) z)) := by
  let B : ℝ := 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R
  apply tendsto_integral_of_dominated_convergence (fun s => ‖K s‖*B)
  · intro n
    exact (hKm.mul ((shortSlopeOperator_measurable _ (sharpTimeKernel_measurable _ R)
      u hu f f.continuous.measurable).comp (by fun_prop))).aestronglyMeasurable
  · exact hKi.norm.mul_const B
  · intro n
    filter_upwards [] with s
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [shortSharp_eq_productSymmetric u f f.continuous _ R (pvInnerRadius_pos R hR n)
      (pvInnerRadius_lt R hR n).le hRsmall]
    exact productSymmetricTruncation_pointwise_bound u _ (hub _) f (_root_.OAI.SchwartzMap.global_lipschitz f) _ R
      (pvInnerRadius_pos R hR n).le (pvInnerRadius_lt R hR n).le
  · filter_upwards [] with s
    exact (shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRsmall _).const_mul (K s)

def principalValueProfileCommutator (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (u : (ℝ×ℝ) → ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) : (ℝ×ℝ) → ℂ :=
  verticalConvolution (verticalProfileKernel q W center) (productSlopePrincipalValue u R f)-
    productSlopePrincipalValue u R (schwartzVerticalProjection q W center f)

theorem sharpVerticalCommutator_tendsto (q : SchwartzMap ℝ ℂ) (W center R : ℝ)
    (hW : 0<W) (hR : 0<R) (hRsmall : R≤1/4) (u : (ℝ×ℝ) → ℝ)
    (hu : Measurable u) (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    Tendsto (fun n => sharpVerticalCommutator q W center (pvInnerRadius R n) R u f z)
      atTop (𝓝 (principalValueProfileCommutator q W center R u f z)) := by
  have hc : verticalConvolution (verticalProfileKernel q W center) f=
      schwartzVerticalProjection q W center f := by
    funext x
    exact (schwartzVerticalProjection_eq_convolution q W center hW f x).symm
  have h1 := verticalConvolution_shortSharp_tendsto (verticalProfileKernel q W center)
    (verticalProfileKernel_continuous q W center).measurable
    (verticalProfileKernel_integrable q W center hW) u hu hub f R hR hRsmall z
  have h2 := shortSharp_tendsto_productSlopePrincipalValue u
    (schwartzVerticalProjection q W center f) (schwartzVerticalProjection q W center f).differentiable
    R hR hRsmall z
  simpa only [sharpVerticalCommutator,principalValueProfileCommutator,Pi.sub_apply,hc] using h1.sub h2

end LipschitzHilbert.PacketRepresentation

end

end OAI
