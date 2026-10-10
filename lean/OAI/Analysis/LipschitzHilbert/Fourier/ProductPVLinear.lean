import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValueBound
import OAI.Analysis.LipschitzHilbert.Estimates.ShortL2Operator

namespace OAI

/-! The actual product-coordinate principal value is linear on Schwartz
inputs, before any boundedness theorem is used. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

theorem productPV_schwartz_add (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (f g : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R (f+g : SchwartzMap (ℝ×ℝ) ℂ) z=
      productSlopePrincipalValue u R f z+productSlopePrincipalValue u R g z := by
  apply tendsto_nhds_unique (shortSharp_tendsto_productSlopePrincipalValue u (f+g)
    (f+g).differentiable R hR hRs z)
  apply ((shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRs z).add
    (shortSharp_tendsto_productSlopePrincipalValue u g g.differentiable R hR hRs z)).congr'
  exact Eventually.of_forall fun n => (shortSlopeOperator_schwartz_add _
    (sharpTimeKernel_integrable _ R (pvInnerRadius_pos R hR n) hR) u f g z).symm

theorem productPV_schwartz_smul (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (c : ℂ) (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R (c • f : SchwartzMap (ℝ×ℝ) ℂ) z=
      c*productSlopePrincipalValue u R f z := by
  apply tendsto_nhds_unique (shortSharp_tendsto_productSlopePrincipalValue u (c • f)
    (c • f).differentiable R hR hRs z)
  apply ((shortSharp_tendsto_productSlopePrincipalValue u f f.differentiable R hR hRs z).const_mul c).congr'
  exact Eventually.of_forall fun _ => (shortSlopeOperator_schwartz_smul _ u f c z).symm

def productPVSchwartzLM (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R) (hRs : R≤1/4) :
    SchwartzMap (ℝ×ℝ) ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) where
  toFun := fun f => productSlopePrincipalValue u R f
  map_add' f g := funext (productPV_schwartz_add u R hR hRs f g)
  map_smul' c f := funext (productPV_schwartz_smul u R hR hRs c f)

@[simp] theorem productPVSchwartzLM_apply (u : (ℝ×ℝ) → ℝ) (R : ℝ) (hR : 0<R)
    (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    productPVSchwartzLM u R hR hRs f=productSlopePrincipalValue u R f := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
