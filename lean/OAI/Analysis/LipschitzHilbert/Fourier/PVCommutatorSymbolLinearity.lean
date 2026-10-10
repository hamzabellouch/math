import OAI.Analysis.LipschitzHilbert.Fourier.BoundedVerticalMultiplier
import OAI.Analysis.LipschitzHilbert.Estimates.PrincipalValueProfileCommutator
import OAI.Analysis.LipschitzHilbert.Fourier.VerticalProjectionAlgebra

namespace OAI

/-! Linearity in the frequency symbol for the actual PV commutator,
without assuming boundedness of the full principal-value operator. -/
noncomputable section
open MeasureTheory
namespace LipschitzHilbert.PacketRepresentation

def schwartzVerticalProfileLM (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] SchwartzMap (ℝ×ℝ) ℂ where
  toFun p := schwartzVerticalProjection p W 0 f
  map_add' p q := schwartzVerticalProjection_add_profile p q W f
  map_smul' c p := by
    apply planar_schwartz_ext_fourier
    intro omega
    simp only [schwartzVerticalProjection_fourier,planarFourier_smul,smul_apply,
      smul_eq_mul,RingHom.id_apply]
    ring

@[simp] theorem schwartzVerticalProfileLM_apply (W : ℝ) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (p : SchwartzMap ℝ ℂ) :
    schwartzVerticalProfileLM W f p=schwartzVerticalProjection p W 0 f := rfl

def pvCommutatorSymbolLM (W : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ) :
    SchwartzMap ℝ ℂ →ₗ[ℂ] ((ℝ×ℝ) → ℂ) :=
  boundedVerticalMultiplierLM W hW (productSlopePrincipalValue u R f)
    (productSlopePrincipalValue_measurable u hum f f.differentiable R hR hRs)
    (2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ)*R)
    (fun z => productSchwartzPV_pointwise_bound u z (hub z) f R hR)-
  (productPVSchwartzLM u R hR hRs).comp (schwartzVerticalProfileLM W f)

@[simp] theorem pvCommutatorSymbolLM_apply (W : ℝ) (hW : 0<W) (u : (ℝ×ℝ) → ℝ)
    (hum : Measurable u) (hub : ∀ z, |u z|≤1)
    (R : ℝ) (hR : 0<R) (hRs : R≤1/4) (f : SchwartzMap (ℝ×ℝ) ℂ)
    (p : SchwartzMap ℝ ℂ) :
    pvCommutatorSymbolLM W hW u hum hub R hR hRs f p=
      principalValueProfileCommutator p W 0 R u f := rfl

end LipschitzHilbert.PacketRepresentation

end

end OAI
