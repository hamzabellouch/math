import OAI.Analysis.LipschitzHilbert.Estimates.ProductPVPointwiseBound
import OAI.Analysis.LipschitzHilbert.Estimates.ProductSlopePrincipalValueBound

namespace OAI

/-! The pointwise principal value is continuous for continuous bounded
slope fields. The removable value at time zero is irrelevant to integration. -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace LipschitzHilbert.PacketRepresentation

def productPVIntegrand (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ)
    (z : ℝ×ℝ) (t : ℝ) : ℂ :=
  t⁻¹ • (f (productSlopeSample u t z)-f (productSlopeSample u (-t) z))

theorem productPV_eq_integral (u : (ℝ×ℝ) → ℝ) (f : (ℝ×ℝ) → ℂ) (R : ℝ)
    (hR : 0≤R) (z : ℝ×ℝ) :
    productSlopePrincipalValue u R f z=
      ∫ t in Set.Ioc 0 R, productPVIntegrand u f z t := by
  rw [productSlopePrincipalValue,intervalIntegral.integral_of_le hR]
  apply setIntegral_congr_ae measurableSet_Ioc
  filter_upwards [volume.ae_ne (0:ℝ)] with t ht _
  exact Function.update_of_ne ht _ _

theorem productPVIntegrand_bound (u : (ℝ×ℝ) → ℝ) (hub : ∀ z, |u z|≤1)
    (f : SchwartzMap (ℝ×ℝ) ℂ) (z : ℝ×ℝ) (t : ℝ) :
    ‖productPVIntegrand u f z t‖≤2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ) :=
  productSymmetricIntegrand_bound u z (hub z) f (_root_.OAI.SchwartzMap.global_lipschitz f) t

theorem productPV_continuous (u : (ℝ×ℝ) → ℝ) (hu : Continuous u)
    (hub : ∀ z, |u z|≤1) (f : SchwartzMap (ℝ×ℝ) ℂ) (R : ℝ) (hR : 0≤R) :
    Continuous (productSlopePrincipalValue u R f) := by
  have he : productSlopePrincipalValue u R f=fun z =>
      ∫ t in Set.Ioc 0 R, productPVIntegrand u f z t :=
    funext (productPV_eq_integral u f R hR)
  rw [he]
  apply continuous_iff_continuousAt.mpr
  intro z
  apply continuousAt_of_dominated (bound:=fun _ => 2*((_root_.OAI.SchwartzMap.globalLipschitzConstant f):ℝ))
  · filter_upwards [] with z
    apply Measurable.aestronglyMeasurable
    unfold productPVIntegrand productSlopeSample
    fun_prop
  · exact Eventually.of_forall fun z => Eventually.of_forall (productPVIntegrand_bound u hub f z)
  · exact integrable_const _
  · filter_upwards [] with t
    unfold productPVIntegrand productSlopeSample
    fun_prop

end LipschitzHilbert.PacketRepresentation

end

end OAI
