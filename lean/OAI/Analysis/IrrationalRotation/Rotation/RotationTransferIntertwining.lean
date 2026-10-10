import OAI.Analysis.IrrationalRotation.Rotation.RotationTransfer
import OAI.Analysis.IrrationalRotation.Rotation.RotationMeasurable

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.Rotation

theorem ae_all_action_factor (θ : ℝ) (b : Circle → ℝ) (f g : Circle → ℂ) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * f x =
        c * g x * (Real.exp (b x) : ℂ)) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      (Real.exp (b (action θ (k + 1) x)) : ℂ) * f (action θ k x) =
        c * g (action θ k x) * (Real.exp (b (action θ k x)) : ℂ) := by
  apply ae_all_iff.mpr
  intro k
  have h := (action_measurePreserving θ k).quasiMeasurePreserving.ae hfactor
  filter_upwards [h] with x hx
  have hstep : action θ k x + (θ : Circle) = action θ (k + 1) x := by
    simp only [action, add_zsmul, one_zsmul]
    abel
  simpa only [hstep] using hx

theorem weightedReal_mem_exponentialTransfer_domain
    (θ : ℝ) (b : Circle → ℝ) (f : C(Circle, ℝ))
    (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * (f x : ℂ) =
        c * g x * (Real.exp (b x) : ℂ))
    (ξ : (exponentialTransfer θ b).domain) :
    weightedReal θ f ξ.val ∈ (exponentialTransfer θ b).domain := by
  apply WeightedShift.field_operator_mem_multiplierDomain
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))
    (fun x k => ((f (action θ k x)) : ℂ))
    (fun x k => g (action θ k x)) c
    (weightedReal θ f) (U * measurableRepresentation θ g C hC hg hb)
  · exact weighted_coordinates_ae θ (complexWeight f)
  · exact U_mul_measurableRepresentation_coordinates_ae θ g C hC hg hb
  · exact ae_all_action_factor θ b (fun x => (f x : ℂ)) g c hfactor

theorem exponentialTransfer_weightedReal
    (θ : ℝ) (b : Circle → ℝ) (f : C(Circle, ℝ))
    (g : Circle → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) (c : ℂ)
    (hfactor : ∀ᵐ x ∂circleMeasure,
      (Real.exp (b (x + (θ : Circle))) : ℂ) * (f x : ℂ) =
        c * g x * (Real.exp (b x) : ℂ))
    (ξ : (exponentialTransfer θ b).domain) :
    exponentialTransfer θ b
      ⟨weightedReal θ f ξ.val,
        weightedReal_mem_exponentialTransfer_domain θ b f g C hC hg hb c hfactor ξ⟩ =
      c • (U * measurableRepresentation θ g C hC hg hb) (exponentialTransfer θ b ξ) := by
  exact WeightedShift.field_multiplier_intertwines
    (fun x k => (Real.exp (b (action θ k x)) : ℂ))
    (fun x k => ((f (action θ k x)) : ℂ))
    (fun x k => g (action θ k x)) c
    (weightedReal θ f) (U * measurableRepresentation θ g C hC hg hb)
    (weighted_coordinates_ae θ (complexWeight f))
    (U_mul_measurableRepresentation_coordinates_ae θ g C hC hg hb)
    (ae_all_action_factor θ b (fun x => (f x : ℂ)) g c hfactor) ξ

end Invariant233.Rotation

end

end OAI
