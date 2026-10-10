import OAI.Analysis.IrrationalRotation.Rotation.ContinuousWeightParameterBridge
import OAI.Analysis.IrrationalRotation.Rotation.RotationTransferIntertwining

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem measurable_complexParameterWeight :
    Measurable (fun x => (p.measurableWeight θ x : ℂ)) :=
  Complex.continuous_ofReal.measurable.comp hp.measurable_parameter_weight

theorem norm_complexParameterWeight_le_one (x : Circle) :
    ‖(p.measurableWeight θ x : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hp.parameter_weight_mem_Ioc x).1] using (hp.parameter_weight_mem_Ioc x).2

theorem continuousWeight_parameter_factor_ae (d : BackgroundBumpData θ) :
    ∀ᵐ x ∂circleMeasure,
      (Real.exp (p.continuousTransfer θ d (x + (θ : Circle))) : ℂ) *
        (p.continuousWeight θ d x : ℂ) =
      (Real.exp (-1) : ℂ) * (p.measurableWeight θ x : ℂ) *
        (Real.exp (p.continuousTransfer θ d x) : ℂ) := by
  obtain ⟨s, _hs, hfull, _hinv, hfactor⟩ :=
    hp.exists_continuousWeight_parameter_factor_domain d
  have hae : ∀ᵐ x ∂circleMeasure, x ∈ s := ae_iff.mpr hfull
  filter_upwards [hae] with x hx
  have hreal := hfactor x hx (0 : ℤ)
  simp only [zero_add, zpow_one, zpow_zero, Equiv.Perm.one_apply, Equiv.coe_addRight] at hreal
  exact_mod_cast hreal

theorem parameter_weightedOperator_mem_algebra :
    Rotation.U * Rotation.measurableRepresentation θ
      (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
      hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one ∈
        Rotation.algebra θ :=
  Rotation.U_mul_measurableRepresentation_mem_algebra θ _ _ _ _ _

theorem continuousWeight_natural_intertwining (d : BackgroundBumpData θ) :
    let f : C(Circle, ℝ) :=
      ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
    let H := Rotation.exponentialTransfer θ (p.continuousTransfer θ d)
    let Tstar := Rotation.U * Rotation.measurableRepresentation θ
      (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
      hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    ∀ ξ : H.domain, ∃ hD : Rotation.weightedReal θ f ξ.val ∈ H.domain,
      H ⟨Rotation.weightedReal θ f ξ.val, hD⟩ =
        (Real.exp (-1) : ℂ) • Tstar (H ξ) := by
  dsimp only
  intro ξ
  let f : C(Circle, ℝ) :=
    ⟨p.continuousWeight θ d, (hp.isContinuousCircleWeight_continuousWeight d).1⟩
  refine ⟨Rotation.weightedReal_mem_exponentialTransfer_domain θ
    (p.continuousTransfer θ d) f (fun x => (p.measurableWeight θ x : ℂ)) 1
    zero_le_one hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    (Real.exp (-1) : ℂ) (hp.continuousWeight_parameter_factor_ae d) ξ, ?_⟩
  exact Rotation.exponentialTransfer_weightedReal θ (p.continuousTransfer θ d) f
    (fun x => (p.measurableWeight θ x : ℂ)) 1 zero_le_one
    hp.measurable_complexParameterWeight hp.norm_complexParameterWeight_le_one
    (Real.exp (-1) : ℂ) (hp.continuousWeight_parameter_factor_ae d) ξ

omit hp in

theorem continuousTransfer_operator_properties (d : BackgroundBumpData θ) :
    let H := Rotation.exponentialTransfer θ (p.continuousTransfer θ d)
    Dense (H.domain : Set Rotation.Hilbert) ∧ IsSelfAdjoint H ∧ H.IsClosed ∧
      Function.Injective H ∧ (∀ ξ : H.domain, 0 ≤ (inner ℂ ξ.val (H ξ)).re) := by
  exact ⟨Rotation.dense_exponentialTransfer_domain θ (measurable_continuousTransfer d),
    Rotation.exponentialTransfer_selfAdjoint θ (measurable_continuousTransfer d),
    Rotation.exponentialTransfer_isClosed θ (measurable_continuousTransfer d),
    Rotation.exponentialTransfer_injective θ _,
    Rotation.exponentialTransfer_nonnegative θ _⟩

end Invariant233.CircleParameterLaws

end

end OAI
