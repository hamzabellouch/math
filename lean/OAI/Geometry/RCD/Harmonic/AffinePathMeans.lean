import OAI.Geometry.RCD.Sobolev.ContinuousAEEqOnTime
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.Normed.Group.Bounded

namespace OAI

/-! # Affine means on every normalized subplan imply affine paths -/

open Set Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem affine_paths_of_normalized_means (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (U : X → ℝ) (hU : Continuous U) (hUc : HasCompactSupport U)
    (hmean : ∀ κ : Measure C(Time,X), κ ≤ π → κ univ ≠ 0 → ∀ t : Time,
      (∫ γ, U (γ t) ∂((κ univ)⁻¹ • κ)) =
        (1-(t:ℝ))*(∫ γ, U (γ 0) ∂((κ univ)⁻¹ • κ))+
          (t:ℝ)*(∫ γ, U (γ 1) ∂((κ univ)⁻¹ • κ))) :
    ∀ᵐ γ ∂π, ∀ t : Time, U (γ t)=(1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1) := by
  obtain ⟨M,hM⟩ := hUc.exists_bound_of_continuous hU
  have hi (ν : Measure C(Time,X)) [IsFiniteMeasure ν] (t : Time) :
      Integrable (fun γ => U (γ t)) ν :=
    Integrable.of_bound (hU.measurable.comp (measurable_path_eval t)).aestronglyMeasurable M
      (Eventually.of_forall fun γ => hM (γ t))
  apply ae_eq_all_time_of_continuous π (fun γ t => U (γ t))
    (fun γ t => (1-(t:ℝ))*U (γ 0)+(t:ℝ)*U (γ 1))
    (Eventually.of_forall fun γ => hU.comp γ.continuous)
    (Eventually.of_forall fun _ => by fun_prop)
  intro t
  let f := fun γ : C(Time,X) => U (γ t)-(1-(t:ℝ))*U (γ 0)-(t:ℝ)*U (γ 1)
  have hif : Integrable f π := ((hi π t).sub ((hi π 0).const_mul _)).sub ((hi π 1).const_mul _)
  have heq : f =ᵐ[π] 0 := by
    apply hif.ae_eq_zero_of_forall_setIntegral_eq_zero
    intro S hS _hSf
    by_cases hz : π S=0
    · rw [Measure.restrict_eq_zero.mpr hz]
      simp
    let κ := π.restrict S
    have hk0 : κ univ ≠ 0 := by simpa only [κ,Measure.restrict_apply_univ] using hz
    have hkt : κ univ ≠ ∞ := measure_ne_top κ univ
    have ha : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hk0
    have ha0 : ((κ univ)⁻¹).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
      ⟨ENNReal.inv_ne_zero.mpr hkt,ha⟩
    have hh := hmean κ Measure.restrict_le_self hk0 t
    have hin (s : Time) : Integrable (fun γ => U (γ s)) ((κ univ)⁻¹ • κ) :=
      (hi κ s).smul_measure ha
    have hfzero : (∫ γ, f γ ∂((κ univ)⁻¹ • κ))=0 := by
      change (∫ γ, U (γ t)-(1-(t:ℝ))*U (γ 0)-(t:ℝ)*U (γ 1) ∂((κ univ)⁻¹ • κ))=0
      rw [integral_sub (f := fun γ : C(Time,X) => U (γ t)-(1-(t:ℝ))*U (γ 0))
          (g := fun γ : C(Time,X) => (t:ℝ)*U (γ 1))
          ((hin t).sub ((hin 0).const_mul (1-(t:ℝ)))) ((hin 1).const_mul (t:ℝ)),
        integral_sub (f := fun γ : C(Time,X) => U (γ t))
          (g := fun γ : C(Time,X) => (1-(t:ℝ))*U (γ 0))
          (hin t) ((hin 0).const_mul (1-(t:ℝ))),integral_const_mul,integral_const_mul]
      linarith only [hh]
    rw [integral_smul_measure,smul_eq_mul] at hfzero
    exact (mul_eq_zero.mp hfzero).resolve_left ha0
  filter_upwards [heq] with γ hγ
  change U (γ t)-(1-(t:ℝ))*U (γ 0)-(t:ℝ)*U (γ 1)=0 at hγ
  linarith only [hγ]

end RegularPointCoordinates

end

end OAI
