import OAI.Analysis.RCDHeat.CDSubplan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Order.ProjIcc

namespace OAI

/-! # Endpoint extension of affine means of bounded continuous path tests -/

open Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem continuous_path_mean (π : Measure C(Time,X)) [IsFiniteMeasure π]
    (U : X → ℝ) (hU : Continuous U) (A : ℝ) (hA : ∀ x, |U x| ≤ A) :
    Continuous (fun t : Time => ∫ γ, U (γ t) ∂π) := by
  apply continuous_of_dominated (bound := fun _ => A)
  · intro t
    exact (hU.measurable.comp (measurable_path_eval t)).aestronglyMeasurable
  · exact fun t => Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using hA (γ t)
  · exact integrable_const A
  · exact Eventually.of_forall fun γ => hU.comp γ.continuous

theorem closed_time_affine (F : Time → ℝ) (hF : Continuous F)
    (α β : ℝ) (hopen : ∀ t : Time, 0 < (t:ℝ) → (t:ℝ) < 1 → F t=α*(t:ℝ)+β) :
    ∀ t : Time, F t=(1-(t:ℝ))*F 0+(t:ℝ)*F 1 := by
  let E := IccExtend (show (0:ℝ) ≤ 1 by norm_num) F
  have he : EqOn E (fun t => α*t+β) (Ioo (0:ℝ) 1) := by
    intro t ht
    simpa only [E,IccExtend,Function.comp_apply,projIcc_of_mem (show (0:ℝ) ≤ 1 by norm_num)
      (show t ∈ Icc (0:ℝ) 1 from ⟨ht.1.le,ht.2.le⟩)]
      using hopen ⟨t,ht.1.le,ht.2.le⟩ ht.1 ht.2
  have hec := he.closure hF.Icc_extend' (by fun_prop)
  rw [closure_Ioo (by norm_num : (0:ℝ) ≠ 1)] at hec
  have hall (t : Time) : F t=α*(t:ℝ)+β := by
    simpa only [E,IccExtend,Function.comp_apply,projIcc_val] using hec t.property
  intro t
  rw [hall t,hall 0,hall 1]
  change α*(t:ℝ)+β = (1-(t:ℝ))*(α*0+β)+(t:ℝ)*(α*1+β)
  ring

end RegularPointCoordinates

end

end OAI
