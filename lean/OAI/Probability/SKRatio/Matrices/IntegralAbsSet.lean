import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
noncomputable section
open Matrix
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal
namespace SKRatioGaussian
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integral_abs_on_set_le {F : Ω → ℝ} (hF : MemLp F 2 μ)
    {s : Set Ω} (hs : MeasurableSet s) :
    (∫ x in s, |F x| ∂μ) ≤ sqrt (∫ x, (F x)^2 ∂μ)*sqrt (μ.real s) := by
  have hG : MemLp (s.indicator (fun _ : Ω => (1:ℝ))) 2 μ :=
    memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top _ _))
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hF) (by simpa using hG)
  have he : (fun x => ‖F x‖*‖s.indicator (fun _ : Ω => (1:ℝ)) x‖) =
      s.indicator (fun x => |F x|) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx,Real.norm_eq_abs]
  have hg : (fun x => ‖s.indicator (fun _ : Ω => (1:ℝ)) x‖^(2:ℝ)) =
      s.indicator (fun _ : Ω => (1:ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [he,hg,integral_indicator hs,integral_indicator hs] at hh
  simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs,← Real.sqrt_eq_rpow,
    integral_const,smul_eq_mul,mul_one,measureReal_restrict_apply_univ] using hh

omit [IsProbabilityMeasure μ] in
lemma integral_exceptional_equal_bound {F G H : Ω → ℝ} {s : Set Ω}
    (hs : MeasurableSet s) (hF : Integrable F μ) (hG : Integrable G μ)
    (hH : Integrable H μ) (he : ∀ x ∉ s, F x=G x)
    (hb : ∀ x ∈ s, ‖F x-G x‖ ≤ H x) :
    |(∫ x, F x ∂μ)-(∫ x, G x ∂μ)| ≤ ∫ x in s, H x ∂μ := by
  rw [← integral_sub hF hG]
  rw [← Real.norm_eq_abs]
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_indicator hs]
  apply integral_mono ((hF.sub hG).norm) (hH.indicator hs)
  intro x
  change ‖F x-G x‖ ≤ s.indicator H x
  by_cases hx : x∈s
  · simpa only [Set.indicator_of_mem hx] using hb x hx
  · simp only [Set.indicator_of_notMem hx,he x hx,sub_self,norm_zero,le_refl]

end SKRatioGaussian

end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
