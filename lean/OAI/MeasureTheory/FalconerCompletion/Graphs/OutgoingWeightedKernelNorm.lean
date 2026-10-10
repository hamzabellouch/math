import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Angular.InverseEndpointCoefficient

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4PrefixShell
open MeasureTheory Set
open scoped ContDiff
variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin (n+1))

lemma outgoingWeightedKernelND_norm (r s : ℝ) (b : V × V → SmoothFunctionND V)
    (c : V × V → ℂ) (z : V × V) (hs : 0 ≤ s) :
    ‖c z*outgoingWeightedKernelND r s b z‖ =
      (dist z.1 z.2*s)^(-(n:ℝ)/2)*
        ‖c z*(b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))‖ := by
  have hW := Real.rpow_nonneg (mul_nonneg (dist_nonneg (x := z.1) (y := z.2)) hs) (-(n:ℝ)/2)
  simp only [outgoingWeightedKernelND,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg hW]
  have he : ‖Complex.exp (Complex.I*(r*dist z.1 z.2))‖=1 := by simp [Complex.norm_exp]
  rw [he]
  ring

lemma outgoingWeightedKernelND_measurable (s : ℝ) (b : V × V → SmoothFunctionND V)
    (c : V × V → ℂ)
    (hc : Measurable (fun z => c z*(b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2)))) :
    Measurable (fun q : ℝ × (V × V) => c q.2*outgoingWeightedKernelND q.1 s b q.2) := by
  have hw : Measurable (fun q : ℝ × (V × V) =>
      (((dist q.2.1 q.2.2*s)^(-(n:ℝ)/2):ℝ):ℂ)) := by fun_prop
  have hp : Measurable (fun q : ℝ × (V × V) =>
      Complex.exp (Complex.I*(q.1*dist q.2.1 q.2.2))) := by fun_prop
  have hm := (hw.mul hp).mul (hc.comp measurable_snd)
  convert hm using 1
  funext q
  simp only [outgoingWeightedKernelND, Pi.mul_apply, Function.comp_apply]
  ring

lemma outgoingWeightedKernelND_integrable (s : ℝ) (hs : 0 < s)
    (b : V × V → SmoothFunctionND V) (c : V × V → ℂ)
    (μ : Measure (V × V)) [IsFiniteMeasure μ] (r : ℝ) {δ C : ℝ}
    (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂μ, δ ≤ dist z.1 z.2*s)
    (hm : Measurable (fun z => c z*(b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))))
    (hb : ∀ᵐ z ∂μ, ‖c z*(b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2))‖ ≤ C) :
    Integrable (fun z => c z*outgoingWeightedKernelND r s b z) μ := by
  apply Integrable.of_bound ((outgoingWeightedKernelND_measurable s b c hm).comp
    (measurable_const.prodMk measurable_id)).aestronglyMeasurable (δ^(-(n:ℝ)/2)*C)
  filter_upwards [hsep,hb] with z hz hzb
  change ‖c z*outgoingWeightedKernelND r s b z‖ ≤ _
  rw [outgoingWeightedKernelND_norm r s b c z hs.le]
  apply mul_le_mul (Real.rpow_le_rpow_of_nonpos hδ hz
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))) hzb
    (norm_nonneg _) (Real.rpow_nonneg hδ.le _)

lemma weighted_pair_integral_measurableND (s : ℝ)
    (b : V × V → SmoothFunctionND V) (c : V × V → ℂ)
    (μ : Measure (V × V)) [SFinite μ] (L : ℝ)
    (hm : Measurable (fun z => c z*(b z).1 ((dist z.1 z.2)⁻¹ • (z.1-z.2)))) :
    Measurable (fun r => L • ∫ z, c z*outgoingWeightedKernelND r s b z ∂μ) :=
  ((outgoingWeightedKernelND_measurable s b c hm).stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.const_smul L

end Attempt4PrefixShell
end GraphLiteralSupport
end
end

end OAI
