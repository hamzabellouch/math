import Mathlib
import OAI.Analysis.CoulombRadii.FormDomain.L2MeasureInclusion

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set
open scoped BigOperators ENNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open MeasureTheory Set Filter
open scoped ENNReal NNReal ContDiff
open scoped Classical
open scoped BigOperators ComplexConjugate
open scoped Classical
open scoped Classical
open MeasureTheory Set Filter
open scoped Classical ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter Module Module.End TopologicalSpace Function
open scoped Classical ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology SchwartzMap FourierTransform ComplexConjugate
namespace Coulomb
variable {Y ι : Type*} [MeasurableSpace Y] [Countable ι]

lemma integrable_tsum_of_summable_norm_integral {ν : Measure Y} {F : ι → Y → ℝ}
    (hF : ∀ i, Integrable (F i) ν) (hs : Summable (fun i => ∫ y, ‖F i y‖ ∂ν)) :
    Integrable (fun y => ∑' i, F i y) ν ∧ ∀ᵐ y ∂ν, Summable (fun i => F i y) := by
  let f : ι → Lp ℝ 1 ν := fun i => (hF i).toL1 (F i)
  have hn (i : ι) : ‖f i‖ = ∫ y, ‖F i y‖ ∂ν := by
    rw [Integrable.norm_toL1_eq_lintegral_norm]
    exact (integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
      (hF i).norm.aestronglyMeasurable).symm
  have he : ∑' i, ‖f i‖ₑ ≠ ⊤ := by
    apply tsum_enorm_ne_top_iff_summable_norm.mpr
    simpa only [hn] using hs
  have ha : ∀ᵐ y ∂ν, ∀ i, f i y = F i y := ae_all_iff.mpr (fun i => (hF i).coeFn_toL1)
  have hb := Lp.hasSum_coeFn_tsum he
  have hc : (fun y => ∑' i, F i y) =ᵐ[ν] (∑' i, f i : Lp ℝ 1 ν) := by
    filter_upwards [ha, hb] with y hy hz
    simpa only [hy] using hz.tsum_eq
  refine ⟨(L1.integrable_coeFn (∑' i, f i)).congr hc.symm, ?_⟩
  filter_upwards [ha, hb] with y hy hz
  simpa only [hy] using hz.summable

lemma l2_weighted_density_integrable {ν : Measure Y} (u : ι → Lp ℂ 2 ν) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hs : Summable (fun i => w i * ‖u i‖^2)) :
    Integrable (fun y => ∑' i, w i * ‖u i y‖^2) ν ∧
      ∀ᵐ y ∂ν, Summable (fun i => w i * ‖u i y‖^2) := by
  apply integrable_tsum_of_summable_norm_integral
  · intro i
    exact ((Lp.memLp (u i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul _
  · simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw _) (sq_nonneg _)),
      integral_const_mul, ← l2_norm_sq] using hs

lemma l2_weighted_density_hasSum {ν : Measure Y} (u : ι → Lp ℂ 2 ν) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : HasSum (fun i => w i * ‖u i‖^2) s) :
    (∫ y, ∑' i, w i * ‖u i y‖^2 ∂ν) = s := by
  have hi (i : ι) : Integrable (fun y => w i * ‖u i y‖^2) ν :=
    ((Lp.memLp (u i)).integrable_norm_pow (by norm_num : (2:ℕ) ≠ 0)).const_mul (w i)
  have hn : Summable (fun i => ∫ y, ‖w i * ‖u i y‖^2‖ ∂ν) := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw _) (sq_nonneg _)),
      integral_const_mul, ← l2_norm_sq] using hs.summable
  have h := hasSum_integral_of_summable_integral_norm hi hn
  simp only [integral_const_mul, ← l2_norm_sq] at h
  exact h.unique hs
end Coulomb

end

end OAI
