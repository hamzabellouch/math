import OAI.Analysis.LipschitzHilbert.Trees.SourceExponentialIntegral
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

namespace OAI

/-! Finite sums of the exact packet-path exponentials may be integrated
against bounded Hilbert-valued tests on a bounded exhaustion. -/

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace
namespace LipschitzHilbert
variable {X σ κ : Type*} [MeasurableSpace X] [Fintype κ]

theorem source_affine_exp_integrable (μ : Measure X)
    (a c d : X → ℂ) (ha : Measurable a) (hc : Measurable c) (hd : Measurable d)
    (haint : Integrable a μ) (B : ℝ) (hB : 0 ≤ B)
    (hcB : ∀ x, ‖c x‖ ≤ B) (hdB : ∀ x, ‖d x‖ ≤ B) (z : ℂ) :
    Integrable (fun x => a x*Complex.exp (c x+z*d x)) μ := by
  apply (haint.norm.mul_const (Real.exp (B+‖z‖*B))).mono'
    (ha.mul (Complex.continuous_exp.measurable.comp (hc.add (hd.const_mul z)))).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  change ‖a x*Complex.exp (c x+z*d x)‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (source_affine_exp_norm_le hB (norm_nonneg z) (hcB x) (hdB x) le_rfl) (norm_nonneg _)

theorem source_integral_finset_affine_exp_entire (μ : Measure X) (S : Finset σ)
    (a c d : σ → X → ℂ) (ha : ∀ s ∈ S, Measurable (a s))
    (hc : ∀ s ∈ S, Measurable (c s)) (hd : ∀ s ∈ S, Measurable (d s))
    (haint : ∀ s ∈ S, Integrable (a s) μ) (B : σ → ℝ) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hcB : ∀ s ∈ S, ∀ x, ‖c s x‖ ≤ B s) (hdB : ∀ s ∈ S, ∀ x, ‖d s x‖ ≤ B s) :
    Differentiable ℂ (fun z => ∫ x, ∑ s ∈ S, a s x*Complex.exp (c s x+z*d s x) ∂μ) := by
  have heq : (fun z => ∫ x, ∑ s ∈ S, a s x*Complex.exp (c s x+z*d s x) ∂μ) =
      fun z => ∑ s ∈ S, ∫ x, a s x*Complex.exp (c s x+z*d s x) ∂μ := by
    funext z
    exact integral_finsetSum S (fun s hs => source_affine_exp_integrable μ _ _ _
      (ha s hs) (hc s hs) (hd s hs) (haint s hs) (B s) (hB s hs) (hcB s hs) (hdB s hs) z)
  rw [heq]
  apply Differentiable.fun_sum
  intro s hs
  exact source_integral_affine_exp_entire μ _ _ _ (ha s hs) (hc s hs) (hd s hs)
    (haint s hs) (B s) (hB s hs) (hcB s hs) (hdB s hs)

theorem source_integral_finite_exponential_pairing_entire
    (μ : Measure X) [IsFiniteMeasure μ] (S : Finset σ)
    (v : σ → X → EuclideanSpace ℂ κ) (c d : σ → X → ℂ)
    (hv : ∀ s ∈ S, Measurable (v s)) (hc : ∀ s ∈ S, Measurable (c s))
    (hd : ∀ s ∈ S, Measurable (d s)) (V B : σ → ℝ) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hvV : ∀ s ∈ S, ∀ x, ‖v s x‖ ≤ V s)
    (hcB : ∀ s ∈ S, ∀ x, ‖c s x‖ ≤ B s) (hdB : ∀ s ∈ S, ∀ x, ‖d s x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b)
    (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x,
      ⟪b x,∑ s ∈ S, Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) := by
  have hpint (s : σ) (hs : s ∈ S) : Integrable (fun x => ⟪b x,v s x⟫_ℂ) μ := by
    apply (integrable_const (|T| * |V s|)).mono' (hb.inner (hv s hs)).aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro x
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul ((hbT x).trans (le_abs_self _)) ((hvV s hs x).trans (le_abs_self _))
        (norm_nonneg _) (abs_nonneg _))
  simp_rw [inner_sum,inner_smul_right,mul_comm (Complex.exp _) _]
  exact source_integral_finset_affine_exp_entire μ S (fun s x => ⟪b x,v s x⟫_ℂ) c d
    (fun s hs => hb.inner (hv s hs)) hc hd hpint B hB hcB hdB

theorem source_integral_finite_exponential_pairing_entire_on
    (μ : Measure X) [IsFiniteMeasure μ] (S : Finset σ) (A : Set X) (hA : MeasurableSet A)
    (v : σ → X → EuclideanSpace ℂ κ) (c d : σ → X → ℂ)
    (hv : ∀ s ∈ S, Measurable (v s)) (hc : ∀ s ∈ S, Measurable (c s))
    (hd : ∀ s ∈ S, Measurable (d s)) (V B : σ → ℝ)
    (hV : ∀ s ∈ S, 0 ≤ V s) (hB : ∀ s ∈ S, 0 ≤ B s)
    (hvV : ∀ s ∈ S, ∀ x ∈ A, ‖v s x‖ ≤ V s)
    (hcB : ∀ s ∈ S, ∀ x ∈ A, ‖c s x‖ ≤ B s)
    (hdB : ∀ s ∈ S, ∀ x ∈ A, ‖d s x‖ ≤ B s)
    (b : X → EuclideanSpace ℂ κ) (hb : Measurable b)
    (T : ℝ) (hbT : ∀ x, ‖b x‖ ≤ T) :
    Differentiable ℂ (fun z => ∫ x in A,
      ⟪b x,∑ s ∈ S, Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) := by
  classical
  let v' := fun s => A.indicator (v s)
  let c' := fun s => A.indicator (c s)
  let d' := fun s => A.indicator (d s)
  have hv' : ∀ s ∈ S, Measurable (v' s) := fun s hs => (hv s hs).indicator hA
  have hc' : ∀ s ∈ S, Measurable (c' s) := fun s hs => (hc s hs).indicator hA
  have hd' : ∀ s ∈ S, Measurable (d' s) := fun s hs => (hd s hs).indicator hA
  have hvV' : ∀ s ∈ S, ∀ x, ‖v' s x‖ ≤ V s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [v',Set.indicator_of_mem hx] using hvV s hs x hx
    · simpa only [v',Set.indicator_of_notMem hx,norm_zero] using hV s hs
  have hcB' : ∀ s ∈ S, ∀ x, ‖c' s x‖ ≤ B s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [c',Set.indicator_of_mem hx] using hcB s hs x hx
    · simpa only [c',Set.indicator_of_notMem hx,norm_zero] using hB s hs
  have hdB' : ∀ s ∈ S, ∀ x, ‖d' s x‖ ≤ B s := by
    intro s hs x
    by_cases hx : x ∈ A
    · simpa only [d',Set.indicator_of_mem hx] using hdB s hs x hx
    · simpa only [d',Set.indicator_of_notMem hx,norm_zero] using hB s hs
  have heq : (fun z => ∫ x in A, ⟪b x,∑ s ∈ S,
      Complex.exp (c s x+z*d s x) • v s x⟫_ℂ ∂μ) =
      (fun z => ∫ x in A, ⟪b x,∑ s ∈ S,
      Complex.exp (c' s x+z*d' s x) • v' s x⟫_ℂ ∂μ) := by
    funext z
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hA] with x hx
    simp only [v',c',d',Set.indicator_of_mem hx]
  rw [heq]
  exact source_integral_finite_exponential_pairing_entire (μ.restrict A) S v' c' d'
    hv' hc' hd' V B hB hvV' hcB' hdB' b hb T hbT

end LipschitzHilbert

end

end OAI
