import Mathlib
import OAI.Analysis.HardSphere.Comparison.ConditionalLikelihood

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory Function Set Filter
open scoped ENNReal BigOperators
namespace HardSphere.Comparison
open ProbabilityTheory
section ReferenceMeasure
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}
  [∀ i, MeasurableSpace (X i)] {R : Type*} [Fintype R]
  (reference : R → LocalCheck X)
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
omit [∀ i, IsProbabilityMeasure (μ i)] in
lemma lintegral_referenceMeasure (s : Finset ι) (x : ∀ i, X i)
    (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u, f (Function.updateFinset x s u) ∂referenceMeasure reference μ s x) =
      lmarginal μ s (fun y ↦ checkWeight reference s y * f y) x /
        checkNormalizer reference μ s x := by
  change (∫⁻ u, f (Function.updateFinset x s u)
    ∂(Measure.pi (fun i : s ↦ μ i)).withDensity
      (fun u ↦ checkWeight reference s (Function.updateFinset x s u) /
        checkNormalizer reference μ s x)) = _
  have hD : Measurable (fun u : ∀ i : s, X i ↦
      checkWeight reference s (Function.updateFinset x s u) / checkNormalizer reference μ s x) :=
    ((measurable_checkWeight reference s).comp measurable_updateFinset).div_const _
  have hF : Measurable (fun u : ∀ i : s, X i ↦ f (Function.updateFinset x s u)) :=
    hf.comp measurable_updateFinset
  rw [lintegral_withDensity_eq_lintegral_mul (Measure.pi (fun i : s ↦ μ i)) hD hF]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  simp_rw [mul_right_comm _ _ (f _)]
  exact lintegral_mul_const _
    (((measurable_checkWeight reference s).mul hf).comp measurable_updateFinset)

end ReferenceMeasure

variable {ι : Type*} [DecidableEq ι] {X Z : ι → Type*}
  [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
  {R C : Type*} [Fintype R] [Fintype C]
  (reference : R → LocalCheck X) (checks : C → LocalCheck (fun i ↦ X i × Z i))
  (μ : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]
  (κ : ∀ i, Kernel (X i) (Z i)) [∀ i, IsFiniteKernel (κ i)]

theorem conditionalLikelihood_mean (s o : Finset ι) (hso : Disjoint s o)
    {a : ℝ≥0∞} (ha : 0 < a)
    (hκm : ∀ i, ∫⁻ x, κ i x Set.univ ∂μ i = 1)
    (hRef : UniformInsertionOn reference μ a (s ∪ o))
    (hcompat : UniformInsertionOn checks (fun i ↦ (μ i).compProd (κ i)) a s)
    (hOutside : ∀ (x : ∀ i, X i) (z : ∀ i, Z i), x ∈ retainedEvent reference o →
      (fun i ↦ (x i,z i)) ∈ retainedEvent checks o)
    (hincl : ∀ (x : ∀ i, X i) (z : ∀ i, Z i),
      checkWeight checks (s ∪ o) (fun i ↦ (x i,z i)) ≤ checkWeight reference (s ∪ o) x)
    (x : ∀ i, X i) (z : ∀ i, Z i) :
    (∫⁻ u, conditionalLikelihood reference checks μ κ s o
      (Function.updateFinset x (s ∪ o) u) z ∂referenceMeasure reference μ (s ∪ o) x) = 1 := by
  rw [lintegral_referenceMeasure reference μ (s ∪ o) x _
    (measurable_conditionalLikelihood reference checks μ κ s o z)]
  have hm := (measurable_checkWeight reference (s ∪ o)).mul
    (measurable_conditionalLikelihood reference checks μ κ s o z)
  have heq : lmarginal μ s (fun y ↦ checkWeight reference (s ∪ o) y *
      conditionalLikelihood reference checks μ κ s o y z) =
      partialNormalizer reference μ s o := by
    funext y
    exact conditionalLikelihood_marginal reference checks μ κ s o hso ha hκm hcompat
      hOutside hincl y z
  rw [lmarginal_union' μ (fun y ↦ checkWeight reference (s ∪ o) y *
    conditionalLikelihood reference checks μ κ s o y z) hm hso, heq]
  have hZ : lmarginal μ o (partialNormalizer reference μ s o) =
      checkNormalizer reference μ (s ∪ o) := by
    exact (lmarginal_union' μ (checkWeight reference (s ∪ o))
      (measurable_checkWeight reference (s ∪ o)) hso).symm
  rw [hZ]
  exact ENNReal.div_self (ne_of_gt (checkNormalizer_pos_on reference ha (s ∪ o) hRef x))
    (ne_top_of_le_ne_top ENNReal.one_ne_top (checkNormalizer_le_one reference (s ∪ o) x))

end HardSphere.Comparison

end

end OAI
