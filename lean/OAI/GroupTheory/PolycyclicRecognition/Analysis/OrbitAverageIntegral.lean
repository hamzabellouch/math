import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteOrbitAverage
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace OAI

/-! # Integrals of finite orbit averages

Convex averaging preserves integrals against an invariant measure, including
its restriction to an almost invariant measurable set.
-/

noncomputable section

namespace PolycyclicRecognition

open MeasureTheory Set
open scoped ENNReal

variable {G X : Type*} [Group G] [MeasurableSpace X]
  [MulAction G X] [MeasurableConstSMul G X]
  (ν : Measure X) [SMulInvariantMeasure G X ν]

/-- Restricting an invariant measure to an almost invariant set is invariant. -/
theorem smulInvariantMeasure_restrict_ae (s : Set X) (hs : MeasurableSet s)
    (hi : ∀ g : G, (g • ·) ⁻¹' s =ᵐ[ν] s) : SMulInvariantMeasure G X (ν.restrict s) := by
  refine ⟨fun g t ht => ?_⟩
  have hp := (measurePreserving_smul g ν).restrict_preimage hs
  rw [Measure.restrict_congr_set (hi g)] at hp
  rw [← Measure.map_apply (measurable_const_smul g) ht, hp.map_eq]

/-- Finite convex averaging preserves every nonnegative integral. -/
theorem FiniteOrbitAverage.lintegral (A : FiniteOrbitAverage G) (f : X → ℝ)
    (hf : Measurable f) (hn : ∀ x, 0 ≤ f x) :
    (∫⁻ x, ENNReal.ofReal (A.apply f x) ∂ν) = ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
  have he (x : X) : ENNReal.ofReal (A.apply f x) =
      ∑ i, ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x)) := by
    rw [FiniteOrbitAverage.apply, ENNReal.ofReal_sum_of_nonneg
      (fun i _ => mul_nonneg (A.nonneg i) (hn _))]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_mul (A.nonneg i)
  simp_rw [he]
  have hm (i : A.index) : Measurable (fun x : X =>
      ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp
      (hf.comp (measurable_const_smul _)))
  rw [lintegral_finsetSum Finset.univ (fun i _ => hm i)]
  have hi (i : A.index) :
      (∫⁻ x, ENNReal.ofReal (A.weight i) * ENNReal.ofReal (f ((A.element i)⁻¹ • x)) ∂ν) =
        ENNReal.ofReal (A.weight i) * ∫⁻ x, ENNReal.ofReal (f x) ∂ν := by
    have hmf : Measurable (fun x : X => ENNReal.ofReal (f ((A.element i)⁻¹ • x))) :=
      ENNReal.measurable_ofReal.comp (hf.comp (measurable_const_smul _))
    rw [lintegral_const_mul _ hmf]
    exact congrArg (fun z => ENNReal.ofReal (A.weight i) * z)
      ((measurePreserving_smul (A.element i)⁻¹ ν).lintegral_comp
        (show Measurable (fun x : X => ENNReal.ofReal (f x)) from
          ENNReal.measurable_ofReal.comp hf))
  simp_rw [hi]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => A.nonneg i), A.mass]
  simp

end PolycyclicRecognition

end

end OAI
