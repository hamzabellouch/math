import OAI.Probability.InvariantIsing.Magnetic.RestrictedPairRootEntropy
import OAI.Probability.InvariantIsing.Fields.FieldPairProductLaw

namespace OAI

/-! The unrestricted member of the constrained sampling construction is
exactly the previously evaluated canonical scalar-field law. -/

noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory IsingPerceptron
open scoped NNReal ENNReal BigOperators

namespace InvariantIsing

lemma finiteFieldIncrements_positive (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    ∀ av ∈ List.ofFn (fun i : Fin n => (b i, v i)), 0 < av.1 := by
  intro av hav
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hav
  exact hb i i.isLt

lemma vectorGaussianTransition_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) (a : ℝ) (r : ℝ≥0) :
    vectorGaussianTransition N a r (restrictedFieldRecursion Finset.univ n b v)
      (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n b v hb).1 =
    fieldVectorTransitionKernel N a r
      (fieldScalarValue (List.ofFn (fun i : Fin n => (b i, v i))) (fun y => Real.log (Real.cosh y)))
      (fieldScalarValue_regular _ (finiteFieldIncrements_positive n b v hb)
        measurable_logCosh logCosh_linearGrowth).1 := by
  ext z : 1
  rw [vectorGaussianTransition_eq_tilted hN a r _ _
    (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n b v hb).2,
    fieldVectorTransitionKernel_eq_tilted a r _ _
      (fieldScalarValue_regular _ (finiteFieldIncrements_positive n b v hb)
        measurable_logCosh logCosh_linearGrowth).2]
  congr 1
  funext y
  rw [restrictedFieldRecursion_univ n b v hb]

lemma restrictedTailSpinKernel_univ {N : ℕ} (hN : 0 < N) (n : ℕ)
    (b : ℕ → ℝ) (v : ℕ → ℝ≥0) (hb : ∀ i < n, 0 < b i) :
    restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n b v hb =
      fieldVectorTailSpinKernel N (List.ofFn (fun i : Fin n => (b i, v i)))
        (finiteFieldIncrements_positive n b v hb) := by
  induction n generalizing b v with
  | zero => exact restrictedSpinKernel_univ N
  | succ n ih =>
    let bs := fun j => b (j + 1)
    let vs := fun j => v (j + 1)
    have hbs : ∀ j < n, 0 < bs j := fun j hj => hb (j + 1) (by omega)
    simp only [List.ofFn_succ, fieldVectorTailSpinKernel]
    change restrictedTailSpinKernel hN Finset.univ Finset.univ_nonempty n bs vs hbs ∘ₖ
      vectorGaussianTransition N (b 0) (v 0) (restrictedFieldRecursion Finset.univ n bs vs)
        (restrictedFieldRecursion_regular hN Finset.univ Finset.univ_nonempty n bs vs hbs).1 = _
    rw [ih bs vs hbs, vectorGaussianTransition_univ hN n bs vs hbs]
    rfl

end InvariantIsing

end

end OAI
