import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldEndpointLoss
import OAI.Probability.InvariantIsing.Fields.FieldCanonicalRootLaw

namespace OAI

/-! The constrained recursion loss, averaged over the actual biased root,
is bounded by the averaged terminal loss. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldStepIncrements (h : FieldStep) :
    List.ofFn (fun i : Fin h.depth => (chainExponent h.cut i, fieldStepVariance h i)) =
      scalarFieldIncrements h := by
  unfold scalarFieldIncrements
  apply congrArg List.ofFn
  funext i
  apply Prod.ext
  · rw [chainExponent_apply h.cut i.isLt]
    rfl
  · simp only [fieldStepVariance, dite_eq_left i.isLt, scalarFieldIncrements, List.get_ofFn]
    congr 3


lemma restrictedFieldRecursion_biased_root_integrable {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    Integrable (restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h))
      (Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) := by
  have hr := restrictedFieldRecursion_regular hN S hS h.depth (chainExponent h.cut)
    (fieldStepVariance h) (fun i hi => ((chainExponent_admissible h.ordered_cut h.first h.last).1 i hi).1)
  exact integrable_linearGrowth_pi _ (fun _ => IsGaussian.integrable_id) _ hr.1 hr.2

theorem restrictedFieldRecursion_root_loss {N : ℕ} (hN : 0 < N)
    (S : Finset (Spin N)) (hS : S.Nonempty) (h : FieldStep) (b : Fin N → ℝ) :
    (∫ z, restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut) (fieldStepVariance h) z -
      restrictedFieldRecursion S h.depth (chainExponent h.cut) (fieldStepVariance h) z
      ∂Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))) ≤
    ∫ y, restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
      ∂fieldCanonicalVectorLaw N h b := by
  let μ := Measure.pi (fun i => gaussianReal (b i) (NNReal.mk (h.height 0) (h.nonneg 0)))
  let η := fieldVectorTailEndpointKernel N (scalarFieldIncrements h) (scalarFieldIncrements_positive h)
  let D := fun y => restrictedFieldTerminal Finset.univ y - restrictedFieldTerminal S y
  have hD := restrictedFieldTerminal_loss_regular S hS
  have hi : Integrable D (η ∘ₘ μ) := by
    rw [fieldCanonicalVectorLaw_root]
    exact fieldCanonicalVectorLaw_linear_integrable N h b D hD.1 hD.2
  have ho : Integrable (fun z => ∫ y, D y ∂η z) μ := by
    rw [Measure.comp_eq_comp_const_apply] at hi
    simpa only [Kernel.const_apply] using hi.integral_comp
  have hl := (restrictedFieldRecursion_biased_root_integrable hN Finset.univ
    Finset.univ_nonempty h b).sub (restrictedFieldRecursion_biased_root_integrable hN S hS h b)
  have hb := chainExponent_admissible h.ordered_cut h.first h.last
  calc
    _ ≤ ∫ z, ∫ y, D y ∂η z ∂μ := by
      apply integral_mono hl ho
      intro z
      have he := restrictedFieldRecursion_endpoint_loss hN S hS h.depth
        (chainExponent h.cut) (fieldStepVariance h) (fun i hi => (hb.1 i hi).1)
        (fun i hi => (hb.1 i hi).2.le) z
      change restrictedFieldRecursion Finset.univ h.depth (chainExponent h.cut)
        (fieldStepVariance h) z - restrictedFieldRecursion S h.depth (chainExponent h.cut)
        (fieldStepVariance h) z ≤ _
      simpa only [fieldStepIncrements] using he
    _ = ∫ y, D y ∂(η ∘ₘ μ) := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      exact (Kernel.integral_comp hi).symm
    _ = _ := by rw [fieldCanonicalVectorLaw_root]

end InvariantIsing

end

end OAI
