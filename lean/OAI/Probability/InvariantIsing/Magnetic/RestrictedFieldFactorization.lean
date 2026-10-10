import OAI.Probability.InvariantIsing.Magnetic.RestrictedFieldRecursion
import OAI.Probability.InvariantIsing.Fields.FieldEndpointProduct
import OAI.Probability.InvariantIsing.Cavity.CavityTiltTransport

namespace OAI

/-! The unrestricted recursion and its canonical transition are exactly
products of the scalar field recursions. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma fieldScalarValue_ofFn (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) :
    fieldScalarValue (List.ofFn (fun i : Fin n => (b i, v i)))
      (fun y => Real.log (Real.cosh y)) =
      cascadeRecursion n b (fun i => gaussianCascadeMarks v i)
        (fun _ p => p.1 + p.2) (fun y => Real.log (Real.cosh y)) := by
  induction n generalizing b v with
  | zero => rfl
  | succ n ih =>
    have ht : ∀ i < n, 0 < b (i + 1) := fun i hi => hb (i + 1) (by omega)
    rw [List.ofFn_succ]
    change gaussianOperator (b 0) (v 0)
      (fieldScalarValue (List.ofFn (fun i : Fin n => (b (i + 1), v (i + 1))))
        (fun y => Real.log (Real.cosh y))) = _
    rw [ih (fun i => b (i + 1)) (fun i => v (i + 1)) ht]
    funext z
    exact gaussianOperator_eq_gaussian_logMean (hb 0 (by omega)).ne' _
      (measurable_cascadeRecursion n _ _ (fun _ => measurable_fst.add measurable_snd)
        measurable_logCosh) z

theorem restrictedFieldRecursion_univ {N : ℕ} (n : ℕ) (b : ℕ → ℝ) (v : ℕ → ℝ≥0)
    (hb : ∀ i < n, 0 < b i) (z : Fin N → ℝ) :
    restrictedFieldRecursion Finset.univ n b v z =
      ∑ i, fieldScalarValue (List.ofFn (fun j : Fin n => (b j, v j)))
        (fun y => Real.log (Real.cosh y)) (z i) := by
  have ht : restrictedFieldTerminal (Finset.univ : Finset (Spin N)) =
      (fun z => ∑ i, Real.log (Real.cosh (z i))) := by
    funext y
    exact restrictedFieldTerminal_univ y
  rw [restrictedFieldRecursion, ht]
  have he := vectorCascade_logCosh_sum N n b v hb (fun _ => 0) z
  simp only [zero_add] at he
  rw [he, fieldScalarValue_ofFn n b v hb]

lemma vectorGaussian_shift {N : ℕ} (v : ℝ≥0) (z : Fin N → ℝ) :
    MeasurePreserving (fun w : Fin N → ℝ => z + w)
      (vectorGaussianLaw N v : Measure (Fin N → ℝ))
      (Measure.pi (fun i => gaussianReal (z i) v)) := by
  apply measurePreserving_pi
  intro i
  refine ⟨measurable_const.add measurable_id, ?_⟩
  change (gaussianReal 0 v).map (fun x : ℝ => z i + x) = gaussianReal (z i) v
  simpa only [zero_add] using gaussianReal_map_const_add (μ := 0) (v := v) (z i)

lemma vectorGaussian_tilt_transition {N : ℕ} (a : ℝ) (v : ℝ≥0)
    (F : ℝ → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) (z : Fin N → ℝ) :
    ((vectorGaussianLaw N v : Measure (Fin N → ℝ)).tilted
      (fun w => a * ∑ i, F ((z + w) i))).map (fun w => z + w) =
        fieldVectorTransitionKernel N a v F hF z := by
  have hm : Measurable (fun y : Fin N → ℝ => a * ∑ i, F (y i)) := by fun_prop
  have he := cavity_tilt_map (vectorGaussianLaw N v : Measure (Fin N → ℝ))
    (fun w => z + w) (measurable_const.add measurable_id) (fun y => a * ∑ i, F (y i)) hm
  rw [(vectorGaussian_shift v z).map_eq, fieldGaussian_product_tilt a v F hF hG z] at he
  exact he

end InvariantIsing

end

end OAI
