import OAI.Probability.InvariantIsing.Fields.FieldEndpointMoment

namespace OAI

/-! Independent canonical endpoint fields have a total second moment
linear in the block size, uniformly over the cascade depth. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace InvariantIsing

def fieldCanonicalVectorLaw (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    Measure (Fin N → ℝ) :=
  Measure.pi (fun i => fieldCanonicalEndpointLaw h (b i))

instance fieldCanonicalVectorLaw_probability (N : ℕ) (h : FieldStep) (b : Fin N → ℝ) :
    IsProbabilityMeasure (fieldCanonicalVectorLaw N h b) := by
  unfold fieldCanonicalVectorLaw
  infer_instance

lemma fieldCanonicalVectorLaw_coordinate_integrable {N : ℕ} (h : FieldStep)
    (b : Fin N → ℝ) (i : Fin N) :
    Integrable (fun z : Fin N → ℝ => z i ^ 2) (fieldCanonicalVectorLaw N h b) :=
  (measurePreserving_eval (fun j => fieldCanonicalEndpointLaw h (b j)) i).integrable_comp_of_integrable
    (fieldCanonicalEndpointLaw_second_moment h (b i)).1

lemma fieldCanonicalVectorLaw_square_integrable {N : ℕ} (h : FieldStep) (b : Fin N → ℝ) :
    Integrable (fun z : Fin N → ℝ => ∑ i, z i ^ 2) (fieldCanonicalVectorLaw N h b) := by
  exact integrable_finsetSum _ (fun i _ => fieldCanonicalVectorLaw_coordinate_integrable h b i)

theorem fieldCanonicalVectorLaw_second_moment {N : ℕ} (h : FieldStep) (b : Fin N → ℝ)
    {B H : ℝ} (hb : ∀ i, |b i| ≤ B) (hH : h.height (Fin.last h.depth) ≤ H) :
    (∫ z : Fin N → ℝ, ∑ i, z i ^ 2 ∂fieldCanonicalVectorLaw N h b) ≤
      N * (2 * Real.exp (2 * B + 4 * H)) := by
  rw [integral_finsetSum _ (fun i _ => fieldCanonicalVectorLaw_coordinate_integrable h b i)]
  calc
    _ ≤ ∑ _i : Fin N, 2 * Real.exp (2 * B + 4 * H) := by
      apply Finset.sum_le_sum
      intro i _
      have he := (fieldCanonicalEndpointLaw_second_moment h (b i)).2
      have hp : (∫ z : Fin N → ℝ, z i ^ 2 ∂fieldCanonicalVectorLaw N h b) =
          ∫ y : ℝ, y ^ 2 ∂fieldCanonicalEndpointLaw h (b i) :=
        (measurePreserving_eval (fun j => fieldCanonicalEndpointLaw h (b j)) i).hasLaw.integral_comp
          (f := fun y : ℝ => y ^ 2) (by fun_prop)
      rw [hp]
      apply he.trans
      have hab := abs_le.mp (hb i)
      have h₁ : Real.exp (2 * b i + 4 * h.height (Fin.last h.depth)) ≤
          Real.exp (2 * B + 4 * H) := Real.exp_le_exp.mpr (by linarith)
      have h₂ : Real.exp (-2 * b i + 4 * h.height (Fin.last h.depth)) ≤
          Real.exp (2 * B + 4 * H) := Real.exp_le_exp.mpr (by linarith)
      linarith
    _ = _ := by simp

end InvariantIsing

end

end OAI
