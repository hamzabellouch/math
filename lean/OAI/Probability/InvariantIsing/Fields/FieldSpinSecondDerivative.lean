import OAI.Probability.InvariantIsing.Fields.FieldTiltAverageDerivative

namespace OAI

/-! The derivative of the actual scalar spin transition, with a
linearly growing potential. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

theorem hasDerivAt_fieldSpinTransition (ζ : ℝ) (v : ℝ≥0)
    {F D a b : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    (hD : Measurable D) (ha : Measurable a) (hb : Measurable b)
    {C M L : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ u, |D u| ≤ C) (hab : ∀ u, |a u| ≤ M) (hbb : ∀ u, |b u| ≤ L)
    (hd : ∀ u, HasDerivAt F (D u) u) (had : ∀ u, HasDerivAt a (b u) u)
    (z : ℝ) :
    HasDerivAt (fieldSpinTransition ζ v F a)
      (fieldSpinTransition ζ v F b z + ζ *
        (fieldSpinTransition ζ v F (fun u => a u * D u) z -
          fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z)) z := by
  have hi := integrable_exp_of_linearGrowth (gaussianReal 0 v)
    (gaussianReal_exponentialNormMoments 0 v)
    (hF.comp (measurable_const.add measurable_id)) (hG.add_left z) ζ
  have hd' (s u : ℝ) : HasDerivAt (fun q => F (q + u)) (D (s + u)) s := by
    convert (hd (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have ha' (s u : ℝ) : HasDerivAt (fun q => a (q + u)) (b (s + u)) s := by
    convert (had (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have h := hasDerivAt_tiltAverage_of_bounded_derivatives (gaussianReal 0 v)
    (fun s u => F (s + u)) (fun s u => a (s + u))
    (fun s u => D (s + u)) (fun s u => b (s + u))
    (fun s => hF.comp (measurable_const.add measurable_id))
    (fun s => ha.comp (measurable_const.add measurable_id))
    (fun s => hD.comp (measurable_const.add measurable_id))
    (fun s => hb.comp (measurable_const.add measurable_id))
    hC hM (fun s u => hDb (s + u)) (fun s u => hab (s + u))
    (fun s u => hbb (s + u)) hd' ha' ζ z hi
  have he : fieldSpinTransition ζ v F a =
      fun s => ∫ u, a (s + u) ∂(gaussianReal 0 v).tilted (fun u => ζ * F (s + u)) := by
    funext s
    exact fieldSpinTransition_eq_shifted ζ v hF ha s
  have hADm : Measurable (fun u => a u * D u) := ha.mul hD
  rw [he, fieldSpinTransition_eq_shifted ζ v hF hb,
    fieldSpinTransition_eq_shifted ζ v hF hADm,
    fieldSpinTransition_eq_shifted ζ v hF hD]
  exact h

lemma fieldSpinTransition_derivative_bound (ζ : ℝ) (v : ℝ≥0)
    {F D a b : ℝ → ℝ} (hF : Measurable F) (hG : HasLinearGrowth F)
    {C M L : ℝ} (_hC : 0 ≤ C) (hM : 0 ≤ M)
    (hDb : ∀ u, |D u| ≤ C) (hab : ∀ u, |a u| ≤ M) (hbb : ∀ u, |b u| ≤ L)
    (z : ℝ) :
    |fieldSpinTransition ζ v F b z + ζ *
      (fieldSpinTransition ζ v F (fun u => a u * D u) z -
        fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z)| ≤
      L + 2 * |ζ| * M * C := by
  have hAD : ∀ u, |a u * D u| ≤ M * C := fun u => by
    rw [abs_mul]
    exact mul_le_mul (hab u) (hDb u) (abs_nonneg _) hM
  have hb' := fieldSpinTransition_bound ζ v hF hG hbb z
  have ha' := fieldSpinTransition_bound ζ v hF hG hab z
  have hd' := fieldSpinTransition_bound ζ v hF hG hDb z
  have had' := fieldSpinTransition_bound ζ v hF hG hAD z
  refine (abs_add_le _ _).trans (add_le_add hb' ?_)
  rw [abs_mul]
  calc
    _ ≤ |ζ| * (|fieldSpinTransition ζ v F (fun u => a u * D u) z| +
        |fieldSpinTransition ζ v F a z * fieldSpinTransition ζ v F D z|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg ζ)
    _ ≤ |ζ| * (M * C + M * C) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg ζ)
      apply add_le_add had'
      rw [abs_mul]
      exact mul_le_mul ha' hd' (abs_nonneg _) hM
    _ = _ := by ring

end InvariantIsing

end

end OAI
