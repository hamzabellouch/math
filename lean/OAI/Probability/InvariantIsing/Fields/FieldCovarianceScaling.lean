import OAI.Probability.InvariantIsing.Fields.FieldRadialBackward

namespace OAI

/-! Exact change of position units between scaled covariance and scaled
terminal log-cosh in the finite one-site field recursion. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set

namespace InvariantIsing

lemma gaussianOperator_scale_position (a v c : ℝ) (hc : 0 ≤ c)
    (F : ℝ → ℝ) (z : ℝ) :
    gaussianOperator a v (fun u => F (c * u)) z =
      gaussianOperator a (c ^ 2 * v) F (c * z) := by
  have hs : Real.sqrt (c ^ 2 * v) = c * Real.sqrt v := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  have he (g : ℝ) : c * (z + Real.sqrt v * g) = c * z + (c * Real.sqrt v) * g := by ring
  simp only [gaussianOperator, hs, he]

lemma gaussianOperator_fold_scale_position (L : List (ℝ × ℝ))
    {c : ℝ} (hc : 0 ≤ c) (F : ℝ → ℝ) (z : ℝ) :
    (L.foldr (fun av f => gaussianOperator av.1 av.2 f) (fun u => F (c * u))) z =
      ((L.map (fun av => (av.1, c ^ 2 * av.2))).foldr
        (fun av f => gaussianOperator av.1 av.2 f) F) (c * z) := by
  induction L generalizing z with
  | nil => rfl
  | cons av L ih =>
    have ht : L.foldr (fun av f => gaussianOperator av.1 av.2 f) (fun u => F (c * u)) =
        fun u => ((L.map (fun av => (av.1, c ^ 2 * av.2))).foldr
          (fun av f => gaussianOperator av.1 av.2 f) F) (c * u) := by
      funext u
      exact ih u
    simp only [List.foldr_cons, List.map_cons, ht]
    exact gaussianOperator_scale_position av.1 av.2 c hc _ z

end InvariantIsing

end

end OAI
