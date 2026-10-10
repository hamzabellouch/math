import OAI.Probability.InvariantIsing.Fields.FieldSpinTransition
import OAI.Probability.InvariantIsing.Arrays.NSpinTensorBackwardDerivative

namespace OAI

/-! Spatial differentiation of the scalar Gaussian operator. The payoff
may grow linearly; only its derivative is bounded. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter Set
open scoped NNReal Topology

namespace InvariantIsing

lemma fieldSpinTransition_eq_shifted (ζ : ℝ) (v : ℝ≥0) {F a : ℝ → ℝ}
    (hF : Measurable F) (ha : Measurable a) (z : ℝ) :
    fieldSpinTransition ζ v F a z =
      ∫ u, a (z + u) ∂(gaussianReal 0 v).tilted (fun u => ζ * F (z + u)) := by
  rw [fieldSpinTransition, integral_tilted_eq_div, integral_tilted_eq_div]
  have hm : Measurable (fun u => Real.exp (ζ * F u) * a u) :=
    (hF.const_mul ζ).exp.mul ha
  rw [field_gaussian_integral_shift v z hm,
    field_gaussian_integral_shift v z (hF.const_mul ζ).exp]

lemma gaussianOperator_eq_logMean_shift {ζ : ℝ} (hζ : ζ ≠ 0)
    (v : ℝ≥0) {F : ℝ → ℝ} (hF : Measurable F) (z : ℝ) :
    gaussianOperator ζ v F z =
      logMean ζ (gaussianReal 0 v) (fun u => F (z + u)) := by
  rw [gaussianOperator_eq_gaussian_exp_integral hζ v hF,
    field_gaussian_integral_shift v z (hF.const_mul ζ).exp, logMean]
  ring

lemma hasDerivAt_gaussianOperator (ζ : ℝ) (v : ℝ≥0) {F D : ℝ → ℝ}
    (hF : Measurable F) (hG : HasLinearGrowth F) (hD : Measurable D)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ u, |D u| ≤ K)
    (hd : ∀ u, HasDerivAt F (D u) u) (z : ℝ) :
    HasDerivAt (gaussianOperator ζ v F) (fieldSpinTransition ζ v F D z) z := by
  have hshift (s u : ℝ) :
      HasDerivAt (fun q => F (q + u)) (D (s + u)) s := by
    convert (hd (s + u)).comp s ((hasDerivAt_id s).add_const u) using 1 <;>
      first | rfl | simp only [mul_one]
  have hm (s : ℝ) : Measurable (fun u => F (s + u)) :=
    hF.comp (measurable_const.add measurable_id)
  have hDm (s : ℝ) : Measurable (fun u => D (s + u)) :=
    hD.comp (measurable_const.add measurable_id)
  by_cases hζ : ζ = 0
  · subst ζ
    have hi := field_gaussian_linear_integrable v 0 (hm z) (hG.add_left z)
    obtain ⟨_, hI⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (Ioo_mem_nhds (by linarith : z - 1 < z) (by linarith : z < z + 1))
      (Eventually.of_forall fun s => (hm s).aestronglyMeasurable) hi
      (hDm z).aestronglyMeasurable
      (ae_of_all _ fun u s _ => by simpa only [Real.norm_eq_abs] using hbound (s + u))
      (integrable_const K) (ae_of_all _ fun u s _ => hshift s u)
    have he : gaussianOperator 0 v F = fun s => ∫ u, F (s + u) ∂gaussianReal 0 v := by
      funext s
      rw [gaussianOperator_eq_gaussian_integral v hF,
        field_gaussian_integral_shift v s hF]
    rw [he, fieldSpinTransition_eq_shifted 0 v hF hD]
    simpa only [zero_mul, tilted_const] using hI
  · have hi := integrable_exp_of_linearGrowth (gaussianReal 0 v)
      (gaussianReal_exponentialNormMoments 0 v) (hm z) (hG.add_left z) ζ
    have h := hasDerivAt_logMean_of_bounded_derivative (gaussianReal 0 v)
      (fun s u => F (s + u)) (fun s u => D (s + u)) hm hDm hK
      (fun s u => hbound (s + u)) hshift hζ z hi
    have he : gaussianOperator ζ v F =
        fun s => logMean ζ (gaussianReal 0 v) (fun u => F (s + u)) := by
      funext s
      exact gaussianOperator_eq_logMean_shift hζ v hF s
    rw [he, fieldSpinTransition_eq_shifted ζ v hF hD]
    exact h

end InvariantIsing

end

end OAI
