import OAI.Probability.InvariantIsing.Fields.FieldEndpointProduct
import OAI.Probability.InvariantIsing.Fields.FieldEndpointMoment

namespace OAI

/-! Integrability of linear-growth vector observables under the actual
canonical endpoint law, uniformly allowing zero-variance increments. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
open scoped BigOperators NNReal

namespace InvariantIsing

lemma integrable_linearGrowth_pi {N : ℕ} (ν : Fin N → Measure ℝ)
    [∀ i, IsProbabilityMeasure (ν i)] (hν : ∀ i, Integrable (fun x : ℝ => x) (ν i))
    (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (Measure.pi ν) := by
  obtain ⟨C, L, _, hL, hb⟩ := hG
  have hi (i : Fin N) : Integrable (fun z : Fin N → ℝ => |z i|) (Measure.pi ν) := by
    exact (measurePreserving_eval ν i).integrable_comp_of_integrable (hν i).abs
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  apply ((integrable_const C).add (hsum.const_mul L)).mono' hF.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs]
  apply (hb z).trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ hL
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg (z i)))).mpr
  intro i
  simpa only [Real.norm_eq_abs] using
    (Finset.single_le_sum (fun j _ => abs_nonneg (z j)) (Finset.mem_univ i))

lemma fieldTailEndpointKernel_integrable_id (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1) (z : ℝ) :
    Integrable (fun y : ℝ => y) (fieldTailEndpointKernel L hL z) := by
  have hp := (fieldTailEndpointKernel_mgf L hL hB 1 z).1
  have hn := (fieldTailEndpointKernel_mgf L hL hB (-1) z).1
  apply (hp.add hn).mono' measurable_id.aestronglyMeasurable
  apply ae_of_all
  intro y
  rw [Real.norm_eq_abs]
  simp only [one_mul, neg_one_mul, Pi.add_apply, id_eq]
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
    linarith [Real.add_one_le_exp y, Real.exp_pos (-y)]
  · rw [abs_of_nonpos (le_of_not_ge hy)]
    linarith [Real.add_one_le_exp (-y), Real.exp_pos y]

lemma fieldVectorTailEndpointKernel_integrable (N : ℕ) (L : List (ℝ × ℝ≥0))
    (hL : ∀ av ∈ L, 0 < av.1) (hB : ∀ av ∈ L, av.1 ≤ 1)
    (z : Fin N → ℝ) (F : (Fin N → ℝ) → ℝ) (hF : Measurable F) (hG : HasLinearGrowth F) :
    Integrable F (fieldVectorTailEndpointKernel N L hL z) := by
  rw [fieldVectorTailEndpointKernel_product]
  exact integrable_linearGrowth_pi _ (fun i => fieldTailEndpointKernel_integrable_id L hL hB (z i))
    F hF hG

end InvariantIsing

end

end OAI
