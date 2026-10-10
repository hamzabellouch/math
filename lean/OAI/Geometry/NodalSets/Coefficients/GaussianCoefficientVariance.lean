import Mathlib.Probability.Distributions.Gaussian.Multivariate

namespace OAI

namespace Yau.Probability
open MeasureTheory ProbabilityTheory
noncomputable section
variable {ι : Type*} [Fintype ι]

def gaussianPairs : Measure (ι × Fin 2 → ℝ) := Measure.pi (fun _ ↦ gaussianReal 0 1)

def pairLinearSum (z : ι → ℂ) (a : ι × Fin 2 → ℝ) : ℝ :=
  ∑ p, (if p.2 = 0 then (z p.1).re else -(z p.1).im)*a p

lemma variance_pairLinearSum (z : ι → ℂ) :
    Var[pairLinearSum z; gaussianPairs] = ∑ i, ‖z i‖^2 := by
  classical
  have hf : pairLinearSum z = ∑ p : ι × Fin 2, (fun a : ι × Fin 2 → ℝ ↦
      (if p.2 = 0 then (z p.1).re else -(z p.1).im)*a p) := by
    funext a
    simp [pairLinearSum]
  rw [hf]
  unfold gaussianPairs
  rw [variance_sum_pi]
  · change (∑ p : ι × Fin 2, Var[fun x : ℝ ↦
        (if p.2 = 0 then (z p.1).re else -(z p.1).im) * id x; gaussianReal 0 1]) = _
    simp_rw [variance_const_mul,variance_id_gaussianReal]
    simp only [mul_one,NNReal.coe_one,Fintype.sum_prod_type,Fin.sum_univ_succ,
      Fin.isValue,Fin.succ_ne_zero,ite_true,ite_false,Fin.sum_univ_zero,add_zero,neg_sq]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [Complex.normSq_apply,pow_two] using (Complex.sq_norm (z i)).symm
  · exact fun p ↦ IsGaussian.memLp_two_id.const_mul _

end
end Yau.Probability

end OAI
