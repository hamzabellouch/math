import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius ENNReal NNReal
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius NNReal
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open MeasureTheory.Measure
open scoped ENNReal NNReal MeasureTheory Topology
open MeasureTheory
noncomputable section
noncomputable section
open MeasureTheory Set NormedSpace
open scoped Topology
noncomputable section
open Matrix Real
open scoped BigOperators Matrix.Norms.Frobenius
noncomputable section
open Set Real
open scoped Topology
noncomputable section
open Matrix Set Filter
open scoped Topology Matrix.Norms.Frobenius
noncomputable section
open Matrix NormedSpace ContinuousLinearMap
open scoped Matrix.Norms.Frobenius
namespace SKRatioGaussian.ComplexMatrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma matrix_hasDerivAt_inverse {Q : ℝ → Matrix ι ι ℂ} {Q' : Matrix ι ι ℂ} {t : ℝ}
    (hQ : HasDerivAt Q Q' t) (hunit : IsUnit (Q t)) :
    HasDerivAt (fun s => (Q s)⁻¹) (-(Q t)⁻¹*Q'*(Q t)⁻¹) t := by
  obtain ⟨u, hu⟩ := hunit
  have hfi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hfi
  have hi := hfi.comp_hasDerivAt t hQ
  have hv : (↑u⁻¹ : Matrix ι ι ℂ) = (Q t)⁻¹ := by
    rw [← hu,Matrix.nonsing_inv_eq_ringInverse,Ring.inverse_unit]
  simpa only [Function.comp_def,← Matrix.nonsing_inv_eq_ringInverse,_root_.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply,hv,neg_mul] using! hi

noncomputable def pathResolvent (z b : ℝ) (A M : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1-z • (A*M)+(z^2*b) • A)⁻¹

lemma pathResolvent_derivative (z b : ℝ) (A M E : Matrix ι ι ℂ)
    (hunit : IsUnit (1-z • (A*M)+(z^2*b) • A)) :
    HasDerivAt (fun t : ℝ => pathResolvent z b A (M+t • E))
      (z • (pathResolvent z b A M*A*E*pathResolvent z b A M)) 0 := by
  have hm : HasDerivAt (fun t : ℝ => M+t • E) E 0 := by
    convert! (hasDerivAt_id (0:ℝ)).smul_const E |>.const_add M using 1
    simp only [one_smul]
  have hq := ((hm.const_mul A).const_smul z).const_sub 1 |>.add_const ((z^2*b) • A)
  have hq' : HasDerivAt (fun t : ℝ => 1-z • (A*(M+t • E))+(z^2*b) • A) (-(z • (A*E))) 0 := hq
  have hi := matrix_hasDerivAt_inverse hq' (by simpa using hunit)
  simpa only [pathResolvent,zero_smul,add_zero,mul_neg,neg_mul,smul_neg,neg_neg,mul_smul_comm,smul_mul_assoc,mul_assoc] using! hi

end SKRatioGaussian.ComplexMatrix

noncomputable section
open Matrix

end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI
