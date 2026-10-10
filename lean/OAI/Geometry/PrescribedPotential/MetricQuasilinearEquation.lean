import Mathlib
import OAI.Geometry.PrescribedPotential.CalabiConnection
import OAI.Geometry.PrescribedPotential.CalabiRicciContraction

namespace OAI

/-! Metric Quasilinear Equation. -/

section

 

noncomputable section
open Set Filter Topology Matrix
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace KaehlerCalculus.LocalKaehlerField
variable {n : ℕ} (K : LocalKaehlerField n)

lemma metric_quasilinear_equation {z : V n} (hz : z ∈ K.domain) :
    (∑ p, ∑ q, ((K.matrix z)⁻¹ p q) •
      mderiv Complex.I (e q) (mderiv (-Complex.I) (e p) K.matrix) z) =
      K.ricciHessian z + ∑ p, ∑ q, ((K.matrix z)⁻¹ p q) •
        (mderiv Complex.I (e q) K.matrix z*(K.matrix z)⁻¹*
          mderiv (-Complex.I) (e p) K.matrix z) := by
  have he := congrArg (fun M => K.matrix z*M) (K.curvature_contraction hz)
  simp only [Matrix.mul_sum,Matrix.mul_smul] at he
  simp only [K.lower_curvature_formula hz,smul_sub,Finset.sum_sub_distrib] at he
  rw [← mul_assoc,Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.mpr (ne_of_gt (K.positive z hz).det_pos)),one_mul] at he
  exact sub_eq_iff_eq_add.mp he
end KaehlerCalculus.LocalKaehlerField

end
end

end OAI
