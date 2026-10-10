import OAI.MathematicalPhysics.Transonic.Exterior.BarrierSound

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorPolynomial
open Polynomial PowerSeries FixedInterval

lemma residual_neg_eval (sigma kappa d : ℝ) (u : PowerSeries ℝ)
    (hu0 : PowerSeries.coeff 0 u=1)
    (he : Formal.residual sigma kappa (3/5) u=0) (x : ℝ) :
    -(residual (-d/256) sigma kappa (3/5) (reflectedTrunc u d)).eval x=
      x^74*hornerValue (fun i => -(residual (-d/256) sigma kappa (3/5)
        (reflectedTrunc u d)).coeff (i+74)) x 0 220 := by
  have hz : ∀ n<74, (residual (-d/256) sigma kappa (3/5)
      (reflectedTrunc u d)).coeff n=0 := by
    apply residual_lowzero
    · simp only [PowerSeries.coeff_rescale,pow_zero,one_mul]
      exact ExteriorJet.scaledReflected_zero hu0
    · exact scaled_full_equation _ _ _ _ u he
  rw [eval_factor _ (degree_residual _ _ _ _ _ (reflectedTrunc_natDegree u d)) hz,
    hornerValue_sum]
  simp only [Finset.mul_sum,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Nat.zero_add]
  ring

end SepticProfile.ExteriorPolynomial

end
end

end OAI
