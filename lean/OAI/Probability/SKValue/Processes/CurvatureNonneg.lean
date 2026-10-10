import Mathlib
import OAI.Probability.SKValue.Coercivity.LiteralCoercivity

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace SKValue
lemma IsDiffusion.curvature_generator_nonneg {W:BrownianSpace} {γ:OrderParameter} {X:ℝ → W.Ω → ℝ}
    (hX:IsDiffusion W γ X) {t:ℝ} (ht:t∈Ioo (0:ℝ) 1):
    0≤∫ z,(iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
      12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
      6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4 ∂W.μ := by
  have hc:=γ.nonneg t ⟨ht.1.le,ht.2⟩
  rcases hc.eq_or_lt with hc|hc
  · rw [←hc]
    simp only [mul_zero,zero_mul,sub_zero,zero_pow (by norm_num: (2:ℕ)≠0),add_zero]
    exact integral_nonneg (fun z ↦ sq_nonneg _)
  · have h:=hX.literal_coercivity ⟨t,ht⟩
    have hn:0≤(1/1000:ℝ)*(∫ z,(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ) := by
      apply mul_nonneg (by norm_num)
      exact integral_nonneg (fun z ↦ by positivity)
    have hn:=hn.trans h
    have he:(fun z ↦ (spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4)=
      (fun z ↦ (γ.coeff t)^2*((iteratedDeriv 3 (deriv (phi W γ t)) (X t z))^2-
        12*γ.coeff t*iteratedDeriv 1 (deriv (phi W γ t)) (X t z)*(iteratedDeriv 2 (deriv (phi W γ t)) (X t z))^2+
        6*(γ.coeff t)^2*(iteratedDeriv 1 (deriv (phi W γ t)) (X t z))^4)) := by
      funext z
      simp only [spatialJet]
      ring
    change 0≤∫ z,(spatialJet (γ.coeff t) (phi W γ t) 3 (X t z))^2-
        12*spatialJet (γ.coeff t) (phi W γ t) 1 (X t z)*(spatialJet (γ.coeff t) (phi W γ t) 2 (X t z))^2+
        6*(spatialJet (γ.coeff t) (phi W γ t) 1 (X t z))^4 ∂W.μ at hn
    rw [he,integral_const_mul] at hn
    exact nonneg_of_mul_nonneg_right hn (sq_pos_of_pos hc)
end SKValue

end

end OAI
