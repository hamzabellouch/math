import OAI.NumberTheory.CubicMoment.Estimates.CubePairAsymptotic
import OAI.NumberTheory.CubicMoment.Estimates.PrincipalContribution

namespace OAI

/-! Scaling of the cubic lattice main term in the Poisson formula. -/
noncomputable section
namespace CubicFirstMoment

lemma cube_poisson_scale {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    A/(9*Real.sqrt N)*(1/(3*(A/(27*N))^(1/3:ℝ))) =
      A^(2/3:ℝ)*N^(-(1/6:ℝ))/9 := by
  calc
    _ = (A/(27*Real.sqrt N))/(A/(27*N))^(1/3:ℝ) := by ring
    _ = _ := by rw [principal_cube_prefactor_scale hA hN]; ring

lemma cube_poisson_root {A N : ℝ} (hA : 0 < A) (hN : 0 < N) :
    ((A/(27*N))^(1/3:ℝ))^3 = A/(27*N) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by positivity : (0:ℝ) ≤ A/(27*N))]
  norm_num

end CubicFirstMoment

end

end OAI
