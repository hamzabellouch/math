import OAI.Combinatorics.Progressions.Geometry.PolarizedCoefficientCoordinates
import OAI.Combinatorics.Progressions.Polynomial.BlockMonomialWeight

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem polarizedLog_diagonal (p : F.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    (eval (fun j => x (π j)) (F.polarizedLog π p)).val = blockPolynomialEval π p.val x := by
  apply squarefreePolynomialEquiv.injective
  ext c
  rw [F.polarizedLog_eval_coefficient, blockPolynomialEval_coefficient, blockExponent_weight π c.val x]
  by_cases hc : c.val = 0
  · rw [F.polarizedCoefficient_zero π p c hc]
    have hz : squarefreePolynomialEquiv (0 : F.SquarefreeAlgebra π).val c = 0 :=
      congrFun (map_zero squarefreePolynomialEquiv) c
    rw [hz]
    simp only [smul_zero, hc, blockExponent_zero, hp]
  · rw [F.polarizedCoefficient_self π p c hc]

end Erdos3.MultidegreeLieFiltration

end

end OAI
