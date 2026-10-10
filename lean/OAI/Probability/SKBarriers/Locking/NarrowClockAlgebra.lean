import Mathlib
import OAI.Probability.SKBarriers.Replicas.TripleClockAlgebra

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def narrowClockPerturbed (a b c r q δ g y K : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleClockMatrix a b c r q i j+
    δ*(!![0,g,-g;g,2*y,0;-g,0,-2*y] : Fin 3 → Fin 3 → ℝ) i j+
    δ^2*K*tripleQuadraticCorrection i j

theorem narrowClockPerturbed_pair_zero (a b c r q δ g K : ℝ) :
    narrowClockPerturbed a b c r q δ g 0 K=tripleClockPerturbed a b c r q δ g K := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [narrowClockPerturbed,tripleClockPerturbed,tripleImbalance]

theorem narrowClockPerturbed_square (a b c r q δ g y K : ℝ) :
    matrixSquare 3 (narrowClockPerturbed a b c r q δ g y K)=
      matrixSquare 3 (tripleClockMatrix a b c r q)+4*δ*y*(b-c)+
      δ^2*(4*g^2+8*y^2+2*K*(b+c-2*q))+4*δ^4*K^2 := by
  norm_num [matrixSquare,Fin.sum_univ_succ,narrowClockPerturbed,tripleClockMatrix,tripleQuadraticCorrection]
  ring

theorem narrowClockPerturbed_common (r δ g K v w : ℝ) :
    (fun i j => narrowClockPerturbed r r r r r δ g g K i j+
      (![v,v+δ*w,v-δ*w] : Fin 3 → ℝ) i*(![v,v+δ*w,v-δ*w] : Fin 3 → ℝ) j)=
      narrowClockPerturbed (r+v^2) (r+v^2) (r+v^2) (r+v^2) (r+v^2) δ (g+v*w) (g+v*w) (K+w^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [narrowClockPerturbed,tripleClockMatrix,tripleQuadraticCorrection] <;> ring

theorem narrowClockPerturbed_singleton (a b r δ g y K v w : ℝ) :
    (fun i j => narrowClockPerturbed a b b r b δ g y K i j+
      (![v,δ*w,-δ*w] : Fin 3 → ℝ) i*(![v,δ*w,-δ*w] : Fin 3 → ℝ) j)=
      narrowClockPerturbed (a+v^2) b b r b δ (g+v*w) y (K+w^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [narrowClockPerturbed,tripleClockMatrix,tripleQuadraticCorrection] <;> ring

theorem narrowClockPerturbed_pair (a b r δ g y K v w : ℝ) :
    (fun i j => narrowClockPerturbed a b b r b δ g y K i j+
      (![0,v+δ*w,v-δ*w] : Fin 3 → ℝ) i*(![0,v+δ*w,v-δ*w] : Fin 3 → ℝ) j)=
      narrowClockPerturbed a (b+v^2) (b+v^2) r (b+v^2) δ g (y+v*w) (K+w^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [narrowClockPerturbed,tripleClockMatrix,tripleQuadraticCorrection] <;> ring

theorem narrowClockPerturbed_common_penalty (r δ g K m v w : ℝ) :
    m/3*(matrixSquare 3 (narrowClockPerturbed (r+v^2) (r+v^2) (r+v^2) (r+v^2) (r+v^2)
        δ (g+v*w) (g+v*w) (K+w^2))-matrixSquare 3 (narrowClockPerturbed r r r r r δ g g K))=
      3*m*((r+v^2)^2-r^2)+4*m*δ^2*((g+v*w)^2-g^2)+4*(m/3)*δ^4*((K+w^2)^2-K^2) := by
  rw [narrowClockPerturbed_square,narrowClockPerturbed_square,
    tripleClockMatrix_square,tripleClockMatrix_square]
  ring

theorem narrowClockPerturbed_singleton_penalty (a b r δ g y K m v w : ℝ) :
    m*(matrixSquare 3 (narrowClockPerturbed (a+v^2) b b r b δ (g+v*w) y (K+w^2))-
      matrixSquare 3 (narrowClockPerturbed a b b r b δ g y K))=
      m*((a+v^2)^2-a^2)+4*m*δ^2*((g+v*w)^2-g^2)+4*m*δ^4*((K+w^2)^2-K^2) := by
  rw [narrowClockPerturbed_square,narrowClockPerturbed_square,
    tripleClockMatrix_square,tripleClockMatrix_square]
  ring

theorem narrowClockPerturbed_pair_penalty (a b r δ g y K m v w : ℝ) :
    m/2*(matrixSquare 3 (narrowClockPerturbed a (b+v^2) (b+v^2) r (b+v^2) δ g (y+v*w) (K+w^2))-
      matrixSquare 3 (narrowClockPerturbed a b b r b δ g y K))=
      2*m*((b+v^2)^2-b^2)+4*m*δ^2*((y+v*w)^2-y^2)+4*(m/2)*δ^4*((K+w^2)^2-K^2) := by
  rw [narrowClockPerturbed_square,narrowClockPerturbed_square,
    tripleClockMatrix_square,tripleClockMatrix_square]
  ring

end SK.Analytic

end
end

end OAI
