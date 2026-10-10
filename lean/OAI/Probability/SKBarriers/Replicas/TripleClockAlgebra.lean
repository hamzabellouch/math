import Mathlib
import OAI.Probability.SKBarriers.Replicas.TriplePerturbation

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleClockMatrix (a b c r q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![a,r,r; r,b,q; r,q,c]

def tripleClockPerturbed (a b c r q δ g G : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleClockMatrix a b c r q i j+δ*g*tripleImbalance i j+
    δ^2*G*tripleQuadraticCorrection i j

theorem tripleClockMatrix_square (a b c r q : ℝ) :
    matrixSquare 3 (tripleClockMatrix a b c r q)=a^2+b^2+c^2+4*r^2+2*q^2 := by
  norm_num [matrixSquare,tripleClockMatrix,Fin.sum_univ_succ]
  ring

theorem tripleClockPerturbed_square (a b c r q δ g G : ℝ) :
    matrixSquare 3 (tripleClockPerturbed a b c r q δ g G)-
      matrixSquare 3 (tripleClockMatrix a b c r q)=
      4*δ^2*g^2+2*δ^2*G*(b+c-2*q)+4*δ^4*G^2 := by
  norm_num [matrixSquare,tripleClockMatrix,tripleClockPerturbed,tripleImbalance,
    tripleQuadraticCorrection,Fin.sum_univ_succ]
  ring

theorem tripleClockPerturbed_symmetric (a b r q δ g G : ℝ) :
    tripleClockPerturbed a b b r q δ g G=triplePerturbedMatrix a b r q δ g G := rfl

theorem tripleClockPerturbed_singleton (a b c r q δ g G v w : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![v,δ*w,-δ*w] : Fin 3 → ℝ) i*(![v,δ*w,-δ*w] : Fin 3 → ℝ) j)=
      tripleClockPerturbed (a+v^2) b c r q δ (g+v*w) (G+w^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_pair (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,v,v] : Fin 3 → ℝ) i*(![0,v,v] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a (b+v^2) (c+v^2) r (q+v^2) δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail0 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![v,0,0] : Fin 3 → ℝ) i*(![v,0,0] : Fin 3 → ℝ) j)=
      tripleClockPerturbed (a+v^2) b c r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail1 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,v,0] : Fin 3 → ℝ) i*(![0,v,0] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a (b+v^2) c r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_tail2 (a b c r q δ g G v : ℝ) :
    (fun i j => tripleClockPerturbed a b c r q δ g G i j+
      (![0,0,v] : Fin 3 → ℝ) i*(![0,0,v] : Fin 3 → ℝ) j)=
      tripleClockPerturbed a b (c+v^2) r q δ g G := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleClockPerturbed,tripleClockMatrix,tripleImbalance,tripleQuadraticCorrection]
  all_goals ring

theorem tripleClockPerturbed_common (r v : ℝ) :
    (fun i j => tripleClockMatrix r r r r r i j+
      (![v,v,v] : Fin 3 → ℝ) i*(![v,v,v] : Fin 3 → ℝ) j)=
      tripleClockMatrix (r+v^2) (r+v^2) (r+v^2) (r+v^2) (r+v^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [tripleClockMatrix] <;> ring

theorem tripleClockPerturbed_tail_penalty (a b c r q δ g G m v : ℝ) :
    m*(matrixSquare 3 (tripleClockPerturbed (a+v^2) (b+v^2) (c+v^2) r q δ g G)-
      matrixSquare 3 (tripleClockPerturbed a b c r q δ g G))=
    m*((a+v^2)^2-a^2+(b+v^2)^2-b^2+(c+v^2)^2-c^2)+4*m*δ^2*G*v^2 := by
  have H := tripleClockPerturbed_square a b c r q δ g G
  have H' := tripleClockPerturbed_square (a+v^2) (b+v^2) (c+v^2) r q δ g G
  rw [tripleClockMatrix_square] at H H'
  linear_combination m*H'-m*H

theorem tripleClockPerturbed_middle_penalty (a b r δ g G m v w : ℝ) :
    m*(matrixSquare 3 (tripleClockPerturbed (a+v^2) b b r b δ (g+v*w) (G+w^2))-
      matrixSquare 3 (tripleClockPerturbed a b b r b δ g G))=
      m*((a+v^2)^2-a^2)+4*m*δ^2*((g+v*w)^2-g^2)+4*m*δ^4*((G+w^2)^2-G^2) := by
  have H := tripleClockPerturbed_square a b b r b δ g G
  have H' := tripleClockPerturbed_square (a+v^2) b b r b δ (g+v*w) (G+w^2)
  rw [tripleClockMatrix_square] at H H'
  linear_combination m*H'-m*H

theorem tripleClockPerturbed_pair_penalty (a b r δ g G m v : ℝ) :
    m/2*(matrixSquare 3 (tripleClockPerturbed a (b+v^2) (b+v^2) r (b+v^2) δ g G)-
      matrixSquare 3 (tripleClockPerturbed a b b r b δ g G))=
      2*m*((b+v^2)^2-b^2) := by
  have H := tripleClockPerturbed_square a b b r b δ g G
  have H' := tripleClockPerturbed_square a (b+v^2) (b+v^2) r (b+v^2) δ g G
  rw [tripleClockMatrix_square] at H H'
  linear_combination m/2*H'-m/2*H

end SK.Analytic

end
end

end OAI
