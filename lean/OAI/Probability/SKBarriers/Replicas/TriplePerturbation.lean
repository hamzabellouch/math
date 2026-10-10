import Mathlib
import OAI.Probability.SKBarriers.Replicas.MatrixGuerraKernel

namespace OAI

section

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory ProbabilityTheory Set
namespace SK.Analytic

def tripleSymmetricMatrix (a b r q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![a,r,r; r,b,q; r,q,b]

def tripleImbalance : Fin 3 → Fin 3 → ℝ := !![0,1,-1; 1,0,0; -1,0,0]
def tripleQuadraticCorrection : Fin 3 → Fin 3 → ℝ := !![0,0,0; 0,1,-1; 0,-1,1]

def triplePerturbedMatrix (a b r q δ g G : ℝ) : Fin 3 → Fin 3 → ℝ :=
  fun i j => tripleSymmetricMatrix a b r q i j+δ*g*tripleImbalance i j+
    δ^2*G*tripleQuadraticCorrection i j

def tripleGram (r δ q : ℝ) : Fin 3 → Fin 3 → ℝ :=
  !![1,r+δ,r-δ; r+δ,1,q; r-δ,q,1]

def tripleModifiedIncrement (v δ k : ℝ) : Fin 3 → ℝ := ![v,δ*k*v,-δ*k*v]

theorem tripleModifiedIncrement_psd (v δ k : ℝ) :
    Matrix.PosSemidef (Matrix.of (fun i j => tripleModifiedIncrement v δ k i*tripleModifiedIncrement v δ k j)) := by
  simpa only [star_trivial, Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (tripleModifiedIncrement v δ k)

theorem tripleModifiedIncrement_change (v δ k : ℝ) :
    (fun i j => tripleModifiedIncrement v δ k i*tripleModifiedIncrement v δ k j)=
      fun i j => tripleSymmetricMatrix (v^2) 0 0 0 i j+
        δ*k*v^2*tripleImbalance i j+δ^2*k^2*v^2*tripleQuadraticCorrection i j := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tripleModifiedIncrement,tripleSymmetricMatrix,tripleImbalance,tripleQuadraticCorrection] <;> ring

theorem triplePerturbedMatrix_square (a b r q δ g G : ℝ) :
    matrixSquare 3 (triplePerturbedMatrix a b r q δ g G)-
      matrixSquare 3 (tripleSymmetricMatrix a b r q)=
      4*δ^2*g^2+4*δ^2*G*(b-q)+4*δ^4*G^2 := by
  norm_num [matrixSquare,triplePerturbedMatrix,tripleSymmetricMatrix,tripleImbalance,
    tripleQuadraticCorrection,Fin.sum_univ_succ]
  ring

theorem triplePerturbedMatrix_endpoint (r q δ K : ℝ) :
    triplePerturbedMatrix 1 1 r q δ 1 K=
      fun i j => tripleGram r δ q i j+δ^2*K*tripleQuadraticCorrection i j := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [triplePerturbedMatrix,tripleSymmetricMatrix,tripleGram,tripleImbalance,tripleQuadraticCorrection] <;> ring

theorem triplePerturbedMatrix_mismatch (β r q δ K : ℝ) :
    β^2/4*matrixSquare 3 (fun i j => tripleGram r δ q i j-
      triplePerturbedMatrix 1 1 r q δ 1 K i j)=β^2*δ^4*K^2 := by
  rw [triplePerturbedMatrix_endpoint]
  norm_num [matrixSquare,tripleQuadraticCorrection,Fin.sum_univ_succ]
  ring

theorem triplePerturbedMatrix_penalty_step (a b r q g G a' b' r' q' g' G' δ m : ℝ) :
    m*((matrixSquare 3 (triplePerturbedMatrix a' b' r' q' δ g' G')-
      matrixSquare 3 (triplePerturbedMatrix a b r q δ g G))-
      (matrixSquare 3 (tripleSymmetricMatrix a' b' r' q')-
      matrixSquare 3 (tripleSymmetricMatrix a b r q)))=
      4*m*δ^2*(g'^2-g^2)+4*m*δ^2*(G'*(b'-q')-G*(b-q))+4*m*δ^4*(G'^2-G^2) := by
  have H := triplePerturbedMatrix_square a b r q δ g G
  have H' := triplePerturbedMatrix_square a' b' r' q' δ g' G'
  linear_combination m*H'-m*H

theorem triplePerturbedMatrix_penalty_lower {m G G' : ℝ} (hm : 0 ≤ m) (hG : 0 ≤ G) (hGG : G ≤ G')
    (a b r q g a' b' r' q' g' δ : ℝ) :
    4*m*δ^2*(g'^2-g^2)+4*m*δ^2*(G'*(b'-q')-G*(b-q)) ≤
      m*((matrixSquare 3 (triplePerturbedMatrix a' b' r' q' δ g' G')-
      matrixSquare 3 (triplePerturbedMatrix a b r q δ g G))-
      (matrixSquare 3 (tripleSymmetricMatrix a' b' r' q')-
      matrixSquare 3 (tripleSymmetricMatrix a b r q))) := by
  rw [triplePerturbedMatrix_penalty_step]
  have H : 0 ≤ 4*m*δ^4*(G'^2-G^2) := mul_nonneg (by positivity)
    (sub_nonneg.mpr ((sq_le_sq₀ hG (hG.trans hGG)).mpr hGG))
  linarith

end SK.Analytic

end
end

end OAI
